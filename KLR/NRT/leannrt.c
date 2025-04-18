/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

// Modified from https://awsdocs-neuron.readthedocs-hosted.com/en/latest/neuron-runtime/nrt-api-guide.html#the-code

#include <stdbool.h>
#include <nrt/nrt.h>
#include <nrt/nrt_experimental.h>
#include <lean/lean.h>

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <errno.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <pthread.h>
#include <fcntl.h>
#include <stdint.h>
#include <unistd.h>

#define DEBUG_ENABLED 0

#if DEBUG_ENABLED
    #define DPRINTF(...) fprintf(stderr, __VA_ARGS__)
#else
    #define DPRINTF(...) ((void)0)
#endif

#define P_ERR(...) fprintf(stderr, __VA_ARGS__)

// Function to mmap a file in the application's memory space,
// it will return a pointer to the mmapped memory and the size
// of the mmapped data will be written to *size
void *mmap_file(const char *filepath, size_t *size) {
    struct stat sb;
    int fd = open(filepath, O_RDONLY);
    if (fd < 0 || fstat(fd, &sb) != 0) {
        P_ERR("Unable to open %s: %s\n", filepath, strerror(errno));
        return MAP_FAILED;
    }
    *size = sb.st_size;
    return mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
}

#define CHECK_RESULT(res, expected, ...)    \
    if (res != expected) {                  \
        fprintf(stderr, __VA_ARGS__);       \
        exit(-1);                           \
    }

// struct used to load input tensors from files
typedef struct {
    const char *name;
    size_t size;
    void *data;
} input_tensor_info_t;

// simple container for input_tensor_info_t
typedef struct {
    input_tensor_info_t *entries;
    int entry_count;
} input_tensor_info_array_t;

// Allocate tensorsets and tensors based on the info_array and returns a valid tensorset in out_tset
// containing all the newly allocated tensors
NRT_STATUS allocate_tensors(nrt_tensor_info_array_t *info_array, nrt_tensor_usage_t usage_type, nrt_tensor_set_t **out_tset) {
    NRT_STATUS result;
    int tensor_idx;
    nrt_tensor_info_t *tensor_info = NULL;
    nrt_tensor_t *tensor = NULL;

    // We allocate a nrt_tensor_set which acts as a containers for nrt_tensors
    result = nrt_allocate_tensor_set(out_tset);
    if (result != NRT_SUCCESS) {
        P_ERR("Couldn't allocate %s tensorset\n", usage_type == NRT_TENSOR_USAGE_INPUT ? "input" : "output");
    }

    for (tensor_idx = 0; tensor_idx < info_array->tensor_count; tensor_idx++) {
        tensor_info = &info_array->tensor_array[tensor_idx];
        if (tensor_info->usage != usage_type) {
            continue;
        }
        // Allocate the tensor with the name and size found in tensor_info_array
        result = nrt_tensor_allocate(NRT_TENSOR_PLACEMENT_DEVICE, 0, tensor_info->size,
                                     tensor_info->name, &tensor);
        if (result != NRT_SUCCESS) {
            P_ERR("Couldn't allocate tensor %s\n", tensor_info->name);
            return result;
        }
        // Finally add the tensors to the newly allocated tensor set
        result = nrt_add_tensor_to_tensor_set(*out_tset, tensor_info->name, tensor);
        if (result != NRT_SUCCESS) {
            P_ERR("Couldn't add tensor %s to tensorset\n", tensor_info->name);
            return result;
        }
    }
    return NRT_SUCCESS;
}

// Tensor iterator handler - returns false if the iteration needs to stop
typedef bool (*tensor_handler)(nrt_tensor_t *, nrt_tensor_info_t *, NRT_STATUS *, void *);

// Iterates through all the tensors in the given tensorset, based on the data in info_array for the given usage_type
// and calls the handler function with the provided args pointer
// Will return the first error returned by a handler
NRT_STATUS iterate_tensors(nrt_tensor_set_t *tset, nrt_tensor_info_array_t *info_array, nrt_tensor_usage_t usage_type,
                           tensor_handler handler, void *args) {
    NRT_STATUS result = NRT_SUCCESS;
    NRT_STATUS final_result = NRT_SUCCESS;
    int tensor_idx;
    nrt_tensor_info_t *tensor_info = NULL;
    nrt_tensor_t *tensor = NULL;

    for (tensor_idx = 0; tensor_idx < info_array->tensor_count; tensor_idx++) {
        tensor_info = &info_array->tensor_array[tensor_idx];
        if (tensor_info->usage != usage_type) {
            continue;
        }
        result = nrt_get_tensor_from_tensor_set(tset, tensor_info->name, &tensor);
        if (result != NRT_SUCCESS) {
            P_ERR("Tensor %s not found in tensor set\n", tensor_info->name);
            continue;
        }
        result = NRT_SUCCESS;
        if ((*handler)(tensor, tensor_info, &result, args) == false) {
            return result;
        }
        if (final_result == NRT_SUCCESS && result != final_result) {
            final_result = result;
        }
    }
    return final_result;
}

// Tensor iteration handler that checks if a tensor has an input file associated with it
// based on the CLI args
bool handler_load_inputs(nrt_tensor_t *tensor, nrt_tensor_info_t *tensor_info, NRT_STATUS *result, void* args) {
    NRT_STATUS res;
    int idx;
    input_tensor_info_array_t *info_array = (input_tensor_info_array_t *)args;
    bool input_found = false;

    for (idx = 0; idx < info_array->entry_count; idx++) {
        if (strcmp(info_array->entries[idx].name, tensor_info->name) != 0) {
            continue;
        }
        if (info_array->entries[idx].size != tensor_info->size) {
            P_ERR("Input file for tensor %s has incorrect size %lu, expected %lu\n",
                  tensor_info->name, info_array->entries[idx].size, tensor_info->size);
            break;
        }
        res = nrt_tensor_write(tensor, info_array->entries[idx].data, 0, tensor_info->size);
        if (res != NRT_SUCCESS) {
            P_ERR("Unable to write content to input tensor %s\n", tensor_info->name);
        } else {
            input_found = true;
        }
    }
    if (!input_found) {
        P_ERR("Input tensor %s will be zero-filled\n", tensor_info->name);
    }
    *result = NRT_SUCCESS;
    return true;
}

// Tensor iteration handler that saves outputs
bool handler_save_outputs(nrt_tensor_t *tensor, nrt_tensor_info_t *tensor_info, NRT_STATUS *result, void* args) {
    static char filename[280];

    lean_object **output_array = (lean_object**) args;

    if (*output_array == NULL) {
        *output_array = lean_mk_empty_array();
    }

    if (!lean_is_array(*output_array)) {
        P_ERR("output_array is not an array");
        exit(-1);
    }

    int fd;

    // Allocating a buffer large enough to read the entire tensor
    void *tensor_data = malloc(tensor_info->size);

    *result = NRT_SUCCESS;
    if (tensor_data == NULL) {
        P_ERR("Unable to allocate memory for saving output tensor %s\n", tensor_info->name);
        *result = NRT_FAILURE;
        return true;
    }

    // Reading the tensor to the newly allocated buffer
    *result = nrt_tensor_read(tensor, tensor_data, 0, tensor_info->size);
    if (*result != NRT_SUCCESS) {
        P_ERR("Unable to read tensor %s\n", tensor_info->name);
        free(tensor_data);
        return true;
    }

    // Saving the tensor to a file
    snprintf(filename, 280, "%s.out", tensor_info->name);

    lean_object* tensor_file = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tensor_file, 0, lean_mk_string(tensor_info->name));
    lean_ctor_set(tensor_file, 1, lean_mk_string(filename));

    *output_array = lean_array_push(*output_array, tensor_file);

    fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) {
        P_ERR("Unable to open %s for writing\n", filename);
        free(tensor_data);
        *result = NRT_FAILURE;
        return true;
    }
    if (write(fd, tensor_data, tensor_info->size) != tensor_info->size) {
        *result = NRT_FAILURE;
        P_ERR("Unable to write tensor %s contents to file %s\n", tensor_info->name, filename);
    }
    close(fd);

    free(tensor_data);

    return true;
}

// Tensor iteration handler that deallocates tensors
bool handler_free_tensor(nrt_tensor_t *tensor, nrt_tensor_info_t *tensor_info, NRT_STATUS *result, void* args) {
    *result = NRT_SUCCESS;
    nrt_tensor_free(&tensor);
    return true;
}

/*
Run a NEFF on input files, generating output files.
The input and output files are the raw bytes representing a tensor.
The dtype and shape of the tensors are found in the NEFF.

Lean types:
- neff_file_name : String
- input_tensorfiles : Array TensorFile
- output : IO (Array TensorFile)
*/
LEAN_EXPORT lean_object* lean_nrt_execute(lean_obj_arg neff_file_name, lean_obj_arg input_tensorfiles) {
    NRT_STATUS result;
    void *neff_data = NULL;
    size_t neff_size = 0;
    void *input_data = NULL;
    input_tensor_info_array_t input_tensor_info_array = {0};

    nrt_model_t *model = NULL;
    nrt_tensor_set_t *inputs = NULL;
    nrt_tensor_set_t *outputs = NULL;

    nrt_tensor_t *tensor = NULL;
    nrt_tensor_info_array_t *tensor_info_array = NULL;

    const char* c_neff_file_name = NULL; 
    size_t input_tensorfile_count = 0;
    lean_object** input_tensorfile_array = NULL;

    if (!lean_is_string(neff_file_name)) {
        P_ERR("neff_file_name is not a Lean String\n");
        exit(-1);
    }

    c_neff_file_name = lean_string_cstr(neff_file_name);

    if (!lean_is_array(input_tensorfiles)) {
        P_ERR("input_tensorfiles is not a Lean Array\n");
        exit(-1);
    }

    input_tensorfile_count = lean_array_size(input_tensorfiles);
    input_tensorfile_array = lean_array_cptr(input_tensorfiles);

    // Try mmapping the NEFF file first, so we can fail fast if not found or
    // mmap fails
    neff_data = mmap_file(c_neff_file_name, &neff_size);
    if (neff_data == MAP_FAILED) {
        P_ERR("Unable to map file %s\n", c_neff_file_name);
        exit(-1);
    }

    // mmap input tensor files (if any provided) and fill the input_tensor_info array
    input_tensor_info_array.entries = malloc(input_tensorfile_count * sizeof(input_tensor_info_t));
    input_tensor_info_array.entry_count = input_tensorfile_count;
    for (int i = 0; i < input_tensorfile_count; i++) {
        input_tensor_info_t *current_input = &input_tensor_info_array.entries[i];
        lean_object* current_tensorfile = input_tensorfile_array[i];
        lean_object* current_name = lean_ctor_get(current_tensorfile, 0);
        if (!lean_is_string(current_name)) {
            P_ERR("Input tensor name %d is not a Lean String\n", i);
            exit(-1);
        }
        lean_object* current_file = lean_ctor_get(current_tensorfile, 1);
        if (!lean_is_string(current_file)) {
            P_ERR("Input tensor file %d is not a Lean String\n", i);
            exit(-1);
        }
        const char* c_current_file = lean_string_cstr(current_file);
        input_data = mmap_file(c_current_file, &current_input->size);
        if (input_data == MAP_FAILED) {
            P_ERR("Unable to mmap inputs file %s\n", c_current_file);
            continue;
        }
        current_input->name = lean_string_cstr(current_name);
        current_input->data = input_data;
    }

    // Before calling any nrt API, nrt_init must be called
    // Since this is not running as part of a framework, the correct parameter for 'framework' is
    // NRT_FRAMEWORK_TYPE_NO_FW and the others can be empty strings
    result = nrt_init(NRT_FRAMEWORK_TYPE_NO_FW, "", "");
    CHECK_RESULT(result, NRT_SUCCESS, "NRTLIB could not be initialized, error: %d\n", (int)result);

    // Loading the NEFF
    DPRINTF("Loading NEFF\n");
    result = nrt_load(neff_data, neff_size, -1, -1, &model);
    CHECK_RESULT(result, NRT_SUCCESS, "Unable to load NEFF\n");

    // In order to allocate tensors, first we need to call nrt_get_model_tensor_info which
    // will give us the model tensors' names and sizes in tensor_info_array
    DPRINTF("Getting IO tensor information\n");
    result = nrt_get_model_tensor_info(model, &tensor_info_array);
    CHECK_RESULT(result, NRT_SUCCESS, "Unable to get model tensor information\n");

    // Allocating tensors
    DPRINTF("Creating I/O data (%ld tensors)\n", tensor_info_array->tensor_count);
    result = allocate_tensors(tensor_info_array, NRT_TENSOR_USAGE_INPUT, &inputs);
    CHECK_RESULT(result, NRT_SUCCESS, "Error allocating input tensors\n");
    result = allocate_tensors(tensor_info_array, NRT_TENSOR_USAGE_OUTPUT, &outputs);
    CHECK_RESULT(result, NRT_SUCCESS, "Error allocating input tensors\n");

    // Loading input files (if provided)
    iterate_tensors(inputs, tensor_info_array, NRT_TENSOR_USAGE_INPUT, handler_load_inputs,
                    (void*) &input_tensor_info_array);

    // Executing model using the tensors in the inputs tensorset and writing the outputs to the tensors
    // in the outputs tensorset
    result = nrt_execute(model, inputs, outputs);
    CHECK_RESULT(result, NRT_SUCCESS, "Error during model execution: %d\n", result);

    // Saving outputs to files
    lean_object *output_tensorfiles = NULL;

    result = iterate_tensors(outputs, tensor_info_array, NRT_TENSOR_USAGE_OUTPUT, handler_save_outputs, &output_tensorfiles);
    if (result != NRT_SUCCESS) {
        P_ERR("Error saving outputs to files\n");
    }

    // Unloading the model
    result = nrt_unload(model);
    if (result != NRT_SUCCESS) {
        P_ERR("Unable to unload NEFF\n");
    }

    DPRINTF("Freeing tensors\n");
    iterate_tensors(inputs, tensor_info_array, NRT_TENSOR_USAGE_INPUT, handler_free_tensor, NULL);
    iterate_tensors(outputs, tensor_info_array, NRT_TENSOR_USAGE_OUTPUT, handler_free_tensor, NULL);

    nrt_destroy_tensor_set(&inputs);
    nrt_destroy_tensor_set(&outputs);

    DPRINTF("Deallocating model tensor info\n");
    // We are done with the tensor_info_array, we can dispose of it
    nrt_free_model_tensor_info(tensor_info_array);

    DPRINTF("Deallocating inputs tensor info\n");
    // Unmapping the input files
    for (int i = 0; i < input_tensor_info_array.entry_count; i++) {
        munmap(input_tensor_info_array.entries[i].data, input_tensor_info_array.entries[i].size);
    }
    if (input_tensor_info_array.entries) {
        free(input_tensor_info_array.entries);
    }

    // Clean-up the runtime
    DPRINTF("Cleaning up the runtime\n");
    nrt_close();

    DPRINTF("DONE\n");
    return lean_io_result_mk_ok(output_tensorfiles);
}
