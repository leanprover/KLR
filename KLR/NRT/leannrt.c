/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

// Modified from https://awsdocs-neuron.readthedocs-hosted.com/en/latest/neuron-runtime/nrt-api-guide.html#the-code
#define _GNU_SOURCE // for vasprintf

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include <lean/lean.h>
#include <nrt/nrt.h>
#include <nrt/nrt_experimental.h>

#define DEBUG_ENABLED 0

#if DEBUG_ENABLED
#define DEBUG_PRINTF(...) fprintf(stderr, __VA_ARGS__)
#else
#define DEBUG_PRINTF(...) ((void)0)
#endif

#define P_ERR(...) fprintf(stderr, __VA_ARGS__)

#define FILENAME_MAX_LENGTH 280

lean_object* io_err(const char* fmt, ...) {
  char* msg = NULL;
  va_list args;
  va_start(args, fmt);
  const int bytes = vasprintf(&msg, fmt, args);
  va_end(args);
  lean_object *lean_msg;
  if (bytes < 0) {
    P_ERR("couldn't format error message: %s", fmt);
    lean_msg = lean_mk_string(fmt);
  } else {
    P_ERR(msg);
    lean_msg = lean_mk_string(msg); // copies
    free(msg);
  }
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_msg));
}

typedef struct {
  const char *name;
  size_t size;
  void *data;
} input_tensor_info_t;

typedef struct {
  input_tensor_info_t *entries;
  int entry_count;
} input_tensor_info_array_t;

// Return NULL on failure (nb: not MAP_FAILED)
void *mmap_file(const char *filepath, size_t *size) {
  assert(filepath != NULL);
  assert(size != NULL);
  int fd = open(filepath, O_RDONLY);
  if (fd < 0) { return NULL; }
  struct stat sb;
  if (fstat(fd, &sb) != 0) { close(fd); return NULL; }
  *size = sb.st_size;
  void *res = mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  return res;
}

/*
Run a NEFF on input files, generating output files.
The input and output files are the raw bytes representing a tensor.
The dtype and shape of the tensors are found in the NEFF.

This function does not clean up resources in the exceptional case.
The Lean program should not attempt to recover from a NRT IO error.

Lean types:
- neff_file_name : String
- input_tensorfiles : Array TensorFile
- output : IO (Array TensorFile)
*/
LEAN_EXPORT lean_object *lean_nrt_execute(b_lean_obj_arg neff_file_name, b_lean_obj_arg input_tensorfiles) {
  assert(lean_is_string(neff_file_name));
  assert(lean_is_array(input_tensorfiles));
  lean_object* lean_result = NULL;

  NRT_STATUS nrt_result;
  bool error = false;

  DEBUG_PRINTF("Mapping NEFF\n");
  size_t neff_size = -1;
  const char *c_neff_file_name = lean_string_cstr(neff_file_name);
  assert(c_neff_file_name != NULL);
  void *neff_data = mmap_file(c_neff_file_name, &neff_size); // Needs munmap
  if (neff_data == NULL) { 
    lean_result = io_err("Unable to map NEFF file: %s", c_neff_file_name); 
    goto cleanup;
  }

  DEBUG_PRINTF("Allocating tensors\n");
  size_t input_tensorfile_count = lean_array_size(input_tensorfiles);
  input_tensor_info_array_t input_tensor_info_array = {0};
  input_tensor_info_array.entries = malloc(input_tensorfile_count * sizeof(input_tensor_info_t)); // Needs free
  if (input_tensor_info_array.entries == NULL) { 
    lean_result = io_err("Can't malloc tensors"); 
    goto cleanup;
  }
  input_tensor_info_array.entry_count = input_tensorfile_count;
  lean_object **input_tensorfile_array = lean_array_cptr(input_tensorfiles);
  assert(input_tensorfile_array != NULL);
  for (int i = 0; i < input_tensorfile_count; i++) {
    input_tensor_info_t *current_input = &input_tensor_info_array.entries[i];
    lean_object *current_tensorfile = input_tensorfile_array[i];
    lean_object *current_name = lean_ctor_get(current_tensorfile, 0);
    lean_object *current_file = lean_ctor_get(current_tensorfile, 1);
    const char *c_current_file = lean_string_cstr(current_file);
    void* input_data = mmap_file(c_current_file, &current_input->size); // Needs munmap
    if (input_data == NULL) {
      lean_result = io_err("Unable to mmap inputs file");
      goto cleanup;
    }
    current_input->name = lean_string_cstr(current_name);
    current_input->data = input_data;
  }

  DEBUG_PRINTF("Initializing runtime\n");
  nrt_result = nrt_init(NRT_FRAMEWORK_TYPE_NO_FW, "", ""); // needs nrt_close
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Can't initialize runtime");
    goto cleanup;
  } 

  DEBUG_PRINTF("Loading NEFF\n");
  nrt_model_t *model = NULL;
  nrt_result = nrt_load(neff_data, neff_size, -1, -1, &model); // Needs nrt_unload
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Can't load NEFF");
    goto cleanup;
  }

  DEBUG_PRINTF("Getting IO tensor information\n");
  nrt_tensor_info_array_t *tensor_info_array = NULL;
  nrt_result = nrt_get_model_tensor_info(model, &tensor_info_array);
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Unable to get model tensor information\n");
    goto cleanup;
  }
  assert(tensor_info_array != NULL);
  assert(tensor_info_array->tensor_array != NULL);

  DEBUG_PRINTF("Creating I/O data (%ld tensors)\n", tensor_info_array->tensor_count);
  nrt_tensor_set_t *input_tensor_set = NULL;
  nrt_tensor_set_t *output_tensor_set = NULL;

  nrt_result = nrt_allocate_tensor_set(&input_tensor_set);
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Unable to allocate input tensorset");
    goto cleanup;
  }
  nrt_result = nrt_allocate_tensor_set(&output_tensor_set);
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Unable to allocate output tensorset");
    goto cleanup;
  }

  for (int i = 0; i < tensor_info_array->tensor_count; i++) {
    nrt_tensor_info_t *tensor_info = &tensor_info_array->tensor_array[i];
    assert(tensor_info != NULL);
    nrt_tensor_t *tensor = NULL;
    nrt_result = nrt_tensor_allocate(NRT_TENSOR_PLACEMENT_DEVICE, 0, tensor_info->size, tensor_info->name, &tensor);
    if (nrt_result != NRT_SUCCESS) {
      lean_result = io_err("Unable to allocate tensor");
      goto cleanup;
    }
    nrt_tensor_set_t *set = tensor_info->usage == NRT_TENSOR_USAGE_INPUT ? input_tensor_set : output_tensor_set;
    nrt_add_tensor_to_tensor_set(set, tensor_info->name, tensor);
    if (nrt_result != NRT_SUCCESS) {
      lean_result = io_err("Unable to add tensor to set");
      goto cleanup;
    }
  }

  DEBUG_PRINTF("Loading input files to input_tensor_set\n");
  for (int i = 0; i < tensor_info_array->tensor_count; i++) {
    nrt_tensor_info_t *tensor_info = &tensor_info_array->tensor_array[i];
    assert(tensor_info != NULL);
    nrt_tensor_t *tensor = NULL;
    if (tensor_info->usage != NRT_TENSOR_USAGE_INPUT) { continue; }
    nrt_result = nrt_get_tensor_from_tensor_set(input_tensor_set, tensor_info->name, &tensor);
    if (nrt_result != NRT_SUCCESS) {
      lean_result = io_err("Unable to read tensor");
      goto cleanup;
    }
    for (int j = 0; j < input_tensor_info_array.entry_count; j++) {
      input_tensor_info_t input_tensor = input_tensor_info_array.entries[j];
      if (strcmp(input_tensor.name, tensor_info->name) != 0) {
        continue;
      }
      if (input_tensor.size != tensor_info->size) {
        lean_result = io_err("Input file for tensor %s has incorrect size %lu, expected %lu", 
          tensor_info->name, input_tensor_info_array.entries[j].size, tensor_info->size);
        goto cleanup;
      }
      nrt_result = nrt_tensor_write(tensor, input_tensor.data, 0, tensor_info->size);
      if (nrt_result != NRT_SUCCESS) {
        lean_result = io_err("Unable to write content to input tensor");
        goto cleanup;
      }
      break; // we found the tensor we wanted
    }
  }  

  DEBUG_PRINTF("Executing model\n");
  nrt_result = nrt_execute(model, input_tensor_set, output_tensor_set);
  if (nrt_result != NRT_SUCCESS) {
    lean_result = io_err("Error during execution");
    goto cleanup;
  } else {
    DEBUG_PRINTF("Execution successful!\n");
  }

  DEBUG_PRINTF("Saving outputs\n");
  lean_object *output_tensorfiles;
  output_tensorfiles = lean_mk_empty_array();
  for (int i = 0; i < tensor_info_array->tensor_count; i++) {
    nrt_tensor_info_t *tensor_info = &tensor_info_array->tensor_array[i];
    assert(tensor_info != NULL);
    nrt_tensor_t *tensor = NULL;
    if (tensor_info->usage != NRT_TENSOR_USAGE_OUTPUT) { continue; }
    void *tensor_data = malloc(tensor_info->size); // needs free
    if (tensor_data == NULL) { 
      lean_result = io_err("Can't malloc tensordata"); 
      goto cleanup;
    }
    nrt_result = nrt_get_tensor_from_tensor_set(output_tensor_set, tensor_info->name, &tensor);
    if (nrt_result != NRT_SUCCESS) { 
      lean_result = io_err("Can't get tensor from set"); 
      goto cleanup;
    }
    nrt_result = nrt_tensor_read(tensor, tensor_data, 0, tensor_info->size);
    if (nrt_result != NRT_SUCCESS) { 
      lean_result = io_err("Can't read tensor"); 
      goto cleanup;
    }
    static char filename[FILENAME_MAX_LENGTH];
    snprintf(filename, FILENAME_MAX_LENGTH, "%s.out", tensor_info->name);
    lean_object *tensor_file = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tensor_file, 0, lean_mk_string(tensor_info->name));
    lean_ctor_set(tensor_file, 1, lean_mk_string(filename));
    output_tensorfiles = lean_array_push(output_tensorfiles, tensor_file);
    int fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) { 
      lean_result = io_err("Can't open output file");
      free(tensor_data);
      goto cleanup;
    }
    if (write(fd, tensor_data, tensor_info->size) != tensor_info->size) { 
      lean_result = io_err("Can't write full output file");
      close(fd);
      free(tensor_data);
      goto cleanup;
    }
    close(fd);
    free(tensor_data);
  }

  lean_result = lean_io_result_mk_ok(output_tensorfiles);

  cleanup:

  DEBUG_PRINTF("Unloading model\n");
  if (model != NULL) {
    nrt_result = nrt_unload(model);
    if (nrt_result != NRT_SUCCESS) {
      P_ERR("Error unloading model\n");
    }
  }
  if (tensor_info_array != NULL) {
    DEBUG_PRINTF("Freeing tensors\n");
    for (int i = 0; i < tensor_info_array->tensor_count; i++) {
      nrt_tensor_info_t *tensor_info = &tensor_info_array->tensor_array[i];
      assert(tensor_info != NULL);
      nrt_tensor_t *tensor = NULL;
      nrt_tensor_set_t *set = tensor_info->usage == NRT_TENSOR_USAGE_INPUT ? input_tensor_set : output_tensor_set;
      nrt_result = nrt_get_tensor_from_tensor_set(set, tensor_info->name, &tensor);
      if (nrt_result != NRT_SUCCESS) {
        P_ERR("Unable to get tensor from set\n");
      } else {
        nrt_tensor_free(&tensor);
      }
    }
  }
  if (input_tensor_set != NULL) {
    nrt_destroy_tensor_set(&input_tensor_set);
  }
  if (output_tensor_set != NULL) {
    nrt_destroy_tensor_set(&output_tensor_set);
  }
  if (tensor_info_array != NULL) {
    if (nrt_free_model_tensor_info(tensor_info_array) != NRT_SUCCESS) {
      P_ERR("Error freeing tensor info\n");
    }
  }
  for (int i = 0; i < input_tensor_info_array.entry_count; i++) {
    void* data = input_tensor_info_array.entries[i].data;
    if (data != NULL) {
      int n = munmap(data, input_tensor_info_array.entries[i].size);
      if (n != 0) { P_ERR("Error freeing input tensor\n"); };
    }
  }
  free(input_tensor_info_array.entries);
  DEBUG_PRINTF("Cleaning up the runtime\n");
  nrt_close();

  if (neff_data != NULL) {
    munmap(neff_data, neff_size);
  }

  return lean_result;
}
