/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

#define _GNU_SOURCE // for vasprintf

#include <lean/lean.h>
#include <stdarg.h>
#include <stdio.h>   // for printf
#include <stdlib.h>  // for malloc, realloc, free
#include <string.h>
#include <archive.h>
#include <archive_entry.h>

#include "lean_util.h"

#define DEBUG_ENABLED 0

#if DEBUG_ENABLED
#define DEBUG_PRINTF(...) fprintf(stderr, __VA_ARGS__); fflush(stderr);
#else
#define DEBUG_PRINTF(...) ((void)0)
#endif

lean_object* create_archive_entry(const char* filename, uint8_t* data, size_t size) {
  lean_object* entry = lean_alloc_ctor(0, 2, 0);
  lean_object* lean_filename = lean_mk_string(filename);
  lean_object* lean_content = lean_alloc_sarray(1, size, size);
  memcpy(lean_sarray_cptr(lean_content), data, size);
  lean_ctor_set(entry, 0, lean_filename);
  lean_ctor_set(entry, 1, lean_content);
  return entry;
}

struct buffer_data {
  char* buffer;
  size_t size;
  size_t used;
};

// Return type changed from int to la_ssize_t to match archive_write_callback type
static la_ssize_t write_callback(struct archive *a, void *client_data, const void *buffer, size_t length) {
  struct buffer_data *data = (struct buffer_data*)client_data;

  // Check if we need to expand the buffer
  if (data->used + length > data->size) {
    size_t new_size = data->size * 2;
    if (new_size < data->used + length) {
      new_size = data->used + length + 65536; // Ensure enough space plus some extra
    }

    DEBUG_PRINTF("Expanding buffer from %zu to %zu bytes\n", data->size, new_size);

    char* new_buffer = (char*)realloc(data->buffer, new_size);
    if (new_buffer == NULL) {
      return -1; // Error code for archive callbacks
    }

    data->buffer = new_buffer;
    data->size = new_size;
  }

  memcpy(data->buffer + data->used, buffer, length);
  data->used += length;
  return length;
}

LEAN_EXPORT lean_object* lean_archive_create_tar(lean_object* entries) {
  struct archive* a;
  struct archive_entry* entry;
  struct buffer_data data;
  int r;

  // Initialize with a reasonable starting size
  data.size = 65536;
  data.used = 0;
  data.buffer = (char*)malloc(data.size);
  if (data.buffer == NULL) {
    return io_err("Failed to allocate memory for archive buffer");
  }

  a = archive_write_new();
  archive_write_set_format_pax_restricted(a); // Use tar format

  // Use our custom write callback that can expand the buffer
  r = archive_write_open(a, &data, NULL, write_callback, NULL);
  if (r != ARCHIVE_OK) {
    free(data.buffer);
    archive_write_free(a);
    return io_err("Failed to open archive for writing: %s", archive_error_string(a));
  }

  lean_object* curr = entries;
  while (!lean_is_scalar(curr)) {
    lean_object* head = lean_ctor_get(curr, 0);
    curr = lean_ctor_get(curr, 1);

    lean_object* filename_obj = lean_ctor_get(head, 0);
    const char* filename = lean_string_cstr(filename_obj);

    lean_object* content_obj = lean_ctor_get(head, 1);

    size_t content_size = lean_sarray_size(content_obj);
    uint8_t* content = lean_sarray_cptr(content_obj);

    entry = archive_entry_new();
    archive_entry_set_pathname(entry, filename);
    archive_entry_set_size(entry, content_size);
    archive_entry_set_filetype(entry, AE_IFREG);
    archive_entry_set_perm(entry, 0644);

    r = archive_write_header(a, entry);
    if (r != ARCHIVE_OK) {
      archive_entry_free(entry);
      archive_write_free(a);
      free(data.buffer);
      return io_err("Failed to write archive header: %s", archive_error_string(a));
    }

    r = archive_write_data(a, content, content_size);
    if (r < 0) {
      archive_entry_free(entry);
      archive_write_free(a);
      free(data.buffer);
      return io_err("Failed to write archive data: %s", archive_error_string(a));
    }

    archive_entry_free(entry);
  }

  r = archive_write_close(a);
  if (r != ARCHIVE_OK) {
    archive_write_free(a);
    free(data.buffer);
    return io_err("Failed to close archive: %s", archive_error_string(a));
  }

  r = archive_write_free(a);
  if (r != ARCHIVE_OK) {
    free(data.buffer);
    return io_err("Failed to free archive: %s", archive_error_string(a));
  }

  DEBUG_PRINTF("Final archive size: %zu bytes\n", data.used);

  lean_object* result = lean_alloc_sarray(1, data.used, data.used);
  memcpy(lean_sarray_cptr(result), data.buffer, data.used);

  free(data.buffer);
  return result;
}

LEAN_EXPORT lean_object* lean_archive_extract_tar(lean_object* bytes) {
  struct archive* a;
  struct archive_entry* entry;
  int r;

  // Debug: Check if bytes is an sarray
  if (!lean_is_sarray(bytes)) {
    return io_err("Expected bytes to be an sarray, but it's not");
  }

  uint8_t* data = lean_sarray_cptr(bytes);
  size_t size = lean_sarray_size(bytes);

  a = archive_read_new();
  archive_read_support_format_all(a);
  archive_read_support_filter_all(a);

  r = archive_read_open_memory(a, data, size);
  if (r != ARCHIVE_OK) {
    archive_read_free(a);
    return io_err("Failed to open archive: %s", archive_error_string(a));
  }

  lean_object* result = lean_box(0); // Empty list

  while (archive_read_next_header(a, &entry) == ARCHIVE_OK) {
    const char* pathname = archive_entry_pathname(entry);
    size_t entry_size = archive_entry_size(entry);

    // Skip directories
    if (archive_entry_filetype(entry) != AE_IFREG) {
      archive_read_data_skip(a);
      continue;
    }

    uint8_t* file_data = (uint8_t*)malloc(entry_size);
    if (file_data == NULL) {
      archive_read_free(a);
      return io_err("Failed to allocate memory for file data");
    }

    size_t bytes_read = archive_read_data(a, file_data, entry_size);
    if (bytes_read != entry_size) {
      free(file_data);
      archive_read_free(a);
      return io_err("Failed to read file data: %s", archive_error_string(a));
    }

    lean_object* archive_entry_obj = create_archive_entry(pathname, file_data, entry_size);
    free(file_data);

    lean_object* new_cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(new_cell, 0, archive_entry_obj);
    lean_ctor_set(new_cell, 1, result);
    result = new_cell;
  }

  r = archive_read_free(a);
  if (r != ARCHIVE_OK) {
    return io_err("Failed to free archive: %s", archive_error_string(a));
  }

  // Reverse the list to maintain original order
  lean_object* reversed = lean_box(0);
  lean_object* curr = result;

  while (!lean_is_scalar(curr)) {
    lean_object* head = lean_ctor_get(curr, 0);
    lean_object* tail = lean_ctor_get(curr, 1);

    lean_object* new_cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(new_cell, 0, head);
    lean_ctor_set(new_cell, 1, reversed);

    reversed = new_cell;
    curr = tail;
  }

  return reversed;
}
