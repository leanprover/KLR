/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

#define _GNU_SOURCE // for vasprintf

#include <lean/lean.h>
#include <stdarg.h>
#include <string.h>
#include <archive.h>
#include <archive_entry.h>

#include "lean_util.h"

lean_object* create_archive_entry(const char* filename, uint8_t* data, size_t size) {
  lean_object* entry = lean_alloc_ctor(0, 2, 0);
  lean_object* lean_filename = lean_mk_string(filename);
  lean_object* lean_content = lean_alloc_sarray(1, size, size);
  memcpy(lean_sarray_cptr(lean_content), data, size);
  
  lean_ctor_set(entry, 0, lean_filename);
  lean_ctor_set(entry, 1, lean_content);
  
  return entry;
}

// Create a tar archive from a list of file entries
LEAN_EXPORT lean_object* lean_archive_create_tar(lean_object* entries) {
  struct archive* a;
  struct archive_entry* entry;
  char* buff;
  size_t buffsize = 65536;
  size_t used = 0;
  int r;

  buff = (char*)malloc(buffsize);
  if (buff == NULL) {
    return io_err("Failed to allocate memory for archive buffer");
  }

  a = archive_write_new();
  archive_write_set_format_pax_restricted(a); // Use tar format
  archive_write_open_memory(a, buff, buffsize, &used);

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
      free(buff);
      return io_err("Failed to write archive header: %s", archive_error_string(a));
    }
    
    r = archive_write_data(a, content, content_size);
    if (r < 0) {
      archive_entry_free(entry);
      archive_write_free(a);
      free(buff);
      return io_err("Failed to write archive data: %s", archive_error_string(a));
    }
    
    archive_entry_free(entry);
  }
  
  r = archive_write_close(a);
  if (r != ARCHIVE_OK) {
    archive_write_free(a);
    free(buff);
    return io_err("Failed to close archive: %s", archive_error_string(a));
  }
  
  r = archive_write_free(a);
  if (r != ARCHIVE_OK) {
    free(buff);
    return io_err("Failed to free archive: %s", archive_error_string(a));
  }
  
  lean_object* result = lean_alloc_sarray(1, used, used);
  memcpy(lean_sarray_cptr(result), buff, used);
  
  free(buff);
  return result;
}

LEAN_EXPORT lean_object* lean_archive_extract_tar(lean_object* bytes) {
  struct archive* a;
  struct archive_entry* entry;
  int r;
  
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
