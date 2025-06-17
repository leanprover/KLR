/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Michael Graeb
*/
#pragma once
#include "stdc.h"

struct region;

struct region *region_create(void);
void region_destroy(struct region *region);

// Return newly allocated memory, or NULL if allocation fails.
// Note that ALL OTHER allocation functions will abort if allocation fails;
// they will never return NULL.
void *region_try_alloc(struct region *region, size_t size);

// Return newly allocated memory.
void *region_alloc(struct region *region, size_t size);

// Return newly allocated copy of null-terminated string.
char *region_strdup(struct region *region, const char *src);

// Return newly allocated copy of string, with at most `len` bytes copied.
// Copying stops when `len` bytes are copied, or a null-terminator is found.
// The new string is always null-terminated.
char *region_strndup(struct region *region, const char *src, size_t len);
