/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Michael Graeb
*/
#include "region.h"
#include "stdc.h"

#include <stdio.h>

struct block {
  size_t size;
  size_t offset;
  struct block *next;
  u8 buf[0];
};

#define BLOCK_SIZE (8192 - sizeof(struct block))
#define LARGE_SIZE 7168

static_assert(BLOCK_SIZE >= LARGE_SIZE,
             "BLOCK_SIZE must hold anything LARGE_SIZE or less");

struct region {
  struct block *blocks;
  struct block *large;
};

static struct block *alloc_block(size_t size) {
  struct block *b = aligned_alloc(64, size + sizeof(*b));
  if (b) {
    b->size = size;
    b->offset = 0;
    b->next = NULL;
  }
  return b;
}

static void free_blocks(struct block *b) {
  while (b) {
    struct block *tmp = b->next;
    free(b);
    b = tmp;
  }
}

struct region *region_create() { return calloc(1, sizeof(struct region)); }

void region_destroy(struct region *region) {
  if (region) {
    free_blocks(region->blocks);
    free_blocks(region->large);
    free(region);
  }
}

void *region_try_alloc(struct region *region, size_t size) {
  if (unlikely(!region))
    return NULL;

  // check for large block
  if (unlikely(size > LARGE_SIZE)) {
    struct block *b = alloc_block(size);
    if (unlikely(!b))
      return NULL;
    b->next = region->large;
    region->large = b;
    return b->buf;
  }

  struct block *b = region->blocks;
  if (unlikely(!b || size > b->size - b->offset)) {
    b = alloc_block(BLOCK_SIZE);
    if (unlikely(!b))
      return NULL;
    b->next = region->blocks;
    region->blocks = b;
  }

  void *p = b->buf + b->offset;
  b->offset += size;
  return p;
}

void *region_alloc(struct region *region, size_t size) {
  void *p = region_try_alloc(region, size);
  if (unlikely(!p)) {
    fprintf(stderr, "Out Of Memory. NKI compiler will abort the program.\n");
    abort();
  }

  return p;
}

char *region_strdup(struct region *region, const char *src) {
  assert(src);
  size_t size = strlen(src) + 1;
  char *dst = region_alloc(region, size);
  // copy everything, including null-terminator
  memcpy(dst, src, size);
  return dst;
}

char *region_strndup(struct region *region, const char *src, size_t len) {
  assert(src);

  // check for null-terminator earlier than `len`
  len = strnlen(src, len);

  char *dst = region_alloc(region, len + 1);
  memcpy(dst, src, len);
  dst[len] = 0; // add null-terminator
  return dst;
}
