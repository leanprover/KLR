/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "region.h"
#include "stdc.h"

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

void *region_alloc(struct region *region, size_t size) {
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
