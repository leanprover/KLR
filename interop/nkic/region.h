/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "stdc.h"

struct region;

struct region *region_create();
void region_destroy(struct region *region);

void *region_alloc(struct region *region, size_t size);
