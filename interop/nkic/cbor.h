/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
*/
#pragma once
#include "stdc.h"
#include <stdio.h>

// Note: this code was written by Q, with minor edits by Q's human assistant PG

// Encoding functions
bool cbor_encode_uint(FILE *out, u64 value);
bool cbor_encode_int(FILE *out, i64 value);
bool cbor_encode_bool(FILE *out, bool value);
bool cbor_encode_float(FILE *out, float value);
bool cbor_encode_double(FILE *out, double value);
bool cbor_encode_string(FILE *out, const char *s, u64 len);
bool cbor_encode_array_start(FILE *out, u64 size);
bool cbor_encode_tag(FILE *out, u8 type, u8 constructor, u8 len);
bool cbor_encode_option(FILE *out, bool isSome);

// Decoding functions
bool cbor_decode_uint(FILE *in, u64 *value);
bool cbor_decode_int(FILE *in, i64 *value);
bool cbor_decode_bool(FILE *in, bool *value);
bool cbor_decode_float(FILE *in, float *value);
bool cbor_decode_double(FILE *in, double *value);
bool cbor_decode_string(FILE *in, char **s, void*(alloc)(void*,size_t), void *arg);
bool cbor_decode_array_start(FILE *in, u64 *size);
bool cbor_decode_tag(FILE *in, u8 *type, u8 *constructor, u8 *len);
bool cbor_decode_option(FILE *in, bool *isSome);

// Functions Lean for generated code
static inline bool String_ser(FILE *out, const char *s) {
  return cbor_encode_string(out, s, 0);
}

bool Bool_des(FILE *out, struct region *region, bool *x);
bool Nat_des(FILE *out, struct region *region, u32 *x);
bool Int_des(FILE *out, struct region *region, i32 *x);
bool Float_des(FILE *out, struct region *region, float *x);
bool String_des(FILE *out, struct region *region, char **s);
