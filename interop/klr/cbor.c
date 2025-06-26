/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
*/
#include "stdc.h"
#include "region.h"
#include "cbor.h"

#include <stdio.h>

// Note: this code was written by Q, with minor edits by Q's human assistant PG

// CBOR Major types
#define CBOR_UINT      0
#define CBOR_NEGINT    1
#define CBOR_BYTESTR   2
#define CBOR_TEXTSTR   3
#define CBOR_ARRAY     4
#define CBOR_MAP       5
#define CBOR_TAG       6
#define CBOR_FLOAT     7

// CBOR simple values and special values
#define CBOR_FALSE     20
#define CBOR_TRUE      21
#define CBOR_NULL      22
#define CBOR_UNDEFINED 23
#define CBOR_FLOAT16   25
#define CBOR_FLOAT32   26
#define CBOR_FLOAT64   27
#define CBOR_BREAK     31

// Helper function to write multiple bytes to the output
static inline bool write_bytes(FILE *out, const u8 *bytes, size_t len) {
  return fwrite(bytes, 1, len, out) == len;
}

// Helper function to read multiple bytes from the input
static inline bool read_bytes(FILE *in, u8 *bytes, size_t len) {
  return fread(bytes, 1, len, in) == len;
}

static inline void to_be_32(u8 *bytes, u32 value) {
  bytes[0] = (u8)(value >> 24);
  bytes[1] = (u8)(value >> 16);
  bytes[2] = (u8)(value >>  8);
  bytes[3] = (u8)(value >>  0);
}

static inline u32 from_be_32(u8 *bytes) {
  return
    ((u32)bytes[0] << 24) |
    ((u32)bytes[1] << 16) |
    ((u32)bytes[2] <<  8) |
    ((u32)bytes[3] <<  0);
}

static inline void to_be_64(u8 *bytes, u64 value) {
  bytes[0] = (u8)(value >> 56);
  bytes[1] = (u8)(value >> 48);
  bytes[2] = (u8)(value >> 40);
  bytes[3] = (u8)(value >> 32);
  bytes[4] = (u8)(value >> 24);
  bytes[5] = (u8)(value >> 16);
  bytes[6] = (u8)(value >>  8);
  bytes[7] = (u8)(value >>  0);
}

static inline u64 from_be_64(u8 *bytes) {
  return
    ((u64)bytes[0] << 56) |
    ((u64)bytes[1] << 48) |
    ((u64)bytes[2] << 40) |
    ((u64)bytes[3] << 32) |
    ((u64)bytes[4] << 24) |
    ((u64)bytes[5] << 16) |
    ((u64)bytes[6] <<  8) |
    ((u64)bytes[7] <<  0);
}

static bool encode_uint(FILE *out, u8 major, u64 value) {
  u8 bytes[9] = { [0] = major << 5 };
  size_t size = 0;

  if (value < 24) {
    // Small value (0-23)
    bytes[0] |= (u8)value;
    size = 1;
  }
  else if (value <= 0xff) {
    // 1-byte value
    bytes[0] |= 24;
    bytes[1] = (u8)value;
    size = 2;
  }
  else if (value <= 0xffff) {
    // 2-byte value
    bytes[0] |= 25;
    bytes[1] = (u8)(value >> 8);
    bytes[2] = (u8)(value >> 0);
    size = 3;
  }
  else if (value <= 0xffffffff) {
    // 4-byte value
    bytes[0] |= 26;
    to_be_32(bytes + 1, (u32)value);
    size = 5;
  } else {
    // 8-byte value
    bytes[0] |= 27;
    to_be_64(bytes + 1, value);
    size = 9;
  }
  return write_bytes(out, bytes, size);
}

// Encode an unsigned integer
bool cbor_encode_uint(FILE *out, u64 value) {
  return encode_uint(out, CBOR_UINT, value);
}

// Encode an integer (positive or negative)
bool cbor_encode_int(FILE *out, i64 value) {
  if (value >= 0) {
    return cbor_encode_uint(out, (u64)value);
  } else {
    return encode_uint(out, CBOR_NEGINT, (u64)(-1 - value));
  }
}

// Encode a boolean value
bool cbor_encode_bool(FILE *out, bool value) {
  u8 byte = (CBOR_FLOAT << 5) | (value ? CBOR_TRUE : CBOR_FALSE);
  return write_bytes(out, &byte, 1);
}

// Encode a floating-point value
bool cbor_encode_float(FILE *out, float value) {
  union {
    float f;
    u32 i;
  } u;
  u.f = value;

  u8 bytes[5];
  bytes[0] = (CBOR_FLOAT << 5) | CBOR_FLOAT32;
  to_be_32(bytes + 1, u.i);
  return write_bytes(out, bytes, 5);
}

// Encode a double floating-point value
bool cbor_encode_double(FILE *out, double value) {
  union {
    double f;
    u64 i;
  } u;
  u.f = value;

  u8 bytes[9];
  bytes[0] = (CBOR_FLOAT << 5) | CBOR_FLOAT64;
  to_be_64(bytes + 1, u.i);
  return write_bytes(out, bytes, 9);
}

// Encode a string
bool cbor_encode_string(FILE *out, const char *s, u64 len) {
  if (len == 0)
    len = strlen(s);
  if (!encode_uint(out, CBOR_TEXTSTR, len))
    return false;
  return write_bytes(out, (u8*)s, len);
}

// Encode the start of an array with a known size
bool cbor_encode_array_start(FILE *out, u64 size) {
  return encode_uint(out, CBOR_ARRAY, size);
}

// Encode a tagged value
bool cbor_encode_tag(FILE *out, u8 type, u8 constructor, u8 len) {
  if (len >= 24)
    return false;

  u8 bytes[3] = {
    0xd9,
    type,
    constructor
  };
  return
    write_bytes(out, bytes, 3) &&
    cbor_encode_array_start(out, len);
}

bool cbor_encode_option(FILE *out, bool isSome) {
  u8 bytes[4] = {
    0xd9, 0xff, isSome, 0x80 | isSome
  };
  return write_bytes(out, bytes, sizeof bytes);
}


static bool decode_uint(FILE *in, u64 *value, u8 *major) {
  u8 byte = 0;
  if (!read_bytes(in, &byte, 1))
    return false;

  *major = byte >> 5;
  u8 info = byte & 0x1F;
  u8 bytes[8];

  if (info < 24) {
    *value = (u64)info;
    return true;
  }

  if (info == 24) {
    if (!read_bytes(in, bytes, 1))
      return false;
    *value = (u64)bytes[0];
    return true;
  }

  if (info == 25) {
    if (!read_bytes(in, bytes, 2))
      return false;
    *value = ((u64)bytes[0] << 8) | (u64)bytes[1];
    return true;
  }

  if (info == 26) {
    if (!read_bytes(in, bytes, 4))
      return false;
    *value = (u64)from_be_32(bytes);
    return true;
  }

  if (info == 27) {
    if (!read_bytes(in, bytes, 8))
      return false;
    *value = from_be_64(bytes);
    return true;
  }

  return false;
}

// Decode an unsigned integer
bool cbor_decode_uint(FILE *in, u64 *value) {
  u8 major = 0;
  return decode_uint(in, value, &major) && major == CBOR_UINT;
}

// Decode an integer (positive or negative)
bool cbor_decode_int(FILE *in, i64 *value) {
  u8 major = 0;
  u64 val = 0;
  if (!decode_uint(in, &val, &major))
    return false;

  if (major == CBOR_UINT) {
    *value = val;
    return true;
  }

  if (major == CBOR_NEGINT) {
    if (val > INT64_MAX)
      return false;
    *value = -1 - (i64)val;
    return true;
  }

  return false;
}

// Decode a boolean value
bool cbor_decode_bool(FILE *in, bool *value) {
  u8 byte;
  if (!read_bytes(in, &byte, 1))
    return false;

  u8 major = byte >> 5;
  u8 info = byte & 0x1F;

  if (major != CBOR_FLOAT)
    return false;

  if (info == CBOR_TRUE) {
    *value = true;
    return true;
  }

  if (info == CBOR_FALSE) {
    *value = false;
    return true;
  }

  return false;
}

// Decode a floating-point value
bool cbor_decode_float(FILE *in, float *value) {
  u8 byte;
  if (!read_bytes(in, &byte, 1))
    return false;

  if (byte != ((CBOR_FLOAT << 5) | CBOR_FLOAT32))
    return false;

  u8 bytes[4];
  if (!read_bytes(in, bytes, 4))
    return false;

  union {
    u32 i;
    float f;
  } u;
  u.i = from_be_32(bytes);
  *value = u.f;
  return true;
}

// Decode a double floating-point value
bool cbor_decode_double(FILE *in, double *value) {
  u8 byte;
  if (!read_bytes(in, &byte, 1))
    return false;

  if (byte != ((CBOR_FLOAT << 5) | CBOR_FLOAT64))
    return false;

  u8 bytes[8];
  if (!read_bytes(in, bytes, 8))
    return false;

  union {
    u64 i;
    double f;
  } u;
  u.i = from_be_64(bytes);
  *value = u.f;
  return true;
}

// Decode a string
bool cbor_decode_string(FILE *in, char **s, void*(alloc)(void*,size_t), void *arg) {
  u8 major = 0;
  u64 len = 0;
  if (!decode_uint(in, &len, &major) || major != CBOR_TEXTSTR)
    return false;

  if (len > 0x10000)
    return false;

  if (alloc == NULL)
    *s = malloc(len+1);
  else
    *s = alloc(arg, len+1);
  if (!*s)
    return false;

  (*s)[len] = 0;
  return read_bytes(in, (u8*)(*s), len);
}

// Decode the start of an array and get its size
bool cbor_decode_array_start(FILE *in, u64 *size) {
  u8 major;
  return decode_uint(in, size, &major) && major == CBOR_ARRAY;
}

// Decode a tagged value
bool cbor_decode_tag(FILE *in, u8 *type, u8 *constructor, u8 *len) {
  u8 bytes[3];
  if (!read_bytes(in, bytes, 3))
    return false;
  if (bytes[0] != 0xd9)
    return false;
  *type = bytes[1];
  *constructor = bytes[2];
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  if (count >= 24)
    return false;
  *len = (u8)count;
  return true;
}

bool cbor_decode_option(FILE *in, bool *isSome) {
  u8 bytes[4];
  if (!read_bytes(in, bytes, 4))
    return false;
  if (bytes[0] != 0xd9 || bytes[1] != 0xff || (bytes[3] & 0xfe) != 0x80)
    return false;
  *isSome = bytes[2];
  return true;
}

// Functions Lean for generated code
bool Bool_des(FILE *out, struct region *region, bool *x) {
  (void)region;
  return cbor_decode_bool(out, x);
}

bool Nat_des(FILE *out, struct region *region, u32 *x) {
  (void)region;
  u64 v = 0;
  if (!cbor_decode_uint(out, &v) || v > UINT_MAX)
    return false;
  *x = (u32)v;
  return true;
}

bool Int_des(FILE *out, struct region *region, i32 *x) {
  (void)region;
  i64 v = 0;
  if (!cbor_decode_int(out, &v) || v > INT_MAX || v < INT_MIN)
    return false;
  *x = (i32)v;
  return true;
}

bool Float_des(FILE *out, struct region *region, float *x) {
  (void)region;
  return cbor_decode_float(out, x);
}

bool String_des(FILE *out, struct region *region, char **s) {
  (void)region;
  return cbor_decode_string(out, s, (void*)region_alloc, region);
}
