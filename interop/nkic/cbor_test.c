/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
*/
#include "stdc.h"
#include "region.c"
#include "cbor.c"
#include <math.h>
#include <stdio.h>

// Note: this code was written by Q, with minor edits by Q's human assistant PG

static char *buf = NULL;
static size_t size = 0;

FILE *create_temp_file() {
  return open_memstream(&buf, &size);
}

void rewind_file(FILE **file) {
  if (fclose(*file)) {
    perror("close_file");
    assert(0);
  }
  *file = fmemopen(buf, size, "r");
  if (!*file) {
    perror("fmemopen");
    assert(0);
  }
}

void close_file(FILE *file) {
  if (fclose(file))
    perror("fclose");
  if (buf)
    free(buf);
  buf = NULL;
  size = 0;
}

// Helper function to compare floats with a small epsilon
bool float_equals(float a, float b) { return fabs(a - b) < 1e-10; }

// Helper function to compare doubles with a small epsilon
bool double_equals(double a, double b) { return fabs(a - b) < 1e-10; }

// Test encoding and decoding unsigned integers
void test_uint() {
  u64 test_values[] = {
    0, 1, 10, 23, 24, 25, 100, 1000, 0xFF, 0x100, 0xFFFF,
    0x10000, 0xFFFFFFFF, 0x100000000, 0xFFFFFFFFFFFFFFFF - 1,
  };
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    u64 value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_uint(file, value));

    // Decode
    rewind_file(&file);
    u64 decoded;
    assert(cbor_decode_uint(file, &decoded));
    assert(decoded == value);
    close_file(file);
  }
}

// Test encoding and decoding negative integers
void test_negint() {
  i64 test_values[] = {
    -1, -10, -24, -25, -100, -1000, -0x100, -0x101, -0x10000,
    -0x10001, -0x100000000LL, -0x100000001LL, -0x7FFFFFFFFFFFFFFFLL
  };
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    i64 value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_int(file, value));

    // Decode
    rewind_file(&file);
    i64 decoded;
    assert(cbor_decode_int(file, &decoded));
    assert(decoded == value);

    close_file(file);
  }
}

// Test encoding and decoding boolean values
void test_bool() {
  bool test_values[] = {true, false};
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    bool value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_bool(file, value));

    // Decode
    rewind_file(&file);
    bool decoded;
    assert(cbor_decode_bool(file, &decoded));
    assert(decoded == value);

    close_file(file);
  }
}

// Test encoding and decoding floating-point values
void test_float() {
  float test_values[] = {
    0.0,  1.0, -1.0, 3.14159, -3.14159, 1e-10, 1e10, -1e-10, -1e10,
    INFINITY, -INFINITY, NAN
  };
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    float value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_float(file, value));

    // Decode
    rewind_file(&file);
    float decoded;
    assert(cbor_decode_float(file, &decoded));

    // Special handling for NaN and infinities
    if (isnan(value)) {
      assert(isnan(decoded));
    } else if (isinf(value)) {
      assert(isinf(decoded));
      assert((value > 0 && decoded > 0) || (value < 0 && decoded < 0));
    } else {
      assert(float_equals(decoded, value));
    }

    close_file(file);
  }
}

// Test encoding and decoding double floating-point values
void test_double() {
  double test_values[] = {
    0.0,  1.0, -1.0, 3.14159, -3.14159, 1e-10, 1e10, -1e-10, -1e10,
    INFINITY, -INFINITY, NAN
  };
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    double value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_double(file, value));

    // Decode
    rewind_file(&file);
    double decoded;
    assert(cbor_decode_double(file, &decoded));

    // Special handling for NaN and infinities
    if (isnan(value)) {
      assert(isnan(decoded));
    } else if (isinf(value)) {
      assert(isinf(decoded));
      assert((value > 0 && decoded > 0) || (value < 0 && decoded < 0));
    } else {
      assert(double_equals(decoded, value));
    }

    close_file(file);
  }
}

void test_string() {
  const char *test_values[] = {
    "", "Hello", "a somewhat longer string"
  };
  int num_values = sizeof(test_values) / sizeof(test_values[0]);

  for (int i = 0; i < num_values; i++) {
    const char *value = test_values[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_string(file, value, 0));

    // Decode
    rewind_file(&file);
    char *decoded = NULL;
    assert(cbor_decode_string(file, &decoded, NULL, NULL));
    assert(strcmp(decoded, value) == 0);
    close_file(file);
  }

}

// Test encoding and decoding arrays
void test_array() {
  // Test fixed-length arrays
  u64 test_sizes[] = {0,   1,    10,   23,    24,     25,
                      100, 1000, 0xFF, 0x100, 0xFFFF, 0x10000};
  int num_sizes = sizeof(test_sizes) / sizeof(test_sizes[0]);

  for (int i = 0; i < num_sizes; i++) {
    u64 size = test_sizes[i];
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_array_start(file, size));

    // Decode
    rewind_file(&file);
    u64 decoded_size;
    assert(cbor_decode_array_start(file, &decoded_size));
    assert(decoded_size == size);
    close_file(file);
  }
}

// Test encoding and decoding tagged values
void test_tagged() {
  // Test tagged values
  u16 test_tags[] = { 0, 1, 10, 23, 24, 25, 100, 1000, 0xFF, 0x100, 0xFFFF };
  int num_tags = sizeof(test_tags) / sizeof(test_tags[0]);

  for (int i = 0; i < num_tags; i++) {
    u16 tag = test_tags[i];
    u8 type = (tag >> 8) & 0xff;
    u8 constr = tag & 0xff;
    u8 len = 1;
    FILE *file = create_temp_file();
    assert(file != NULL);

    // Encode
    assert(cbor_encode_tag(file, type, constr, len));

    // Decode
    rewind_file(&file);
    u8 decoded_type, decoded_constr, decoded_len;
    assert(cbor_decode_tag(file, &decoded_type, &decoded_constr, &decoded_len));
    assert(decoded_type == type);
    assert(decoded_constr == constr);
    assert(decoded_len == len);
    close_file(file);
  }
}

// Test encoding and decoding options
void test_option() {
  for (int i = 0; i < 2; i++) {
    FILE *file = create_temp_file();
    assert(file != NULL);

    bool opt = i == 1;
    // Encode
    assert(cbor_encode_option(file, opt));

    // Decode
    rewind_file(&file);
    bool decoded_opt;
    assert(cbor_decode_option(file, &decoded_opt));
    assert(decoded_opt == opt);
    close_file(file);
  }
}

// Test a complex example with nested arrays and mixed types
void test_complex() {
  FILE *file = create_temp_file();
  assert(file != NULL);

  // Encode a complex structure: [1, -2, true, 3.14, [100, 200]]

  // Start outer array with 5 elements
  assert(cbor_encode_array_start(file, 5));

  // Element 1: integer 1
  assert(cbor_encode_int(file, 1));

  // Element 2: integer -2
  assert(cbor_encode_int(file, -2));

  // Element 3: boolean true
  assert(cbor_encode_bool(file, true));

  // Element 4: float 3.14
  assert(cbor_encode_float(file, 3.14));

  // Element 5: array with 2 elements
  assert(cbor_encode_array_start(file, 2));

  // Nested element 1: integer 100
  assert(cbor_encode_int(file, 100));

  // Nested element 2: integer 200
  assert(cbor_encode_int(file, 200));

  // Decode the complex structure
  rewind_file(&file);

  // Decode outer array
  u64 outer_size;
  assert(cbor_decode_array_start(file, &outer_size));
  assert(outer_size == 5);

  // Decode element 1: integer 1
  i64 int_value;
  assert(cbor_decode_int(file, &int_value));
  assert(int_value == 1);

  // Decode element 2: integer -2
  assert(cbor_decode_int(file, &int_value));
  assert(int_value == -2);

  // Decode element 3: boolean true
  bool bool_value;
  assert(cbor_decode_bool(file, &bool_value));
  assert(bool_value == true);

  // Decode element 4: float 3.14
  float float_value;
  assert(cbor_decode_float(file, &float_value));
  assert(float_equals(float_value, 3.14));

  // Decode element 5: array with 2 elements
  u64 inner_size;
  assert(cbor_decode_array_start(file, &inner_size));
  assert(inner_size == 2);

  // Decode nested element 1: integer 100
  assert(cbor_decode_int(file, &int_value));
  assert(int_value == 100);

  // Decode nested element 2: integer 200
  assert(cbor_decode_int(file, &int_value));
  assert(int_value == 200);

  close_file(file);
}

int main() {
  printf("Running CBOR tests... ");
  fflush(stdout);

  test_uint();
  test_negint();
  test_bool();
  test_float();
  test_double();
  test_string();
  test_array();
  test_tagged();
  test_option();
  test_complex();

  printf("all tests passed!\n");
  return 0;
}
