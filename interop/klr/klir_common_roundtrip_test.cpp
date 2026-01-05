/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Round trip tests for KLR serialization/deserialization functions
*/

#include <iostream>
#include <cstdio>
#include <cstring>
#include <vector>
#include <cassert>
#include <cmath>
#include "klir_common.hpp"

using namespace std;
using namespace klr;

// Helper function to create a temporary file for testing
FILE *create_temp_file() { return tmpfile(); }

// Test helper to check if two floats are approximately equal
bool float_equal(float a, float b, float epsilon = 1e-6f) {
  return fabs(a - b) < epsilon;
}

// Test Prop round trip
bool test_prop_roundtrip() {
  cout << "Testing Prop round trip... ";

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  Prop original;

  // Serialize
  if (!Prop_ser(temp, original)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Prop deserialized = Prop_des(temp);

  fclose(temp);

  // Prop is an empty struct, so if we got here without exceptions, it worked
  // Suppress unused variable warning
  (void)deserialized;
  cout << "PASSED" << endl;
  return true;
}

// Test Bool round trip
bool test_bool_roundtrip() {
  cout << "Testing Bool round trip... ";

  vector<Bool> test_values = {true, false};

  for (Bool original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Bool_ser(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Bool deserialized = Bool_des(temp);

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Nat round trip
bool test_nat_roundtrip() {
  cout << "Testing Nat round trip... ";

  vector<Nat> test_values = {0, 1, 42, 255, 65535, 4294967295U};

  for (Nat original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Nat_ser(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Nat deserialized = Nat_des(temp);

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Int round trip
bool test_int_roundtrip() {
  cout << "Testing Int round trip... ";

  vector<Int> test_values = {-2147483648, -1000, -1, 0, 1, 1000, 2147483647};

  for (Int original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Int_ser(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Int deserialized = Int_des(temp);

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Float round trip
bool test_float_roundtrip() {
  cout << "Testing Float round trip... ";

  vector<Float> test_values = {0.0f,     -0.0f,     1.0f,     -1.0f,
                               3.14159f, -2.71828f, 1e-10f,   1e10f,
                               -1e-10f,  -1e10f,    INFINITY, -INFINITY};

  for (Float original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Float_ser(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Float deserialized = Float_des(temp);

    fclose(temp);

    // Special handling for infinity values
    if (isinf(original)) {
      if (!isinf(deserialized) ||
          (signbit(original) != signbit(deserialized))) {
        cout << "FAILED (expected " << original << ", got " << deserialized
             << ")" << endl;
        return false;
      }
    } else if (!float_equal(original, deserialized)) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  // Test NaN separately (NaN != NaN)
  {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file for NaN)" << endl;
      return false;
    }

    Float original = NAN;

    if (!Float_ser(temp, original)) {
      cout << "FAILED (serialization failed for NaN)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Float deserialized = Float_des(temp);
    fclose(temp);

    if (!isnan(deserialized)) {
      cout << "FAILED (expected NaN, got " << deserialized << ")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test String round trip
bool test_string_roundtrip() {
  cout << "Testing String round trip... ";

  vector<String> test_values = {
      "",
      "hello",
      "Hello, World!",
      "String with spaces and punctuation: !@#$%^&*()",
      "Unicode: αβγδε",
      "Newlines\nand\ttabs",
      "Very long string: " + string(1000, 'x')};

  for (const String &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!String_ser(temp, original)) {
      cout << "FAILED (serialization failed for \"" << original.substr(0, 50)
           << "...\")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    String deserialized = String_des(temp);

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected \"" << original.substr(0, 50) << "...\", got \""
           << deserialized.substr(0, 50) << "...\")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test tag serialization/deserialization
bool test_tag_roundtrip() {
  cout << "Testing tag round trip... ";

  vector<tuple<u8, u8, u8>> test_values = {{0, 0, 0},
                                           {1, 2, 3},
                                           {255, 255, 23}, // len must be < 24
                                           {42, 17, 15}};

  for (auto [orig_type, orig_constructor, orig_len] : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!serialize_tag(temp, orig_type, orig_constructor, orig_len)) {
      cout << "FAILED (serialization failed for tag " << (int)orig_type << ","
           << (int)orig_constructor << "," << (int)orig_len << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    u8 type, constructor, len;
    if (!deserialize_tag(temp, &type, &constructor, &len)) {
      cout << "FAILED (deserialization failed)" << endl;
      fclose(temp);
      return false;
    }

    fclose(temp);

    if (orig_type != type || orig_constructor != constructor ||
        orig_len != len) {
      cout << "FAILED (expected " << (int)orig_type << ","
           << (int)orig_constructor << "," << (int)orig_len << ", got "
           << (int)type << "," << (int)constructor << "," << (int)len << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test array start serialization/deserialization
bool test_array_start_roundtrip() {
  cout << "Testing array start round trip... ";

  vector<u64> test_values = {0, 1, 10, 100, 1000, 18446744073709551615ULL};

  for (u64 original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!serialize_array_start(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    u64 deserialized;
    if (!deserialize_array_start(temp, &deserialized)) {
      cout << "FAILED (deserialization failed)" << endl;
      fclose(temp);
      return false;
    }

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test option serialization/deserialization
bool test_option_roundtrip() {
  cout << "Testing option round trip... ";

  vector<bool> test_values = {true, false};

  for (bool original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!serialize_option(temp, original)) {
      cout << "FAILED (serialization failed for " << original << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    bool deserialized;
    if (!deserialize_option(temp, &deserialized)) {
      cout << "FAILED (deserialization failed)" << endl;
      fclose(temp);
      return false;
    }

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (expected " << original << ", got " << deserialized << ")"
           << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

int main() {
  cout << "Running KLR serialization/deserialization round trip tests..."
       << endl
       << endl;

  int passed = 0;
  int total = 0;

  // Run all tests
  if (test_prop_roundtrip())
    passed++;
  total++;
  if (test_bool_roundtrip())
    passed++;
  total++;
  if (test_nat_roundtrip())
    passed++;
  total++;
  if (test_int_roundtrip())
    passed++;
  total++;
  if (test_float_roundtrip())
    passed++;
  total++;
  if (test_string_roundtrip())
    passed++;
  total++;
  if (test_tag_roundtrip())
    passed++;
  total++;
  if (test_array_start_roundtrip())
    passed++;
  total++;
  if (test_option_roundtrip())
    passed++;
  total++;

  cout << endl
       << "Results: " << passed << "/" << total << " tests passed" << endl;

  if (passed == total) {
    cout << "All tests PASSED!" << endl;
    return 0;
  } else {
    cout << "Some tests FAILED!" << endl;
    return 1;
  }
}