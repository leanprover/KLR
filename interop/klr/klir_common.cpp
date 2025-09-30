/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "klir_common.hpp"
namespace klr {

extern "C" {
// Decoding functions
bool cbor_decode_uint(FILE *in, u64 *value);
bool cbor_decode_int(FILE *in, i64 *value);
bool cbor_decode_bool(FILE *in, bool *value);
bool cbor_decode_float(FILE *in, float *value);
bool cbor_decode_double(FILE *in, double *value);
bool cbor_decode_string(FILE *in, char **s, void *(alloc)(void *, size_t),
                        void *arg);
bool cbor_decode_array_start(FILE *in, u64 *size);
bool cbor_decode_tag(FILE *in, u8 *type, u8 *constructor, u8 *len);
bool cbor_decode_option(FILE *in, bool *isSome);
}

bool deserialize_tag(FILE *in, u8 *type, u8 *constructor, u8 *len) {
  return cbor_decode_tag(in, type, constructor, len);
}

bool deserialize_array_start(FILE *in, u64 *size) {
  return cbor_decode_array_start(in, size);
}

bool deserialize_option(FILE *in, bool *isSome) {
  return cbor_decode_option(in, isSome);
}

Prop Prop_des(FILE *in) { return Prop(); }

Bool Bool_des(FILE *in) {
  Bool res;
  if (!cbor_decode_bool(in, &res))
    throw std::runtime_error("expecting Bool");
  return res;
}

Nat Nat_des(FILE *in) {
  u64 res;
  if (!cbor_decode_uint(in, &res))
    throw std::runtime_error("expecting Nat");
  return res;
}

Int Int_des(FILE *in) {
  i64 res;
  if (!cbor_decode_int(in, &res))
    throw std::runtime_error("expecting Int");
  return res;
}

Float Float_des(FILE *in) {
  float res;
  if (!cbor_decode_float(in, &res))
    throw std::runtime_error("expecting Float");
  return res;
}

String String_des(FILE *in) {
  char *res = NULL;
  if (!cbor_decode_string(in, &res, NULL, NULL))
    throw std::runtime_error("expecting String");

  String result = res;
  free(res); // std::string make a copy
  return res;
}

} // namespace klr
