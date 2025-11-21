/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once
#include <memory>
#include <list>
#include <sstream>

namespace klr {

#define check_size(s, n)                                                       \
  static_assert(sizeof(s) == n, "sizeof " #s " unexpected")

typedef uint8_t u8;
typedef uint64_t u64;
typedef int64_t i64;

typedef bool Bool;
typedef int32_t Int;
typedef uint32_t Nat;
typedef float Float;

check_size(Float, 4);

using String = std::string;

struct Prop {};

template <class T> using Ptr = std::shared_ptr<T>;

template <class T> Ptr<T> ptr() { return std::make_shared<T>(); }

template <class T> using List = std::list<T>;

// template <class T> List<T> list() { return ptr<std::list<T>>(); }

template <class T> using Option = std::optional<T>;

bool deserialize_tag(FILE *in, u8 *type, u8 *constructor, u8 *len);
bool deserialize_array_start(FILE *in, u64 *size);
bool deserialize_option(FILE *in, bool *isSome);

Prop Prop_des(FILE *out);
Bool Bool_des(FILE *out);
Nat Nat_des(FILE *out);
Int Int_des(FILE *out);
Float Float_des(FILE *out);
String String_des(FILE *out);

} // namespace klr
