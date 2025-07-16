/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once
#include <memory>
#include <list>

namespace klr {

#define check_size(s, n)                                                       \
  static_assert(sizeof(s) == n, "sizeof " #s " unexpected")

typedef int32_t Int;
typedef uint32_t Nat;
typedef float Float;

check_size(Float, 4);

using String = std::string;

struct Prop {};

template <class T> using Ptr = std::shared_ptr<T>;

template <class T> Ptr<T> ptr() { return std::make_shared<T>(); }

template <class T> using List = Ptr<std::list<Ptr<T>>>;

template <class T> List<T> list() {
  return std::make_shared<std::list<Ptr<T>>>();
}

} // namespace klr
