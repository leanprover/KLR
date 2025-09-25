/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once

// Like shared_ptr/unique_ptr, but for raw pointers that use explicit reference counting functions.
// When setting the raw pointer, it's adopted at its current refcount.
// The destructor calls the decref function, if the raw pointer is non-null.
// When copying from another refcount_ptr, the incref function is called, if the raw pointer is non-null.
// When moving from another refcount_ptr, the raw pointer is stolen, and its refcount does not change.
//
// Use .release() to take ownership of the raw pointer, removing it from the refcount_ptr without affecting its refcount.
// Use .release() when passing the pointer to a functions that take a raw pointer and "steal a reference"
// (reference stealing is the default behavior for lean APIs).
template <class T, auto INCREF_FN, auto DECREF_FN>
class refcount_ptr
{
public:
  // default constructor: empty refcount_ptr
  refcount_ptr() noexcept
  : ptr(nullptr) {}

  // nullptr constructor: empty refcount_ptr
  refcount_ptr(nullptr_t) noexcept
  : ptr(nullptr) {}

  // raw pointer constructor: take ownership of pointer, leaving refcount unchanged
  explicit refcount_ptr(T *ptr_) noexcept
  : ptr(ptr_) {}

  // move constructor: take ownership of pointer from `other`, leaving refcount unchanged and `other` empty
  refcount_ptr(refcount_ptr &&other) noexcept
  : ptr(other.ptr) {
    other.ptr = nullptr;
  }

  // copy constructor: share ownership of pointer with `other`, pointer is incref'd  (if non-null)
  refcount_ptr(const refcount_ptr &other) noexcept
  : ptr(other.ptr) {
    incref_safely();
  }

  // on destruction, decref pointer (if non-null)
  ~refcount_ptr() {
    if (ptr) {
      DECREF_FN(ptr);
    }
  }

  // move assignment: take ownership of pointer from `other`, leaving refcount unchanged and `other` empty
  // Any previously held pointer is decref'd.
  refcount_ptr &operator=(refcount_ptr &&other) noexcept {
    reset(other.release());
    return *this;
  }

  // copy assignment: share ownership of pointer with `other`, pointer is incref'd  (if non-null)
  // Any previously held pointer is decref'd.
  refcount_ptr &operator=(const refcount_ptr &other) noexcept {
    reset(other.ptr);
    incref_safely();
    return *this;
  }

  // null assignment: decref current pointer (if any), and reset it to nullptr
  refcount_ptr &operator=(nullptr_t) noexcept {
    reset();
    return *this;
  }

  explicit operator bool() const noexcept { return ptr != nullptr; }

  // release ownership of the pointer and return it, leaving refcount unchanged
  T *release() noexcept {
    T *tmp = ptr;
    ptr = nullptr;
    return tmp;
  }

  // decref current pointer (if any), and take ownership of new pointer (if any) at its current refcount
  void reset(T *ptr_ = nullptr) noexcept {
    if (ptr) {
      DECREF_FN(ptr);
    }
    ptr = ptr_;
  }

  T *get() const noexcept { return ptr; }
  T *operator->() const noexcept { return ptr; }
  T &operator*() const noexcept { return *ptr; }

private:
  void incref_safely() noexcept {
    if (ptr) {
      INCREF_FN(ptr);
    }
  }

  T *ptr;
};
