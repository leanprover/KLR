/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
A simple big array type

This structure is designed to avoid memory copies when adding elements to an
array. It does this by keeping an array of arrays, each of which will only be
filled to its initial capacity.
-/

namespace KLR.Util

structure BigArray (a : Type) where
  capacity : Nat := 1024
  children : Nat := 10
  arr : Array (Array a) := (Array.emptyWithCapacity children).push
                           (Array.emptyWithCapacity capacity)

namespace BigArray

def push (ba : BigArray a) (x : a) : BigArray a :=
  let index := ba.arr.size - 1
  let child := ba.arr[index]!
  if child.size >= ba.capacity then
    let child := Array.emptyWithCapacity ba.capacity
    let child := child.push x
    let arr := ba.arr.push child
    { ba with arr }
  else
    let child := child.push x
    let arr := ba.arr.set! index child
    { ba with arr }

#guard
  let ba : BigArray Nat := { capacity := 2 }
  let ba := ba.push 1
  let ba := ba.push 2
  let ba := ba.push 3
  ba.arr.size == 2 &&
  ba.arr[0]!.size == 2 &&
  ba.arr[1]!.size == 1 &&
  ba.arr[0]![0]! == 1 &&
  ba.arr[0]![1]! == 2 &&
  ba.arr[1]![0]! == 3
