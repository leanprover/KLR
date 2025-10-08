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

import KLR.Py.Parser
import KLR.Py.Pretty

namespace KLR.Py._Test

mutual

def Exp.printTree (e : Exp) : Std.Format :=
  match e with
  | { exp, .. } => Exp'.printTree exp

def Exp'.printTree (e : Exp') : Std.Format :=
  match e with
  | .binOp op x y =>
    let (op, _) := op.reprPrec
    let x := cont ++ nest (Exp.printTree x)
    let y := last ++ nest (Exp.printTree y)
    join [s!"({op})", x, y]
  | .unaryOp op x =>
    let (op, _) := op.reprPrec
    let x := last ++ nest (Exp.printTree x)
    join [s!"({op})", x]
  | .ifExp cond thn els =>
    let cond := cont ++ nest (Exp.printTree cond)
    let thn := cont ++ nest (Exp.printTree thn)
    let els := last ++ nest (Exp.printTree els)
    join ["(ite)", cond, thn, els]
  | _ => e.reprPrec 0
where
  nest x := Std.Format.nest 5 x
  join (l : List Std.Format) := Std.Format.joinSep l "\n"
  cont := " |---"
  last := " '---"

end

def Stmt.printExpTree (s : Stmt) : Std.Format :=
  match s.stmt with
  | .exp e => Exp.printTree e
  | _ => "not an expression"

/--
Print expression trees, used to debug associativity
-/
def Prog.printExpTree (p : Prog) : Std.Format :=
  let es := p.stmts.map Stmt.printExpTree
  Std.Format.joinSep es "\n"

open Tokenizer (Token TokenKind)

def Tokenizer.tokensToString (tokens : Array Token) : String :=
  String.intercalate " " (tokens.map (TokenKind.toString ∘ Token.kind)).toList

def Tokenizer.test (s : String) : String :=
  let tokens := Tokenizer.run s "<input>"
  match tokens with
  | .ok tokens => tokensToString tokens
  | .error msg => msg

macro "#py" s:str : command => `(#eval IO.println <| Parser.run $s "<input>")

macro "#py_tokens" s:str : command => `(#eval Tokenizer.test $s)

macro "#py_exp_tree" s:str : command => `(#eval Prog.printExpTree <$> (Parser.run $s "<input>"))

/-- info: "1 NEWLINE" -/
#guard_msgs in #py_tokens "
1
"

/-- info: "( ) NEWLINE" -/
#guard_msgs in #py_tokens "
(


) # asdfasdf
# asdfasd
"

/--
info:
(+)
 |---(+)
      |---1
      '---2
 '---3
-/
#guard_msgs in #py_exp_tree "1 + 2 + 3
"

/--
info:
(**)
 |---1
 '---(**)
      |---2
      '---3
-/
#guard_msgs in #py_exp_tree "1 ** 2 ** 3
"

/--
info:
(+)
 |---1
 '---(*)
      |---2
      '---3
-/
#guard_msgs in #py_exp_tree "1 + 2 * 3
"

/--
info:
(ite)
 |---True
 |---0
 '---(ite)
      |---False
      |---1
      '---2
-/
#guard_msgs in #py_exp_tree "0 if True else 1 if False else 2
"

/--
info: error:
SyntaxError: <input>:1:8:
  0 == 1 == 2
         ^^
chaining of comparison operators is not allowed
-/
#guard_msgs in #py "0 == 1 == 2"

/--
info: error:
SyntaxError: <input>:1:3:
  - not a
    ^^^
precedence level is low, consider parentheses
-/
#guard_msgs in #py "- not a"

/--
info: ok:
def a():
  a, b = 1, 2
  a()
  pass
-/
#guard_msgs in #py "
def a(): a, b = 1, 2; a(); pass
"

/--
info: error:
SyntaxError: <input>:4:3:
    foo[1:1]()
    ^^^^^^^^^
please parenthesize calling a subscript expression, or it will be parsed as a generic function call
-/
#guard_msgs in #py "
def foo():
  a = 0
  foo[1:1]()
  return a
"

/-- info: ok: "a b c" -/
#guard_msgs in #py "
\"\"\"a b c\"\"\"
"

/--
info: ok:
def foo():
  def s[A](a:A) -> A:
    return a
  return s[int](0)
-/
#guard_msgs in #py "
def foo():
  def s[A](a : A) -> A:
    return a
  return s[int](0)
"

/--
info: ok: def a(x:int=10):
  x = y + x
  return None
-/
#guard_msgs in #py "
def a(x:int=10):
  x = y \
       + x
  return
"

/--
info: ok:
import nki

import nki.language as nl

@nki.jit
def nki_tensor_add_kernel(a_input, b_input):
  "NKI kernel to compute element-wise addition of two input tensors
      "
  assert a_input.shape == b_input.shape
  assert a_input.shape[0] <= nl.tile_size.pmax
  a_tile = nl.load(a_input)
  b_tile = nl.load(b_input)
  c_tile = nl.add(a_tile, b_tile)
  c_output = nl.ndarray(a_input.shape, dtype=a_input.dtype, buffer=nl.shared_hbm)
  nl.store(c_output, value=c_tile)
  return c_output
-/
#guard_msgs in #py "
import nki
import nki.language as nl


@nki.jit
def nki_tensor_add_kernel(a_input, b_input):

    \"\"\"NKI kernel to compute element-wise addition of two input tensors
    \"\"\"

    # Check all input/output tensor shapes are the same for element-wise operation
    assert a_input.shape == b_input.shape

    # Check size of the first dimension does not exceed on-chip memory tile size limit,
    # so that we don't need to tile the input to keep this example simple
    assert a_input.shape[0] <= nl.tile_size.pmax

    # Load the inputs from device memory to on-chip memory
    a_tile = nl.load(a_input)
    b_tile = nl.load(b_input)

    # Specify the computation (in our case: a + b)
    c_tile = nl.add(a_tile, b_tile)

    # Create a HBM tensor as the kernel output
    c_output = nl.ndarray(a_input.shape, dtype=a_input.dtype, buffer=nl.shared_hbm)

    # Store the result to c_output from on-chip memory to device memory
    nl.store(c_output, value=c_tile)

    # Return kernel output as function output
    return c_output
"

/--
info: ok:
def tensor_avgpool_kernel_(in_tensor, out_tensor, pool_size):
  sz_cin, sz_hin, sz_win = in_tensor.shape
  sz_cout, sz_hout, sz_wout = out_tensor.shape
  assert sz_cin == sz_cout
  sz_p = sz_cin
  sz_pool = pool_size
  i_p = nl.arange(sz_p)[:, None, None]
  i_win = nl.arange(sz_win)[None, None, :]
  i_hin = nl.arange(sz_hin)[None, :, None]
  i_wout = nl.arange(sz_wout)[None, None, :]
  i_hout = nl.arange(sz_hout)[None, :, None]
  i_0 = nl.arange(sz_p)[:, None, None, None, None]
  i_1 = nl.arange(sz_hin // sz_pool)[None, :, None, None, None]
  i_2 = nl.arange(sz_pool)[None, None, :, None, None]
  i_3 = nl.arange(sz_win // sz_pool)[None, None, None, :, None]
  i_4 = nl.arange(sz_pool)[None, None, None, None, :]
  in_tile = nl.ndarray([sz_p, sz_hin, sz_win], dtype=in_tensor.dtype)
  in_tile[:, :, :] = nl.load(in_tensor[i_p, i_hin, i_win])
  out_tile = nl.sum(in_tile[i_0, sz_pool * i_1 + i_2, sz_pool * i_3 + i_4], axis=[2, 4]) / (pool_size * pool_size)
  nl.store(out_tensor[i_p, i_hout, i_wout], value=out_tile)

def np_average_pool_2D(in_tensor, pool_size):
  c, h_in, w_in = in_tensor.shape
  reshaped = in_tensor.reshape(c, h_in // pool_size, pool_size, w_in // pool_size, pool_size)
  return np.nanmean(reshaped, axis=(2, 4))
-/
#guard_msgs in #py "

def tensor_avgpool_kernel_(in_tensor, out_tensor, pool_size):
  # Get input/output dimensions
  sz_cin, sz_hin, sz_win = in_tensor.shape
  sz_cout, sz_hout, sz_wout = out_tensor.shape
  assert sz_cin == sz_cout

  # Set relevant sizes
  sz_p = sz_cin
  sz_pool = pool_size

  # Generate tensor h/w index patterns
  # 3D indexing according to [C, H, W]
  i_p = nl.arange(sz_p)[:, None, None] # 3D for
  i_win = nl.arange(sz_win)[None, None, :]
  i_hin = nl.arange(sz_hin)[None, :, None]

  i_wout = nl.arange(sz_wout)[None, None, :]
  i_hout = nl.arange(sz_hout)[None, :, None]

  # Generate pool index patterns (requires two extra dimensions, for the pool window)
  i_0 = nl.arange(sz_p)[:, None, None, None, None] #
  i_1 = nl.arange(sz_hin//sz_pool)[None, :, None, None, None] # y_outer
  i_2 = nl.arange(sz_pool)[None, None, :, None, None] # y_inner
  i_3 = nl.arange(sz_win//sz_pool)[None, None, None, :, None] # x_outer
  i_4 = nl.arange(sz_pool)[None, None, None, None, :] # x_inner

  # Load input data from external memory to on-chip memory
  # Declare ndarray to force a 3D tensor (temporary requirement)
  in_tile = nl.ndarray([sz_p, sz_hin, sz_win], dtype=in_tensor.dtype)
  in_tile[:,:,:] = nl.load(in_tensor[i_p, i_hin, i_win])

  # Perform the pooling operation:
  # We use numpy's advanced indexing, in order to extend in_tile to 5D, and then reduce-average two dimension.
  # axis[0] is the index for p_dim, and thus doesn't participate in the reduction operation.
  # axis[1] and axis[2] together index the rows, with axis[2] responsible for inner strides
  # (i.e. inside a pooling window), and axis[1] responsible for the outer strides. As such, we reduce over axis[2].
  # Similarly, axis[3] and axis[4] together index the columns, and we thus reduce over axis[4].
  out_tile = nl.sum(in_tile[i_0, sz_pool*i_1+i_2, sz_pool*i_3+i_4], axis=[2,4]) / (pool_size*pool_size)

  # Store the results back to external memory
  nl.store(out_tensor[i_p, i_hout, i_wout], value=out_tile)


# Reference NumPy implementation
def np_average_pool_2D(in_tensor, pool_size):
  c, h_in, w_in = in_tensor.shape
  reshaped = in_tensor.reshape(c, h_in // pool_size, pool_size, w_in // pool_size, pool_size)
  return np.nanmean(reshaped, axis=(2, 4))

"
/--
info: ok:
def foo(x:int, y:float, z:str, w:bool) -> None:
  return None

def bar[A](f:[] -> A, a:A) -> A:
  return a

def baz[A](f:forall A. [A] -> A, a:A) -> A:
  x : iter[int] = [10, 20, 30]
  for i in x:
    print(i)
  return f[A](a)

def t[dt, M, N](a:tensor[A, dt], b:tensor[(M, N, 10), int]):
  pass

def lists(a:list[int], b:tuple[int, float]):
  pass
-/
#guard_msgs in #py "

def foo(x : int, y : float, z : str, w : bool) -> None:
  return

def bar[A](f : [] -> A, a : A) -> A:
  return a

def baz[A](f : forall A. [A] -> A, a : A) -> A:
  x : iter[int] = [10, 20, 30]
  for i in x:
    print(i)
  return f[A](a)

def t[dt, M, N](a : tensor[A, dt], b : tensor[(M, N, 10), int]):
  pass

def lists(a : list[int], b : tuple[int, float]):
  pass

"

/--
info: ok:
def tile[M, N](s:tensor[(M, N), int])
where
  32 | M
  N <= 128
:
  pass
-/
#guard_msgs in #py "

def tile[M, N](s : tensor[(M, N), int])
where
  32 | M
  N <= 128
:
  pass

"

/--
info: ok:
def aug_assign(n:int):
  x = x + 1
-/
#guard_msgs in  #py "
def aug_assign(n : int):
  x += 1
"
