/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Lib
import KLR.Semantics.Memory
import KLR.Semantics.SmallStep
import TensorLib.Iterator

set_option grind.warning false

/-- A physical ChipIndex cannot be free allocated. -/
def ChipIndex.IsPhysical : KLR.Core.ChipIndex → Prop
| .psumPhysIndex
| .sbufPhysIndex => True
| _ => False

namespace NML

open KLR.Core TensorLib

/-! # NML, Neuron Modeling Language
The language is parameterized by a type of floating point numbers, see `KLR/Semantics/Float.lean`. -/

/-- A pointer to a tensor that carries additional metadata.
NB. No size contstraints on the tensor (like Address). Minimum size can be computed
from shape and layout. -/
structure TensorHandle where
  /-- Memory bank in which the tensor is stored -/
  index : ChipIndex
  /-- Multiaffine equation mapping tensor indices to indices in the address space. -/
  layout : AffineMap
  /-- Logical description of a tensor shape -/
  shape : KLR.Core.Shape
  /-- The affine map must have the same dimensions as -/
  layout_wf : layout.free_strides.length = shape.freeDims.length
  /- Datatype of the tensor's values. TODO: Add a wf predicate to the state interpretation that checks that all tensors are well-typed? -/
  dtype : KLR.Core.Dtype
  /-- (Optional) name of the tensor -/
  name  : Option String

def TensorHandle.Store? (r : TensorHandle) (m : NeuronMemory DataT) : Option (LocalStore DataT) :=
  ChipMemory.get_store m r.index

/-- NML program state.
From the perspective of the logic, state is anything that we want to represent using separating conjunction.
In particular, state should frame around weakest preconditions (P -∗ wp .. Q implies (s ∗ P) -∗ wp .. (s ∗ Q) for
all pieces of state `s`).

Local bindings are not a part of state, because they do not obey the frame property! -/
structure State (DataT : Type _) where
  memory : KLR.Core.NeuronMemory DataT

/-- NML values.
A value should be thought of as an expression that does not reduce. -/
inductive Value (DataT : Type _)
| unit
| bool     (b : Bool)
| int      (i : Int)
| string   (s : String)
/-- [ tupV ] Tuple values -/
| tupV     (v : List <| Value DataT)
/-- [ data ] An individual unit piece of data.
This Float does not necessarily behave like a float. Its semantics are given by an
NMLEnv struct. -/
| data     (d : DataT)
/-- [ ptr ] A pointer to an entire tensor in memory -/
| ptr      (p : TensorHandle)
/-- [ uptr ] A raw reference to a chip in memory -/
| uptr     (i : ChipIndex)
/-- [ iptr ] A raw reference to a location inside a chip's memory -/
| iptr     (i : Nat × Nat)
/-- [ iref ] A reference to an iterator value.
We give all of our iterators explicit names so that proof rules can represent
relationships between them. -/
| iref     (i : Nat)
/-- [ lidx ] A logical index into a tensor. -/
| lidx     (l : List Int)
/-- [ tens ] (internal) The value of tensor  -/
| tens     (s : LocalStore DataT)
/-- (internal) A continuation -/
| kont

/-- NML Unops that operate on Data-/
inductive Dunop (DataT  : Type) where
/-- [cst] The constant function -/
| cst (v : DataT)
/-- [internal] An arbitrary Lean function.
All (total) dunops can be represented this way, but it makes pretty printing NML
expressions difficult. -/
| lean (f : DataT → DataT)


/-- NML Unops that operate on Data-/
inductive TSDunop (DataT  : Type) where
/-- [add] Add a constant to the -/
| add
| cst



/-- NML expressions.
Expressions are allowed to read and update the program state.
Expressions can refer to the local context, but they are lexically scoped and cannot update it. -/
inductive Expr (DataT : Type)
/-- [ val ] Fully-reduced expression. -/
| val           (v : Value DataT)
/-- [ var ] Variable reference. -/
| var           (x : String)
/-- [ tup ] Tuples
TODO: Stepping rules  -/
| tup           (es : List <| Expr DataT)
/-- [ view ] Create a new TensorHandle referencing a prior memory location
TODO: Stepping rules -/
| view          (eshape edst : Expr DataT)
/-- [ dunop ] Apply a unary function to a piece of data. -/
| dunop         (e : Expr DataT) (f : Dunop DataT)
/-- [ alloc ] Nonphysical tensor allocation.
Generate a new, empty, nonphysical tensor block inside the given memory. -/
| alloc         (m : Memory)
/-- [ readp ] Raw point read.
Access the data stored in a given chip at a given index. This read is "raw"
in the sense that it does not perform any layout calculations. -/
| readp         (chip index : Expr DataT)
/-- [ idx ] A list of expressions, that should be thought of as reducing to a single logical address. -/
| idx           (l : List (Expr DataT))
/-- [ chip ] Access the chip (uptr) from the metadata of a ptr -/
| chip          (ptr : Expr DataT)
/-- [ ix ] Compute the raw location (iptr) of an address given a logical address. -/
| ix            (ptr : Expr DataT) (index : Expr DataT)
/-- (internal) Return the entire store behind a ChipIndex  -/
| deref_store   (e : Expr DataT)

/-- Iterator expressions -/
inductive IteratorS where
| affineRange    (start step : Int) (num : Nat)

/-- Locals: A context mapping variable names to values. -/
def Locals (DataT : Type _) := String → Option (Value DataT)
def Locals.emp : Locals DataT := fun _ => .none
def Locals.bind (s : Locals DataT) (x : String) (v : Value DataT) : Locals DataT:=
  fun x' => if x = x' then .some v else s x'

/-- A structure that contains a TensorLib iterator.
The iterator may be finished, in which case its carrier is .none. -/
structure Iterator (DataT : Type _) where
  I : Type
  [instIIter : TensorLib.Iterator I (Value DataT)]
  car : I

structure AffineIter where
  start     : Int
  peek      : Int
  num       : Nat
  start_num : Nat
  step      : Int

instance instIterAffineIter {DataT : Type _} : TensorLib.Iterator AffineIter (NML.Value DataT) where
  next r :=
    match r.num with
    | .zero      => .none
    | .succ num' => .some ⟨r.start, r.peek + r.step, num', r.start_num, r.step⟩
  peek r  := NML.Value.int r.peek
  size r  := r.num
  reset r := ⟨r.start, r.start, r.start_num, r.start_num, r.step⟩

@[simp] def AffineIter.asList' (peek step : Int) (num : Nat) : List (@Value DataT) :=
  match num with
  | .zero      => [NML.Value.int peek]
  | .succ num' => NML.Value.int peek :: AffineIter.asList' (peek + step) step num'

@[simp] def AffineIter.asList (A : AffineIter) : List (@Value DataT) :=
    asList' A.peek A.step A.num

/-
theorem AffineIter.asList_next_none {A : AffineIter} :
    TensorLib.Iterator.next (iter := AffineIter) (value := @Value DataT) A = .none →
    A.asList = [NML.Value.int (DataT := DataT) A.peek] := by
  s orry

theorem AffineIter.asList_next_some {A : AffineIter} :
    (TensorLib.Iterator.next (iter := AffineIter) (value := @Value DataT) A = .some A') →
    A.asList = (NML.Value.int (DataT := DataT) A.peek) :: A'.asList := by
  s orry
-/

-- Right now: the IteratorS semantics work for all choices of DataT
def IteratorS.toIterator {DataT : Type _} : IteratorS → Iterator DataT
| .affineRange start step num => .mk AffineIter ⟨start, start, num, num, step⟩

instance {i : Iterator DataT} : TensorLib.Iterator i.I (Value DataT) := Iterator.instIIter _

def Iterator.peek (i : Iterator DataT) : Value DataT := i.instIIter.peek i.car

def Iterator.advance (i : Iterator DataT) : Option (Iterator DataT) :=
  i.instIIter.next i.car |>.bind fun ii => .some <| Iterator.mk i.I ii

/-- Iterators: A context mapping iterator identifiers to values. -/
def Iterators DataT := Nat → Option (Iterator DataT)
def Iterators.emp : Iterators DataT := fun _ => .none
def Iterators.bind (s : Iterators DataT) (x : Nat) (v : Option (Iterator DataT)) : Iterators DataT :=
  fun x' => if x = x' then v else s x'

theorem Iterators.bind_bind (Is : Iterators DataT) x (I : Iterator DataT) (I' : Option (Iterator DataT)):
    (Is.bind x I |>.bind x I') = Is.bind x I' := by
  unfold Iterators.bind
  refine funext (fun _ => ?_)
  split <;> rfl

structure LocalContext (DataT : Type _) where
  loc : Locals DataT
  it : Iterators DataT

def LocalContext.emp : LocalContext DataT := ⟨.emp, .emp⟩

/-- Get a variable in a local context. -/
@[simp] def LocalContext.getv (lc : LocalContext DataT) (x : String) : Option (Value DataT) :=
  lc.loc x

/-- Bind a variable in a local context. Only valid for contexts that are not ignored. -/
@[simp] def LocalContext.bindv (lc : LocalContext DataT) (x : String) (v : (Value DataT)) : LocalContext DataT where
  loc := lc.loc.bind x v
  it := lc.it

/-- Peek the next value in an iterator from the local context. Only valid if the context is not ignored -/
@[simp] def LocalContext.peeki (lc : LocalContext DataT) (n : Nat) : Option (Value DataT):=
  lc.it n |>.bind (·.peek)

/-- Advance an iterator in the local context. -/
@[simp] def LocalContext.nexti (lc : LocalContext DataT) (n : Nat) : LocalContext DataT where
  loc := lc.loc
  it :=
    match (lc.it n) with
    | .none => lc.it
    | .some i => lc.it.bind n i.advance

/-- Bind a variable in a local context. Only valid for contexts that are not ignored. -/
@[simp] def LocalContext.bindi (lc : LocalContext DataT) (n : Nat) (i : Iterator DataT) : LocalContext DataT where
  loc := lc.loc
  it := lc.it.bind n i

/-- NML statements.
Statements can read and write both the state and the local context. -/
inductive Stmt (DataT : Type _) where
/-- [ ret ] Return statement. Early returns are permitted. -/
| ret          (e : Expr DataT)
/-- [ assign ] Let-binding statement. -/
| assign       (x : Option String) (e : Expr DataT)
/-- [ tensor-scalar operator, in-place, applies to the entire tensor ] -/
| tsdunop      (i : Expr DataT) (op : TSDunop DataT) (v : Expr DataT)
/-- [ mkiter ] Register an iterator variable in the current scope. The iterator variable must be fresh.
As of now, all iterators must be known statically. In principle, i can be changed to use a new "iterator expression"
that allows iterators to depend on eg. the local bindings. I am expressing it this way (rather than having
iterators be values) to avoid difficult cases such as iterators of iterators. -/
| mkiter       (n : Nat) (i : IteratorS)
/-- [ loop ] Looping construct. The argument should evaluate to a iterator variable. -/
| loop         (x : String) (it : Expr DataT) (body : List (Stmt DataT))
/-- [ setp ] Set a single memory location -/
| setp         (chip index val : (Expr DataT))

abbrev StackFrame (DataT : Type _) := (List (Stmt DataT)) × LocalContext DataT

/-- A NML Program during execution. Namely, one of
- A list of statements, and a context to execute them in, or
- A completed execution, its return value. -/
inductive ExecState (DataT : Type _) where
/- Program is executing -/
| run   (s : StackFrame DataT)
/- Program has encountered a return statement or has ran out of statements to execute.
The latter case (the value kont) is not short-circuiting. Returning anything else is.
-/
| done  (v : Value DataT)


structure ProgState (DataT : Type _) where
  /-- The frame that is currently executing -/
  current : ExecState DataT
  /-- The remaining frames to execute -/
  context : List (StackFrame DataT)

def Value.ExpectInt : Expr DataT → Option Int | .val (.int z) => some z | _ => none

/-- NML Enviornment
All paramaters required to define a semantics for NML -/
class NMLEnv (DataT : Type _) where
  intoDataT : Float → DataT
  addInt : Int → DataT → DataT
  evalDunop : Dunop DataT → DataT → DataT

def Dtype.Interp (DataT : Type _) (d : KLR.Core.Dtype) : Type _ :=
  match d with
  | .uint64   => UInt64
  | .uint32   => UInt32
  | .uint16   => UInt16
  | .uint8    => UInt8
  | .int64    => Int64
  | .int32    => Int32
  | .int16    => Int16
  | .int8     => Int8
  | .float16 | .float32r | .float32 | .float8e5 | .float8e4 | .float8e3 | .bfloat16 => DataT


@[simp] def ExprStep [NMLEnv DataT] (e : Expr DataT) (ctx : LocalContext DataT) (s : State DataT) : Option (Expr DataT × State DataT) :=
  match e with
  /- Var step: Look the variable up in the local context. -/
  | .var x =>
      ctx.getv x |>.bind fun v =>
      some ⟨.val v, s⟩

  /- Data unop -/
  | .dunop (.val <| .data d) f =>
      some (.val <| .data <| NMLEnv.evalDunop f d, s)
  | .dunop ed f =>
      ExprStep ed ctx s |>.bind fun ⟨ed', s'⟩ =>
      some (.dunop ed' f, s')

  /- Allocation (currently: sbuf only) -/
  | .alloc .sbuf =>
      let ⟨dst, memory'⟩ := ChipMemory.freshSBUFStore s.memory
      some ⟨.val <| .uptr dst, .mk memory'⟩

  /- Read point from memory -/
  | .readp (.val <| .uptr c) (.val <| .iptr i) =>
      s.memory.get ⟨c, i⟩ |>.bind fun vd =>
      some ⟨.val <| .data vd, s⟩
  | .readp (.val <| .uptr c) ei =>
      ExprStep ei ctx s |>.bind fun ⟨ei', s'⟩ =>
      some ⟨.readp (.val <| .uptr c) ei', s'⟩
  | .readp ec ei =>
      ExprStep ec ctx s |>.bind fun ⟨ec', s'⟩ =>
      some ⟨.readp ec' ei, s'⟩

  /- Logical index expressions (currently: static indices only) -/
  | .idx e => List.mapM (Value.ExpectInt ) e |>.bind (.some ⟨.val <| .lidx ·, s⟩)

  /- Chip expressions -/
  | .chip (.val <| .ptr t) => some ⟨.val <| .uptr t.index, s⟩
  | .chip e =>
      ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
      some ⟨.chip e', s'⟩

  /- Index expressions -/
  | .ix (.val <| .ptr t) (.val <| .lidx li) =>
      match li with
      | [] => none
      | pn :: fns =>
        if fns.length ≠ t.shape.freeDims.length then none else
        let p := t.layout.par pn
        let f := t.layout.free fns
        some ⟨.val <| .iptr ⟨p.toNat, f.toNat⟩, s⟩
  | .ix (.val <| .ptr t) ei =>
      ExprStep ei ctx s |>.bind fun ⟨ei', s'⟩ =>
      some ⟨.ix (.val <| .ptr t) ei', s'⟩
  | .ix ep ei =>
      ExprStep ep ctx s |>.bind fun ⟨ep', s'⟩ =>
      some ⟨.ix ep' ei, s'⟩

  /- Store dereferencing -/
  | .deref_store (.val <| .uptr i) =>
      s.memory.get_store i |>.bind fun vs =>
      some ⟨.val <| .tens vs, s⟩
  | .deref_store e =>
      ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
      some ⟨.deref_store e', s'⟩

  | _ => none

/- Execution is complete when there are no stack frames. -/
@[simp] def NML.toVal (e : ProgState DataT) : Option (Value DataT) :=
  match e with
  | ⟨.done v, []⟩ => .some v
  | ⟨.run ⟨[], _⟩, []⟩ => .some .kont
  | _ => .none

def TSDunop.app_addZ (st : LocalStore DataT) [NMLEnv DataT] (z : Int) : LocalStore DataT:=
  (hhmap (fun _ d => some <| NMLEnv.addInt z d) st)

def TSDunop.app_cst [NMLEnv DataT] (d : DataT) : LocalStore DataT :=
  .mk <| fun _ => .some d

@[simp] def NML.step [NMLEnv DataT] (e : ProgState DataT × State DataT) :
      Option (ProgState DataT × State DataT) :=
  match e with
  -- Topmost frame is done but did not return a value.
  -- There are no more frames.
  -- This is the continuation value, which signifies this.
  | ⟨⟨.run ⟨[], _⟩, []⟩, _⟩ => .none
  -- Topmost frame is done but did not return a value.
  -- There is a pending frame.
  -- This will load and execute the pending frame.
  | ⟨⟨.run ⟨[], _⟩, ftop :: frest⟩, s⟩ => .some ⟨⟨.run ftop, frest⟩, s⟩

  -- Done states do not step
  | ⟨⟨.done _, _⟩, _⟩ => .none

  -- Topmost frame is not done
  | ⟨⟨.run ⟨(p :: ps), ctx⟩, F⟩, s⟩ =>
    match p with

    /- Return -/
    | .ret (.val v) =>
        -- Return with a value immediately skips all pendings stack frames
        some ⟨⟨.done v, []⟩, s⟩
    | .ret e =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨.ret e' :: ps, ctx⟩, F⟩, s'⟩

    /- Assignment -/
    | .assign (.some x) (.val v) =>
        some ⟨⟨.run ⟨ps, ctx.bindv x v⟩, F⟩, s⟩
    | .assign (.some x) e =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.assign (.some x) e') :: ps, ctx⟩, F⟩, s'⟩

    /- Sequencing -/
    | .assign .none (.val _) =>
        some ⟨⟨.run ⟨ps, ctx⟩, F⟩, s⟩
    | .assign .none e =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.assign .none e') :: ps, ctx⟩, F⟩, s'⟩

    /- Register a new static iterator -/
    | .mkiter n it =>
        some ⟨⟨.run ⟨ps, ctx.bindi n it.toIterator⟩, F⟩, s⟩

    /- Tensor-scalar unops, modeled as in-place operation (eg. GPSIMD) -/
    | .tsdunop (.val <| .uptr i) .add (.val <| .int z) =>
        match ChipMemory.get_store s.memory i with
        | .none => .none
        | .some st =>
            some ⟨⟨.run ⟨ps, ctx⟩, F⟩,
              { s with memory := ChipMemory.set_store s.memory i (some <| TSDunop.app_addZ st z)} ⟩
    | .tsdunop (.val <| .uptr i) .cst (.val <| .int 0) =>
          some ⟨⟨.run ⟨ps, ctx⟩, F⟩,
              { s with memory := ChipMemory.set_store s.memory i (some <| TSDunop.app_cst (NMLEnv.intoDataT 0))} ⟩
    | .tsdunop (.val <| .uptr i) op e =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨.tsdunop (.val <| .uptr i) op e' :: ps, ctx⟩, F⟩, s'⟩
    | .tsdunop e op ec  =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨.tsdunop e' op ec :: ps, ctx⟩, F⟩, s'⟩

    /- Loop -/
    | .loop x (.val <| .iref i) b =>
        match ctx.peeki i with
        | .none => .some ⟨⟨.run ⟨ps, ctx⟩, F⟩, s⟩
        | .some itv =>
            .some ⟨⟨.run ⟨b, ctx.bindv x itv⟩, ⟨.loop x (.val <| .iref i) b :: ps, ctx.nexti i⟩ :: F⟩, s⟩
    | .loop x e b =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.loop x e' b :: ps), ctx⟩, F⟩, s'⟩

    /- Set point -/
    | .setp (.val <| .uptr i) (.val <| .iptr x) (.val <| .data v) =>
        some ⟨⟨.run ⟨ps, ctx⟩, F⟩, { s with memory := ChipMemory.set s.memory ⟨i, x⟩ (some v) }⟩
    | .setp (.val <| .uptr i) (.val <| .iptr x) e  =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.setp (.val <| .uptr i) (.val <| .iptr x) e' :: ps), ctx⟩, F⟩, s'⟩
    | .setp (.val <| .uptr i) e ev  =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.setp (.val <| .uptr i) e' ev :: ps), ctx⟩, F⟩, s'⟩
    | .setp e ei ev  =>
        ExprStep e ctx s |>.bind fun ⟨e', s'⟩ =>
        some ⟨⟨.run ⟨(.setp e' ei ev :: ps), ctx⟩, F⟩, s'⟩

    -- | _ => .none


theorem NML.toVal_run_isSome_inv v : toVal ⟨ExecState.run ⟨f, loc⟩, c2⟩ = some v →
    c2 = [] ∧ f = [] := by cases f <;> cases c2 <;> simp [toVal]

instance NML.Semantics [NMLEnv DataT] : SmallStep (ProgState DataT) (Value DataT) (State DataT) where
  Step e1 e2 := NML.step e1 = .some e2
  toVal := NML.toVal
  toVal_isSome_isStuck {c _} _ _ := by
    rcases c with ⟨(⟨f, loc⟩|_), c2⟩
    · intro H
      rcases X : (toVal { current := ExecState.run (f, loc), context := c2 })
      · rw [X] at H; simp at H
      rcases NML.toVal_run_isSome_inv _ X with ⟨rfl, rfl⟩
      simp [step]
    · simp [toVal]

instance [NMLEnv DataT] : Det (ProgState DataT) (Value DataT) (State DataT) where
  step_det {c c'} := by
    simp only [Step]
    intro H _ H'
    obtain ⟨rfl⟩ := H' ▸ H
    rfl

/-  TODO: This section is good but needs a few major changes.
-- 1. "Simple Frames" should be defined semantically first, to avoid explicit induction over NML syntax.
-- 2. The proofs which do need to NML-specific induction should use tactics (like ewp_solve) that
--    are robust against additions to the language.
-- 3. The statement of these lemmas need to be easy to solve from the frontend. At the moment there
--    is a ton of cruft around putting things in uwp format which is causing those nasty defeq timeouts.

/-- Predicate to restrict our loop lifting rule to programs with simple control flow.
No nested loops (yet), no early returns. -/
@[simp] def SimpleFrame : NML.Stmt DataT → Prop
| .ret _  | .loop _ _ _ => False | _ => True

@[simp] def SimpleStackFrame (P : NML.StackFrame DataT) : Prop :=
  List.forall P.1 SimpleFrame

theorem SimpleFrame.frame_inv [NMLEnv DataT] {P : StackFrame DataT} :
  SimpleStackFrame P →
  Step (Prog := ProgState DataT) (Val := Value DataT) ⟨⟨ExecState.run P, []⟩, s⟩ ⟨⟨ExecState.run P', F⟩, s'⟩ →
  F = [] := by
  sorry
  -- rcases P with ⟨los, loc⟩
  -- simp
  -- cases los
  -- · simp [Step]
  -- · rename_i s0 los
  --   cases s0 <;> simp [List.forall]
  --   · simp [Step, Locals.bind, Option.bind]; grind
  --   · simp [Step, Locals.bind, Option.bind]; grind
  --   · simp [Step, Locals.bind, Option.bind]; grind

-- TODO: More simple frame elmmas
-- TODO: Define SimpleFrame semantically rather than by induction
-- A Simple statement is one that executies without adding any frames and just
-- peels off the first statment. It also doesn't return.

theorem StepN_run_noframe_inv [NMLEnv DataT] {c : ProgState DataT × State DataT}
    (Hsf : SimpleStackFrame P)
    (H : SmallStep.StepN n ⟨⟨ExecState.run P, []⟩, s⟩ c) :
    ∃ P' s', c = ⟨⟨ExecState.run P', []⟩, s'⟩ := by
  revert P s c
  induction n
  · intro P s c Hsf H
    obtain ⟨rfl⟩ := SmallStep.stepN_zero_inv H
    exists P
    exists s
  · intro P s c Hsf
    rename_i n IH
    intro H
    -- Cases on the next step
    rw [Nat.add_comm] at H
    obtain ⟨⟨⟨esn, Fn⟩, sn⟩, Hnext, Hrest⟩ := SmallStep.StepN_add_iff.mp H; clear H
    have Hnext' := SmallStep.stepN_1_iff_step.mp Hnext; clear Hnext
    rcases esn with (P'|v)
    · -- Run.
      -- Apply the IH. Frame is empty by lemma
      obtain ⟨rfl⟩ := SimpleFrame.frame_inv Hsf Hnext'
      -- For all simple stack frame cases, P' is P minus the first statement
      -- The remainder is still a simple stack frame
      sorry
    · -- Done.
      exfalso
      rcases P with ⟨los, loc⟩
      cases los
      · simp_all [Step]
      · sorry
        -- rename_i head _
        -- -- There's only one way to step to done and that is if head is .ret
        -- -- TODO: Make this a lemma
        -- cases head <;> simp_all [List.forall]
        -- · simp [Step] at Hnext'
        --   sorry
        -- · sorry
        -- · sorry

-- Might as well use simpleFrame here since we need noFrame inv anyways
theorem StepN_run_noframe_lift [NMLEnv DataT] {P : StackFrame DataT} {F : List (StackFrame DataT)}
    (H : SmallStep.StepN (Prog := ProgState DataT) n (⟨⟨ExecState.run P, []⟩, s⟩) ⟨⟨ExecState.run P', []⟩, s'⟩) :
    SmallStep.StepN (Prog := ProgState DataT) n (⟨⟨ExecState.run P, F⟩, s⟩) ⟨⟨ExecState.run P', F⟩, s'⟩ := by
  revert P s s'
  induction n
  · intro s s' P H
    obtain ⟨rfl⟩ := SmallStep.stepN_zero_inv H
    exact SmallStep.StepN.done rfl
  · rename_i n IH
    intro s s' P H
    rw [Nat.add_comm] at H ⊢
    obtain ⟨⟨⟨esn, Fn⟩, sn⟩, Hnext, Hrest⟩ := SmallStep.StepN_add_iff.mp H; clear H
    rcases esn with (P'|v)
    · sorry
    · sorry
    -- idk something will work though

    -- apply SmallStep.StepN_add_iff.mpr
    -- exists ({ current := esn, context := Fn }, sn)
    -- refine ⟨?_, ?_⟩
    -- · apply SmallStep.stepN_1_iff_step.mpr
    --   have Hnext' := SmallStep.stepN_1_iff_step.mp Hnext
    --   sorry
    -- · have IH' := @IH sn s'
    --
    --   sorry


-/
/-

theorem NML.returnContInv [NMLEnv DataT] {b : List (Stmt DataT)} :
    Step (Val := Value DataT) (ExecState.run b ℓ, s) (ExecState.done Value.cont, s') → b = [] ∧ s = s' := by
  cases b with | nil => simp [Step] | cons h t => ?_
  intro H
  exfalso
  s orry
  -- simp [Step, step] at H <;> unfold step at H
  -- -- All cases are .run
  -- s orry
/-
open SmallStep in
theorem NML.intoFrameCont [NMLEnv DataT] k pc ℓc s' :
    ∀ (b : List (Stmt DataT)) ℓ (s : State DataT),
    StepN (Val := Value DataT) k ⟨ExecState.run b ℓ, s⟩ ⟨ExecState.done .cont, s'⟩ →
    StepN (Val := Value DataT) k ⟨ExecState.run (.frame b ℓ :: pc) ℓc, s⟩ ⟨ExecState.run pc ℓc, s'⟩ := by
  induction k
  · -- N = 0: Contradiction base case
    intros _ _ _ H
    cases (stepN_zero_inv H)
  · rename_i n IH
    intro b ℓ s H
    cases n
    · -- N = 1: The real base case
      clear IH
      simp only [Nat.zero_add] at ⊢ H
      have H' := stepN_1_iff_step.mp H
      apply stepN_1_iff_step.mpr
      -- The only way for the H' step to happen is if b is empty
      obtain ⟨rfl, rfl⟩ := NML.returnContInv H'
      simp [Step]
    · rename_i n
      generalize HN : (n + 1) = N
      rw [HN] at H IH
      -- We can split off the first step of execution from H and the goal
      rw [Nat.add_comm] at H ⊢
      obtain ⟨⟨pnext, snext⟩, Hstep, Hcont⟩ := StepN_add_iff.mp H
      apply StepN_add_iff.mpr
      -- pnext must be .run or else we would not be able to take N > 0 steps out of it
      cases pnext
      · rename_i bnext ctxnext
        exists ⟨ExecState.run (Stmt.frame bnext ctxnext :: pc) ℓc, snext ⟩
        refine ⟨?_, IH _ _ _ Hcont⟩
        apply stepN_1_iff_step.mpr
        simp [Step]
        -- b cannot be empty
        cases b
        · -- Contradiction with Hcont
          s orry
        · simp [step]
          rw [stepN_1_iff_step.mp Hstep]
          rfl
      · -- Contradict Hcont
        s orry
-/
-/

section properties

open NML
variable {DataT : Type _} [NMLEnv DataT]

/-! NML program properties

All steps in the operational semantics are one of the following:
- An ExprStep that lifts other ExprSteps
- ExprStep that doesn't lift and is pure
- A Step that lifts ExprSteps
- A pure step
- An impure step of reduction

The last case will have bespoke proof rules, however the proof rules for all other
cases can be handled generically. Formally, these cases correspond to TODO,
TODO, and TODO, and they are proven below. -/


/-- An expression with a hole lifts ExprSteps in that hole. -/
def EELift (ek : Expr DataT → Expr DataT) : Prop := ∀ {e e' s s' loc},
    ExprStep e loc s = some (e', s') →
    ExprStep (ek e) loc s = some (ek e', s')

syntax "solveEELift" : tactic
macro_rules
  | `(tactic|solveEELift) =>
  `(tactic|
      intro e _ _ _ _;
      cases e with
      | val _ => simp [ExprStep]
      | _ => simp only [ExprStep]; intro H; rw [H]; simp)

theorem EELift.dunop_arg : EELift (.dunop (DataT := DataT) · f) := by
  solveEELift

theorem  EELift.readp_i : EELift (.readp (DataT := DataT) (.val <| .uptr c) ·) := by
  solveEELift

theorem EELift.readp_c : EELift (.readp (DataT := DataT) · ei) := by
  solveEELift

theorem EELift.chip_c : EELift (.chip (DataT := DataT) ·) := by
  solveEELift

theorem EELift.ix_ptr : EELift (.ix (DataT := DataT) · elidx) := by
  solveEELift

theorem EELift.ix_lidx : EELift (.ix (DataT := DataT) (.val <| .ptr t) ·) := by
  solveEELift

theorem EELift.deref_store : EELift (.deref_store (DataT := DataT) ·) := by
  solveEELift

/-- A pure step of expression reduction given some pure assumption -/
def EPure (e e' : Expr DataT) (HP : LocalContext DataT → Prop) : Prop :=
  ∀ s loc, HP loc → ExprStep e loc s = some (e', s)

/-- A LocalContext binds a given variable to a value -/
@[simp] def LCBindP (x : String) (v : Value DataT) : LocalContext DataT → Prop :=
  fun lc => lc.loc x = some v

/-- The trivial constraint on a LocalContext -/
@[simp] def LCTrueP : LocalContext DataT → Prop := fun _ => True

/-- Expect a list of exprs to be all values -/
@[simp] def LCIntList (le : List (Expr DataT)) : LocalContext DataT → Prop :=
  fun _ => List.all le (Value.ExpectInt · |>.isSome)

/-- Expect a tensor to have the shape for a logical index -/
@[simp] def LCTShape (t : TensorHandle) (lf : List Int): LocalContext DataT → Prop :=
  fun _ => lf.length = t.shape.freeDims.length

@[simp] abbrev Expr.asIntV : Expr DataT → Int | (.val <| .int z) => z | _ => 0

theorem EPure.var : EPure (DataT := DataT) (.var x) (.val v) (LCBindP x v) := by
  intro _ _ HP; simp [ExprStep]
  rw [HP]
  simp

theorem EPure.dunop : EPure (.dunop (.val <| .data (d : DataT)) f) (.val <| .data <| NMLEnv.evalDunop f d) LCTrueP := by
  intro _ _ HP; simp [ExprStep]

/- TODO: Finish this proof, maybe?
-- It is a good start, but the details are annoying I'm not sure if this is exactly how we should
-- represent indices anyways.

theorem EPure.idx : EPure (DataT := DataT) (.idx e) (.val <| .lidx <| e.map Expr.asIntV) (LCIntList e) := by
  rename_i DataT
  intro _ _ HP
  obtain ⟨lz, rfl⟩ : ∃ lz : List Int, e = lz.map (fun z => .val <| .int z) := by
    exists e.map Expr.asIntV
    simp
    conv=> lhs; rw [← List.map_id' e]
    simp at HP
    refine List.map_eq_map_iff.mpr (fun z He => ?_)
    have HP := HP z He
    cases z <;> simp [Value.ExpectInt] at HP
    rename_i v
    cases v  <;> simp [Value.ExpectInt] at HP
    simp
  clear HP
  rw [List.map_map]
  -- have Hinv : (Expr.asIntV  ∘ fun z => Expr.val (DataT := DataT) (Value.int z)) = id := by rfl
  -- rw [Hinv, List.map_id]
  -- simp [ExprStep]
  -- induction lz with | nil => simp | cons h t => ?_
  -- rename_i IH
  -- simp [List.mapM_cons]
  -- induction e with | nil => simp at HP ⊢ | cons h t => ?_
  -- rename_i IH
  -- simp only [LCIntList, List.all_cons, Bool.and_eq_true, List.all_eq_true] at HP
  -- obtain ⟨HP1, HP2⟩ := HP
  -- cases Hh : (Value.ExpectInt DataT h) with | none => simp [Hh] at HP1 | some hv => ?_
  -- simp
  -- refine Option.bind_eq_some_iff.mpr ?_
  -- exists (h.asIntV :: List.map Expr.asIntV t)
  -- refine ⟨?_, rfl⟩
  -- simp_all
  s orry
-/


theorem EPure.chip : EPure (.chip (DataT := DataT) <| .val <| .ptr t) (.val <| .uptr t.index) LCTrueP := by
  intro _ _ HP; simp [ExprStep]

theorem EPure.ix :
  EPure (.ix (.val <| .ptr t) (.val <| .lidx (lp :: lf)))
        (.val <| .iptr ⟨Int.toNat <| t.layout.par lp, Int.toNat <| t.layout.free lf⟩)
        (LCTShape t lf) (DataT := DataT) := by
  intro _ _ HP; simp [ExprStep]
  rw [HP]

/-- A statement lifts expression steps to steps of the head expression -/
def EPLift (sk : Expr DataT → Stmt DataT) : Prop := ∀ {e e' s s' ps loc F},
    ExprStep e loc s = some (e', s') →
    Step (Prog := ProgState DataT)
      ⟨⟨ExecState.run ⟨sk e :: ps, loc⟩, F⟩, s⟩
      ⟨⟨ExecState.run ⟨sk e':: ps, loc⟩, F⟩, s'⟩

syntax "solveEPLift" : tactic
macro_rules
  | `(tactic|solveEPLift) =>
  `(tactic|
    intro e _ _ _ _ _ _;
    cases e with
    | val _ => simp [ExprStep]
    | _ => simp only [Step, step]; intro H; rw [H]; simp)

def EPLift.ret_arg : EPLift (.ret (DataT := DataT) ·) := by
  solveEPLift

def EPLift.seq_arg : EPLift (.assign (DataT := DataT) none ·) := by
  solveEPLift

def EPLift.assign_arg : EPLift (.assign (DataT := DataT) (some x) ·) := by
  solveEPLift

-- def EPLift.loop_iter : EPLift (.loop (DataT := DataT) x · b) := by
--   solveEPLift

def EPLift.setp_chip : EPLift (.setp (DataT := DataT) · ei ev) := by
  solveEPLift

def EPLift.setp_ix : EPLift (.setp (DataT := DataT) (.val <| .uptr i) · ev) := by
  solveEPLift

def EPLift.setp_val : EPLift (.setp (DataT := DataT) (.val <| .uptr i) (.val <| .iptr x) ·) := by
  solveEPLift

def EPLift.tsdunop_loc : EPLift (.tsdunop (DataT := DataT) · op ev) := by
  solveEPLift

def EPLift.tsdunop_val : EPLift (.tsdunop (DataT := DataT) (.val <| .uptr i) op ·) := by
  solveEPLift

-- Pure head steps
-- Do not depend on state but can change the local bindings
-- This is most of them actually!

/-- A pure step of program reduction -/
def SPure (e e' : ProgState DataT) (HP : Prop) : Prop :=
  ∀ s, HP → Step ⟨e, s⟩ ⟨e', s⟩

theorem SPure.ret : SPure (DataT := DataT)
    ⟨.run ⟨(.ret <| .val v) :: ps, loc⟩, F⟩
    ⟨.done v, []⟩ True := by
  intro s _; simp [Step]

theorem SPure.assign : SPure (DataT := DataT)
    ⟨.run ⟨(.assign (.some x) <| .val v) :: ps, loc⟩, F⟩
    ⟨.run ⟨ps, loc.bindv x v⟩, F⟩ True := by
  intro s _; simp [Step]

theorem SPure.seq : SPure (DataT := DataT)
    ⟨.run ⟨(.assign .none <| .val v) :: ps, loc⟩, F⟩
    ⟨.run ⟨ps, loc⟩, F⟩ True := by
  intro s _; simp [Step]

theorem SPure.mkiter : SPure (DataT := DataT)
    ⟨.run ⟨.mkiter n it :: ps, loc⟩, F⟩
    ⟨.run ⟨ps, loc.bindi n it.toIterator⟩, F⟩ True := by
  intro s _; simp [Step]

theorem SPure.frameEmp : SPure (DataT := DataT) ⟨.run ⟨[], loc⟩, F1 :: FS⟩ ⟨.run F1, FS⟩ True := by
  intro s _; simp [Step]

@[simp] abbrev PLoopExit (ctx : LocalContext DataT) (n : Nat) : Prop := ctx.peeki n = none

theorem SPure.loopExit : SPure (DataT := DataT)
    ⟨.run ⟨(.loop x (.val <| .iref i) b :: ps), loc⟩, F⟩
    ⟨.run ⟨ps, loc⟩, F⟩ (PLoopExit loc i) := by
  intro s H; simp only [Step, step]; rw [H]

@[simp] abbrev PLoopContinue (ctx : LocalContext DataT) (n : Nat) (v : Value DataT) : Prop :=
  ctx.peeki n = some v

theorem SPure.loopContinue : SPure (DataT := DataT)
    ⟨.run ⟨(.loop x (.val <| .iref i) b :: ps), loc⟩, F⟩
    ⟨.run ⟨b, loc.bindv x v⟩, ⟨.loop x (.val <| .iref i) b :: ps, loc.nexti i⟩ :: F⟩
    (PLoopContinue loc i v) := by
  intro s H; simp only [Step, step]; rw [H]

theorem SPure.frameExit : SPure (DataT := DataT)
    ⟨.run ⟨[], ctx⟩, ftop :: frest⟩ ⟨.run ftop, frest⟩ True := by
  intro s _; simp [Step]

-- |  => .some


-- Lifted head steps
-- This is basically only frame



/-

/- ## Pure Expression steps -/

/-- PureExprStep. An expression can be stepped regardless of its state.
Any restriction on the local context can be encoded using the PL predicate. -/
def PureExprStep {DataT : Type _} (p p' : NML.Expr DataT) (PL : LocalContext DataT → Prop) : Prop :=
  ∀ s : NML.State DataT, ∀ l, PL l → NML.ExprStep DataT p l s = some ⟨p', s⟩


theorem VarPureE {x : String} {v : NML.Value DataT} :
    PureExprStep (.var x) (.val v) (ValPurePL _ x v) := by
  intro σ l H; simp_all

/- ## Pure steps -/

/-- Assignment of a value to none is Pure -/
theorem SeqPure : SmallStep.PureStep (NML.ExecState.run (.assign .none (.val v) :: p') loc) (.run p' loc) :=
  fun _ => by simp [Step]

theorem AssignPure : SmallStep.PureStep (NML.ExecState.run (.assign (.some s) (.val v) :: p') loc)
    (.run p' (loc.bindv _ s v)) :=
  fun _ => by simp [Step]

theorem RetPure {v : NML.Value DataT} :
    SmallStep.PureStep (NML.ExecState.run (.ret (.val v) :: p') loc) (.done v) :=
  fun _ => by simp [Step]

-- theorem LoopExitPure [TensorLib.Iterator I (NML.Value DataT)] :
--     SmallStep.PureStep (NML.ExecState.run <| ⟨NML.Stmt.loop (DataT := DataT) I s .none body, loc⟩ :: p) (.run p) :=
--   fun _ => NML.step.loop_exit

-- theorem LoopNterPure [TensorLib.Iterator I (NML.Value DataT)] :
--     SmallStep.PureStep (State := @NML.State DataT) (Val := @NML.Value DataT)
--       (NML.ExecState.run <| .cons ⟨.loop I x (.some i) b, loc⟩ p)
--       (NML.ExecState.run <|
--           .cons ⟨.blockC b, loc.bind _ x (TensorLib.Iterator.peek i)⟩ <|
--           .cons ⟨.loop I x (TensorLib.Iterator.next (@NML.Value DataT) i) b, loc⟩ <| p) :=
--     fun _ => NML.step.loop_nter _

-- TODO: Make this less ad-hoc and
theorem AssignPureExpr (H : PureExprStep e1 e2 PL) (Hl : PL loc):
    SmallStep.PureStep
      (NML.ExecState.run (.assign (.some s) e1 :: p') loc)
      (NML.ExecState.run (.assign (.some s) e2 :: p') loc) := by
  intro σ
  simp [Step, NML.step, ExecState.run]
  cases e1 <;> try simp only [NML.step]; rw [H σ _ Hl]; rfl
  simp [PureExprStep] at H
  apply H σ _ Hl |>.elim


theorem RetPureExpr (H : PureExprStep e1 e2 PL) (Hl : PL loc):
    SmallStep.PureStep
      (NML.ExecState.run (.ret e1 :: p') loc)
      (NML.ExecState.run (.ret e2 :: p') loc) := by
  intro σ
  simp [Step, NML.step, ExecState.run]
  cases e1 <;> try simp only [NML.step]; rw [H σ _ Hl]; rfl
  simp [PureExprStep] at H
  apply H σ _ Hl |>.elim



/-


theorem SetpEChipPureExpr (H : PureExprStep e e' PL) (Hl : PL loc) :
    SmallStep.PureStep
      (NML.ExecState.run <| .cons ⟨.setp e e2 e3, loc⟩ p)
      (NML.ExecState.run <| .cons ⟨.setp e' e2 e3, loc⟩ p) := by
  intro σ
  apply NML.step.setpEChip
  apply H σ
  apply Hl

theorem SetpEChipPureIndex (H : PureExprStep e e' PL) (Hl : PL loc) :
    SmallStep.PureStep
      (NML.ExecState.run <| .cons ⟨.setp (.val <| .uptr i) e  e3, loc⟩ p)
      (NML.ExecState.run <| .cons ⟨.setp (.val <| .uptr i) e' e3, loc⟩ p) := by
  intro σ
  apply NML.step.setpEIndex
  apply H σ
  apply Hl

theorem StepEChipPureVal (H : PureExprStep e e' PL) (Hl : PL loc) :
    SmallStep.PureStep
      (NML.ExecState.run <| .cons ⟨.setp (.val <| .uptr i) (.val <| .iptr x) e  , loc⟩ p)
      (NML.ExecState.run <| .cons ⟨.setp (.val <| .uptr i) (.val <| .iptr x) e' , loc⟩ p) := by
  intro σ
  apply NML.step.setpEVal
  apply H σ
  apply Hl


-- #check (AssignPureExpr VarPureE _)

abbrev withNoContext {DataT} (L : List (NML.Stmt DataT)) : NML.ExecState DataT :=
  .run <| L.map (⟨·, NML.Locals.Emp DataT⟩)


-- Lots of the aync steps do reductions at the head expression.
-- This prop defines

-- Lifting: Expr step to Step

/-- A given Expr + Hole lifts Expr steps to program steps -/
def ExprLift {DataT : Type _} (p : NML.Expr DataT → NML.Stmt DataT) : Prop :=
  ∀ e e' s s' l ps ,
    NML.ExprStep DataT e l s e' s' →
    NML.step DataT ⟨.run <| ⟨p e, l⟩ :: ps, s⟩ ⟨.run <| ⟨p e', l⟩ :: ps, s'⟩

theorem LiftERet : ExprLift (DataT := DataT) NML.Stmt.ret := by
  intro e e' s s' l ps He
  exact NML.step.retE He

theorem LiftEAsn : ExprLift (DataT := DataT) (NML.Stmt.assign x) := by
  intro e e' s s' l ps He
  cases x
  · exact NML.step.seqE He
  · exact NML.step.asnE He

theorem LiftEChipSetp : ExprLift (DataT := DataT) (NML.Stmt.setp · e₂ e₃) := by
  intro e e' s s' l ps He
  exact NML.step.setpEChip He

theorem LiftEIndexSetp : ExprLift (DataT := DataT) (NML.Stmt.setp (.val <| .uptr i) · e₃) := by
  intro e e' s s' l ps He
  exact NML.step.setpEIndex He

theorem LiftEValSetp : ExprLift (DataT := DataT) (NML.Stmt.setp (.val <| .uptr i) (.val <| .iptr x) ·) := by
  intro e e' s s' l ps He
  exact NML.step.setpEVal He
-/
-/



end properties
