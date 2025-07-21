/-
# NKI Dataflow

This file uses the Dataflow solver (`InnerMapImpl.Solution`) from `Dataflow.lean`
to analyize NKI functions.

For example, see `test_kernel` below, serialized NKI ASTs can be generated from `klr compile`,
converted to CFGs by the `NKIWalker` class below,
paired with definitions of variable well-definition corresponding to syntactic defs and uses,
and analyzed to get `𝕏opt : Option SolutionT`, which can be printed to view the liveness of
all variables at all program points `#eval 𝕏opt`
-/

import KLR.NKI.Basic
import KLR.Compile.Dataflow
import KLR.Compile.DataflowTestKernels

open KLR.NKI

section DefVarAction

  inductive VarAction where
    | Read (name : String) (pos : Pos)
    | Write (name : String) (ty : Option Expr) (pos : Pos)
    | None

  instance VarAction.toString : ToString VarAction where
    toString := fun
      | Read name pos => s!"Read({name} @ {pos.line}, {pos.column})"
      | Write name _ pos => s!"Write({name} @ {pos.line}, {pos.column})"
      | _ => "None"

  def VarAction.var := fun
    | Read name _ => some name
    | Write name _ _ => some name
    | _ => none

end DefVarAction

section DefNKIWalker

  structure NKIWalker where
    num_nodes : ℕ
    num_nodes_nonzero : num_nodes > 0
    last_node : ℕ
    actions : ℕ → VarAction
    edges : ℕ → ℕ → Bool
    breaks : List ℕ
    conts : List ℕ
    rets : List ℕ
    vars : List String --list of varnames seen

  instance NKIWalker.toString : ToString NKIWalker where
    toString walker :=
      let row n :=
        let tgts := (List.range walker.num_nodes).filter (walker.edges n)
        let num := if n = walker.last_node then s!"[{n} (exit)]" else s!"[{n}]"
        s!"Node {num} : {walker.actions n} ↦ Nodes {tgts}\n"
      String.intercalate "\n" ((List.range walker.num_nodes).map row ++ ["vars: ", walker.vars.toString])

  def NKIWalker.init : NKIWalker := {
    num_nodes := 1
    num_nodes_nonzero := by trivial
    last_node := 0
    actions _ := VarAction.None
    edges _ _ := false
    breaks := []
    conts := []
    rets := []
    vars := []
  }

  def NKIWalker.Node (walker : NKIWalker) : Type := Fin (walker.num_nodes)
  def NKIWalker.Var (walker : NKIWalker) : Type := Fin (walker.vars.length)

  def NKIWalker.reads (walker : NKIWalker) (n : walker.Node) (v : walker.Var) : Bool :=
    match walker.actions n.val with
    | VarAction.Read name _ => name = walker.vars.get v
    | _ => false

  def NKIWalker.writes (walker : NKIWalker) (n : walker.Node) (v : walker.Var) : Bool :=
    match walker.actions n.val with
    | VarAction.Write name _ _ => name = walker.vars.get v
    | _ => false

  def NKIWalker.is_path (walker : NKIWalker) : List walker.Node → Bool := fun
    | [] => True
    | [n] => walker.edges 0 n.val
    | n₁ :: n₀ :: tl => walker.is_path (n₀ :: tl) ∧ (walker.edges n₀.val n₁.val)

  def NKIWalker.is_path_lowers (walker : NKIWalker) :
    ∀ n ℓ, walker.is_path (n::ℓ) → walker.is_path ℓ := by {
      intro n₁ ℓ₁ h
      cases ℓ₁ with | nil => simp [is_path] | cons n₀ ℓ₀
      simp_all [is_path]
    }

  structure NKIWalker.Path (walker : NKIWalker) where
    nodes : List walker.Node
    nodes_sound : walker.is_path nodes


  -- a path can always be unrolled into a shorter valid one, with proof of an edge across the unrolling
  def NKIWalker.Path.unroll (walker : NKIWalker) (𝕡 : walker.Path)
    : 𝕡.nodes.length ≥ 2 →
      ∃ (n₁ n₀ : walker.Node) (tl : List walker.Node),
        (walker.edges n₀.val n₁.val) ∧ (n₁ :: n₀ :: tl = 𝕡.nodes) ∧ (walker.is_path (n₀ :: tl)) := by {
          intro not_tiny
          rcases 𝕡_def : 𝕡.nodes
          simp [𝕡_def] at not_tiny
          rename_i n₁ tl₁
          rcases tl₁_def : tl₁
          simp [𝕡_def, tl₁_def] at not_tiny
          rename_i n₀ tl₀
          exists n₁, n₀, tl₀
          apply And.intro
          {
            let sound := 𝕡.nodes_sound
            simp [𝕡_def, tl₁_def, is_path] at sound
            exact sound.right
          }
          {
            simp [←tl₁_def]
            apply walker.is_path_lowers n₁ tl₁
            rw [←𝕡_def]
            apply 𝕡.nodes_sound
          }
        }

  def NKIWalker.Path.writes_somewhere (walker : NKIWalker) (𝕡 : walker.Path) (v : walker.Var) : Bool :=
    𝕡.nodes.tail.any (walker.writes . v)

  -- easier to rewrite this than find it in the library lol
  abbrev mem_lifts {α} (a : α) (ℓ : List α) : a ∈ ℓ.tail → a ∈ ℓ := by {
    intro h
    cases ℓ
    contradiction
    simp_all
  }

  def NKIWalker.Path.writes_somewhere_lifts (walker : NKIWalker) (𝕡₀ 𝕡₁ : walker.Path) (v : walker.Var)
    : 𝕡₁.nodes.tail = 𝕡₀.nodes → 𝕡₀.writes_somewhere walker v → 𝕡₁.writes_somewhere walker v := by {
      simp [writes_somewhere]
      intro unroll n₀ n₀_in n₀_writes
      exists n₀
      apply And.intro
      simp [unroll]
      apply mem_lifts
      assumption
      assumption
    }

  def NKIWalker.Path.true_at_terminus (walker : NKIWalker) (𝕡 : walker.Path) (motive : walker.Node → Bool) : Bool :=
    match 𝕡.nodes with
    | n :: _ => motive n
    | _ => false

  def NKIWalker.Path.reads_at_terminus (walker : NKIWalker) (𝕡 : walker.Path) (v : walker.Var) : Bool :=
    𝕡.true_at_terminus walker (walker.reads . v)

  -- proving (or failing to prove) this is the goal!!
  def NKIWalker.sound (walker : NKIWalker) : Prop :=
    ∀ (𝕡 : walker.Path) v, (𝕡.reads_at_terminus walker v) → (𝕡.writes_somewhere walker v)

  def NKIWalker.processAction (walker : NKIWalker) (action : VarAction) : NKIWalker :=
    let N := walker.num_nodes
    {walker with
      num_nodes := N + 1
      num_nodes_nonzero := by simp
      last_node := N
      actions n := if n = N then action else walker.actions n
      edges A B := (A, B) = (walker.last_node, N)
                  ∨ (walker.edges A B)
      vars := match action.var with
              | some var => if var ∈ walker.vars then walker.vars else walker.vars.concat var
              | none => walker.vars
    }


  def NKIWalker.setLast (walker : NKIWalker) (last_node : ℕ) : NKIWalker := {walker with
    last_node := last_node
  }


  def NKIWalker.addEdge (walker : NKIWalker) (a b : ℕ) : NKIWalker := {walker with
    edges A B := (A, B) = (a, b) ∨ walker.edges A B
  }


  def NKIWalker.addBreak (walker : NKIWalker) : NKIWalker := {walker with
    breaks := walker.breaks ++ [walker.last_node]
  }


  def NKIWalker.clearBreaks (walker : NKIWalker) : NKIWalker := {walker with
    breaks := []
  }

  def NKIWalker.addContinue (walker : NKIWalker): NKIWalker := {walker with
    conts := walker.conts ++ [walker.last_node]
  }


  def NKIWalker.clearConts (walker : NKIWalker) : NKIWalker := {walker with
    conts := []
  }


  def NKIWalker.addReturn (walker : NKIWalker) : NKIWalker := {walker with
    rets := walker.rets ++ [walker.last_node]
  }

  /-mutual
  def NKIWalker.processExpr (walker : NKIWalker) (expr : Expr) : Nat :=
    match h : expr.expr with
    | Expr'.tuple x => (walker.processExprList x).sum
    | _ => 0
    termination_by sizeOf expr
    decreasing_by cases expr; simp at h; rw [h]; simp; omega
  def NKIWalker.processExprList (walker : NKIWalker) (exprs : List Expr) : List Nat :=
    exprs.map walker.processExpr
    termination_by sizeOf exprs
  end-/

  mutual

  def NKIWalker.processExpr (walker : NKIWalker) (expr : Expr) : NKIWalker :=
    let ⟨expr, pos⟩ := expr
    match _ : expr with
    | Expr'.value _ => walker
    | Expr'.var (name : String) => walker.processAction (VarAction.Read name pos)
    | Expr'.proj (expr : Expr) _ => walker.processExpr expr
    | Expr'.tuple (elements : List Expr) => walker.processExprList elements
    | Expr'.access (expr : Expr) _ => walker.processExpr expr
    | Expr'.binOp _ left right => (walker.processExpr left).processExpr right
    | Expr'.ifExp test body orelse =>
      let body_walker := ((walker.processExpr test).processExpr body)
      let orelse_walker := ((body_walker.setLast walker.last_node).processExpr orelse)
      let complete_walker := (orelse_walker.processAction VarAction.None)
      complete_walker.addEdge body_walker.last_node complete_walker.last_node
    | Expr'.call (f: Expr) (args: List Expr) (_ : List Keyword) =>
      (walker.processExpr f).processExprList args
    termination_by sizeOf expr
    decreasing_by
      all_goals {
        try {rename_i expr' _<;> rcases h' : (expr, expr') with ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩ <;> simp_all <;> omega}
        try {rcases h' : expr with ⟨⟨⟩, ⟨⟩⟩ <;> simp_all <;> omega}
      }


  def NKIWalker.processExprList (walker : NKIWalker) (exprs : List Expr) : NKIWalker :=
    exprs.foldl NKIWalker.processExpr walker
    termination_by sizeOf exprs
  end

  mutual

  def NKIWalker.processStmt (walker : NKIWalker) (stmt : Stmt) : NKIWalker :=
    let ⟨stmt, pos⟩ := stmt
    match _ : stmt with
    | Stmt'.expr (e : Expr) => walker.processExpr e
    | Stmt'.assert (e : Expr) => walker.processExpr e
    | Stmt'.ret (e : Expr) => (walker.processExpr e).addReturn
    | Stmt'.assign ⟨Expr'.var name, _⟩ (ty : Option Expr) (e : Option Expr) =>
      let withty := (match ty with | some ty => walker.processExpr ty | none => walker)
      let withe := (match e with | some e => withty.processExpr e | none => withty)
      withe.processAction (VarAction.Write name ty pos)
    | Stmt'.assign _ (ty : Option Expr) (e : Option Expr) =>
      let withty := (match ty with | some ty => walker.processExpr ty | none => walker)
      let withe := (match e with | some e => withty.processExpr e | none => withty)
      withe.processAction (VarAction.Write "<unhandled: writes_to_non_identifier>" ty pos)
    | Stmt'.ifStm (e : Expr) (thn : List Stmt) (els : List Stmt) =>
      let then_walker := (walker.processExpr e).processStmtList thn
      let else_walker := (then_walker.setLast walker.last_node).processStmtList els
      let complete := else_walker.processAction VarAction.None
      complete.addEdge then_walker.last_node complete.last_node
    | Stmt'.forLoop (x : Expr) (iter: Expr) (body: List Stmt) =>
      let intro_walker := (walker.processExpr x).processExpr iter
      let outer_breaks := intro_walker.breaks
      let outer_conts := intro_walker.conts
      let inner_walker := ((intro_walker.clearBreaks).clearConts).processAction VarAction.None
      let enter_node := inner_walker.last_node
      let inner_walked := inner_walker.processStmtList body
      let nearly_complete := (inner_walked.addEdge inner_walked.last_node enter_node).setLast enter_node
      let complete := nearly_complete.processAction VarAction.None
      let exit_node := complete.last_node
      let with_conts := complete.conts.foldl (fun walker cont ↦ walker.addEdge cont enter_node) complete
      let with_breaks := complete.breaks.foldl (fun walker brk ↦ walker.addEdge brk exit_node) with_conts
      {with_breaks with
        conts := outer_conts
        breaks := outer_breaks
      }
    | Stmt'.breakLoop => (walker.processAction VarAction.None).addBreak
    | Stmt'.continueLoop => (walker.processAction VarAction.None).addContinue
    termination_by sizeOf stmt
    decreasing_by
      try rcases h : (thn, stmt) with ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩ <;> simp_all <;> omega
      try rcases h : (els, stmt) with ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩ <;> simp_all <;> omega
      try rcases h : (body, stmt) with ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩ <;> simp_all <;> omega


  def NKIWalker.processStmtList (walker : NKIWalker) (stmts : List Stmt) : NKIWalker :=
    stmts.foldl NKIWalker.processStmt walker
    termination_by sizeOf stmts
  end


  def NKIWalker.processFun (f : Fun) : NKIWalker :=
    let body_walker := (NKIWalker.init.processStmtList f.body).processAction VarAction.None
    body_walker.rets.foldl (fun walker ret ↦ walker.addEdge ret body_walker.last_node) body_walker


  def NKIWalker.isClosed (walker : NKIWalker) := walker.breaks.isEmpty ∧ walker.conts.isEmpty

end DefNKIWalker

section WithKernel
  variable [HasKernel]

  abbrev 𝕂 := HasKernel.kernel

  /-
    Perform the walk of the AST, converting it into a CFG
  -/
  def walker [HasKernel] : NKIWalker := NKIWalker.processFun 𝕂

  /-
    extract the transitions from the walker
  -/
  def transitions (n k : ℕ) (pre : Bool) : Bool :=
    (n = 0) ∨
    if _ : k < walker.vars.length then
      match walker.actions n with
        | VarAction.Write name _ _ => ¬ (name = walker.vars[k]) ∧ pre
        | _ => pre
    else
      pre

  instance : Preorder Bool where
    le_refl := by trivial
    le_trans := by trivial

  instance : HasBot Bool where
    bot := false

  instance : ToString Bool where
    toString := fun
      | true => "❌"
      | false => "✅"


  /-
    perform dataflow analysis
  -/
  def 𝕏opt := (Solution
        (ρ:=Bool)
        (le_supl:=by trivial)
        (le_supr:=by trivial)
        (num_nodes:=walker.num_nodes)
        (num_keys:=walker.vars.length)
        (edges:=walker.edges)
        (transitions:=transitions)).map (fun a ↦ {a with
          key_labels k := walker.vars[k]?
        })

  variable (h𝕏 : 𝕏opt.isSome)

  abbrev 𝕏 := 𝕏opt.get h𝕏
  abbrev ℙ := walker.Path
  abbrev 𝕟 := walker.Node
  abbrev 𝕍 := walker.Var
  abbrev 𝔼 (n₀ n₁ : walker.Node) := walker.edges n₀.val n₁.val

  abbrev ν (n : 𝕟) (v : 𝕍) := (𝕏 h𝕏).vals n.val v.val n.isLt v.isLt

  abbrev σ (n₀ n₁ : 𝕟) (v : 𝕍) (𝔼n:𝔼 n₀ n₁): transitions n₀.val v.val (ν h𝕏 n₀ v) ≤ ν h𝕏 n₁ v := by {
    apply (𝕏 h𝕏).props n₀.val n₁.val v.val n₀.isLt n₁.isLt v.isLt 𝔼n
  }

  --#check 𝕏
  --#check ν
  --#check σ
  --#check ℙ

  abbrev var_def (n : 𝕟) (v : 𝕍) : Bool := ¬ν h𝕏 n v
  def NKIWalker.Path.var_def_at_terminus (𝕡 : ℙ) (v : 𝕍) : Bool := 𝕡.true_at_terminus walker (var_def h𝕏 . v)

  def NKIWalker.Path.not_def_at_entry (𝕡 : ℙ) (v : 𝕍) : 𝕡.nodes.length = 1 → ¬ 𝕡.var_def_at_terminus h𝕏 v :=
    match h : 𝕡.nodes with
    | [n] => by {
        intro
        cases v
        rename_i k hk
        simp [NKIWalker.Path.var_def_at_terminus, NKIWalker.Path.true_at_terminus]
        rw [h]
        simp
        have h_edge: walker.edges 0 n.val := by {
          have h𝕡 := 𝕡.nodes_sound
          unfold NKIWalker.is_path at h𝕡
          rw [h] at h𝕡
          simp at h𝕡
          assumption
        }
        apply σ h𝕏 ⟨0,  walker.num_nodes_nonzero⟩ n ⟨k, hk⟩ h_edge
        simp [transitions, LE.le, instLEOfPreorder, Preorder.toLE, instPreorderBool_compile, Bool.instLE]
      }
    | [] | _ :: _ :: _ => by simp

  @[simp]
  abbrev NKIWalker.Path.motive (𝕡 : ℙ) (v : 𝕍) : Prop
    := 𝕡.var_def_at_terminus h𝕏 v → 𝕡.writes_somewhere walker v

  @[simp]
  abbrev length_motive n := ∀ (𝕡 : ℙ) v, 𝕡.nodes.length = n → (𝕡.motive h𝕏 v)

  abbrev sound_at_zero : length_motive h𝕏 0 := by {
    simp [NKIWalker.Path.var_def_at_terminus, NKIWalker.Path.true_at_terminus,  NKIWalker.Path.writes_somewhere]
    intro _ _ is_zero
    simp [is_zero]
  }

  abbrev sound_at_one : length_motive h𝕏 1 := by {
    simp
    intro 𝕡 v _ _
    exfalso
    apply (𝕡.not_def_at_entry h𝕏 v)
    assumption
    assumption
  }

  abbrev sound_ind : ∀ len, len ≥ 1 → length_motive h𝕏 len → length_motive h𝕏 (len + 1) := by {
    unfold length_motive
    intro len len_nonzero IndHyp 𝕡₁ v 𝕡₁_len ν₁
    cases 𝕡₁_def : 𝕡₁
    rename_i nodes₁ is_path₁
    let ⟨n₁, n₀, tl₀, ε, unroll, is_path₀⟩ := 𝕡₁.unroll walker (by omega)
    simp [NKIWalker.Path.var_def_at_terminus, NKIWalker.Path.true_at_terminus, ←unroll] at ν₁
    let 𝕡₀ : ℙ := ⟨n₀ :: tl₀, is_path₀⟩
    cases ν₀ : ν h𝕏 n₀ v
    {
      -- v is defined at n₀ - the terminus of 𝕡₀, so writes somewhere by ind hypo, then lift
      rw [←𝕡₁_def]
      apply (NKIWalker.Path.writes_somewhere_lifts walker 𝕡₀ 𝕡₁ v); simp [←unroll, 𝕡₀]
      apply IndHyp
      simp [←unroll] at 𝕡₁_len
      simp [𝕡₀]
      assumption
      simp [NKIWalker.Path.var_def_at_terminus, NKIWalker.Path.true_at_terminus, 𝕡₀]
      assumption
    }
    {
      -- is not defined at n₀ -- the terminus of 𝕡₀, but is at n₁, the terminus of 𝕡₁
      -- since we have ε : edge from n₀ to n₁, σ n₀ n₀
      let σ' := σ h𝕏 n₀ n₁ v ε
      simp [transitions, LE.le, instLEOfPreorder, Preorder.toLE, instPreorderBool_compile, Bool.instLE, ν₀, ν₁] at σ'
      let ⟨_, σ''⟩ := σ'
      cases action_def : walker.actions n₀.val <;> rw [action_def] at σ'' <;> try simp at σ''
      rename_i _ name _
      simp [NKIWalker.Path.writes_somewhere]
      simp [𝕡₁_def] at unroll
      simp [←unroll, action_def, NKIWalker.writes]
      apply Or.inl
      assumption
    }
  }

  abbrev sound_everywhere : ∀ n, length_motive h𝕏 n := fun
    | 0 => sound_at_zero h𝕏
    | 1 => sound_at_one h𝕏
    | n + 2 => sound_ind h𝕏 (n + 1) (by omega) (sound_everywhere (n + 1))

  def no_def_without_a_write : ∀ (𝕡 : ℙ) v, (𝕡.var_def_at_terminus h𝕏 v) → (𝕡.writes_somewhere walker v) := by {
    intro 𝕡 v
    apply sound_everywhere
    rfl
  }

  abbrev is_safe_at (n : 𝕟) (v : 𝕍) : Prop := walker.reads n v → var_def h𝕏 n v

  abbrev is_safe : Prop := ∀ (n : 𝕟) (v : 𝕍), is_safe_at h𝕏 n v

  abbrev local_safety_decidable : ∀ n v, Decidable (is_safe_at h𝕏 n v) := by {
    intro n v
    unfold is_safe_at
    cases reads? : walker.reads n v <;>
    cases defs? : var_def h𝕏 n v <;>
    simp [is_safe_at] <;> try {apply isTrue; trivial}
    apply isFalse; trivial
  }

  inductive Maybe (P : Prop) -- option type plus message option
  | Yes : P → Maybe P
  | No : Maybe P
  | NoBC : String → Maybe P  --no because of message

  instance Maybe.toString : ToString (Maybe P) where
    toString := fun
    | Yes _ => s!"YES [SAFETY PROVEN]"
    | No => "NO [SAFETY NOT PROVEN]"
    | NoBC s => s!"NO [SAFETY NOT PROVEN] BECAUSE: {s}"

  def Maybe.well? (s : Maybe P) := match s with
  | No => false
  | _ => true

  def decide_success : Maybe (𝕏opt.isSome) := by {
   cases h : 𝕏opt with | none => apply Maybe.No | some => {
    apply Maybe.Yes; simp
   }
  }

  abbrev forall_fin {n} (f : Fin n → Bool) : Bool := (Vector.ofFn f).all (.)

  abbrev forall_fin_sound (f : Fin n → Bool) : forall_fin f → (m : Fin n) → (f m) := by {
    simp [forall_fin]
    intro h m
    apply h
  }

  abbrev 𝕀 (α) (a : α) := a

  def get_unsafe_reads : List VarAction :=
    (List.ofFn (fun n : 𝕟 ↦ (n, List.ofFn (𝕀 𝕍)))).flatMap (fun (n, vs) ↦
      if vs.any (fun v ↦ ¬ decide (is_safe_at h𝕏 n v)) then [walker.actions n.val] else [])

  def get_unsafe_pos : List Pos :=
    (get_unsafe_reads h𝕏).flatMap (fun | VarAction.Read _ pos => [pos] | _ => [])

  --def print_unsafe_reads : String :=
    --(get_unsafe_reads h𝕏).foldl

  def decide_safety : Maybe (is_safe h𝕏) := by {
    let safe := forall_fin (fun n ↦ forall_fin (fun v ↦ decide (is_safe_at h𝕏 n v)))
    by_cases safety : safe
    swap;
    -- if any reads occur where a var isnt def this will hit and fail
    apply Maybe.NoBC; apply kernel_highlighted_repr; apply get_unsafe_pos h𝕏
    apply Maybe.Yes
    unfold is_safe
    intro n v
    have safety_at_n := forall_fin_sound _ safety n
    have safety := (forall_fin_sound _ safety_at_n v)
    apply of_decide_eq_true
    assumption
  }

  section IfSafe
    variable (safety : ∀ (n : 𝕟) (v : 𝕍), walker.reads n v → ¬ν h𝕏 n v)

    def no_read_without_a_def : ∀ (𝕡 : ℙ) v, (𝕡.reads_at_terminus walker v) → (𝕡.var_def_at_terminus h𝕏 v)
          := by {
            simp [NKIWalker.Path.var_def_at_terminus, NKIWalker.Path.reads_at_terminus, NKIWalker.Path.true_at_terminus]
            intro 𝕡 v h
            cases nodes_def : 𝕡.nodes with | nil | cons n ℓ <;> simp_all [nodes_def]
          }

    def no_read_without_a_write : walker.sound := by {
      unfold NKIWalker.sound
      intro 𝕡 name reads
      apply no_def_without_a_write
      apply no_read_without_a_def
      assumption
      assumption
    }
  end IfSafe

  def decide_sound : Maybe (walker.sound) := by {
    clear h𝕏
    cases decide_success with
      | No | NoBC _ => apply Maybe.No
      | Yes success
    cases (decide_safety success) with
      | No => apply Maybe.No
      | NoBC s => apply Maybe.NoBC s
      | Yes safety
    apply Maybe.Yes
    apply no_read_without_a_write success
    intro n v h
    have specific_safety := safety n v h
    simp [is_safe_at, var_def] at specific_safety
    rw [specific_safety]
    trivial
  }
end WithKernel

instance : HasKernel := safe_kernel_1

#eval decide_sound

instance : HasKernel := unsafe_kernel_2

#eval decide_sound

instance : HasKernel := unsafe_kernel_3

#eval decide_sound
