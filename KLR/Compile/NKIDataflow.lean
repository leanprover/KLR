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

open KLR.NKI

section DefVarAction

  inductive VarAction where
    | Read (name : String)
    | Write (name : String) (ty : Option Expr)
    | None

  instance VarAction.toString : ToString VarAction where
    toString := fun
      | Read name => s!"Read({name})"
      | Write name _ => s!"Write({name})"
      | None => "None"

  def VarAction.var := fun
    | Read name => some name
    | Write name _ => some name
    | None => none

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
    | VarAction.Read name => name = walker.vars.get v
    | _ => false

  def NKIWalker.writes (walker : NKIWalker) (n : walker.Node) (v : walker.Var) : Bool :=
    match walker.actions n.val with
    | VarAction.Write name _ => name = walker.vars.get v
    | _ => false

  def NKIWalker.isPath (walker : NKIWalker) : List walker.Node → Bool := fun
    | [] => True
    | [n] => walker.edges 0 n.val
    | n₁ :: n₀ :: tl => walker.isPath (n₀ :: tl) ∧ (walker.edges n₀.val n₁.val)

  structure NKIWalker.Path (walker : NKIWalker) where
    nodes : List walker.Node
    nodes_sound : walker.isPath nodes

  def NKIWalker.Path.unroll (walker : NKIWalker) (𝕡 : walker.Path)
    : 𝕡.nodes.length ≥ 2 →
      ∃ (n₁ n₀ : walker.Node) (tl : List walker.Node),
        (walker.edges n₀.val n₁.val) ∧ (n₁ :: n₀ :: tl = 𝕡.nodes) ∧ (walker.isPath (n₀ :: tl)) := by {
            sorry
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
    let ⟨expr, _⟩ := expr
    match _ : expr with
    | Expr'.value _ => walker
    | Expr'.var (name : String) => walker.processAction (VarAction.Read name)
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
    let ⟨stmt, _⟩ := stmt
    match _ : stmt with
    | Stmt'.expr (e : Expr) => walker.processExpr e
    | Stmt'.assert (e : Expr) => walker.processExpr e
    | Stmt'.ret (e : Expr) => (walker.processExpr e).addReturn
    | Stmt'.assign ⟨Expr'.var name, _⟩ (ty : Option Expr) (e : Option Expr) =>
      let withty := (match ty with | some ty => walker.processExpr ty | none => walker)
      let withe := (match e with | some e => withty.processExpr e | none => withty)
      withe.processAction (VarAction.Write name ty)
    | Stmt'.assign _ (ty : Option Expr) (e : Option Expr) =>
      let withty := (match ty with | some ty => walker.processExpr ty | none => walker)
      let withe := (match e with | some e => withty.processExpr e | none => withty)
      withe.processAction (VarAction.Write "NONVAR" ty)
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

section Test

  /-
  file test.py:
  def test():
    x = 0
    if cond0:
      print(x)
    else:
      y = 0
      print(y)
    print(y)

  bash: `klr compile test.py` yields the following serialization of a NKI Kernel
  -/

  def test_kernel : Kernel := {
    entry := "test.test",
    funs := [{name := "test.test",
              file := "unknown",
              line := 1,
              body := [{ stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "x",
                                      pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 2, column := 5, lineEnd := some 2, columnEnd := some 6 } }),
                          pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.ifStm
                                    { expr := KLR.NKI.Expr'.var "cond0",
                                      pos := { line := 3, column := 4, lineEnd := some 3, columnEnd := some 9 } }
                                    [{stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "print",
                                                              pos := { line := 4,
                                                                        column := 2,
                                                                        lineEnd := some 4,
                                                                        columnEnd := some 7 } }
                                                            [{ expr := KLR.NKI.Expr'.var "x",
                                                                pos := {line := 4,
                                                                        column := 8,
                                                                        lineEnd := some 4,
                                                                        columnEnd := some 9 } }]
                                                            [],
                                                  pos := { line := 4,
                                                            column := 2,
                                                            lineEnd := some 4,
                                                            columnEnd := some 10 } },
                                      pos := {line := 4, column := 2, lineEnd := some 4, columnEnd := some 10 } }]
                                    [{stmt := KLR.NKI.Stmt'.assign
                                                { expr := KLR.NKI.Expr'.var "y",
                                                  pos := { line := 6,
                                                            column := 2,
                                                            lineEnd := some 6,
                                                            columnEnd := some 3 } }
                                                none
                                                (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                                        pos := { line := 6,
                                                                  column := 6,
                                                                  lineEnd := some 6,
                                                                  columnEnd := some 7 } }),
                                      pos := { line := 6, column := 2, lineEnd := some 6, columnEnd := some 7 } },
                                    { stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "print",
                                                              pos := { line := 7,
                                                                        column := 2,
                                                                        lineEnd := some 7,
                                                                        columnEnd := some 7 } }
                                                            [{ expr := KLR.NKI.Expr'.var "y",
                                                                pos := {line := 7,
                                                                        column := 8,
                                                                        lineEnd := some 7,
                                                                        columnEnd := some 9 } }]
                                                            [],
                                                  pos := { line := 7,
                                                            column := 2,
                                                            lineEnd := some 7,
                                                            columnEnd := some 10 } },
                                      pos := { line := 7, column := 2, lineEnd := some 7, columnEnd := some 10 } }],
                          pos := { line := 3, column := 1, lineEnd := some 7, columnEnd := some 10 } },
                        { stmt := KLR.NKI.Stmt'.expr
                                    { expr := KLR.NKI.Expr'.call
                                                { expr := KLR.NKI.Expr'.var "print",
                                                  pos := {line := 8,
                                                          column := 1,
                                                          lineEnd := some 8,
                                                          columnEnd := some 6 } }
                                                [{expr := KLR.NKI.Expr'.var "y",
                                                  pos := {line := 8,
                                                            column := 7,
                                                            lineEnd := some 8,
                                                            columnEnd := some 8 } }]
                                                [],
                                      pos := { line := 8, column := 1, lineEnd := some 8, columnEnd := some 9 } },
                          pos := { line := 8, column := 1, lineEnd := some 8, columnEnd := some 9 } }],
              args := [] }],
    args := [],
    globals := [] }

  /-
    Perform the walk of the AST, converting it into a CFG
  -/
  def walker := NKIWalker.processFun test_kernel.funs[0]
  #eval walker

  /-
    extract the transitions from the walker
  -/
  def transitions (n k : ℕ) (pre : Bool) : Bool :=
    (n = 0) ∨
    if _ : k < walker.vars.length then
      match walker.actions n with
        | VarAction.Write name _ => ¬ (name = walker.vars[k]) ∧ pre
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

  #eval 𝕏opt
  /-
  Node 0: x:✅ cond0:✅ print:✅ y:✅
  Node 1: x:❌ cond0:❌ print:❌ y:❌
  Node 2: x:✅ cond0:❌ print:❌ y:❌
  Node 3: x:✅ cond0:❌ print:❌ y:❌
  Node 4: x:✅ cond0:❌ print:❌ y:❌
  Node 5: x:✅ cond0:❌ print:❌ y:❌
  Node 6: x:✅ cond0:❌ print:❌ y:✅
  Node 7: x:✅ cond0:❌ print:❌ y:✅
  Node 8: x:✅ cond0:❌ print:❌ y:❌
  Node 9: x:✅ cond0:❌ print:❌ y:❌
  Node 10: x:✅ cond0:❌ print:❌ y:❌
  Node 11: x:✅ cond0:❌ print:❌ y:❌
  -/

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

  #check 𝕏
  #check ν
  #check σ
  #check ℙ


  def NKIWalker.Path.var_def_at_terminus (𝕡 : ℙ) (v : 𝕍) : Bool := 𝕡.true_at_terminus walker (¬ν h𝕏 . v)

  def NKIWalker.Path.not_def_at_entry (𝕡 : ℙ) (v : walker.Var) : 𝕡.nodes.length = 1 → ¬ 𝕡.var_def_at_terminus h𝕏 v :=
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
          unfold NKIWalker.isPath at h𝕡
          rw [h] at h𝕡
          simp at h𝕡
          assumption
        }
        apply σ h𝕏 ⟨0,  walker.num_nodes_nonzero⟩ n ⟨k, hk⟩ h_edge
        simp [transitions, LE.le, instLEOfPreorder, Preorder.toLE, instPreorderBool_compile, Bool.instLE]
      }
    | [] | _ :: _ :: _ => by simp

  @[simp]
  abbrev NKIWalker.Path.motive (𝕡 : ℙ) (v : walker.Var) : Prop
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

  --no def without a write
  def ℍ : ∀ (𝕡 : ℙ) v, (𝕡.var_def_at_terminus h𝕏 v) → (𝕡.writes_somewhere walker v) := by {
    intro 𝕡 v
    apply sound_everywhere
    rfl
  }

  --no read without a def
  def 𝕀 : ∀ (𝕡 : ℙ) v, (𝕡.reads_at_terminus walker v) → (𝕡.var_def_at_terminus h𝕏 v)
        := by {
          sorry -- proof by relying an an easily computable hypothesis (abstracted as a var to prove this goal)
        }

  -- no read without a write :)
  def 𝕁 : walker.sound := by {
    unfold NKIWalker.sound
    intro 𝕡 name reads
    apply ℍ
    apply 𝕀
    assumption
    assumption
  }

end Test
