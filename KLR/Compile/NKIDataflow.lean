import KLR.NKI.Basic
import KLR.Compile.Dataflow

open KLR.NKI

inductive VarAction where
  | Read (name : String)
  | Write (name : String) (ty : Option Expr)
  | None

instance VarAction.toString : ToString VarAction where
  toString := fun
    | Read name => s!"Read({name})"
    | Write name _ => s!"Write({name})"
    | None => "None"

@[simp]
def VarAction.var := fun
  | Read name => some name
  | Write name _ => some name
  | None => none

structure NKIWalker where
  num_nodes : ℕ
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
      let num := if n = walker.last_node then s!"{n}[exit]" else s!"{n}"
      s!"{num} {walker.actions n} ↦ {tgts}\n"
    String.intercalate "\n" ((List.range walker.num_nodes).map row ++ ["vars: ", walker.vars.toString])

@[simp]
def NKIWalker.init : NKIWalker := {
  num_nodes := 1
  last_node := 0
  actions _ := VarAction.None
  edges _ _ := false
  breaks := []
  conts := []
  rets := []
  vars := []
}

@[simp]
def NKIWalker.processAction (walker : NKIWalker) (action : VarAction) : NKIWalker :=
  let N := walker.num_nodes
  {walker with
    num_nodes := N + 1
    last_node := N
    actions n := if n = N then action else walker.actions n
    edges A B := (A, B) = (walker.last_node, N)
                ∨ (walker.edges A B)
    vars := match action.var with
            | some var => if var ∈ walker.vars then walker.vars else walker.vars.concat var
            | none => walker.vars
  }

@[simp]
def NKIWalker.setLast (walker : NKIWalker) (last_node : ℕ) : NKIWalker := {walker with
  last_node := last_node
}

@[simp]
def NKIWalker.addEdge (walker : NKIWalker) (a b : ℕ) : NKIWalker := {walker with
  edges A B := (A, B) = (a, b) ∨ walker.edges A B
}

@[simp]
def NKIWalker.addBreak (walker : NKIWalker) : NKIWalker := {walker with
  breaks := walker.breaks ++ [walker.last_node]
}

@[simp]
def NKIWalker.clearBreaks (walker : NKIWalker) : NKIWalker := {walker with
  breaks := []
}

def NKIWalker.addContinue (walker : NKIWalker): NKIWalker := {walker with
  conts := walker.conts ++ [walker.last_node]
}

@[simp]
def NKIWalker.clearConts (walker : NKIWalker) : NKIWalker := {walker with
  conts := []
}

@[simp]
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
@[simp]
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

@[simp]
def NKIWalker.processExprList (walker : NKIWalker) (exprs : List Expr) : NKIWalker :=
  exprs.foldl NKIWalker.processExpr walker
  termination_by sizeOf exprs
end

mutual
@[simp]
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

@[simp]
def NKIWalker.processStmtList (walker : NKIWalker) (stmts : List Stmt) : NKIWalker :=
  stmts.foldl NKIWalker.processStmt walker
  termination_by sizeOf stmts
end

@[simp]
def NKIWalker.processFun (f : Fun) : NKIWalker :=
  let body_walker := (NKIWalker.init.processStmtList f.body).processAction VarAction.None
  body_walker.rets.foldl (fun walker ret ↦ walker.addEdge ret body_walker.last_node) body_walker

@[simp]
def NKIWalker.isClosed (walker : NKIWalker) := walker.breaks.isEmpty ∧ walker.conts.isEmpty


/-
def test():
	x = 0
	if cond0:
		print(x)
	else:
		y = 0
		print(y)
	print(y)
-/
@[simp]
def test_kernel : Kernel := {
  entry := "test.test",
  funs := [{ name := "test.test",
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
                                  [{ stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "print",
                                                             pos := { line := 4,
                                                                      column := 2,
                                                                      lineEnd := some 4,
                                                                      columnEnd := some 7 } }
                                                           [{ expr := KLR.NKI.Expr'.var "x",
                                                              pos := { line := 4,
                                                                       column := 8,
                                                                       lineEnd := some 4,
                                                                       columnEnd := some 9 } }]
                                                           [],
                                                 pos := { line := 4,
                                                          column := 2,
                                                          lineEnd := some 4,
                                                          columnEnd := some 10 } },
                                     pos := { line := 4, column := 2, lineEnd := some 4, columnEnd := some 10 } }]
                                  [{ stmt := KLR.NKI.Stmt'.assign
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
                                                              pos := { line := 7,
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
                                                pos := { line := 8,
                                                         column := 1,
                                                         lineEnd := some 8,
                                                         columnEnd := some 6 } }
                                              [{ expr := KLR.NKI.Expr'.var "y",
                                                 pos := { line := 8,
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
def test():
	x = 0
	x
-/
@[simp]
def test_kernel_min : Kernel := {
  entry := "test.test",
  funs := [{ name := "test.test",
             file := "unknown",
             line := 1,
             body := [{ stmt := KLR.NKI.Stmt'.expr
                                  { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                    pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } },
                        pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }],
             args := [] }],
  args := [],
  globals := [] }

@[simp]
def walker := NKIWalker.processFun test_kernel_min.funs[0]
#eval walker

@[simp]
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
    | true => "_"
    | false => "DEF"


#eval walker.num_nodes
example : walker.num_nodes = 2 := by {
  simp
}

#eval walker.vars.length
example : walker.vars.length = 0 := by {
  simp
}


--attribute [df_simp] List.foldl
--attribute [df_simp] Vector.ofFn
--attribute [df_simp] Array.ofFn

def 𝕐 : NKIWalker := ({ num_nodes := 1, last_node := 0, actions := fun x => VarAction.None,
                                  edges := fun _ _ => false, breaks := [], conts := [], rets := [],
                                  vars := [] } : NKIWalker).processStmtList
                              [{
                                  stmt :=
                                    Stmt'.assign
                                      { expr := Expr'.var "x",
                                        pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }
                                      none
                                      (some
                                        { expr := Expr'.value (Value.int 0),
                                          pos := { line := 2, column := 5, lineEnd := some 2, columnEnd := some 6 } }),
                                  pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 6 } },
                                {
                                  stmt :=
                                    Stmt'.expr
                                      { expr := Expr'.var "x",
                                        pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 2 } },
                                  pos :=
                                    { line := 3, column := 1, lineEnd := some 3, columnEnd := some 2 } }]


#eval 𝕐.num_nodes
example : 𝕐.num_nodes = 3:= by {
  unfold 𝕐
  unfold NKIWalker.processStmtList
  simp

}


@[simp]
def 𝕏opt := (Solution
      (ρ:=Bool)
      (le_supl:=by trivial)
      (le_supr:=by trivial)
      (num_nodes:=walker.num_nodes)
      (num_keys:=walker.vars.length)
      (edges:=walker.edges)
      (transitions:=transitions))


#eval 𝕏opt
#synth (BEq (ℕ × Bool))

--theorem optsimp {α} (a : α) : (Option.some a).isSome := by simp

theorem 𝕏present : 𝕏opt.isSome := by {
    unfold 𝕏opt
    unfold Solution
    unfold FiniteDataflowProblem
    unfold DataflowProblem.solve
    dsimp only []
    unfold DataflowProblem.solve_to_depth
    dsimp only []
    unfold ν₀
    unfold Δ
    unfold Δ₀
    unfold is_fix
    dsimp only [NodeMap.fold]



    unfold NodeMap.of_func NodeMap.fold NodeMap.app_unary NodeMap.get
    dsimp





    unfold FiniteNodeMap

    let FNM := (FiniteNodeMap walker.num_nodes)
    let F [NodeMap ℕ] [BEq (⟦ℕ, Bool⟧ × Bool)]:= fun a => (
              ⟪↦(⊥, true)⟫ fold⟪⟪↦(⊥, true)⟫map⟪fun x => x.fst⟫,fun a ν₀ =>
                          if (⟪↦(⊥, true)⟫◃a).snd = true then ν₀⊔δ ⟪↦(⊥, true)⟫ a else ν₀⟫◃a,
              (⟪↦(⊥, true)⟫◃a).fst
                !=
                ⟪↦(⊥, true)⟫fold⟪⟪↦(⊥, true)⟫map⟪fun x => x.fst⟫,fun a ν₀ =>
                            if (⟪↦(⊥, true)⟫◃a).snd = true then ν₀⊔δ ⟪↦(⊥, true)⟫ a else ν₀⟫◃a)
    rw [F]

}



def 𝕏 := 𝕏opt.get 𝕏present


      /-(by {
        unfold Option.isSome
        simp [df_simp]

        repeat unfold DataflowProblem.solve_to_depth



        unfold Option.isSome.match_1 Option.casesOn Option.rec

        simp [df_simp]



      })-/
#eval! 𝕏

example : 𝕏.vals 2 0 (by {simp}) (by {}) = false

theorem reads_valid
  : ∀ n k, (hn: n < walker.num_nodes) → (hk: k < walker.vars.length) →
    walker.actions n = VarAction.Read (walker.vars[k]) → 𝕏.vals n k hn hk :=
    fun n k hn hk h ↦ match n with
      | 0 => sorry
      | 1 => sorry
      | 2 => sorry
      | 3 => sorry
      | 4 => sorry
      | 5 => sorry
      | 6 => sorry
      | 7 => sorry
      | 8 => sorry
      | 9 => sorry
      | 10 => sorry
      | 11 => sorry
      | n + 12 => sorry




structure Path where
  nodes : List ℕ
  nonempty : nodes ≠ []
  sound : ∀ i (_ : i < nodes.length - 1), walker.edges nodes[i] nodes[i+1]

def Path.motive (path : Path) :=
  𝕏.vals (path.nodes.getLast path.nonempty)

  match walker.actions (path.nodes.getLast path.nonempty) with
  | VarAction.Read name =>
   ∃ i, i < path.nodes.length - 1 ∧ walker.actions i = VarAction.Read name
  | _ => True
