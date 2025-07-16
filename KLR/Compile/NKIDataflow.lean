import KLR.NKI.Basic

open KLR.NKI

abbrev ℕ := Nat

inductive VarAction where
  | Read (name : String)
  | Write (name : String) (ty : Option Expr)
  | None

structure NKIWalker where
  num_nodes : ℕ
  last_node : ℕ
  actions : ℕ → VarAction
  edges : ℕ → ℕ → Bool
  breaks : List ℕ
  conts : List ℕ
  rets : List ℕ

def NKIWalker.init : NKIWalker := {
  num_nodes := 1
  last_node := 0
  actions _ := VarAction.None
  edges _ _ := false
  breaks := []
  conts := []
  rets := []
}

def NKIWalker.processAction (walker : NKIWalker) (action : VarAction) : NKIWalker :=
  let N := walker.num_nodes
  {walker with
    num_nodes := N + 1
    last_node := N
    actions n := if n = N then action else walker.actions n
    edges A B := (A, B) = (walker.last_node, N)
                ∨ (walker.edges A B)
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
  | Stmt'.assign (x : Expr) (ty : Option Expr) (e : Option Expr) =>
    let withx := (walker.processExpr x)
    let withty := (match ty with | some ty => withx.processExpr ty | none => withx)
    match e with | some e => withty.processExpr e | none => withty
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
