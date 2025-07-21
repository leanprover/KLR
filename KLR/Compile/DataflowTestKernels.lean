import KLR.NKI.Basic
open KLR.NKI

section TestKernels

def start_highlight := "⦃!" --"◯" --"⇉"
def end_highlight := "⦄" --"◯" --"⇇"

class HasKernel where
    kernel : Fun
    kernel_str : String

instance : ToString Pos where toString p := s!"{p.line}, {p.lineEnd}, {p.column}, {p.columnEnd}"

def highlight_pos_set [HasKernel] (actions : List Pos) (s : String) : String :=
  let newlines : List Nat := (List.range s.length).filter (fun n ↦ s.toList[n]! = '\n')

  let findStart (pos : Pos) : List Nat := [newlines[pos.line - 1]! + pos.column + 1]
  let findEnd (pos : Pos) : List Nat := match pos.lineEnd, pos.columnEnd with
    | some l, some c => [newlines[l - 1]! + c + 1]
    | _, _ => []
  let starts := actions.flatMap findStart
  let ends := actions.flatMap findEnd
  let out_str_at n : List Char :=
    let st := if n ∈ starts then start_highlight.toList else []
    let ed := if n ∈ ends then end_highlight.toList else []
    st ++ ed ++ [s.toList[n]!]
  ⟨((List.range s.length).flatMap out_str_at)⟩

def kernel_highlighted_repr [HasKernel] (actions : List Pos) : String :=
  highlight_pos_set actions HasKernel.kernel_str


def safe_kernel_1 : HasKernel where
  kernel_str :="
  def test():
  x = 0
  c = 0
  p = 0
  if c:
    p(x)
  else:
    y = 0
    p(y)
  p(x)"
  kernel := { name := "test.test",
              file := "unknown",
              line := 1,
              body := [{ stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "x",
                                      pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 2, column := 5, lineEnd := some 2, columnEnd := some 6 } }),
                          pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "c",
                                      pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 3, column := 5, lineEnd := some 3, columnEnd := some 6 } }),
                          pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "p",
                                      pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 4, column := 5, lineEnd := some 4, columnEnd := some 6 } }),
                          pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.ifStm
                                    { expr := KLR.NKI.Expr'.var "c",
                                      pos := { line := 5, column := 4, lineEnd := some 5, columnEnd := some 5 } }
                                    [{ stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "p",
                                                              pos := { line := 6,
                                                                        column := 2,
                                                                        lineEnd := some 6,
                                                                        columnEnd := some 3 } }
                                                            [{ expr := KLR.NKI.Expr'.var "x",
                                                                pos := { line := 6,
                                                                          column := 4,
                                                                          lineEnd := some 6,
                                                                          columnEnd := some 5 } }]
                                                            [],
                                                  pos := { line := 6,
                                                            column := 2,
                                                            lineEnd := some 6,
                                                            columnEnd := some 6 } },
                                        pos := { line := 6, column := 2, lineEnd := some 6, columnEnd := some 6 } }]
                                    [{ stmt := KLR.NKI.Stmt'.assign
                                                { expr := KLR.NKI.Expr'.var "y",
                                                  pos := { line := 8,
                                                            column := 2,
                                                            lineEnd := some 8,
                                                            columnEnd := some 3 } }
                                                none
                                                (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                                          pos := { line := 8,
                                                                    column := 6,
                                                                    lineEnd := some 8,
                                                                    columnEnd := some 7 } }),
                                         pos := { line := 8, column := 2, lineEnd := some 8, columnEnd := some 7 } },
                                    { stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "p",
                                                              pos := { line := 9,
                                                                        column := 2,
                                                                        lineEnd := some 9,
                                                                        columnEnd := some 3 } }
                                                            [{ expr := KLR.NKI.Expr'.var "y",
                                                                pos := { line := 9,
                                                                          column := 4,
                                                                          lineEnd := some 9,
                                                                         columnEnd := some 5 } }]
                                                            [],
                                                  pos := { line := 9,
                                                            column := 2,
                                                            lineEnd := some 9,
                                                            columnEnd := some 6 } },
                                      pos := { line := 9, column := 2, lineEnd := some 9, columnEnd := some 6 } }],
                          pos := { line := 5, column := 1, lineEnd := some 9, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.expr
                                    { expr := KLR.NKI.Expr'.call
                                                { expr := KLR.NKI.Expr'.var "p",
                                                  pos := { line := 10,
                                                           column := 1,
                                                           lineEnd := some 10,
                                                            columnEnd := some 2 } }
                                                [{ expr := KLR.NKI.Expr'.var "x",
                                                   pos := { line := 10,
                                                            column := 3,
                                                            lineEnd := some 10,
                                                            columnEnd := some 4 } }]
                                                [],
                                      pos := { line := 10, column := 1, lineEnd := some 10, columnEnd := some 5 } },
                          pos := { line := 10, column := 1, lineEnd := some 10, columnEnd := some 5 } }],
              args := [] }

def unsafe_kernel_2 : HasKernel where
  kernel_str := "
def test():
	x = 0
	c = 0
	p = 0
	if c:
		p(x)
	else:
		y = 0
		p(y)
	p(y)
  "
  kernel := { name := "test.test",
              file := "unknown",
              line := 1,
              body := [{ stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "x",
                                      pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 2, column := 5, lineEnd := some 2, columnEnd := some 6 } }),
                          pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "c",
                                      pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 3, column := 5, lineEnd := some 3, columnEnd := some 6 } }),
                          pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.assign
                                    { expr := KLR.NKI.Expr'.var "p",
                                      pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 2 } }
                                    none
                                    (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                            pos := { line := 4, column := 5, lineEnd := some 4, columnEnd := some 6 } }),
                          pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.ifStm
                                    { expr := KLR.NKI.Expr'.var "c",
                                      pos := { line := 5, column := 4, lineEnd := some 5, columnEnd := some 5 } }
                                    [{ stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "p",
                                                              pos := { line := 6,
                                                                        column := 2,
                                                                        lineEnd := some 6,
                                                                        columnEnd := some 3 } }
                                                            [{ expr := KLR.NKI.Expr'.var "x",
                                                                pos := { line := 6,
                                                                          column := 4,
                                                                          lineEnd := some 6,
                                                                          columnEnd := some 5 } }]
                                                            [],
                                                  pos := { line := 6,
                                                            column := 2,
                                                            lineEnd := some 6,
                                                            columnEnd := some 6 } },
                                        pos := { line := 6, column := 2, lineEnd := some 6, columnEnd := some 6 } }]
                                    [{ stmt := KLR.NKI.Stmt'.assign
                                                { expr := KLR.NKI.Expr'.var "y",
                                                  pos := { line := 8,
                                                            column := 2,
                                                            lineEnd := some 8,
                                                            columnEnd := some 3 } }
                                                none
                                                (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                                        pos := { line := 8,
                                                                  column := 6,
                                                                  lineEnd := some 8,
                                                                  columnEnd := some 7 } }),
                                        pos := { line := 8, column := 2, lineEnd := some 8, columnEnd := some 7 } },
                                    { stmt := KLR.NKI.Stmt'.expr
                                                { expr := KLR.NKI.Expr'.call
                                                            { expr := KLR.NKI.Expr'.var "p",
                                                              pos := { line := 9,
                                                                        column := 2,
                                                                        lineEnd := some 9,
                                                                        columnEnd := some 3 } }
                                                            [{ expr := KLR.NKI.Expr'.var "y",
                                                                pos := { line := 9,
                                                                         column := 4,
                                                                          lineEnd := some 9,
                                                                          columnEnd := some 5 } }]
                                                            [],
                                                  pos := { line := 9,
                                                            column := 2,
                                                            lineEnd := some 9,
                                                            columnEnd := some 6 } },
                                      pos := { line := 9, column := 2, lineEnd := some 9, columnEnd := some 6 } }],
                          pos := { line := 5, column := 1, lineEnd := some 9, columnEnd := some 6 } },
                        { stmt := KLR.NKI.Stmt'.expr
                                    { expr := KLR.NKI.Expr'.call
                                                { expr := KLR.NKI.Expr'.var "p",
                                                  pos := { line := 10,
                                                            column := 1,
                                                             lineEnd := some 10,
                                                              columnEnd := some 2 } }
                                                [{ expr := KLR.NKI.Expr'.var "y",
                                                    pos := { line := 10,
                                                               column := 3,
                                                               lineEnd := some 10,
                                                                columnEnd := some 4 } }]
                                                [],
                                      pos := { line := 10, column := 1, lineEnd := some 10, columnEnd := some 5 } },
                          pos := { line := 10, column := 1, lineEnd := some 10, columnEnd := some 5 } }],
              args := [] }


def unsafe_kernel_3 : HasKernel where
  kernel_str := "
def test():
	x = 0
	c = 0
	p = 0
	if c:
		p(x)
		for z in x:
			w = 0
			p(w)
			p(z)
		p(w)
		p(z)
	else:
		y = 0
		p(x)
		p(y)
	p(x)
	p(y)
	p(z)"
  kernel := {name := "test.test",
             file := "unknown",
             line := 1,
             body := [{ stmt := KLR.NKI.Stmt'.assign
                                  { expr := KLR.NKI.Expr'.var "x",
                                    pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 2 } }
                                  none
                                  (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                          pos := { line := 2, column := 5, lineEnd := some 2, columnEnd := some 6 } }),
                        pos := { line := 2, column := 1, lineEnd := some 2, columnEnd := some 6 } },
                      { stmt := KLR.NKI.Stmt'.assign
                                  { expr := KLR.NKI.Expr'.var "c",
                                    pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 2 } }
                                  none
                                  (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                          pos := { line := 3, column := 5, lineEnd := some 3, columnEnd := some 6 } }),
                        pos := { line := 3, column := 1, lineEnd := some 3, columnEnd := some 6 } },
                      { stmt := KLR.NKI.Stmt'.assign
                                  { expr := KLR.NKI.Expr'.var "p",
                                    pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 2 } }
                                  none
                                  (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                          pos := { line := 4, column := 5, lineEnd := some 4, columnEnd := some 6 } }),
                        pos := { line := 4, column := 1, lineEnd := some 4, columnEnd := some 6 } },
                      { stmt := KLR.NKI.Stmt'.ifStm
                                  { expr := KLR.NKI.Expr'.var "c",
                                    pos := { line := 5, column := 4, lineEnd := some 5, columnEnd := some 5 } }
                                  [{ stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "p",
                                                             pos := { line := 6,
                                                                      column := 2,
                                                                      lineEnd := some 6,
                                                                      columnEnd := some 3 } }
                                                           [{ expr := KLR.NKI.Expr'.var "x",
                                                              pos := { line := 6,
                                                                       column := 4,
                                                                       lineEnd := some 6,
                                                                       columnEnd := some 5 } }]
                                                           [],
                                                 pos := { line := 6,
                                                          column := 2,
                                                          lineEnd := some 6,
                                                          columnEnd := some 6 } },
                                     pos := { line := 6, column := 2, lineEnd := some 6, columnEnd := some 6 } },
                                   { stmt := KLR.NKI.Stmt'.forLoop
                                               { expr := KLR.NKI.Expr'.var "z",
                                                 pos := { line := 7,
                                                          column := 6,
                                                          lineEnd := some 7,
                                                          columnEnd := some 7 } }
                                               { expr := KLR.NKI.Expr'.var "x",
                                                 pos := { line := 7,
                                                          column := 11,
                                                          lineEnd := some 7,
                                                          columnEnd := some 12 } }
                                               [{ stmt := KLR.NKI.Stmt'.assign
                                                            { expr := KLR.NKI.Expr'.var "w",
                                                              pos := { line := 8,
                                                                       column := 3,
                                                                       lineEnd := some 8,
                                                                       columnEnd := some 4 } }
                                                            none
                                                            (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                                                    pos := { line := 8,
                                                                              column := 7,
                                                                              lineEnd := some 8,
                                                                              columnEnd := some 8 } }),
                                                  pos := { line := 8,
                                                           column := 3,
                                                           lineEnd := some 8,
                                                           columnEnd := some 8 } },
                                                { stmt := KLR.NKI.Stmt'.expr
                                                            { expr := KLR.NKI.Expr'.call
                                                                        { expr := KLR.NKI.Expr'.var "p",
                                                                          pos := { line := 9,
                                                                                   column := 3,
                                                                                   lineEnd := some 9,
                                                                                   columnEnd := some 4 } }
                                                                        [{ expr := KLR.NKI.Expr'.var "w",
                                                                           pos := { line := 9,
                                                                                    column := 5,
                                                                                    lineEnd := some 9,
                                                                                    columnEnd := some 6 } }]
                                                                        [],
                                                              pos := { line := 9,
                                                                       column := 3,
                                                                       lineEnd := some 9,
                                                                       columnEnd := some 7 } },
                                                  pos := { line := 9,
                                                           column := 3,
                                                           lineEnd := some 9,
                                                           columnEnd := some 7 } },
                                                { stmt := KLR.NKI.Stmt'.expr
                                                            { expr := KLR.NKI.Expr'.call
                                                                        { expr := KLR.NKI.Expr'.var "p",
                                                                          pos := { line := 10,
                                                                                   column := 3,
                                                                                   lineEnd := some 10,
                                                                                   columnEnd := some 4 } }
                                                                        [{ expr := KLR.NKI.Expr'.var "z",
                                                                           pos := { line := 10,
                                                                                    column := 5,
                                                                                    lineEnd := some 10,
                                                                                    columnEnd := some 6 } }]
                                                                        [],
                                                              pos := { line := 10,
                                                                       column := 3,
                                                                       lineEnd := some 10,
                                                                       columnEnd := some 7 } },
                                                  pos := { line := 10,
                                                           column := 3,
                                                           lineEnd := some 10,
                                                           columnEnd := some 7 } }],
                                     pos := { line := 7, column := 2, lineEnd := some 10, columnEnd := some 7 } },
                                   { stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "p",
                                                             pos := { line := 11,
                                                                      column := 2,
                                                                      lineEnd := some 11,
                                                                      columnEnd := some 3 } }
                                                           [{ expr := KLR.NKI.Expr'.var "w",
                                                              pos := { line := 11,
                                                                       column := 4,
                                                                       lineEnd := some 11,
                                                                       columnEnd := some 5 } }]
                                                           [],
                                                 pos := { line := 11,
                                                          column := 2,
                                                          lineEnd := some 11,
                                                          columnEnd := some 6 } },
                                     pos := { line := 11, column := 2, lineEnd := some 11, columnEnd := some 6 } },
                                   { stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "p",
                                                             pos := { line := 12,
                                                                      column := 2,
                                                                      lineEnd := some 12,
                                                                      columnEnd := some 3 } }
                                                           [{ expr := KLR.NKI.Expr'.var "z",
                                                              pos := { line := 12,
                                                                       column := 4,
                                                                       lineEnd := some 12,
                                                                       columnEnd := some 5 } }]
                                                           [],
                                                 pos := { line := 12,
                                                          column := 2,
                                                          lineEnd := some 12,
                                                          columnEnd := some 6 } },
                                     pos := { line := 12, column := 2, lineEnd := some 12, columnEnd := some 6 } }]
                                  [{ stmt := KLR.NKI.Stmt'.assign
                                               { expr := KLR.NKI.Expr'.var "y",
                                                 pos := { line := 14,
                                                          column := 2,
                                                          lineEnd := some 14,
                                                          columnEnd := some 3 } }
                                               none
                                               (some { expr := KLR.NKI.Expr'.value (KLR.NKI.Value.int 0),
                                                        pos := { line := 14,
                                                                    column := 6,
                                                                    lineEnd := some 14,
                                                                    columnEnd := some 7 } }),
                                     pos := { line := 14, column := 2, lineEnd := some 14, columnEnd := some 7 } },
                                   { stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "p",
                                                             pos := { line := 15,
                                                                      column := 2,
                                                                      lineEnd := some 15,
                                                                      columnEnd := some 3 } }
                                                           [{ expr := KLR.NKI.Expr'.var "x",
                                                              pos := { line := 15,
                                                                       column := 4,
                                                                       lineEnd := some 15,
                                                                       columnEnd := some 5 } }]
                                                           [],
                                                 pos := { line := 15,
                                                          column := 2,
                                                          lineEnd := some 15,
                                                          columnEnd := some 6 } },
                                     pos := { line := 15, column := 2, lineEnd := some 15, columnEnd := some 6 } },
                                   { stmt := KLR.NKI.Stmt'.expr
                                               { expr := KLR.NKI.Expr'.call
                                                           { expr := KLR.NKI.Expr'.var "p",
                                                             pos := { line := 16,
                                                                      column := 2,
                                                                      lineEnd := some 16,
                                                                      columnEnd := some 3 } }
                                                           [{ expr := KLR.NKI.Expr'.var "y",
                                                              pos := { line := 16,
                                                                       column := 4,
                                                                       lineEnd := some 16,
                                                                       columnEnd := some 5 } }]
                                                           [],
                                                 pos := { line := 16,
                                                          column := 2,
                                                          lineEnd := some 16,
                                                          columnEnd := some 6 } },
                                     pos := { line := 16, column := 2, lineEnd := some 16, columnEnd := some 6 } }],
                        pos := { line := 5, column := 1, lineEnd := some 16, columnEnd := some 6 } },
                      { stmt := KLR.NKI.Stmt'.expr
                                  { expr := KLR.NKI.Expr'.call
                                              { expr := KLR.NKI.Expr'.var "p",
                                                pos := { line := 17,
                                                         column := 1,
                                                         lineEnd := some 17,
                                                         columnEnd := some 2 } }
                                              [{ expr := KLR.NKI.Expr'.var "x",
                                                 pos := { line := 17,
                                                          column := 3,
                                                          lineEnd := some 17,
                                                          columnEnd := some 4 } }]
                                              [],
                                    pos := { line := 17, column := 1, lineEnd := some 17, columnEnd := some 5 } },
                        pos := { line := 17, column := 1, lineEnd := some 17, columnEnd := some 5 } },
                      { stmt := KLR.NKI.Stmt'.expr
                                  { expr := KLR.NKI.Expr'.call
                                              { expr := KLR.NKI.Expr'.var "p",
                                                pos := { line := 18,
                                                         column := 1,
                                                         lineEnd := some 18,
                                                         columnEnd := some 2 } }
                                              [{ expr := KLR.NKI.Expr'.var "y",
                                                 pos := { line := 18,
                                                          column := 3,
                                                          lineEnd := some 18,
                                                          columnEnd := some 4 } }]
                                              [],
                                    pos := { line := 18, column := 1, lineEnd := some 18, columnEnd := some 5 } },
                        pos := { line := 18, column := 1, lineEnd := some 18, columnEnd := some 5 } },
                      { stmt := KLR.NKI.Stmt'.expr
                                  { expr := KLR.NKI.Expr'.call
                                              { expr := KLR.NKI.Expr'.var "p",
                                                pos := { line := 19,
                                                         column := 1,
                                                         lineEnd := some 19,
                                                         columnEnd := some 2 } }
                                              [{ expr := KLR.NKI.Expr'.var "z",
                                                 pos := { line := 19,
                                                          column := 3,
                                                          lineEnd := some 19,
                                                          columnEnd := some 4 } }]
                                              [],
                                    pos := { line := 19, column := 1, lineEnd := some 19, columnEnd := some 5 } },
                        pos := { line := 19, column := 1, lineEnd := some 19, columnEnd := some 5 } }],
             args := [] }

end TestKernels
