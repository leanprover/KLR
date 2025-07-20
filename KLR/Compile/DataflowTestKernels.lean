import KLR.NKI.Basic
open KLR.NKI

class HasKernel where
    kernel : Fun
    repr : String

def safe_kernel_1 : HasKernel where
  repr := "
  def test():
	x = 0
	c = 0
	p = 0
	if c:
		p(x)
	else:
		y = 0
		p(y)
	p(x)
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
  repr := "
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
