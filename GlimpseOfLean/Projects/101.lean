import Mathlib
-- import Mathlib.Combinatorics.SimpleGraph.Basic
-- import Mathlib.Combinatorics.SimpleGraph.Path
-- import Mathlib.Combinatorics.SimpleGraph.Connectivity
-- import Mathlib.Data.Int.Basic
-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Fin.Basic
-- import Mathlib.Data.List.Basic
-- import Mathlib.Data.Seq.Seq

/--define rectilinear and unit length graphs--/
structure RectNode where
  a : ℕ
  i : ℕ
  x : ℤ
  y : ℤ
  even_sum : Even (x+y)

def Adj (u v : RectNode) : Prop :=

  sorry
/--define sequence graphs-/
