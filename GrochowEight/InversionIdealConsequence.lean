import Mathlib.Data.Matrix.ColumnRowPartitioned

open Matrix

/-- The inversion rule can carry a linear combination of its input entries
to a new entry, with no products of input entries in either displayed product. -/
theorem inversionIdealConsequenceMatrix
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (f : Matrix ι Unit R) (g : Matrix Unit ι R) :
    ∃ A B : Matrix ((ι ⊕ Unit) ⊕ Unit) ((ι ⊕ Unit) ⊕ Unit) R,
      A * B = fromBlocks 1 (fromRows f 0) 0 1 ∧
      B * A = fromBlocks 1 (fromRows f (g * f)) 0 1 := by
  let U : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R := fromBlocks 1 0 g 1
  let L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R := fromBlocks 1 0 (-g) 1
  have hLU : L * U = 1 := by
    simp [L, U, fromBlocks_multiply, fromBlocks_one]
  have hUL : U * L = 1 := by
    simp [L, U, fromBlocks_multiply, fromBlocks_one]
  have hcol : L * fromRows f (g * f) = fromRows f 0 := by
    simp [L, fromBlocks_mul_fromRows]
  refine ⟨fromBlocks L 0 0 1, fromBlocks U (fromRows f (g * f)) 0 1, ?_, ?_⟩
  · simp [fromBlocks_multiply, hLU, hcol]
  · simp [fromBlocks_multiply, hUL]

#print axioms inversionIdealConsequenceMatrix
