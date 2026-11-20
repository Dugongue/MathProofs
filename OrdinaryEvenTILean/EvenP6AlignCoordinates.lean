import EvenP6AlignClassify

namespace EvenTI.PrimaryAlignment

open scoped BigOperators
open Matrix Module Polynomial EvenTI.Contract
open Mathproof.Problem17ComparatorPrimaryAlign

variable {K : Type} [Field K] [DecidableEq K] {m : ℕ}

/-- Evaluate a coefficient word as a matrix over the original base field. -/
def scalarMatrix (A : Matrix (Fin m) (Fin m) K) (c : Fin m → K) :
    Matrix (Fin m) (Fin m) K :=
  ∑ i : Fin m, c i • A ^ i.val

theorem scalarMatrix_eq_rootAction (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m)
    (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) (c : Fin m → K) :
    scalarMatrix A c =
      matrixRootAction p A hA ((fieldBasis p hp hd).equivFun.symm c) := by
  rw [Basis.equivFun_symm_apply, map_sum]
  simp only [scalarMatrix, map_smul, fieldBasis_apply, map_pow, matrixRootAction_root]

/-- In the two common-field coordinate frames, any actual intertwiner
multiplies all vectors by the same unique scalar. -/
theorem fieldVector_transport_iff (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B X : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0) :
    B * X = X * A ↔ ∃! c : AdjoinRoot p, ∀ d, X.mulVec (fieldVector p A hA d) =
      fieldVector p B hB (c * d) := by
  have hg := simpleGauge_eq_some p hp hd A (B := B) hA
  let G := krylovMatrix B * (krylovMatrix A)⁻¹
  change simpleGauge A B = some G at hg
  have he : ∀ c : AdjoinRoot p, X = G * matrixRootAction p A hA c ↔
      ∀ d, X.mulVec (fieldVector p A hA d) = fieldVector p B hB (c * d) := by
    intro c
    have hstep (d : AdjoinRoot p) :
        (G * matrixRootAction p A hA c).mulVec (fieldVector p A hA d) =
          fieldVector p B hB (c * d) := by
      rw [← Matrix.mulVec_mulVec, ← fieldVector_mul, simpleGauge_mulVec p hp hd A B hA hB G hg]
    constructor
    · rintro rfl
      exact hstep
    · intro h
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨d, rfl⟩ := fieldVector_surjective p hp hd A hA v
      change X.mulVec (fieldVector p A hA d) =
        (G * matrixRootAction p A hA c).mulVec (fieldVector p A hA d)
      exact (h d).trans (hstep d).symm
  rw [simpleGauge_classify p hp hd A B hA hB G hg]
  exact existsUnique_congr he

/-- The computed repeated-block scan is exhaustive under the ambient
square-dimension budget. -/
theorem mem_boundedUnits_of_square_budget [Fintype K] (F : FieldEncoding K) (budget : ℕ)
    (A B X : Matrix (Fin m) (Fin m) K) (h : Fintype.card K ^ (m * m) ≤ budget) :
    X ∈ boundedUnits F budget A B ↔ B * X = X * A ∧ IsUnit X := by
  have hx := (Nat.pow_le_pow_right Fintype.card_pos (intertwinerBasis_length_le A B)).trans h
  simp [mem_boundedUnits, hx]

#print axioms scalarMatrix_eq_rootAction
#print axioms fieldVector_transport_iff
#print axioms mem_boundedUnits_of_square_budget

end EvenTI.PrimaryAlignment
