import EvenP6AlignWordTable

namespace EvenTI.PrimaryAlignment

open Matrix Polynomial
open EvenTI.CellProducer

variable {K : Type} [Field K] [DecidableEq K] {m : ℕ}

/-- A genuine simple-block unit acts on the actual computed coordinate
table by multiplication with a nonzero coefficient word. -/
theorem simpleWordAction_of_intertwiner (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B X : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0)
    (T : WordTable K (Fin m)) (hT : prepareSimpleWordTable A = some T)
    (hX : B * X = X * A) (hunit : IsUnit X) :
    ∃ c : Fin m → K, c ≠ 0 ∧ ∀ d,
      X.mulVec ((krylovMatrix A).mulVec d) = (krylovMatrix B).mulVec (T.multiply c d) := by
  let D := (fieldBasis p hp hd).equivFun.symm
  obtain ⟨u, hu, _⟩ := (fieldVector_transport_iff p hp hd A B X hA hB).mp hX
  have hne : u ≠ 0 := by
    intro h
    have hv := hu 1
    rw [h, zero_mul, map_zero, fieldVector_one] at hv
    have hv' := Matrix.mulVec_injective_iff_isUnit.mpr hunit (hv.trans (Matrix.mulVec_zero _).symm)
    exact firstVector_ne_zero (K := K) (hd ▸ (Fact.out : Irreducible p).natDegree_pos) hv'
  refine ⟨D.symm u, fun hz => hne ?_, fun d => ?_⟩
  · have h := congrArg D hz
    rwa [D.apply_symm_apply, map_zero] at h
  · obtain ⟨_,hm⟩ := prepareSimpleWordTable_model p hp hd A hA T hT
    rw [krylovMatrix_mulVec p hp hd A hA, krylovMatrix_mulVec p hp hd B hB]
    change X.mulVec (fieldVector p A hA (D d)) =
      fieldVector p B hB (D (T.multiply (D.symm u) d))
    rw [show D (T.multiply (D.symm u) d) = D (D.symm u) * D d from hm _ _,
      D.apply_symm_apply]
    exact hu (D d)

#print axioms simpleWordAction_of_intertwiner

end EvenTI.PrimaryAlignment
