import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.RingTheory.Ideal.Operations

namespace GrochowIdealTransfers

open Matrix

theorem rank_transpose_sum {F ι : Type*} [Field F] [Fintype ι] (X : Matrix ι ι F) :
    (X + X.transpose).rank ≤ X.rank + X.rank := by
  have h := LinearMap.range_add_le X.mulVecLin X.transpose.mulVecLin
  calc
    (X + X.transpose).rank
        ≤ Module.finrank F (LinearMap.range X.mulVecLin ⊔
            LinearMap.range X.transpose.mulVecLin : Submodule F (ι → F)) := by
          rw [Matrix.rank, Matrix.mulVecLin_add]
          exact Submodule.finrank_mono h
    _ ≤ X.rank + X.transpose.rank := Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = X.rank + X.rank := by rw [Matrix.rank_transpose]

theorem transpose_sum_section {F ι : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    (S : Matrix ι ι F) (hS : S.IsSymm) :
    ∃ X : Matrix ι ι F, X + X.transpose = S := by
  refine ⟨(2 : F)⁻¹ • S, ?_⟩
  rw [Matrix.transpose_smul, hS.eq, ← add_smul, ← two_mul, mul_inv_cancel₀ htwo, one_smul]

theorem frobenius_difference_mem_power {R : Type*} [CommRing R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (e : ℕ) (I : Ideal R) (a b : R) (h : a - b ∈ I) :
    a ^ (p ^ e) - b ^ (p ^ e) ∈ I ^ (p ^ e) := by
  rw [← sub_pow_char_pow]
  exact Ideal.pow_mem_pow h _

#print axioms rank_transpose_sum
#print axioms transpose_sum_section
#print axioms frobenius_difference_mem_power

end GrochowIdealTransfers
