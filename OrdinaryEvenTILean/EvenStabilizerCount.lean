import EvenStabilizerRank
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace EvenTI.Action

open Matrix

variable {K : Type*} [Field K] [Fintype K] {n l : Nat}

private theorem subIdentity_mulVec_zero_iff (g : Changes K (l + 1) n)
    (x : Tensor K (l + 1) n) :
    (productMatrix g - 1).mulVecLin x = 0 ↔ act g x = x := by
  change (productMatrix g - 1).mulVec x = 0 ↔ act g x = x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rfl

/-- The exact fixed-point count incurs at least the full complementary-mode
factor in the denominator when a physical mode is nonscalar. -/
theorem nonscalar_fixed_count (g : Changes K (l + 1) n) (i : Fin (l + 1))
    (hn : 0 < n) (hg : ¬ ∃ u : Kˣ, g i = scalar u) :
    Nat.card {x : Tensor K (l + 1) n // act g x = x} *
      Fintype.card K ^ (n ^ l) ≤ Fintype.card (Tensor K (l + 1) n) := by
  classical
  let f := (productMatrix g - 1).mulVecLin
  let e : {x : Tensor K (l + 1) n // act g x = x} ≃ f.ker :=
    Equiv.subtypeEquivRight fun x => (subIdentity_mulVec_zero_iff g x).symm
  letI : Fintype f.ker := Fintype.ofFinite _
  have hRank : n ^ l ≤ Module.finrank K f.range :=
    rank_sub_one_of_nonscalar g i hn hg
  have hsum := f.finrank_range_add_finrank_ker
  have hker : Module.finrank K f.ker + n ^ l ≤ Module.finrank K (Tensor K (l + 1) n) := by
    change Module.finrank K f.ker + n ^ l ≤ Module.finrank K (Coord (l + 1) n → K)
    omega
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := f.ker),
    ← pow_add, Module.card_eq_pow_finrank (K := K) (V := Tensor K (l + 1) n)]
  exact Nat.pow_le_pow_right (Fintype.card_pos (α := K)) hker

#print axioms nonscalar_fixed_count

end EvenTI.Action
