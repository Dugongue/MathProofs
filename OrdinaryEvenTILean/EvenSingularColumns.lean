import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

namespace Mathproof.EvenOrdinaryTISingular

open scoped BigOperators

private theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h0' j (hj : j ∈ s) := h0 j (Finset.mem_insert_of_mem hj)
    have h1' j (hj : j ∈ s) := h1 j (Finset.mem_insert_of_mem hj)
    have hp : (∏ j ∈ s, (1 - f j)) ≤ 1 :=
      Finset.prod_le_one (fun j hj => sub_nonneg.mpr (h1' j hj))
        (fun j hj => sub_le_self _ (h0' j hj))
    have hfi : 0 ≤ f i := h0 _ (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      1 - (1 - f i) * (∏ j ∈ s, (1 - f j)) =
          1 - (∏ j ∈ s, (1 - f j)) + f i * (∏ j ∈ s, (1 - f j)) := by ring
      _ ≤ (∑ j ∈ s, f j) + f i := add_le_add (ih h0' h1') (mul_le_of_le_one_right hfi hp)
      _ = _ := add_comm _ _

section
variable {K V : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]

open Module

/-- The failure probability for a uniformly chosen tuple of columns.
This is the precise conditioning error used for the rectangular block law. -/
theorem dependent_column_fraction_le (b : ℕ) (hb : b ≤ finrank K V) :
    1 - (Nat.card {x : Fin b → V // LinearIndependent K x} : ℝ) /
      (Fintype.card (Fin b → V) : ℝ) ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(finrank K V) * ((Fintype.card K : ℝ) - 1)) := by
  classical
  let m := finrank K V
  let q : ℝ := Fintype.card K
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hm : 0 < q^m := pow_pos hq0 _
  have hn (i : Fin b) : Fintype.card K ^ i.val ≤ Fintype.card K ^ m :=
    Nat.pow_le_pow_right (by exact Fintype.card_pos) (i.isLt.le.trans hb)
  have hpow (i : Fin b) : q ^ i.val ≤ q ^ m := by
    dsimp only [q]
    exact_mod_cast hn i
  have hcard : (Fintype.card (Fin b → V) : ℝ) = (q^m)^b := by
    rw [Fintype.card_fun, Module.card_eq_pow_finrank (K := K) (V := V), Fintype.card_fin]
    push_cast
    rfl
  have hgood : (Nat.card {x : Fin b → V // LinearIndependent K x} : ℝ) =
      ∏ i : Fin b, (q^m - q^i.val) := by
    rw [card_linearIndependent hb, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (hn i)]
    push_cast
    rfl
  rw [hcard, hgood, ← show ∏ _ : Fin b, q^m = (q^m)^b by simp, ← Finset.prod_div_distrib]
  calc
    _ ≤ ∑ i : Fin b, q ^ i.val / q^m := by
      simpa only [sub_div, div_self hm.ne'] using
        one_sub_prod_le_sum Finset.univ (fun i : Fin b => q ^ i.val / q^m)
          (fun _ _ => div_nonneg (pow_nonneg hq0.le _) hm.le)
          (fun i _ => (div_le_one hm).mpr (hpow i))
    _ = _ := by
      rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range,
        geom_sum_eq hq.ne', div_div, mul_comm ((q - 1))]

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.dependent_column_fraction_le
