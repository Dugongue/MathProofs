import EvenP2Mean
import EvenP2FormsKernel

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Classical Matrix
open EvenTI.Action EvenTI.Primary Module Matrix
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_one)

noncomputable section

private theorem sum_kernel_indicator {K V W : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] (A : V →ₗ[K] W) :
    (∑ v : V, if A v = 0 then (1 : ℝ) else 0) =
      ((Fintype.card K ^ finrank K A.ker : ℕ) : ℝ) := by
  letI : Fintype A.ker := Fintype.ofFinite _
  have hCount := Module.card_eq_pow_finrank (K := K) (V := A.ker)
  rw [← hCount]
  simp only [Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.refl A.ker)

theorem large_kernel_fraction {K V W Ω : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype Ω]
    (A : Ω → V →ₗ[K] W) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ v : V, v ≠ 0 → event (fun x => A x v = 0) ≤ (Fintype.card V : ℝ)⁻¹) :
    event (fun x => n < Fintype.card K ^ finrank K (A x).ker) ≤ 2 / n := by
  let h (x : Ω) : ℝ := (Fintype.card K ^ finrank K (A x).ker : ℕ)
  have hm : mean h ≤ 2 := by
    simp only [h, ← sum_kernel_indicator, mean_sum]
    change (∑ v : V, event (fun x => A x v = 0)) ≤ 2
    calc
      _ ≤ ∑ v : V, ((if v = 0 then 1 else 0) + (Fintype.card V : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v = 0
        · rw [if_pos hv]
          have h1 : event (fun x => A x v = 0) ≤ 1 := by
            rw [event_as_fraction]
            exact uniformFraction_le_one _
          exact h1.trans (le_add_of_nonneg_right (by positivity))
        · simpa [hv] using h0 v hv
      _ = 2 := by
        have hc : (Fintype.card V : ℝ) ≠ 0 := by positivity
        simp [Finset.sum_add_distrib, hc, one_add_one_eq_two]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀' hnR).mpr
  refine le_trans ?_ hm
  rw [event, ← mean_mul]
  apply mean_mono
  intro x
  by_cases hx : n < Fintype.card K ^ finrank K (A x).ker
  · simp only [if_pos hx, mul_one, h]
    exact_mod_cast (Nat.le_of_lt hx)
  · simp [hx, h]

theorem square_cut_large_corank {K : Type*} [Field K] [Fintype K]
    {s n : ℕ} (hn : 0 < n) :
    event (fun T : Tensor K (s+s) n => n < Fintype.card K ^ finrank K (rightCutKernel T).ker)
      ≤ 2 / n := by
  apply large_kernel_fraction (fun T : Tensor K (s+s) n => rightCutKernel T) n hn
  intro v hv
  rw [event_as_fraction, rightCutKernel_zero_fraction v hv]
  rw [Fintype.card_fun, cut_side_card, Nat.cast_pow, one_div]

#print axioms large_kernel_fraction
#print axioms square_cut_large_corank

end
end Mathproof.EvenTI.Singular.Coverage
