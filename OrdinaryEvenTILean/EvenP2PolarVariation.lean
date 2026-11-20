import FourierTransfer
import EvenP2PolarCharacters
import EvenPrimaryFourier
import Mathlib.FieldTheory.Finiteness

namespace Mathproof.EvenOrdinaryTISingular

open scoped TensorProduct Matrix BigOperators
open Module LinearMap Matrix
open Mathproof.Problem17PolarAssembly Mathproof.Problem17TracePairing
open Mathproof.EvenOrdinaryTISingular.PolarOperator
open Mathproof.Problem17TensorEscape
open Mathproof.Problem17TraceCharacters Mathproof.Problem17FourierTransfer

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}



variable {S R : MatSubspace K n}
variable (hS : S ≤ TraceSpace K n) (hR : R ≤ TraceSpace K n)

section Finite

variable [Fintype K]

noncomputable local instance : Fintype (S ⊗[K] R) :=
  @Fintype.ofFinite _ (Module.finite_of_finite K)

noncomputable local instance : Fintype (jointTarget K n) := Fintype.ofFinite _

theorem jointTarget_card_le :
    Fintype.card (jointTarget K n) ≤ Fintype.card K ^ (2 * (n*n)) := by
  rw [Module.card_eq_pow_finrank (K:=K) (V:=jointTarget K n)]
  apply Nat.pow_le_pow_right (by positivity)
  have h := Submodule.finrank_le (jointTarget K n)
  simp only [Module.finrank_prod, finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, two_mul] at h ⊢
  exact h

set_option maxHeartbeats 650000 in
/-- Joint total variation on arbitrary projected trace-zero subspaces, with the
codimension-dependent exponent used in the even-order singular-cut proof. -/
theorem restricted_covariant_variation_sq (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (c : ℕ) (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c) :
    ((∑ y, ‖Mathproof.Problem18FourierCore20260930.uniformImageWeight
      (restrictedCovariants hS hR) y - (Fintype.card (jointTarget K n) : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card (jointTarget K n) : ℝ) *
        ((Fintype.card K : ℝ) ^ ((n - 4*c) * (n*n - 2*c)))⁻¹ / 4 := by
  refine image_variation_of_polar_rank (V:=S ⊗[K] R) (F:=K) (G:=jointTarget K n)
    (restrictedCovariants hS hR) ((n-4*c)*(n*n-2*c)) ?_
  intro χ hχ
  obtain ⟨P,Q,h,hr⟩ := restricted_character_polar_rank hS hR ψ hψ c hSc hRc χ hχ
  refine ⟨ψ, (fun z => jointValue P Q (embed (subspaceTensor hS hR z) ^ 2)),
    restrictedPolar hS hR P Q, hψ, h, ?_, hr⟩
  intro x y
  change jointValue P Q (embed (subspaceTensor hS hR (x+y)) ^ 2) =
    jointValue P Q (embed (subspaceTensor hS hR x) ^ 2) +
    jointValue P Q (embed (subspaceTensor hS hR y) ^ 2) +
    supportedPolar P Q (subspaceTensor hS hR y) (subspaceTensor hS hR x)
  rw [map_add]
  let u := subspaceTensor hS hR x
  let v := subspaceTensor hS hR y
  have h := jointValue_square_add P Q v u
  rw [add_comm v u, add_comm (jointValue P Q (embed v ^ 2))
    (jointValue P Q (embed u ^ 2))] at h
  exact h


/-- The enumerator budget bounds codimension strongly enough for an
exponent of four times the number of entries in a retained anchor. -/
theorem restricted_polar_exponent_ge (q n c : ℕ)
    (hq : 2 ≤ q) (hn : 64 ≤ n) (hc : q ^ c ≤ n) :
    4 * (n*n) ≤ (n - 4*c) * (n*n - 2*c) := by
  have hsmall : 8*c ≤ n := by
    by_cases hs : c ≤ 8
    · omega
    · have hp (k : ℕ) : 8 * (8+k) ≤ 2 ^ (8+k) := by
        induction k with
        | zero => decide
        | succ k ih =>
          rw [show 8 + (k+1) = (8+k)+1 by omega, pow_succ]
          omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 8 ≤ c by omega)
      exact (hp k).trans ((Nat.pow_le_pow_left hq _).trans hc)
  have hN : n ≤ n*n := by
    simpa using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
  have ha : 8 ≤ n-4*c := by omega
  have hb : n*n ≤ 2 * (n*n-2*c) := by omega
  calc
    4 * (n*n) ≤ 4 * (2 * (n*n-2*c)) := Nat.mul_le_mul_left 4 hb
    _ = 8 * (n*n-2*c) := by omega
    _ ≤ _ := Nat.mul_le_mul_right (n*n-2*c) ha

/-- L1 distance from the exact joint matrix law on a uniform tensor crop.
The trace target works in characteristic two and in odd characteristic. -/
theorem restricted_covariant_l1_error (c : ℕ) (hn : 64 ≤ n)
    (hc : Fintype.card K ^ c ≤ n)
    (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c) :
    (∑ y, |EvenTI.Primary.weight (restrictedCovariants hS hR) y -
      (Fintype.card (jointTarget K n) : ℝ)⁻¹|) ≤
      ((Fintype.card K : ℝ) ^ (n*n))⁻¹ := by
  have : Nontrivial (AddChar K ℂ) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [AddChar.card_eq]
    exact Fintype.one_lt_card)
  obtain ⟨ψ, hψ⟩ := exists_ne (1 : AddChar K ℂ)
  apply (EvenTI.Primary.weight_L1_le_of_fourier_sq _ _
    (restricted_covariant_variation_sq hS hR ψ hψ c hSc hRc)).trans
  let q := (Fintype.card K : ℝ)
  let w := n*n
  let e := (n - 4*c) * (n*n - 2*c)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos (α := K))
  have hcard : (Fintype.card (jointTarget K n) : ℝ) ≤ q^(2*w) := by
    dsimp [q,w]
    exact_mod_cast (jointTarget_card_le (K := K) (n := n))
  have hExp : 4*w ≤ e :=
    restricted_polar_exponent_ge _ n c Fintype.one_lt_card hn hc
  have hProduct : (Fintype.card (jointTarget K n) : ℝ) * (q^w)^2 ≤ q^e := by
    calc
      _ ≤ q^(2*w) * (q^w)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = q^(4*w) := by rw [← pow_mul, ← pow_add, show 2*w+w*2 = 4*w by omega]
      _ ≤ q^e := pow_le_pow_right₀ hq1 hExp
  have hB : (Fintype.card (jointTarget K n) : ℝ) * (q^e)⁻¹ ≤ ((q^w)⁻¹)^2 := by
    calc
      _ = (Fintype.card (jointTarget K n) : ℝ) / q^e := (div_eq_mul_inv _ _).symm
      _ ≤ 1 / (q^w)^2 := (div_le_div_iff₀ (pow_pos hq0 _) (by positivity)).mpr
        (by simpa only [one_mul] using hProduct)
      _ = _ := by rw [one_div, inv_pow]
  change 2 * Real.sqrt ((Fintype.card (jointTarget K n) : ℝ) * (q^e)⁻¹ / 4) ≤ (q^w)⁻¹
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card (jointTarget K n) : ℝ) * (q^e)⁻¹ / 4)]
  nlinarith
end Finite
end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.restricted_covariant_variation_sq

#print axioms Mathproof.EvenOrdinaryTISingular.restricted_polar_exponent_ge
#print axioms Mathproof.EvenOrdinaryTISingular.restricted_covariant_l1_error



