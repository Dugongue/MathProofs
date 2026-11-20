import EvenP3RecipLowMass

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.Sampling Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenOrdinaryTISingular (uniformFraction)

noncomputable section

variable {K H L J R I B BL : Type*} [Field K] [Fintype K] [Nonempty I]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype R] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq R]
variable [DecidableEq I] [DecidableEq B] [DecidableEq BL]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option (J ⊕ R)) (I := I) (B := B)
local notation "Rect" => (Matrix I B K)
local notation "T" => (traceKernel (K := K) (I := I))

private theorem labelForm_symmetric (c : Module.Dual K (Matrix I I K)) (x y : T) :
    labelForm T c x y = labelForm T c y x := by
  change c (x.val * y.val + y.val * x.val) = c (y.val * x.val + x.val * y.val)
  rw [add_comm]

private theorem fiberFailureAverage_congr_fintype {X : Type*} {Y : X → Type*}
    (f g : Fintype X) (E : (x : X) → Y x → Prop) :
    @fiberFailureAverage X f Y E = @fiberFailureAverage X g Y E :=
  congrArg (fun t => @fiberFailureAverage X t Y E) (Subsingleton.elim _ _)

set_option maxHeartbeats 400000 in
private theorem projected_failure_bound {a r : ℕ} [Fintype Bases] [Nonempty Bases]
    {W : Type*} [AddCommGroup W] [Module K W] [Fintype W] [Module.Finite K W]
    [Fintype (Dual K (J → W))]
    (g : T →ₗ[K] W) (hg : Function.Surjective g)
    (high : Fin a ↪ H) (low : BL ↪ L)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K Rect)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hRank : ∀ P : Matrix I I K, (∀ t : K, P ≠ t • 1) →
      uniformFraction (BL → Rect) (fun U => Part1.coefficientRank P U < r) ≤ δ) :
    uniformFraction Bases (fun A => ¬ Function.Surjective ((LinearMap.compLeft g J).comp
        (smallRows (matrixPrimal A.val.1) (matrixDual A.val.2) T (baseline_row_trace_zero A)))) ≤
      4 * (Fintype.card K : ℝ) ^ (Fintype.card J * finrank K W) *
        (δ + 1 / (Fintype.card K : ℝ)^(a*r)) := by
  classical
  let e : (J → W) ≃ₗ[K] Matrix J (Fin (finrank K W)) K :=
    LinearEquiv.piCongrRight (fun _ => (Module.finBasis K W).equivFun)
  have hd : finrank K (J → W) = Fintype.card J * finrank K W := by
    rw [e.finrank_eq, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  have hlabels : Fintype.card {z : Dual K (J → W) // z ≠ 0} ≤
      Fintype.card K ^ (Fintype.card J * finrank K W) := by
    apply (Fintype.card_le_of_injective
      (fun z : {z : Dual K (J → W) // z ≠ 0} => z.val) Subtype.val_injective).trans
    rw [Module.card_eq_pow_finrank (K := K) (V := Dual K (J → W)), Subspace.dual_finrank_eq, hd]
  apply (actualSmallRows_bad_mass_le_model g high low htotal).trans
  have h := unconditioned_quotientRows_bad_le (a := a) (r := r) (J := J) (L := BL) g hg δ hRank
  have hc : (Fintype.card {z : Dual K (J → W) // z ≠ 0} : ℝ) ≤
      (Fintype.card K : ℝ) ^ (Fintype.card J * finrank K W) := by exact_mod_cast hlabels
  let E (U : BL → Rect) (D : Fin a → J → Ann U) :=
    ¬ Function.Surjective (quotientRows g U D)
  have hb (f : Fintype (BL → Rect)) :
      @fiberFailureAverage (BL → Rect) f (fun U => Fin a → J → Ann U) E ≤
        (Fintype.card K : ℝ) ^ (Fintype.card J * finrank K W) *
          (δ + 1 / (Fintype.card K : ℝ)^(a*r)) := by
    have h' := h.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    convert h' using 1 <;> first
      | rfl
      | exact fiberFailureAverage_congr_fintype f _ E
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb _) (by norm_num)

set_option maxHeartbeats 400000 in
private theorem badPolar_le_badRows [Fintype Bases]
    (c : Module.Dual K (Matrix I I K)) :
    uniformFraction Bases
      (fun A => finrank K (squarePolar
        (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)) (traceBlocks c)).range <
        (Fintype.card J ^ 2 - 1) * finrank K (labelForm T c).range) ≤
    uniformFraction Bases (fun A => ¬ Function.Surjective
      ((LinearMap.compLeft (labelForm T c).rangeRestrict J).comp
        (smallRows (matrixPrimal A.val.1) (matrixDual A.val.2) T (baseline_row_trace_zero A)))) := by
  apply uniformFraction_le_of_imp
  intro A hn hs
  have hl := shear_polar_rank_of_small_quotient (matrixPrimal A.val.1) (matrixDual A.val.2)
    T (baseline_row_trace_zero A) c (labelForm_symmetric c) hs
  exact (Nat.not_lt_of_ge hl) hn

set_option maxHeartbeats 500000 in
/-- A fixed Fourier label controls its own quotient, so the failure
exponent involves only its restricted rank and the retained target count. -/
theorem actualSmallPolar_bad_mass_le {a r : ℕ} [Fintype Bases] [Nonempty Bases]
    (c : Module.Dual K (Matrix I I K)) (high : Fin a ↪ H) (low : BL ↪ L)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K Rect)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hRank : ∀ P : Matrix I I K, (∀ t : K, P ≠ t • 1) →
      uniformFraction (BL → Rect) (fun U => Part1.coefficientRank P U < r) ≤ δ) :
    uniformFraction Bases
      (fun A => finrank K (squarePolar
        (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)) (traceBlocks c)).range <
        (Fintype.card J ^ 2 - 1) * finrank K (labelForm T c).range) ≤
      4 * (Fintype.card K : ℝ) ^ (Fintype.card J * finrank K (labelForm T c).range) *
        (δ + 1 / (Fintype.card K : ℝ)^(a*r)) := by
  classical
  let C := labelForm T c
  let ρ := finrank K C.range
  let W := Fin ρ → K
  let : Module.Free K (↥C.range) := Module.Free.of_divisionRing K (↥C.range)
  let : Module.Finite K (↥C.range) := Module.Finite.of_surjective C.rangeRestrict C.surjective_rangeRestrict
  let e : (↥C.range) ≃ₗ[K] W := (Module.finBasis K (↥C.range)).equivFun
  let g : T →ₗ[K] W := e.toLinearMap.comp C.rangeRestrict
  have hg : Function.Surjective g := e.surjective.comp C.surjective_rangeRestrict
  letI : Fintype W := inferInstanceAs (Fintype (Fin ρ → K))
  letI : Module.Finite K W := inferInstanceAs (Module.Finite K (Fin ρ → K))
  letI : Fintype (Dual K (J → W)) :=
    Fintype.ofInjective (fun f : Dual K (J → W) => (f : (J → W) → K)) DFunLike.coe_injective
  have hbase := badPolar_le_badRows (H := H) (L := L) (J := J) (R := R) (B := B) c
  apply hbase.trans
  have hg' := projected_failure_bound (K := K) (H := H) (L := L) (J := J) (R := R)
    (I := I) (B := B) (BL := BL) (W := W) (a := a) (r := r) g hg high low htotal δ hδ hRank
  have hd : finrank K W = ρ := by
    change finrank K (Fin ρ → K) = ρ
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [hd] at hg'
  apply le_trans _ hg'
  apply uniformFraction_le_of_imp
  intro A hb hs
  apply hb
  intro y
  obtain ⟨x, hx⟩ := hs (fun t => e (y t))
  refine ⟨x, funext fun t => e.injective ?_⟩
  exact congrFun hx t

#print axioms actualSmallPolar_bad_mass_le

end
end Mathproof.EvenTI.Reciprocal.SquareLow
