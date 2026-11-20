import EvenP1ProbAverage
import EvenP1ProbLabel
import EvenP1ProbArithmetic

namespace Mathproof.EvenTI.Reciprocal.PartOne

open Matrix Module LinearMap
open scoped Matrix BigOperators
open Mathproof.EvenTI.Reciprocal.Next (traceKernel traceKernel_codim)
open Mathproof.EvenOrdinaryTISingular (uniformFraction)

noncomputable section

variable {K I B L J : Type*} [Field K] [Fintype K]
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [DecidableEq B]
    [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

theorem traceTuple_finrank :
    finrank K (J → traceKernel (K := K) (I := I)) =
      Fintype.card J * (Fintype.card I ^ 2 - 1) := by
  let T := traceKernel (K := K) (I := I)
  let E : (J → T) ≃ₗ[K] Matrix J (Fin (finrank K T)) K :=
    LinearEquiv.piCongrRight (fun _ => (Module.finBasis K T).equivFun)
  change finrank K (J → T) = _
  rw [E.finrank_eq, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  have h := (traceKernel (K := K) (I := I)).finrank_quotient_add_finrank
  rw [traceKernel_codim, Module.finrank_matrix, Module.finrank_self, mul_one, ← pow_two] at h
  rw [show finrank K (traceKernel (K := K) (I := I)) = Fintype.card I ^ 2 - 1 by omega]

local notation "T" => (J → traceKernel (K := K) (I := I))
local notation "UType" => (L → Matrix I B K)
local notation "Labels" => {z : Dual K T // z ≠ 0}

private def dualFintype : Fintype (Dual K T) := by
  classical
  letI : Fintype (traceKernel (K := K) (I := I)) :=
    Fintype.ofInjective (Subtype.val : traceKernel (K := K) (I := I) → Matrix I I K)
      Subtype.val_injective
  exact Fintype.ofInjective (fun f : Dual K T => (f : T → K)) DFunLike.coe_injective

private def annFintype (U : UType) : Fintype (J → Ann U) := by
  letI : Fintype (Dual K (Matrix I B K)) :=
    Fintype.ofEquiv (Matrix B I K) (rectDual (K := K) (I := I) (B := B)).toEquiv
  exact Fintype.ofInjective (fun (v : J → Ann U) t => (v t).val) (by
    intro x y hxy
    funext t
    exact Subtype.ext (congrFun hxy t))

private theorem labelCount_le [Fintype (Dual K T)] [Fintype Labels] :
    Fintype.card Labels ≤ Fintype.card K ^ (Fintype.card J * (Fintype.card I^2 - 1)) := by
  calc
    _ ≤ Fintype.card (Dual K T) :=
      Fintype.card_le_of_injective (Subtype.val : Labels → Dual K T) Subtype.val_injective
    _ = _ := by
      rw [Module.card_eq_pow_finrank (K := K) (V := Dual K T), Subspace.dual_finrank_eq]
      exact congrArg (fun t => Fintype.card K ^ t) (traceTuple_finrank (K := K) (I := I) (J := J))

private theorem label_rank_cutoff {r : ℕ} {d : ℝ} (z : Labels)
    (hRank : ∀ P : Matrix I I K, (∀ c : K, P ≠ c • 1) →
      uniformFraction UType (fun U => Part1.coefficientRank P U < r) ≤ d) :
    uniformFraction UType (fun U => finrank K (coeff z.val U).range < r) ≤ d := by
  obtain ⟨t, P, hn, ht⟩ := exists_nonscalar_component z.val z.property
  have hmono :
      uniformFraction UType (fun U => finrank K (coeff z.val U).range < r) ≤
        uniformFraction UType (fun U => Part1.coefficientRank P U < r) := by
    apply uniformFraction_le_of_imp
    exact fun U h => lt_of_le_of_lt (coeff_rank_ge_of_component z.val U t P ht) h
  exact hmono.trans (hRank P hn)

set_option maxHeartbeats 160000 in
/-- Combine the rank bound for each nonscalar component with the independent
dual row product law. This is the failure event of the selected shear map. -/
theorem unconditioned_bad_le {a r : ℕ} (δ : ℝ) (hδ : 0 ≤ δ)
    (hRank : ∀ P : Matrix I I K, (∀ c : K, P ≠ c • 1) →
      uniformFraction UType (fun U => Part1.coefficientRank P U < r) ≤ δ) :
    fiberFailureAverage (fun (U : UType) (V : Fin a → J → Ann U) =>
      ¬ Function.Surjective (selectedRows U V)) ≤
      (Fintype.card K : ℝ)^(Fintype.card J * (Fintype.card I ^ 2 - 1)) *
        (δ + 1/(Fintype.card K : ℝ)^(a*r)) := by
  classical
  letI : Fintype (Dual K T) := dualFintype
  letI : ∀ U : UType, Fintype (J → Ann U) := annFintype
  letI : ∀ U : UType, AddCommGroup (J → Ann U) := fun _ => inferInstance
  letI : ∀ U : UType, Module K (J → Ann U) := fun _ => inferInstance
  have h := average_nonsurjective_le_of_cutoff (K := K)
    (X := UType) (V := fun U => J → Ann U)
    (W := T) (Z := L → K) (D := Fin a → L → K) (a := a)
    (fun U V => selectedRows U V)
    (fun z U => coeff z.val U)
    (fun z U V hkill => coeff_zero_of_comp_zero z.val U V hkill)
    r δ (fun z => label_rank_cutoff z hRank)
  have hLabel : Fintype.card Labels ≤ Fintype.card K ^ (Fintype.card J * (Fintype.card I^2 - 1)) :=
    labelCount_le
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hLabel) (add_nonneg hδ (by positivity)))
theorem unconditioned_selectedRows_bad_le
    (hJ : Fintype.card J = Fintype.card I - 1)
    (hL : Fintype.card L = Fintype.card B / 5)
    (hI : 200 ≤ Fintype.card I) (hB : Fintype.card I^2 ≤ Fintype.card B)
    (hRank : ∀ P : Matrix I I K, (∀ c : K, P ≠ c • 1) →
      uniformFraction (L → Matrix I B K)
          (fun U => Part1.coefficientRank P U < Fintype.card L / 2) ≤
        (2:ℝ)^(Fintype.card L) /
          (Fintype.card K : ℝ)^((Fintype.card L - Fintype.card L/2) *
            (Fintype.card B-Fintype.card L-Fintype.card L/2))) :
    fiberFailureAverage (fun (U : L → Matrix I B K)
      (V : Fin (Fintype.card B/5) → J → Ann U) =>
        ¬ Function.Surjective (selectedRows U V)) ≤
      1/(Fintype.card K : ℝ)^(Fintype.card I^2) := by
  have h := unconditioned_bad_le (K := K) (I := I) (B := B) (L := L) (J := J) (a := Fintype.card B/5)
    (r := Fintype.card L/2) _ (by positivity) hRank
  rw [hL, hJ] at h
  apply h.trans
  exact cutoff_union_bound (Fintype.card K) (Fintype.card I) (Fintype.card B)
    (by exact_mod_cast (show 2 ≤ Fintype.card K from Fintype.one_lt_card)) hI hB

#print axioms unconditioned_bad_le
#print axioms unconditioned_selectedRows_bad_le

end
end Mathproof.EvenTI.Reciprocal.PartOne
