import EvenP1Average
import EvenNextRecipOddAnchor
import Mathlib.FieldTheory.Finiteness

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical
open Matrix EvenTI.Primary Mathproof.EvenTI.Reciprocal.Next

noncomputable section

variable {K H L J I B : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J]
variable [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "TraceZero" => traceKernel (K := K) (I := I)
local notation "Full" => (⊤ : Submodule K (Matrix I I K))

abbrev AnchorTrace (K R I : Type*) [Field K] [Fintype R] [Fintype I] :=
  {Z : Matrix I I K // Z.trace = (Fintype.card R : K)^2}

local notation "Target" => AnchorTrace K (Sum H L × Option J) I

def traceAnchor [CharP K 2] (A : Bases) : Target :=
  ⟨Small.anchor A, Small.trace_anchor_charTwo A⟩

def traceTranslate [CharP K 2] (A : Bases) : TraceZero ≃ Target where
  toFun z := ⟨z.val + Small.anchor A, by
    have hz : z.val.trace = 0 := z.property
    rw [Matrix.trace_add, hz, zero_add, Small.trace_anchor_charTwo]⟩
  invFun z := ⟨z.val - Small.anchor A, by
    change (z.val - Small.anchor A).trace = 0
    rw [Matrix.trace_sub, z.property, Small.trace_anchor_charTwo, sub_self]⟩
  left_inv z := Subtype.ext (add_sub_cancel_right z.val (Small.anchor A))
  right_inv z := Subtype.ext (sub_add_cancel z.val (Small.anchor A))

def fullTranslate (A : Bases) : Full ≃ Matrix I I K where
  toFun z := z.val + Small.anchor A
  invFun z := ⟨z - Small.anchor A, Submodule.mem_top⟩
  left_inv z := Subtype.ext (add_sub_cancel_right z.val (Small.anchor A))
  right_inv z := sub_add_cancel z (Small.anchor A)

private theorem nontrivial_character : ∃ ψ : AddChar K ℂ, ψ ≠ 1 := by
  have : Nontrivial (AddChar K ℂ) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [AddChar.card_eq]
    exact Fintype.one_lt_card)
  exact exists_ne 1

abbrev anchorError (K I : Type*) [Field K] [Fintype K] [Fintype I] :=
  ((Fintype.card K : ℝ)^(Fintype.card I ^ 2))⁻¹

private theorem sqrt_polar_le {S : Submodule K (Matrix I I K)} [Fintype S] :
    2 * Real.sqrt ((Fintype.card S : ℝ) *
      ((Fintype.card K : ℝ)^(4 * Fintype.card I ^ 2))⁻¹ / 4) ≤ anchorError K I := by
  let q := (Fintype.card K : ℝ)
  let w := Fintype.card I ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos (α := K))
  have hcard : Fintype.card S ≤ Fintype.card K ^ w := by
    calc
      _ ≤ Fintype.card (Matrix I I K) := Fintype.card_le_of_injective _ Subtype.val_injective
      _ = _ := by
        rw [Module.card_eq_pow_finrank (K := K), Module.finrank_matrix, Module.finrank_self,
          mul_one]
        dsimp [w]
        rw [pow_two]
  have hc : (Fintype.card S : ℝ) ≤ q^w := by
    dsimp [q]
    exact_mod_cast hcard
  have hpos : 0 < q^(4*w) := pow_pos hq _
  have hW : q^w * (q^w)^2 ≤ q^(4*w) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hq1 (by omega)
  have hProduct : (Fintype.card S : ℝ) * (q^w)^2 ≤ q^(4*w) :=
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hW
  have hB : (Fintype.card S : ℝ) * (q^(4*w))⁻¹ ≤ ((q^w)⁻¹)^2 := by
    have hww : 0 < (q^w)^2 := by positivity
    calc
      _ = (Fintype.card S : ℝ) / q^(4*w) := (div_eq_mul_inv _ _).symm
      _ ≤ 1 / (q^w)^2 := (div_le_div_iff₀ hpos hww).mpr (by simpa only [one_mul] using hProduct)
      _ = _ := by rw [one_div, inv_pow]
  change 2 * Real.sqrt ((Fintype.card S : ℝ) * (q^(4*w))⁻¹ / 4) ≤ (q^w)⁻¹
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card S : ℝ) * (q^(4*w))⁻¹ / 4)]
  nlinarith

theorem trace_marginal_of_bad_mass [CharP K 2] [Nonempty I] [Fintype Bases] [Nonempty Bases]
    [Fintype TraceZero] [Fintype Target]
    (hJ : Fintype.card J = Fintype.card I - 1) (hn : 8 ≤ Fintype.card I) :
    marginalError (traceAnchor : Bases → Target) ≤
      anchorError K I + 2 * event (fun A : Bases => ¬ Function.Surjective (baselineRows A)) := by
  obtain ⟨ψ, hψ⟩ := nontrivial_character (K := K)
  apply marginalError_of_good_baselines (fun X => shearEquiv X) traceAnchor
    (fun A => Function.Surjective (baselineRows A)) _ (by positivity)
  intro A hA
  let f : UpperShear K H L (Option J) → TraceZero :=
    fun X => ⟨Small.anchor (applyShear X A) - Small.anchor A, anchor_difference_mem_traceKernel A X⟩
  have he : (fun X => traceAnchor (shearEquiv X A)) = traceTranslate A ∘ f := by
    funext X
    exact Subtype.ext (sub_add_cancel _ _).symm
  rw [he, marginalError_equiv]
  exact (weight_L1_le_of_fourier_sq f _ (highOrder_anchor_variation_sq_charTwo A hJ hn hA ψ hψ)).trans
    (sqrt_polar_le (S := TraceZero))

theorem odd_marginal_of_bad_mass [Nonempty I] [Fintype Bases] [Nonempty Bases] [Fintype Full]
    (hJ : Fintype.card J = Fintype.card I - 1) (hn : 8 ≤ Fintype.card I) (h₂ : (2 : K) ≠ 0) :
    marginalError (Small.anchor : Bases → Matrix I I K) ≤
      anchorError K I + 2 * event (fun A : Bases => ¬ Function.Surjective (baselineRows A)) := by
  obtain ⟨ψ, hψ⟩ := nontrivial_character (K := K)
  apply marginalError_of_good_baselines (fun X => shearEquiv X) Small.anchor
    (fun A => Function.Surjective (baselineRows A)) _ (by positivity)
  intro A hA
  let f : UpperShear K H L (Option J) → Full :=
    fun X => ⟨Small.anchor (applyShear X A) - Small.anchor A, Submodule.mem_top⟩
  have he : (fun X => Small.anchor (shearEquiv X A)) = fullTranslate A ∘ f := by
    funext X
    exact (sub_add_cancel _ _).symm
  rw [he, marginalError_equiv]
  exact (weight_L1_le_of_fourier_sq f _ (highOrder_anchor_variation_sq_odd A hJ hn hA h₂ ψ hψ)).trans
    (sqrt_polar_le (S := Full))

#print axioms trace_marginal_of_bad_mass
#print axioms odd_marginal_of_bad_mass

end
end Mathproof.EvenTI.Reciprocal.Coverage
