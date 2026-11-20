import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Mathproof.Problem17PrimaryTail
open Matrix
noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [Fintype ι] [Nonempty ι]

/-- Translation identifies all trace fibers and a free trace coordinate. -/
def trace_fiber_product (a : K) :
    Matrix ι ι K ≃ K × {A : Matrix ι ι K // A.trace = a} := by
  classical
  let u : ι := Classical.choice ‹Nonempty ι›
  let h (x : K) : Matrix ι ι K := Matrix.single u u x
  have ht (x : K) : (h x).trace = x := by simp [h]
  refine {
    toFun := fun A => (A.trace, ⟨A - h A.trace + h a, by simp [Matrix.trace_add, Matrix.trace_sub, ht]⟩)
    invFun := fun z => z.2.val - h a + h z.1
    left_inv := by
      intro A
      change A - h A.trace + h a - h a + h A.trace = A
      abel
    right_inv := ?_ }
  rintro ⟨t, ⟨A, hA⟩⟩
  have hz : (A - h a + h t).trace = t := by simp [Matrix.trace_add, Matrix.trace_sub, ht, hA]
  refine Prod.ext hz ?_
  apply Subtype.ext
  change A - h a + h t - h (A - h a + h t).trace + h a = A
  rw [hz]
  abel

omit [Fintype K] in
theorem trace_fiber_card_mul (a : K) :
    Nat.card {A : Matrix ι ι K // A.trace = a} * Nat.card K = Nat.card (Matrix ι ι K) := by
  rw [Nat.card_congr (trace_fiber_product a), Nat.card_prod, mul_comm]

/-- Conditioning on a specified trace amplifies an arbitrary event by at most the field size. -/
theorem trace_condition_amplification (a : K) (P : Matrix ι ι K → Prop) :
    (Nat.card {A : Matrix ι ι K // A.trace = a ∧ P A} : ℝ) /
      Nat.card {A : Matrix ι ι K // A.trace = a} ≤
    (Nat.card K : ℝ) * ((Nat.card {A : Matrix ι ι K // P A} : ℝ) / Nat.card (Matrix ι ι K)) := by
  classical
  have ha : 0 < Nat.card {A : Matrix ι ι K // A.trace = a} := by
    obtain ⟨A, hA⟩ := Matrix.trace_surjective (n := ι) a
    letI : Nonempty {A : Matrix ι ι K // A.trace = a} := ⟨⟨A, hA⟩⟩
    exact Nat.card_pos
  have hp : Nat.card {A : Matrix ι ι K // A.trace = a ∧ P A} ≤
      Nat.card {A : Matrix ι ι K // P A} :=
    Nat.card_le_card_of_injective (fun A => ⟨A.val, A.property.2⟩)
      (fun _ _ h => Subtype.ext (congrArg (fun x : {A : Matrix ι ι K // P A} => x.val) h))
  have hcast : (Nat.card {A : Matrix ι ι K // A.trace = a ∧ P A} : ℝ) ≤
      Nat.card {A : Matrix ι ι K // P A} := by exact_mod_cast hp
  rw [← trace_fiber_card_mul a, Nat.cast_mul]
  have hq : (Nat.card K : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
  have he : (Nat.card K : ℝ) *
      ((Nat.card {A : Matrix ι ι K // P A} : ℝ) /
        ((Nat.card {A : Matrix ι ι K // A.trace = a} : ℝ) * Nat.card K)) =
      (Nat.card {A : Matrix ι ι K // P A} : ℝ) / Nat.card {A : Matrix ι ι K // A.trace = a} := by
    field_simp [hq]
  rw [he]
  exact div_le_div_of_nonneg_right hcast (by positivity)

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.trace_condition_amplification
