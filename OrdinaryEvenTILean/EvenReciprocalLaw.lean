import EvenReciprocalShear
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Shears act by bijections on the space of exact primal/dual bases. The
uniform source expectation can therefore be recovered by averaging over an
independent uniform shear after conditioning on the baseline. -/
namespace Mathproof.EvenTI.Reciprocal
open scoped BigOperators Matrix
open Matrix

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

abbrev BasisPairs (K R C : Type*) [Field K] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] :=
  {as : Matrix R C K × Matrix R C K // as.1 * as.2ᵀ = 1 ∧ as.2ᵀ * as.1 = 1}

theorem shearMatrix_neg (X : UpperShear K H L J) :
    shearMatrix (-X) = -shearMatrix X := by
  ext ⟨a,j⟩ ⟨b,s⟩
  cases a <;> cases b <;> simp [shearMatrix]

abbrev ReciprocalBasis :=
  BasisPairs K (Sum H L × J) (I × B)

def applyShear (X : UpperShear K H L J)
    (A : ReciprocalBasis (K := K) (H := H) (L := L) (J := J) (I := I) (B := B)) :
    ReciprocalBasis (K := K) (H := H) (L := L) (J := J) (I := I) (B := B) :=
  ⟨((1 + shearMatrix X) * A.val.1, (1 - shearMatrix X)ᵀ * A.val.2),
    shear_dual_pair A.val.1 A.val.2 X A.property.1 A.property.2⟩

theorem applyShear_neg_cancel (X : UpperShear K H L J) (A : ReciprocalBasis
    (K := K) (H := H) (L := L) (J := J) (I := I) (B := B)) :
    applyShear (-X) (applyShear X A) = A := by
  apply Subtype.ext
  apply Prod.ext
  · change (1 + shearMatrix (-X)) * ((1 + shearMatrix X) * A.val.1) = A.val.1
    rw [shearMatrix_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc,
      (shearMatrix_inverse X).2, Matrix.one_mul]
  · change (1 - shearMatrix (-X))ᵀ * ((1 - shearMatrix X)ᵀ * A.val.2) = A.val.2
    rw [shearMatrix_neg, sub_neg_eq_add, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      (shearMatrix_inverse X).2, Matrix.transpose_one, Matrix.one_mul]

def shearEquiv (X : UpperShear K H L J) : ReciprocalBasis
    (K := K) (H := H) (L := L) (J := J) (I := I) (B := B) ≃ ReciprocalBasis
    (K := K) (H := H) (L := L) (J := J) (I := I) (B := B) where
  toFun := applyShear X
  invFun := applyShear (-X)
  left_inv := applyShear_neg_cancel X
  right_inv := by
    intro A
    simpa only [neg_neg] using applyShear_neg_cancel (-X) A

section Average
variable {A X : Type*} [Fintype A] [Fintype X] [Nonempty A] [Nonempty X]

/-- Uniform averaging is unchanged when an independent parameter applies a
permutation to the sampled state. -/
theorem uniform_average_equiv (e : X → A ≃ A) (f : A → ℝ) :
    (∑ a, (∑ x, f (e x a)) / Fintype.card X) / Fintype.card A =
      (∑ a, f a) / Fintype.card A := by
  congr 1
  have hsum (x : X) : ∑ a, f (e x a) = ∑ a, f a :=
    Equiv.sum_comp (e x) f
  have hn : (Fintype.card X : ℝ) ≠ 0 := by positivity
  calc
    _ = (∑ a, ∑ x, f (e x a)) / Fintype.card X := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hn]


/-- A uniform event bound on good baselines plus the fraction of bad baselines
bounds the corresponding event for the uniform source. -/
theorem uniform_event_of_good_baselines (e : X → A ≃ A) (f : A → ℝ)
    (hf : ∀ a, f a ≤ 1) (good : A → Prop) [DecidablePred good]
    (p : ℝ) (hp : 0 ≤ p)
    (hgood : ∀ a, good a → (∑ x, f (e x a)) / Fintype.card X ≤ p) :
    (∑ a, f a) / Fintype.card A ≤
      p + ((Finset.univ.filter (fun a => ¬ good a)).card : ℝ) / Fintype.card A := by
  classical
  rw [← uniform_average_equiv e f]
  have hn : (0 : ℝ) < Fintype.card A := by positivity
  let bad := Finset.univ.filter (fun a => ¬ good a)
  change _ ≤ p + (bad.card : ℝ) / Fintype.card A
  have hb (a : A) : (∑ x, f (e x a)) / Fintype.card X ≤
      p + (if a ∈ bad then 1 else 0) := by
    by_cases ha : good a
    · have hn : a ∉ bad := by simp [bad, ha]
      simpa [hn] using hgood a ha
    · have hy : a ∈ bad := by simp [bad, ha]
      have hs : (∑ x, f (e x a)) / Fintype.card X ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).mpr
        simpa using Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hf (e x a))
      simpa [hy] using hs.trans (le_add_of_nonneg_left hp)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hb a)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_mem_eq] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ Fintype.card A * p + bad.card := hs
    _ = (p + (bad.card : ℝ) / Fintype.card A) * Fintype.card A := by
      field_simp <;> ring


end Average

end Mathproof.EvenTI.Reciprocal

#print axioms Mathproof.EvenTI.Reciprocal.shearEquiv
#print axioms Mathproof.EvenTI.Reciprocal.uniform_average_equiv
#print axioms Mathproof.EvenTI.Reciprocal.uniform_event_of_good_baselines
