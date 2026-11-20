import Mathproof.Meta.Problem18PrimaryIntertwinerBoundary20260930
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace Mathproof.Problem18PrimaryCentralizerCard20260930
open Classical
open Mathproof.Problem18PrimaryTraceBoundary20260930
open Mathproof.Problem18PrimaryIntertwinerBoundary20260930
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

abbrev SymmetricCentralizer (t c : E) :=
  {T : E ≃ₗ[K] E // (∀ x, T (t*x)=t*T x) ∧
    ∀ x y, Algebra.trace K E (c*T x*T y)=Algebra.trace K E (c*x*y)}

/-- The actual isometry centralizer of a simple symmetric primary operator
is precisely the two-root group, including its collapse in characteristic two. -/
noncomputable def symmetricCentralizerEquiv (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    SymmetricCentralizer (K := K) t c ≃ {z : E // z^2=1} where
  toFun T := ⟨T.val 1, by
    have hsc : ∀ x, T.val x = T.val 1*x :=
      primary_intertwiner_scalar T.val.toLinearMap t ht T.property.1
    have h := (trace_scalar_isometry_iff (K := K) c c (T.val 1)).mp
      (by intro x y; simpa only [hsc x,hsc y] using T.property.2 x y)
    exact mul_left_cancel₀ hc (h.trans (mul_one c).symm)⟩
  invFun z := ⟨scalarEquiv z.val (by
      intro hz; have h := z.property; rw [hz,zero_pow (by omega)] at h; exact zero_ne_one h), by
    constructor
    · intro x
      change z.val*(t*x)=t*(z.val*x)
      ring
    · exact (trace_scalar_isometry_iff (K := K) c c z.val).mpr (by rw [z.property,mul_one])⟩
  left_inv T := by
    apply Subtype.ext
    ext x
    exact (primary_intertwiner_scalar T.val.toLinearMap t ht T.property.1 x).symm
  right_inv z := by
    apply Subtype.ext
    exact mul_one z.val

theorem symmetricCentralizer_card (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    Nat.card (SymmetricCentralizer (K := K) t c) = Nat.card {z : E // z^2=1} :=
  Nat.card_congr (symmetricCentralizerEquiv t c ht hc)

theorem squareRootsOne_card_charTwo [CharP E 2] :
    Nat.card {z : E // z^2=1} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨1,by simp⟩,?_⟩
  intro z
  apply Subtype.ext
  have h : z.val^2=(1:E)^2 := by simpa using z.property
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

noncomputable def squareRootsOneEquivBool (h2 : (2:E) ≠ 0) :
    {z : E // z^2=1} ≃ Bool where
  toFun z := if z.val=1 then false else true
  invFun b := ⟨if b then -1 else 1,by cases b <;> simp⟩
  left_inv z := by
    apply Subtype.ext
    have h : z.val^2=(1:E)^2 := by simpa using z.property
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · simp [h]
    · have hn : (-1:E) ≠ 1 := by
        intro he
        apply h2
        linear_combination -he
      simp [h,hn]
  right_inv b := by
    have hn : (-1:E) ≠ 1 := by
      intro he
      apply h2
      linear_combination -he
    cases b <;> simp [hn]

theorem squareRootsOne_card_odd (h2 : (2:E) ≠ 0) :
    Nat.card {z : E // z^2=1} = 2 := by
  rw [Nat.card_congr (squareRootsOneEquivBool h2)]
  simp

theorem symmetricCentralizer_card_charTwo [CharP E 2] (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    Nat.card (SymmetricCentralizer (K := K) t c) = 1 := by
  rw [symmetricCentralizer_card t c ht hc, squareRootsOne_card_charTwo]

theorem symmetricCentralizer_card_odd (h2 : (2:E) ≠ 0) (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    Nat.card (SymmetricCentralizer (K := K) t c) = 2 := by
  rw [symmetricCentralizer_card t c ht hc, squareRootsOne_card_odd h2]

section Hermitian
variable [StarRing E]
abbrev HermitianCentralizer (t c : E) :=
  {T : E ≃ₗ[K] E // (∀ x, T (t*x)=t*T x) ∧
    ∀ x y, Algebra.trace K E (c*star (T x)*T y)=Algebra.trace K E (c*star x*y)}

noncomputable def hermitianCentralizerEquiv (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    HermitianCentralizer (K := K) t c ≃ {z : E // star z*z=1} where
  toFun T := ⟨T.val 1,by
    have hsc : ∀ x, T.val x = T.val 1*x :=
      primary_intertwiner_scalar T.val.toLinearMap t ht T.property.1
    have h := (trace_hermitian_scalar_isometry_iff (K := K) c c (T.val 1)).mp
      (by intro x y; simpa only [hsc x,hsc y] using T.property.2 x y)
    exact mul_left_cancel₀ hc (h.trans (mul_one c).symm)⟩
  invFun z := ⟨scalarEquiv z.val (by
      intro hz; have h := z.property; simp [hz] at h),by
    constructor
    · intro x
      change z.val*(t*x)=t*(z.val*x)
      ring
    · exact (trace_hermitian_scalar_isometry_iff (K := K) c c z.val).mpr
        (by rw [z.property,mul_one])⟩
  left_inv T := by
    apply Subtype.ext
    ext x
    exact (primary_intertwiner_scalar T.val.toLinearMap t ht T.property.1 x).symm
  right_inv z := by
    apply Subtype.ext
    exact mul_one z.val

theorem hermitianCentralizer_card (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) :
    Nat.card (HermitianCentralizer (K := K) t c) = Nat.card {z : E // star z*z=1} :=
  Nat.card_congr (hermitianCentralizerEquiv t c ht hc)
end Hermitian
end Mathproof.Problem18PrimaryCentralizerCard20260930
