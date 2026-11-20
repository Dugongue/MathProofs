import Mathproof.Meta.Problem18PrimaryTraceBoundary20260930
import Mathlib.Algebra.CharP.Two

/-! Exact primary operator isometry from field multiplication and trace duality.
These are algebraic sufficient-and-necessary results, independent of runtime. -/
namespace Mathproof.Problem18PrimaryIntertwinerBoundary20260930
open Mathproof.Problem18PrimaryTraceBoundary20260930
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

theorem commutes_all_scalars (T : E →ₗ[K] E) (t : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤)
    (hT : ∀ x, T (t*x)=t*T x) : ∀ z x, T (z*x)=z*T x := by
  intro z
  have hz : z ∈ Algebra.adjoin K ({t} : Set E) := by rw [ht]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      have he : z=t := Set.mem_singleton_iff.mp hz
      subst z
      exact hT
  | algebraMap r =>
      intro x
      simp only [← Algebra.smul_def, map_smul]
  | add u v hu hv ihu ihv =>
      intro x
      simp only [add_mul, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
      intro x
      rw [mul_assoc, ihu, ihv, mul_assoc]

/-- Every linear intertwiner of a field generator is multiplication by its value at one. -/
theorem primary_intertwiner_scalar (T : E →ₗ[K] E) (t : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤)
    (hT : ∀ x, T (t*x)=t*T x) (x : E) : T x=T 1*x := by
  simpa only [mul_one, mul_comm] using commutes_all_scalars T t ht hT x 1

noncomputable def scalarEquiv (z : E) (hz : z ≠ 0) : E ≃ₗ[K] E :=
  { LinearMap.mulLeft K z with
    invFun := fun x => z⁻¹*x
    left_inv := by intro x; simp [← mul_assoc,hz]
    right_inv := by intro x; simp [← mul_assoc,hz] }

/-- The complete simple-primary symmetric isometry problem is one square-root test. -/
theorem primary_isometry_iff_square (t c d : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0) (hd : d ≠ 0) :
    (∃ T : E ≃ₗ[K] E, (∀ x, T (t*x)=t*T x) ∧
      ∀ x y, Algebra.trace K E (c*T x*T y) = Algebra.trace K E (d*x*y)) ↔
      ∃ z : E, z^2=d/c := by
  rw [← trace_scalar_isometry_square_iff (K := K) c d hc hd]
  constructor
  · rintro ⟨T,hT,hiso⟩
    have hsc : ∀ x, T x=T 1*x := primary_intertwiner_scalar T.toLinearMap t ht hT
    refine ⟨T 1,?_,?_⟩
    · exact fun hz => one_ne_zero (T.injective (hz.trans (map_zero T).symm))
    · intro x y
      simpa only [hsc x, hsc y] using hiso x y
  · rintro ⟨z,hz,hiso⟩
    refine ⟨scalarEquiv z hz,?_,?_⟩
    · intro x
      change z*(t*x)=t*(z*x)
      ring
    · exact hiso

/-- Characteristic two removes all sign choices in a primary intertwiner. -/
theorem primary_isometry_unique_charTwo [CharP E 2] (t c d : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hc : c ≠ 0)
    (T U : E ≃ₗ[K] E)
    (hT : ∀ x, T (t*x)=t*T x) (hU : ∀ x, U (t*x)=t*U x)
    (hTi : ∀ x y, Algebra.trace K E (c*T x*T y)=Algebra.trace K E (d*x*y))
    (hUi : ∀ x y, Algebra.trace K E (c*U x*U y)=Algebra.trace K E (d*x*y)) : T=U := by
  have htS : ∀ x, T x=T 1*x := primary_intertwiner_scalar T.toLinearMap t ht hT
  have huS : ∀ x, U x=U 1*x := primary_intertwiner_scalar U.toLinearMap t ht hU
  have hts : c*(T 1)^2=d := (trace_scalar_isometry_iff (K := K) c d (T 1)).mp
    (by intro x y; simpa only [htS x, htS y] using hTi x y)
  have hus : c*(U 1)^2=d := (trace_scalar_isometry_iff (K := K) c d (U 1)).mp
    (by intro x y; simpa only [huS x, huS y] using hUi x y)
  have hs : (T 1)^2=(U 1)^2 := mul_left_cancel₀ hc (hts.trans hus.symm)
  have h1 : T 1=U 1 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  ext x
  rw [htS x,huS x,h1]

section Hermitian
variable [StarRing E]

/-- The corresponding simple Hermitian scalar test is exactly a norm equation. -/
theorem trace_hermitian_scalar_isometry_iff (c d z : E) :
    (∀ x y, Algebra.trace K E (c*star (z*x)*(z*y)) =
      Algebra.trace K E (d*star x*y)) ↔ c*(star z*z)=d := by
  constructor
  · intro h
    apply trace_coefficient_ext (K := K)
    intro x
    convert h 1 x using 1 <;> simp only [mul_one,star_one,star_mul] <;> congr 1 <;> ring
  · intro h x y
    have he : c*star (z*x)*(z*y) = (c*(star z*z))*star x*y := by
      rw [star_mul]; ring
    rw [he,h]

/-- The complete primary Hermitian intertwiner isometry is a nonzero scalar norm test. -/
theorem primary_hermitian_isometry_iff_norm (t c d : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤) (hd : d ≠ 0) :
    (∃ T : E ≃ₗ[K] E, (∀ x, T (t*x)=t*T x) ∧
      ∀ x y, Algebra.trace K E (c*star (T x)*T y)=Algebra.trace K E (d*star x*y)) ↔
      ∃ z : E, c*(star z*z)=d := by
  constructor
  · rintro ⟨T,hT,hiso⟩
    refine ⟨T 1,(trace_hermitian_scalar_isometry_iff (K := K) c d (T 1)).mp ?_⟩
    have hsc : ∀ x, T x=T 1*x := primary_intertwiner_scalar T.toLinearMap t ht hT
    intro x y
    simpa only [hsc x, hsc y] using hiso x y
  · rintro ⟨z,hz⟩
    have hnz : z ≠ 0 := by intro h0; apply hd; simpa [h0] using hz.symm
    refine ⟨scalarEquiv z hnz,?_,?_⟩
    · intro x
      change z*(t*x)=t*(z*x)
      ring
    · exact (trace_hermitian_scalar_isometry_iff (K := K) c d z).mpr hz
end Hermitian
end Mathproof.Problem18PrimaryIntertwinerBoundary20260930
