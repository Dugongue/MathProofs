import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Constructive algebraic description of simple symmetric primary blocks.
The coefficient is constructed by trace duality, and the isometry test is an exact
square equation. No decomposition algorithm or complexity bound is postulated. -/
namespace Mathproof.Problem18PrimaryTraceBoundary20260930
open LinearMap
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

def Balanced (B : LinearMap.BilinForm K E) : Prop := ∀ t x y, B (t*x) y = B x (t*y)

noncomputable def traceCoefficient (B : LinearMap.BilinForm K E) : E :=
  ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).symm (B 1)

theorem traceCoefficient_spec (B : LinearMap.BilinForm K E) (x : E) :
    Algebra.trace K E (traceCoefficient B*x) = B 1 x := by
  exact LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm K E) (B 1) x

theorem balanced_trace_representation (B : LinearMap.BilinForm K E) (hB : Balanced B) (x y : E) :
    B x y = Algebra.trace K E (traceCoefficient B*x*y) := by
  have h := hB x 1 y
  rw [mul_one] at h
  rw [h, ← traceCoefficient_spec B (x*y), mul_assoc]

theorem trace_coefficient_ext (c d : E)
    (h : ∀ x, Algebra.trace K E (c*x) = Algebra.trace K E (d*x)) : c=d := by
  apply ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).injective
  ext x
  exact h x

/-- Every balanced bilinear form has one and only one trace coefficient. -/
theorem balanced_trace_existsUnique (B : LinearMap.BilinForm K E) (hB : Balanced B) :
    ∃! c : E, ∀ x y, B x y = Algebra.trace K E (c*x*y) := by
  refine ⟨traceCoefficient B, balanced_trace_representation B hB, ?_⟩
  intro c hc
  apply trace_coefficient_ext (K := K)
  intro x
  simpa only [mul_one] using (hc x 1).symm.trans (balanced_trace_representation B hB x 1)

theorem traceCoefficient_ne_zero (B : LinearMap.BilinForm K E) (hB : Balanced B)
    (hnd : B.Nondegenerate) : traceCoefficient B ≠ 0 := by
  intro hzero
  apply hnd.ne_zero
  ext x y
  rw [balanced_trace_representation B hB, hzero, zero_mul, zero_mul, map_zero]
  rfl

/-- Primary-block preservation is exactly the scalar square equation. -/
theorem trace_scalar_isometry_iff (c d z : E) :
    (∀ x y, Algebra.trace K E (c*(z*x)*(z*y)) = Algebra.trace K E (d*x*y)) ↔
      c*z^2=d := by
  constructor
  · intro h
    apply trace_coefficient_ext (K := K)
    intro x
    convert h x 1 using 1 <;> congr 1 <;> ring
  · intro h x y
    have he : c*(z*x)*(z*y) = (c*z^2)*x*y := by ring
    rw [he,h]

/-- A nondegenerate primary isometry is found precisely by extracting a square root. -/
theorem trace_scalar_isometry_square_iff (c d : E) (hc : c ≠ 0) (hd : d ≠ 0) :
    (∃ z : E, z ≠ 0 ∧ ∀ x y,
      Algebra.trace K E (c*(z*x)*(z*y)) = Algebra.trace K E (d*x*y)) ↔
      ∃ z : E, z^2 = d/c := by
  constructor
  · rintro ⟨z,hz,h⟩
    refine ⟨z, ?_⟩
    apply (eq_div_iff hc).mpr
    simpa only [mul_comm] using (trace_scalar_isometry_iff (K := K) c d z).mp h
  · rintro ⟨z,hz⟩
    have he : c*z^2=d := by rw [hz]; field_simp
    refine ⟨z,?_,(trace_scalar_isometry_iff (K := K) c d z).mpr he⟩
    intro hz0
    apply hd
    simpa [hz0] using he.symm

/-- Self-adjointness for one algebra generator propagates to every field scalar. -/
theorem balanced_of_generator (B : LinearMap.BilinForm K E) (t : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤)
    (hadj : ∀ x y, B (t*x) y = B x (t*y)) : Balanced B := by
  intro z
  have hz : z ∈ Algebra.adjoin K ({t} : Set E) := by rw [ht]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      have he : z=t := Set.mem_singleton_iff.mp hz
      subst z
      exact hadj
  | algebraMap r =>
      intro x y
      simp only [← Algebra.smul_def, map_smul, LinearMap.smul_apply]
  | add u v hu hv ihu ihv =>
      intro x y
      simp only [add_mul, map_add, LinearMap.add_apply, ihu, ihv]
  | mul u v hu hv ihu ihv =>
      intro x y
      rw [mul_assoc, ihu, ihv]
      congr 1
      ring

/-- Thus an actual generating self-adjoint primary operator supplies its trace form. -/
theorem generator_trace_existsUnique (B : LinearMap.BilinForm K E) (t : E)
    (ht : Algebra.adjoin K ({t} : Set E) = ⊤)
    (hadj : ∀ x y, B (t*x) y = B x (t*y)) :
    ∃! c : E, ∀ x y, B x y = Algebra.trace K E (c*x*y) :=
  balanced_trace_existsUnique B (balanced_of_generator B t ht hadj)

end Mathproof.Problem18PrimaryTraceBoundary20260930
