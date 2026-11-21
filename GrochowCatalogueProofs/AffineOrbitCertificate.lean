import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Coordinate certificate for the equal-size affine-orbit ambiguity. -/

namespace GrochowCatalogueAffine

abbrev Point (K : Type*) := K × K × K

def shearShift {K : Type*} [Field K] (p x : Point K) : Point K :=
  (x.1 + p.1, x.2.1 + p.2.1, x.2.2 + p.2.2 + p.1 * x.2.1)

def productParameters {K : Type*} [Field K] (p q : Point K) : Point K :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

theorem shearShift_comp {K : Type*} [Field K] (p q x : Point K) :
    shearShift p (shearShift q x) = shearShift (productParameters p q) x := by
  apply Prod.ext
  · dsimp [shearShift, productParameters]
    ring
  · apply Prod.ext <;> dsimp [shearShift, productParameters] <;> ring

theorem shearShift_regular {K : Type*} [Field K] (x y : Point K) :
    ∃! p : Point K, shearShift p x = y := by
  let p : Point K := (y.1 - x.1, y.2.1 - x.2.1,
    y.2.2 - x.2.2 - (y.1 - x.1) * x.2.1)
  refine ⟨p, ?_, ?_⟩
  · apply Prod.ext
    · dsimp [shearShift, p]
      ring
    · apply Prod.ext <;> dsimp [shearShift, p] <;> ring
  · intro q h
    have h₁ := congrArg (fun z : Point K => z.1) h
    have h₂ := congrArg (fun z : Point K => z.2.1) h
    have h₃ := congrArg (fun z : Point K => z.2.2) h
    change x.1 + q.1 = y.1 at h₁
    change x.2.1 + q.2.1 = y.2.1 at h₂
    change x.2.2 + q.2.2 + q.1 * x.2.1 = y.2.2 at h₃
    have eq₁ : q.1 = y.1 - x.1 := by linear_combination h₁
    have eq₂ : q.2.1 = y.2.1 - x.2.1 := by linear_combination h₂
    rw [eq₁] at h₃
    apply Prod.ext
    · exact eq₁
    · apply Prod.ext
      · exact eq₂
      · change q.2.2 = y.2.2 - x.2.2 - (y.1 - x.1) * x.2.1
        linear_combination h₃

theorem shearShift_noncommuting (K : Type*) [Field K] :
    shearShift ((1, 0, 0) : Point K) (shearShift (0, 1, 0) (0, 0, 0)) ≠
    shearShift ((0, 1, 0) : Point K) (shearShift (1, 0, 0) (0, 0, 0)) := by
  intro h
  have hh := congrArg (fun z : Point K => z.2.2) h
  simpa [shearShift] using hh

end GrochowCatalogueAffine

#print axioms GrochowCatalogueAffine.shearShift_comp
#print axioms GrochowCatalogueAffine.shearShift_regular
#print axioms GrochowCatalogueAffine.shearShift_noncommuting
