import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

namespace Mathproof.MinimumGeneration

open scoped BigOperators

variable {K M Q I J : Type*} [CommRing K] [AddCommGroup M] [Module K M]

section Sections

variable [Mul Q]

/-- The linear coboundary operator on the coordinate of a section. -/
def sectionBoundary (action : Q → M →ₗ[K] M) :
    (Q → M) →ₗ[K] (Q × Q → M) where
  toFun f p := f (p.1 * p.2) - f p.1 - action p.1 (f p.2)
  map_add' f g := by
    funext p
    change (f (p.1 * p.2) + g (p.1 * p.2)) -
      (f p.1 + g p.1) - action p.1 (f p.2 + g p.2) =
      (f (p.1 * p.2) - f p.1 - action p.1 (f p.2)) +
        (g (p.1 * p.2) - g p.1 - action p.1 (g p.2))
    rw [map_add]
    abel
  map_smul' a f := by
    funext p
    change a • f (p.1 * p.2) - a • f p.1 - action p.1 (a • f p.2) =
      a • (f (p.1 * p.2) - f p.1 - action p.1 (f p.2))
    rw [map_smul, smul_sub, smul_sub]

/-- Section coordinates differ by a derivation, and adding a derivation
preserves the section equation. -/
theorem sectionBoundary_eq_iff_sub_mem_ker (action : Q → M →ₗ[K] M)
    (f b : Q → M) :
    sectionBoundary action f = sectionBoundary action b ↔
      f - b ∈ (sectionBoundary action).ker := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- The parameters for which the induced extension admits a section form a
submodule. This statement applies to each simple quotient coordinate. -/
def splitParameters {V : Type*} [AddCommGroup V] [Module K V]
    (action : Q → M →ₗ[K] M) (cocycleProjection : V →ₗ[K] (Q × Q → M)) :
    Submodule K V :=
  (sectionBoundary action).range.comap cocycleProjection

theorem mem_splitParameters_iff {V : Type*} [AddCommGroup V] [Module K V]
    (action : Q → M →ₗ[K] M) (projection : V →ₗ[K] (Q × Q → M)) (v : V) :
    v ∈ splitParameters action projection ↔
      ∃ b : Q → M, sectionBoundary action b = projection v := by
  rfl

end Sections

/-- Evaluate a cochain at the entries of a proposed quotient witness. -/
def evaluateTuple (q : I → Q) : (Q → M) →ₗ[K] (I → M) where
  toFun f i := f (q i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Dependencies

variable [Mul Q]

/-- Linear independence of the correction rows modulo evaluated derivations
spells out the absence of a nonzero combination realized by a derivation. -/
theorem rows_independent_iff (action : Q → M →ₗ[K] M) (q : I → Q)
    (rows : J → I → M) :
    LinearIndependent K (fun j =>
      (((sectionBoundary action).ker.map (evaluateTuple (K := K) q)).mkQ) (rows j)) ↔
      ∀ z : J →₀ K, ∀ f : Q → M, sectionBoundary action f = 0 →
        Finsupp.linearCombination K rows z = evaluateTuple (K := K) q f → z = 0 := by
  let U := (sectionBoundary action).ker.map (evaluateTuple (K := K) q)
  change LinearIndependent K (U.mkQ ∘ rows) ↔ _
  rw [linearIndependent_iff]
  constructor
  · intro h z f hf heq
    apply h z
    rw [← LinearMap.map_finsupp_linearCombination, heq]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact ⟨f, hf, rfl⟩
  · intro h z hz
    rw [← LinearMap.map_finsupp_linearCombination] at hz
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz
    obtain ⟨f, hf, heq⟩ := hz
    exact h z f hf heq.symm

end Dependencies

end Mathproof.MinimumGeneration
