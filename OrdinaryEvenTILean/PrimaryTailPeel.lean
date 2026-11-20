import PrimaryTailBlock
import Mathproof.Meta.Problem18PrimaryNonzeroBoundary20260930

namespace Mathproof.Problem17PrimaryTail
open Module LinearMap Polynomial
open Mathproof.Problem18PrimaryNonzeroBoundary20260930
open Mathproof.Problem18PrimaryRestrictionBoundary20260930
open Mathproof.Problem18IrreducibleOperatorCard20260930
open Mathproof.Problem18PfaffianSimplePrimaryModule20260930
noncomputable section
set_option linter.style.haveILetI false

variable {K V : Type*} [Field K] [Fintype K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A characteristic factor supplies an actual invariant subspace with exactly
that characteristic polynomial, including when the ambient primary part is repeated. -/
theorem exists_irreducible_restriction (T : End K V) (f : K[X])
    (hf : f.Monic) (hi : Irreducible f) (hd : f ∣ T.charpoly) :
    ∃ S : Submodule K V, ∃ hS : Preserves T S, (T.restrict hS).charpoly = f := by
  let W := (aeval T f).ker
  let B := T.restrict (primary_kernel_invariant T f)
  have hW : W ≠ ⊥ := primary_kernel_ne_bot T f hi hd
  obtain ⟨v, hv⟩ : ∃ v : W, v ≠ 0 := by
    by_contra! h
    apply hW
    apply (Submodule.eq_bot_iff W).mpr
    intro x hx
    exact congrArg (fun y : W => y.val) (h ⟨x, hx⟩)
  have hb : aeval B f = 0 := primary_restriction_annihilated T f
  letI : Fact (Irreducible f) := ⟨hi⟩
  let E := AdjoinRoot f
  letI : FiniteDimensional K E := (AdjoinRoot.powerBasis hi.ne_zero).finite
  letI : Module E W := simplePrimaryModule B f hb
  letI : IsScalarTower K E W := simplePrimaryScalarTower B f hb
  let g₀ : E →ₗ[E] W := (LinearMap.id : E →ₗ[E] E).smulRight v
  let g : E →ₗ[K] V := W.subtype.comp (g₀.restrictScalars K)
  have hg : Function.Injective g := by
    intro a b h
    have h' : a • v = b • v := Subtype.ext h
    exact smul_left_injective E hv h'
  have hT (a : E) : T (g a) = g (AdjoinRoot.root f * a) := by
    change (B (a • v)).val = ((AdjoinRoot.root f * a) • v : W).val
    rw [mul_smul, root_smul_eq B f hb]
  let S := g.range
  have hS : Preserves T S := by
    rintro x ⟨a, rfl⟩
    exact ⟨AdjoinRoot.root f * a, (hT a).symm⟩
  let e := LinearEquiv.ofInjective g hg
  have he : e.conj (LinearMap.mulLeft K (AdjoinRoot.root f)) = T.restrict hS := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := e.surjective x
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, mulLeft_apply]
    change g (AdjoinRoot.root f * a) = T (g a)
    exact (hT a).symm
  refine ⟨S, hS, ?_⟩
  rw [← he, LinearEquiv.charpoly_conj, root_mul_charpoly f hf]

theorem exists_peel (T : End K V) (f : K[X]) (hf : f.Monic) (hi : Irreducible f)
    (k : ℕ) (hk : f ^ (k+1) ∣ T.charpoly) :
    ∃ S : Submodule K V, ∃ hS : Preserves T S, finrank K S = f.natDegree ∧
      (T.restrict hS).charpoly = f ∧ f ^ k ∣ (quotientBlock T S hS).charpoly := by
  have hd : f ∣ T.charpoly := (show f ∣ f ^ (k+1) by rw [pow_succ']; exact dvd_mul_right _ _).trans hk
  obtain ⟨S,hS,he⟩ := exists_irreducible_restriction T f hf hi hd
  refine ⟨S, hS, ?_, he, ?_⟩
  · rw [← (T.restrict hS).charpoly_natDegree, he]
  · rw [invariant_charpoly_split T S hS, he, pow_succ'] at hk
    exact (mul_dvd_mul_iff_left hi.ne_zero).mp hk

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.exists_peel
