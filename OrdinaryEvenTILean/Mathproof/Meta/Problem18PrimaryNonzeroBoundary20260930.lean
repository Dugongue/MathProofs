import Mathproof.Meta.Problem18PrimaryRestrictionBoundary20260930
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

namespace Mathproof.Problem18PrimaryNonzeroBoundary20260930
open Polynomial Module
open scoped TensorProduct
open Mathproof.Problem18PrimaryRestrictionBoundary20260930

/-- Polynomial functional calculus on an eigenvector, retaining its original coefficient field. -/
theorem eigenvector_aeval_apply {K E W : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup W] [Module K W] [Module E W] [IsScalarTower K E W]
    (T : Module.End E W) (a : E) (v : W) (hv : T.HasEigenvector a v) (p : K[X]) :
    (Polynomial.aeval T p) v=(Polynomial.aeval a p) • v := by
  induction p using Polynomial.induction_on' with
  | add p q ih iq => simp only [map_add,LinearMap.add_apply,ih,iq,add_smul]
  | monomial n c =>
      simp only [Polynomial.aeval_monomial,← Algebra.smul_def,LinearMap.smul_apply,
        hv.pow_apply,smul_assoc]

/-- Every irreducible factor of the characteristic polynomial has a nonzero actual primary kernel.
The proof passes to AdjoinRoot only to detect a nonzero eigenvector, then descends noninvertibility. -/
theorem primary_kernel_ne_bot {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V]
    (S : Module.End K V) (h : K[X]) (hi : Irreducible h) (hd : h ∣ S.charpoly) :
    LinearMap.ker (Polynomial.aeval S h) ≠ ⊥ := by
  letI : Fact (Irreducible h) := ⟨hi⟩
  let E := AdjoinRoot h
  let T : Module.End E (E ⊗[K] V) := S.baseChange E
  have hr : (S.charpoly.map (algebraMap K E)).IsRoot (AdjoinRoot.root h) := by
    obtain ⟨q,hq⟩ := hd
    rw [hq,Polynomial.map_mul]
    apply Polynomial.root_mul_right_of_isRoot
    exact AdjoinRoot.isRoot_root h
  have hev : T.HasEigenvalue (AdjoinRoot.root h) := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly T _).mpr
    simpa only [T,LinearMap.charpoly_baseChange] using hr
  obtain ⟨v,hv⟩ := hev.exists_hasEigenvector
  have ha : Polynomial.aeval (AdjoinRoot.root h) h=0 := by
    rw [AdjoinRoot.aeval_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton h))
  have hz : (Polynomial.aeval T h) v=0 := by
    rw [eigenvector_aeval_apply T _ v hv h,ha,zero_smul]
  intro hk
  have hu : IsUnit (Polynomial.aeval S h) := (LinearMap.isUnit_iff_ker_eq_bot _).mpr hk
  have hbu : IsUnit (Polynomial.aeval T h) := by
    have hh := hu.map (Module.End.baseChangeHom K E V)
    rwa [← Polynomial.aeval_algHom_apply] at hh
  have hinj := ((Module.End.isUnit_iff _).mp hbu).injective
  exact hv.2 (hinj (hz.trans (map_zero _).symm))

/-- Full nonzero primary field coordinates for every monic irreducible characteristic factor. -/
theorem squarefree_primary_coordinates {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Module.End K V) (h : K[X]) (hm : h.Monic) (hi : Irreducible h)
    (hd : h ∣ S.charpoly) (hs : Squarefree S.charpoly) :
    ∃ e : AdjoinRoot h ≃ₗ[K] LinearMap.ker (Polynomial.aeval S h),
      ∀ x, e (AdjoinRoot.root h*x)=(S.restrict (primary_kernel_invariant S h)) (e x) :=
  (squarefree_primary_kernel_coordinates S h hm hi hd hs).resolve_left
    (primary_kernel_ne_bot S h hi hd)


/-- Exact characteristic polynomial of each actual irreducible primary restriction. -/
theorem squarefree_primary_restriction_charpoly {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Module.End K V) (h : K[X]) (hm : h.Monic) (hi : Irreducible h)
    (hd : h ∣ S.charpoly) (hs : Squarefree S.charpoly) :
    (S.restrict (primary_kernel_invariant S h)).charpoly=h := by
  obtain ⟨q,hq⟩ := hd
  have hc : IsCoprime h q := isRelPrime_iff_isCoprime.mp
    (squarefree_mul_iff.mp (hq ▸ hs)).1
  have hcompl : IsCompl (LinearMap.ker (Polynomial.aeval S h))
      (LinearMap.ker (Polynomial.aeval S q)) :=
    Mathproof.Meta.Problem18SpectralDecomposition20260930.isCompl_primarySpaces_of_charpoly_eq_mul hc hq
  have hsf := squarefree_restrict_charpoly S _ _ hcompl
    (primary_kernel_invariant S h) (primary_kernel_invariant S q) hs
  rcases primary_charpoly_one_or_eq (S.restrict (primary_kernel_invariant S h)) h hm hi
    (primary_restriction_annihilated S h) hsf with he | he
  · exfalso
    apply primary_kernel_ne_bot S h hi ⟨q,hq⟩
    apply Submodule.finrank_eq_zero.mp
    rw [← (S.restrict (primary_kernel_invariant S h)).charpoly_natDegree,he]
    exact Polynomial.natDegree_one
  · exact he

end Mathproof.Problem18PrimaryNonzeroBoundary20260930

