import Mathproof.Meta.Problem18SpectralDecomposition20260930
import Mathproof.Meta.Problem18PfaffianSimplePrimaryModule20260930
import Mathproof.Meta.Problem18PrimaryScalarCharpolyBoundary20260930
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Squarefree.Basic

namespace Mathproof.Problem18PrimaryRestrictionBoundary20260930
open Polynomial Module
open Mathproof.Problem18PfaffianSimplePrimaryModule20260930
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial factors across actual invariant complementary subspaces. -/
theorem charpoly_eq_restrict_mul (S : Module.End K V) (P Q : Submodule K V)
    (hc : IsCompl P Q) (hP : ∀ x ∈ P, S x ∈ P) (hQ : ∀ x ∈ Q, S x ∈ Q) :
    S.charpoly = (S.restrict hP).charpoly * (S.restrict hQ).charpoly := by
  let e := Submodule.prodEquivOfIsCompl P Q hc
  have he : (S.restrict hP).prodMap (S.restrict hQ) = e.symm.conj S := by
    apply LinearMap.ext
    intro x
    apply e.injective
    simp only [LinearEquiv.conj_apply,LinearEquiv.symm_symm,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    simp only [e,Submodule.coe_prodEquivOfIsCompl,LinearMap.prodMap_apply,
      LinearMap.coprod_apply,LinearMap.coe_restrict_apply,Submodule.coe_subtype]
    change S x.1.val + S x.2.val = S (x.1.val+x.2.val)
    exact (map_add S _ _).symm
  rw [← LinearMap.charpoly_prodMap,he,LinearEquiv.charpoly_conj]

theorem restrict_charpoly_dvd (S : Module.End K V) (P Q : Submodule K V)
    (hc : IsCompl P Q) (hP : ∀ x ∈ P, S x ∈ P) (hQ : ∀ x ∈ Q, S x ∈ Q) :
    (S.restrict hP).charpoly ∣ S.charpoly := by
  rw [charpoly_eq_restrict_mul S P Q hc hP hQ]
  exact dvd_mul_right _ _

theorem squarefree_restrict_charpoly (S : Module.End K V) (P Q : Submodule K V)
    (hc : IsCompl P Q) (hP : ∀ x ∈ P, S x ∈ P) (hQ : ∀ x ∈ Q, S x ∈ Q)
    (hs : Squarefree S.charpoly) : Squarefree (S.restrict hP).charpoly :=
  fun x hx => hs x (hx.trans (restrict_charpoly_dvd S P Q hc hP hQ))

/-- Once an actual restricted operator has irreducible characteristic polynomial,
its canonical quotient-field action has rank one. -/
theorem simplePrimary_finrank_eq_one [Fintype K]
    (S : Module.End K V) (h : K[X]) (hirr : Irreducible h)
    (hzero : Polynomial.aeval S h = 0) (hchar : S.charpoly=h) :
    letI : Fact (Irreducible h) := ⟨hirr⟩
    letI := simplePrimaryModule S h hzero
    Module.finrank (AdjoinRoot h) V=1 := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI := simplePrimaryModule S h hzero
  letI : IsScalarTower K (AdjoinRoot h) V := simplePrimaryScalarTower S h hzero
  have hE : Module.finrank K (AdjoinRoot h)=h.natDegree := finrank_quotient_span_eq_natDegree
  have hV : Module.finrank K V=h.natDegree := by rw [← S.charpoly_natDegree,hchar]
  have htower := Module.finrank_mul_finrank K (AdjoinRoot h) V
  rw [hE,hV] at htower
  exact Nat.eq_of_mul_eq_mul_right hirr.natDegree_pos (by simpa [mul_comm] using htower)

/-- Concrete existence of field coordinates intertwining the original operator.
The field action is constructed from the operator, not supplied as an oracle. -/
theorem exists_primary_coordinates [Fintype K]
    (S : Module.End K V) (h : K[X]) (hirr : Irreducible h) (hchar : S.charpoly=h) :
    ∃ e : AdjoinRoot h ≃ₗ[K] V, ∀ x, e (AdjoinRoot.root h*x)=S (e x) := by
  have hzero : Polynomial.aeval S h=0 := by rw [← hchar]; exact S.aeval_self_charpoly
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI := simplePrimaryModule S h hzero
  letI : IsScalarTower K (AdjoinRoot h) V := simplePrimaryScalarTower S h hzero
  letI : FiniteDimensional (AdjoinRoot h) V := FiniteDimensional.right K (AdjoinRoot h) V
  let e : AdjoinRoot h ≃ₗ[AdjoinRoot h] V := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_self,simplePrimary_finrank_eq_one S h hirr hzero hchar])
  refine ⟨e.restrictScalars K,fun x => ?_⟩
  change e (AdjoinRoot.root h • x)=S (e x)
  rw [map_smul,root_smul_eq]


/-- Polynomial evaluation commutes with taking an invariant restriction. -/
theorem restrict_aeval_coe (S : Module.End K V) (P : Submodule K V)
    (hP : ∀ x ∈ P, S x ∈ P) (p : K[X]) (x : P) :
    ((Polynomial.aeval (S.restrict hP) p) x : V)=(Polynomial.aeval S p) x := by
  have hp (n : ℕ) (y : P) : (((S.restrict hP)^n) y : V)=(S^n) y := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ',Module.End.mul_apply,LinearMap.coe_restrict_apply,ih]
  induction p using Polynomial.induction_on' with
  | add p q ih iq => simpa only [map_add,LinearMap.add_apply,Submodule.coe_add,ih,iq]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial,← Algebra.smul_def,LinearMap.smul_apply,
        Submodule.coe_smul_of_tower,hp]

theorem primary_kernel_invariant (S : Module.End K V) (h : K[X]) :
    ∀ x ∈ LinearMap.ker (Polynomial.aeval S h), S x ∈ LinearMap.ker (Polynomial.aeval S h) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  have he := congrArg (fun T : Module.End K V => T x)
    (((Commute.all h X).map (Polynomial.aeval S)).eq)
  simpa only [Polynomial.aeval_X,Module.End.mul_apply,LinearMap.mem_ker.mp hx,map_zero]
    using he

theorem primary_restriction_annihilated (S : Module.End K V) (h : K[X]) :
    Polynomial.aeval (S.restrict (primary_kernel_invariant S h)) h=0 := by
  ext x
  rw [restrict_aeval_coe]
  exact LinearMap.mem_ker.mp x.property

/-- A squarefree characteristic polynomial and an irreducible annihilator force
an actual primary operator to have characteristic polynomial one or that irreducible. -/
theorem primary_charpoly_one_or_eq [Fintype K]
    (S : Module.End K V) (h : K[X]) (hm : h.Monic) (hi : Irreducible h)
    (hz : Polynomial.aeval S h=0) (hs : Squarefree S.charpoly) :
    S.charpoly=1 ∨ S.charpoly=h := by
  letI : Fact (Irreducible h) := ⟨hi⟩
  letI := simplePrimaryModule S h hz
  have hc := Problem18PrimaryScalarCharpolyBoundary20260930.simplePrimary_charpoly_pow S h hm hi hz
  have hd : Module.finrank (AdjoinRoot h) V ≤ 1 := by
    by_contra hn
    have hn2 : 2 ≤ Module.finrank (AdjoinRoot h) V := by omega
    have hh : h*h ∣ S.charpoly := by
      rw [hc]
      refine ⟨h^(Module.finrank (AdjoinRoot h) V-2),?_⟩
      rw [← pow_two,← pow_add,Nat.add_sub_of_le hn2]
    exact hi.not_isUnit (hs h hh)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
  · left; simpa [hd] using hc
  · right; simpa [hd] using hc

/-- Every actual primary kernel of a squarefree operator is either zero or has
explicit field coordinates; no field-module structure is assumed. -/
theorem primary_kernel_zero_or_coordinates [Fintype K]
    (S : Module.End K V) (h q : K[X]) (hm : h.Monic) (hi : Irreducible h)
    (hc : IsCoprime h q) (hf : S.charpoly=h*q) (hs : Squarefree S.charpoly) :
    LinearMap.ker (Polynomial.aeval S h)=⊥ ∨
    ∃ e : AdjoinRoot h ≃ₗ[K] LinearMap.ker (Polynomial.aeval S h),
      ∀ x, e (AdjoinRoot.root h*x)=(S.restrict (primary_kernel_invariant S h)) (e x) := by
  have hcompl : IsCompl (LinearMap.ker (Polynomial.aeval S h))
      (LinearMap.ker (Polynomial.aeval S q)) :=
    Mathproof.Meta.Problem18SpectralDecomposition20260930.isCompl_primarySpaces_of_charpoly_eq_mul hc hf
  have hsf := squarefree_restrict_charpoly S _ _ hcompl
    (primary_kernel_invariant S h) (primary_kernel_invariant S q) hs
  rcases primary_charpoly_one_or_eq (S.restrict (primary_kernel_invariant S h)) h hm hi
    (primary_restriction_annihilated S h) hsf with he | he
  · left
    apply Submodule.finrank_eq_zero.mp
    rw [← (S.restrict (primary_kernel_invariant S h)).charpoly_natDegree,he]
    exact Polynomial.natDegree_one
  · right
    exact exists_primary_coordinates (S.restrict (primary_kernel_invariant S h)) h hi he


/-- The factorization and complementary coprimality are derived from squarefreeness. -/
theorem squarefree_primary_kernel_coordinates [Fintype K]
    (S : Module.End K V) (h : K[X]) (hm : h.Monic) (hi : Irreducible h)
    (hd : h ∣ S.charpoly) (hs : Squarefree S.charpoly) :
    LinearMap.ker (Polynomial.aeval S h)=⊥ ∨
    ∃ e : AdjoinRoot h ≃ₗ[K] LinearMap.ker (Polynomial.aeval S h),
      ∀ x, e (AdjoinRoot.root h*x)=(S.restrict (primary_kernel_invariant S h)) (e x) := by
  obtain ⟨q,hq⟩ := hd
  have hc : IsCoprime h q := isRelPrime_iff_isCoprime.mp
    (squarefree_mul_iff.mp (hq ▸ hs)).1
  exact primary_kernel_zero_or_coordinates S h q hm hi hc hq hs

end Mathproof.Problem18PrimaryRestrictionBoundary20260930

