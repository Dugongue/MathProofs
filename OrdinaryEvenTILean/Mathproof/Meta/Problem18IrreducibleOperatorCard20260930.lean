import Mathproof.Meta.Problem18PrimaryOperatorOrbit20260930
import Mathproof.Meta.Problem18PrimaryNonzeroBoundary20260930
import Mathproof.Meta.Problem18PrimaryScalarCharpolyBoundary20260930
import Mathlib.Algebra.GroupWithZero.Units.Fintype

set_option autoImplicit false

namespace Mathproof.Problem18IrreducibleOperatorCard20260930
noncomputable section
open Classical Polynomial
open Mathproof.Problem18PrimaryOperatorOrbit20260930
open Mathproof.Problem18PrimaryIntertwinerBoundary20260930
open Mathproof.Problem18PrimaryNonzeroBoundary20260930
variable {K : Type*} [Field K] [Fintype K]

noncomputable local instance finiteAdjoinRoot (h : K[X]) [Fact (Irreducible h)] :
    FiniteDimensional K (AdjoinRoot h) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite

local instance finiteRoot (h : K[X]) [Fact (Irreducible h)] : Finite (AdjoinRoot h) :=
  Finite.of_injective (Module.finBasis K (AdjoinRoot h)).equivFun
    (Module.finBasis K (AdjoinRoot h)).equivFun.injective

local instance finiteEnd {V : Type*} [AddCommGroup V] [Module K V] [Finite V] :
    Finite (Module.End K V) :=
  Finite.of_injective (fun T : Module.End K V => (T : V → V)) DFunLike.coe_injective

/-- Jev round27: the actual primary coordinates cover all of V by Cayley-Hamilton. -/
theorem irreducible_charpoly_coordinates {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (S : Module.End K V)
    (h : K[X]) (hm : h.Monic) (hi : Irreducible h) (hS : S.charpoly=h) :
    ∃ e : AdjoinRoot h ≃ₗ[K] V,∀ x,e (AdjoinRoot.root h*x)=S (e x) := by
  have hs : Squarefree S.charpoly := hS.symm ▸ hi.squarefree
  have hd : h ∣ S.charpoly := by rw [hS]
  obtain ⟨e,he⟩ := squarefree_primary_coordinates S h hm hi hd hs
  have hz : Polynomial.aeval S h=0 := hS ▸ S.aeval_self_charpoly
  have hk : LinearMap.ker (Polynomial.aeval S h)=⊤ := by rw [hz,LinearMap.ker_zero]
  let E := e.trans ((LinearEquiv.ofEq _ _ hk).trans Submodule.topEquiv)
  refine ⟨E,?_⟩
  intro x
  exact congrArg Subtype.val (he x)

/-- The constructed coordinates give literal conjugation of endomorphisms. -/
theorem irreducible_charpoly_conjugate (h : K[X]) [Fact (Irreducible h)]
    (hm : h.Monic) (S : Module.End K (AdjoinRoot h))
    (hS : S.charpoly=h) :
    ∃ e : AdjoinRoot h ≃ₗ[K] AdjoinRoot h,
      e.conj (LinearMap.mulLeft K (AdjoinRoot.root h))=S := by
  obtain ⟨e,he⟩ := irreducible_charpoly_coordinates S h hm Fact.out hS
  refine ⟨e,?_⟩
  ext x
  simpa only [LinearEquiv.conj_apply_apply,LinearMap.mulLeft_apply,
    LinearEquiv.apply_symm_apply] using he (e.symm x)

/-- The reference field-multiplication operator has the prescribed polynomial. -/
theorem root_mul_charpoly (h : K[X]) [Fact (Irreducible h)] (hm : h.Monic) :
    (LinearMap.mulLeft K (AdjoinRoot.root h)).charpoly=h := by
  let pb := AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero
  rw [← LinearMap.charpoly_toMatrix _ pb.basis]
  change (Algebra.leftMulMatrix pb.basis pb.gen).charpoly=h
  rw [charpoly_leftMulMatrix,AdjoinRoot.minpoly_powerBasis_gen_of_monic hm]

section Scalar
variable {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]

noncomputable def scalarCentralizerEquiv (t : E)
    (ht : Algebra.adjoin K ({t} : Set E)=⊤) :
    OperatorCentralizer (fun _ _ : E => (0:K)) (LinearMap.mulLeft K t) ≃ Eˣ where
  toFun T := Units.mk0 (T.val 1) (by
    intro hz
    exact one_ne_zero (T.val.injective (hz.trans (map_zero T.val).symm)))
  invFun z := ⟨scalarEquiv z.val z.ne_zero,by
    constructor
    · intro x y; rfl
    · intro x
      change z.val*(t*x)=t*(z.val*x)
      ring⟩
  left_inv T := by
    apply Subtype.ext
    ext x
    exact (primary_intertwiner_scalar T.val.toLinearMap t ht T.property.2 x).symm
  right_inv z := by apply Units.ext; exact mul_one z.val

end Scalar

/-- Exact irreducible characteristic-polynomial count in the actual full endomorphism ensemble. -/
theorem irreducible_operator_card (h : K[X]) [Fact (Irreducible h)] (hm : h.Monic) :
    Nat.card {S : Module.End K (AdjoinRoot h) // S.charpoly=h}*(Nat.card (AdjoinRoot h)-1)=
      Nat.card (AdjoinRoot h ≃ₗ[K] AdjoinRoot h) := by
  let E := AdjoinRoot h
  let t := AdjoinRoot.root h
  let B : E → E → K := fun _ _ => 0
  have he : MulAction.orbit (isometrySubgroup B) (LinearMap.mulLeft K t) ≃
      {S : Module.End K E // S.charpoly=h} := Equiv.subtypeEquivRight (fun S => by
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨Q,rfl⟩
      change (Q.val.conj (LinearMap.mulLeft K t)).charpoly=h
      rw [Q.val.charpoly_conj,root_mul_charpoly h hm]
    · intro hS
      obtain ⟨Q,hQ⟩ := irreducible_charpoly_conjugate h hm S hS
      exact ⟨⟨Q,fun _ _ => rfl⟩,hQ⟩)
  have hg : isometrySubgroup B ≃ (E ≃ₗ[K] E) :=
    Equiv.subtypeUnivEquiv (fun _ => by intro x y; rfl)
  have hcount := operator_orbit_card B (LinearMap.mulLeft K t)
  rw [Nat.card_congr he,Nat.card_congr (scalarCentralizerEquiv t
    (AdjoinRoot.adjoinRoot_eq_top (f := h))),Nat.card_congr hg] at hcount
  letI : Fintype E := Fintype.ofFinite E
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using hcount

/-- A uniform 2/|E| occurrence bound, with no assumed random-matrix law. -/
theorem irreducible_operator_card_bound (h : K[X]) [Fact (Irreducible h)] (hm : h.Monic) :
    Nat.card {S : Module.End K (AdjoinRoot h) // S.charpoly=h}*Nat.card (AdjoinRoot h) ≤
      2*Nat.card (Module.End K (AdjoinRoot h)) := by
  let E := AdjoinRoot h
  have hc : Nat.card E ≤ 2*(Nat.card E-1) := by
    have hp : 2 ≤ Nat.card E := by
      letI : Fintype E := Fintype.ofFinite E
      simpa only [Nat.card_eq_fintype_card] using
        (Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := E)))
    omega
  have hg : Nat.card (E ≃ₗ[K] E) ≤ Nat.card (Module.End K E) :=
    Nat.card_le_card_of_injective (fun T : E ≃ₗ[K] E => T.toLinearMap)
      (fun T U hTU => LinearEquiv.toLinearMap_injective hTU)
  calc
    _ ≤ Nat.card {S : Module.End K E // S.charpoly=h}*(2*(Nat.card E-1)) :=
      Nat.mul_le_mul_left _ hc
    _ = 2*(Nat.card {S : Module.End K E // S.charpoly=h}*(Nat.card E-1)) := by ring
    _ = 2*Nat.card (E ≃ₗ[K] E) := by rw [irreducible_operator_card h hm]
    _ ≤ _ := Nat.mul_le_mul_left 2 hg

/-- The same actual occurrence bound in every finite-dimensional coordinate space. -/
theorem irreducible_operator_card_bound_any {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : K[X]) (hm : h.Monic) (hi : Irreducible h) :
    Nat.card {S : Module.End K V // S.charpoly=h}*Nat.card K^h.natDegree ≤
      2*Nat.card (Module.End K V) := by
  letI : Fact (Irreducible h) := ⟨hi⟩
  by_cases hn : Nonempty {S : Module.End K V // S.charpoly=h}
  · obtain ⟨S,hS⟩ := hn
    obtain ⟨e,he⟩ := irreducible_charpoly_coordinates S h hm hi hS
    let E := AdjoinRoot h
    let ee : Module.End K E ≃ Module.End K V := e.conj.toEquiv
    let ec : {T : Module.End K E // T.charpoly=h} ≃
        {T : Module.End K V // T.charpoly=h} :=
      ee.subtypeEquiv (fun T => by
        change T.charpoly=h ↔ (e.conj T).charpoly=h
        rw [LinearEquiv.charpoly_conj])
    have hd : Module.finrank K E=h.natDegree := finrank_quotient_span_eq_natDegree
    have hc : Nat.card E=Nat.card K^h.natDegree := by
      letI : Fintype E := Fintype.ofFinite E
      simp only [Nat.card_eq_fintype_card]
      rw [Module.card_eq_pow_finrank (K := K) (V := E),hd]
    rw [← Nat.card_congr ec,← Nat.card_congr ee,← hc]
    exact irreducible_operator_card_bound h hm
  · haveI : IsEmpty {S : Module.End K V // S.charpoly=h} := not_nonempty_iff.mp hn
    simp only [Nat.card_of_isEmpty,zero_mul,Nat.zero_le]
end
end Mathproof.Problem18IrreducibleOperatorCard20260930

