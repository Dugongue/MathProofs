import Mathproof.Meta.Problem18PrimaryCentralizerCard20260930
import Mathproof.Meta.Problem18PrimaryTraceCount20260930
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false

namespace Mathproof.Problem18PrimaryOperatorOrbit20260930
noncomputable section
open Classical
open Mathproof.Problem18PrimaryCentralizerCard20260930

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Actual linear isometries. No chosen transitivity or orbit representative is assumed. -/
def isometrySubgroup (B : V → V → K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {T | ∀ x y,B (T x) (T y)=B x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro T U hT hU x y
    exact (hT (U x) (U y)).trans (hU x y)
  inv_mem' := by
    intro T hT x y
    have h := hT (T.symm x) (T.symm y)
    simpa only [LinearEquiv.coe_inv,LinearEquiv.apply_symm_apply] using h.symm

instance (priority := 2000) operatorSMul (B : V → V → K) :
    SMul (isometrySubgroup B) (Module.End K V) := ⟨fun Q T => Q.val.conj T⟩

instance operatorAction (B : V → V → K) :
    MulAction (isometrySubgroup B) (Module.End K V) where
  smul Q T := Q.val.conj T
  one_smul T := by ext x; rfl
  mul_smul Q R T := by ext x; rfl

@[simp] theorem operator_smul_apply (B : V → V → K) (Q : isometrySubgroup B)
    (T : Module.End K V) (x : V) : (Q • T) x=Q.val (T (Q.val.symm x)) := rfl

abbrev OperatorCentralizer (B : V → V → K) (S : Module.End K V) :=
  {T : V ≃ₗ[K] V // (∀ x y,B (T x) (T y)=B x y) ∧ ∀ x,T (S x)=S (T x)}

noncomputable def stabilizerEquivCentralizer (B : V → V → K) (S : Module.End K V) :
    MulAction.stabilizer (isometrySubgroup B) S ≃ OperatorCentralizer B S where
  toFun Q := ⟨Q.val.val,Q.val.property,by
    intro x
    have h := congrArg (fun T : Module.End K V => T (Q.val.val x)) Q.property
    simpa only [operator_smul_apply,LinearEquiv.symm_apply_apply] using h⟩
  invFun Q := ⟨⟨Q.val,Q.property.1⟩,by
    ext x
    change Q.val (S (Q.val.symm x))=S x
    simpa only [LinearEquiv.apply_symm_apply] using Q.property.2 (Q.val.symm x)⟩
  left_inv Q := rfl
  right_inv Q := rfl

/-- Exact count of the actual conjugation orbit, with its actual commuting isometries. -/
theorem operator_orbit_card (B : V → V → K) (S : Module.End K V) :
    Nat.card (MulAction.orbit (isometrySubgroup B) S)*Nat.card (OperatorCentralizer B S)=
      Nat.card (isometrySubgroup B) := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (isometrySubgroup B) S)
  rw [Nat.card_prod,Nat.card_congr (stabilizerEquivCentralizer B S)] at h
  exact h

section Primary
variable {E : Type*} [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

def symmetricPairing (c : E) (x y : E) : K := Algebra.trace K E (c*x*y)

noncomputable def symmetricOperatorCentralizerEquiv (t c : E) :
    OperatorCentralizer (symmetricPairing (K := K) c) (LinearMap.mulLeft K t) ≃
      SymmetricCentralizer (K := K) t c where
  toFun T := ⟨T.val,T.property.2,T.property.1⟩
  invFun T := ⟨T.val,T.property.2,T.property.1⟩
  left_inv T := rfl
  right_inv T := rfl

/-- Simple symmetric primary operator orbits have exactly the proved scalar stabilizer. -/
theorem symmetric_primary_orbit_card (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E)=⊤) (hc : c ≠ 0) :
    Nat.card (MulAction.orbit (isometrySubgroup (symmetricPairing (K := K) c))
      (LinearMap.mulLeft K t))*Nat.card {z : E // z^2=1} =
        Nat.card (isometrySubgroup (symmetricPairing (K := K) c)) := by
  have h := operator_orbit_card (symmetricPairing (K := K) c) (LinearMap.mulLeft K t)
  rw [Nat.card_congr (symmetricOperatorCentralizerEquiv t c),
    symmetricCentralizer_card t c ht hc] at h
  exact h

theorem symmetric_primary_orbit_card_charTwo [CharP E 2] (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E)=⊤) (hc : c ≠ 0) :
    Nat.card (MulAction.orbit (isometrySubgroup (symmetricPairing (K := K) c))
      (LinearMap.mulLeft K t))=Nat.card (isometrySubgroup (symmetricPairing (K := K) c)) := by
  simpa only [squareRootsOne_card_charTwo,mul_one] using symmetric_primary_orbit_card t c ht hc

theorem symmetric_primary_orbit_card_odd (h2 : (2:E) ≠ 0) (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E)=⊤) (hc : c ≠ 0) :
    Nat.card (MulAction.orbit (isometrySubgroup (symmetricPairing (K := K) c))
      (LinearMap.mulLeft K t))*2=Nat.card (isometrySubgroup (symmetricPairing (K := K) c)) := by
  simpa only [squareRootsOne_card_odd h2] using symmetric_primary_orbit_card t c ht hc

variable [StarRing E]
def hermitianPairing (c : E) (x y : E) : K := Algebra.trace K E (c*star x*y)

noncomputable def hermitianOperatorCentralizerEquiv (t c : E) :
    OperatorCentralizer (hermitianPairing (K := K) c) (LinearMap.mulLeft K t) ≃
      HermitianCentralizer (K := K) t c where
  toFun T := ⟨T.val,T.property.2,T.property.1⟩
  invFun T := ⟨T.val,T.property.2,T.property.1⟩
  left_inv T := rfl
  right_inv T := rfl

/-- The fixed-Hermitian-primary conjugation orbit is counted by its actual norm-one stabilizer. -/
theorem hermitian_primary_orbit_card (t c : E)
    (ht : Algebra.adjoin K ({t} : Set E)=⊤) (hc : c ≠ 0) :
    Nat.card (MulAction.orbit (isometrySubgroup (hermitianPairing (K := K) c))
      (LinearMap.mulLeft K t))*Nat.card {z : E // star z*z=1} =
        Nat.card (isometrySubgroup (hermitianPairing (K := K) c)) := by
  have h := operator_orbit_card (hermitianPairing (K := K) c) (LinearMap.mulLeft K t)
  rw [Nat.card_congr (hermitianOperatorCentralizerEquiv t c),
    hermitianCentralizer_card t c ht hc] at h
  exact h

end Primary
end
end Mathproof.Problem18PrimaryOperatorOrbit20260930
