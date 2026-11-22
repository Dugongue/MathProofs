import EvenP21ScalarDecode
import EvenP20ScalarUnpadded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P21Scalar
open EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar
open EvenTI.CellPreparation EvenOrdinaryTI.LiveRows
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.LiveAlgebra

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The exponent seen by a native field-block occurrence. -/
def occurrenceExponent {s t d : ℕ}
    (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (v : Option (Fin s)) (negative : Bool) : ZMod (Fintype.card K-1) :=
  let k := z (nativeSourcePhysicalSlot t d v)-z (nativePinPhysicalSlot s t d)
  if negative then -k else k

theorem occurrenceExponent_eq_iff {s t d : ℕ}
    (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (v u : Option (Fin s)) (negative : Bool) :
    occurrenceExponent (K:=K) z v negative=occurrenceExponent (K:=K) z u negative ↔
      z (nativeSourcePhysicalSlot t d v)=z (nativeSourcePhysicalSlot t d u) := by
  cases negative <;> simp [occurrenceExponent]

/-- Free, pinned and negative occurrences use exactly the same raw positive
slot test. The inverse is applied only to the common mode exponent. -/
theorem occurrence_units_liftBase {s t d : ℕ} (X : Fin s → Type) (Y : Fin t → Type)
    [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
    [∀ v, Fintype (SignedSource (K := K) X v)] [∀ j, Fintype (SignedTarget (K := K) X Y j)]
    {E : Type} [Field E] [Algebra K E] (L : BaseUnitLog K)
    (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (v : Option (Fin s)) (negative : Bool) (e : withBase (K:=K) X v →ₐ[K] E) :
    let x := recoverSignedHom (d:=d) X Y
      (liftBaseCoordinates (d:=d+2) (SignedSource (K := K) X) (SignedTarget (K := K) X Y)
        L (Multiplicative.ofAdd z))
    let a := pinBase X x v
    Units.map e.toRingHom.toMonoidHom (if negative then a⁻¹ else a) =
      baseUnit (L.decode (occurrenceExponent (K:=K) z v negative)) := by
  let x := recoverSignedHom (d:=d) X Y
    (liftBaseCoordinates (d:=d+2) (SignedSource (K := K) X) (SignedTarget (K := K) X Y)
      L (Multiplicative.ofAdd z))
  let k := z (nativeSourcePhysicalSlot t d v)-z (nativePinPhysicalSlot s t d)
  have hBase : pinBase (K:=K) X x v = (baseUnit (L.decode k) : (withBase (K:=K) X v)ˣ) := by
    cases v with
    | none =>
      have hzero : L.decode (0 : ZMod (Fintype.card K-1))=1 := map_one L.mulEquiv
      simp [pinBase,k,nativeSourcePhysicalSlot,hzero,baseUnit]
    | some j =>
      exact recoverSignedHom_liftBase X Y L z j
  change Units.map e.toRingHom.toMonoidHom
    (if negative then (pinBase (K:=K) X x v)⁻¹ else pinBase (K:=K) X x v) =
      baseUnit (L.decode (if negative then -k else k))
  rw [hBase]
  cases negative
  · exact map_baseUnit e _
  · simp only [if_true]
    change Units.map e.toRingHom.toMonoidHom (baseUnit (L.mulEquiv (Multiplicative.ofAdd k)))⁻¹ =
      baseUnit (L.mulEquiv ((Multiplicative.ofAdd k)⁻¹))
    rw [map_inv,map_baseUnit]
    change (Units.map (algebraMap K E).toMonoidHom (L.mulEquiv (Multiplicative.ofAdd k)))⁻¹ =
      Units.map (algebraMap K E).toMonoidHom (L.mulEquiv ((Multiplicative.ofAdd k)⁻¹))
    simp only [map_inv]

#print axioms occurrence_units_liftBase
end EvenTI.P21Scalar





