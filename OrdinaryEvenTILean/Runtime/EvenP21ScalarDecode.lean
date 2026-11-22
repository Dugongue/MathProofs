import EvenP15ScalarPrefixProbe
import EvenP9AffineMultiplication
import EvenP20ScalarNativeCRTMeaning

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace EvenTI.P21Scalar
open EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar
open EvenTI.CellPreparation EvenOrdinaryTI.LiveRows EvenOrdinaryTI.CellPrefix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private local instance baseOrder : NeZero (Fintype.card K-1) :=
  ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

local macro "moveNumberedField" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP8SignedRecovery `EvenTI.Part8.moveField))

private theorem numberedBase {I : Type} {s : ℕ} (X : I → Type)
    [∀ i, Field (X i)] [∀ i, Algebra K (X i)] (e : Fin s ≃ I) (a : Fin s → Kˣ) (i : I) :
    fromNumbered X e (fun j => baseUnit (a j)) i = baseUnit (a (e.symm i)) := by
  have transport (v w : I) (h : v=w) (b : Kˣ) :
      Units.map (moveNumberedField X h).toMonoidHom (baseUnit b) = (baseUnit b : (X w)ˣ) := by
    subst w
    apply Units.ext
    rfl
  exact transport _ _ (e.apply_symm_apply i) _

private theorem physicalOriginalBase {s t d : ℕ} (X : Fin s → Type) (Y : Fin t → Type)
    [∀ i, Field (X i)] [∀ j, Field (Y j)]
    [∀ i, Algebra K (X i)] [∀ j, Algebra K (Y j)]
    (a : Fin (VarCount s t d) → Kˣ) (i : Fin s) :
    physicalOriginal (d:=d) X Y (baseAssignment X Y a) i = baseUnit (a (varIndex (.inl i))) := by
  let b (v : Var s t d) : (varField X Y v)ˣ :=
    match v with
    | .inl i => baseUnit (A:=X i) (a (varIndex (.inl i)))
    | .inr ji => baseUnit (A:=Y ji.1) (a (varIndex (.inr ji)))
  have hb : baseAssignment X Y a = toPhysical X Y b := by
    funext v
    change (baseUnit (a v) : (physicalVarField X Y v)ˣ) = b (varIndex.symm v)
    have h := congrArg (fun j => (baseUnit (a j) : (physicalVarField X Y v)ˣ))
      (varIndex.apply_symm_apply v).symm
    refine h.trans ?_
    unfold prefixVariableAlgebra physicalVarField
    generalize varIndex.symm v = j
    cases j <;> rfl
  rw [hb]
  change original X Y (fromPhysical X Y (toPhysical X Y b)) i=_
  rw [from_toPhysical]
  rfl

/-- Decode the actual signed positive copy after dividing by the physical pin.
This formula applies to the literal vector returned by the CRT solver. -/
theorem recoverSignedHom_liftBase {s t d : ℕ} (X : Fin s → Type) (Y : Fin t → Type)
    [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
    [∀ v, Fintype (SignedSource (K := K) X v)] [∀ j, Fintype (SignedTarget (K := K) X Y j)]
    (L : BaseUnitLog K) (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (v : Fin s) :
    (recoverSignedHom (d:=d) X Y
      (liftBaseCoordinates (d:=d+2) (SignedSource (K := K) X) (SignedTarget (K := K) X Y)
        L (Multiplicative.ofAdd z)) v : (X v)ˣ) =
      baseUnit (L.decode
        (z (nativePositivePhysicalSlot t d v)-z (nativePinPhysicalSlot s t d))) := by
  let E := withBase (K := K) (twinField X)
  let e := signedVariableOrder s
  let x : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → Kˣ := fun j => L.decode (z j)
  have hOrig : physicalOriginal (d:=d+2) (SignedSource (K:=K) X) (SignedTarget (K:=K) X Y)
        (baseAssignment (d:=d+2) (SignedSource (K:=K) X) (SignedTarget (K:=K) X Y) x) =
      fun i => baseUnit (x (varIndex (.inl i))) := by
    funext i
    exact physicalOriginalBase (K:=K) _ _ x i
  change unsignFilled X (fromNumbered E e
    (physicalOriginal (d:=d+2) (SignedSource (K:=K) X) (SignedTarget (K:=K) X Y)
      (baseAssignment (d:=d+2) (SignedSource (K:=K) X) (SignedTarget (K:=K) X Y) x))) v = _
  rw [hOrig]
  change fromNumbered E e (fun i => baseUnit (x (varIndex (.inl i)))) (some (v,false)) *
    (baseUnit (fromNumbered E e (fun i => baseUnit (x (varIndex (.inl i)))) none))⁻¹ = _
  rw [numberedBase,numberedBase]
  have hId (a : Kˣ) : (baseUnit a : Kˣ)=a := by
    apply Units.ext
    simp [baseUnit]
  rw [hId]
  change baseUnit (L.mulEquiv (Multiplicative.ofAdd (z (nativePositivePhysicalSlot t d v)))) *
      (baseUnit (L.mulEquiv (Multiplicative.ofAdd (z (nativePinPhysicalSlot s t d)))))⁻¹ =
    baseUnit (L.mulEquiv
      (Multiplicative.ofAdd (z (nativePositivePhysicalSlot t d v)) /
        Multiplicative.ofAdd (z (nativePinPhysicalSlot s t d))))
  rw [map_div]
  simp only [baseUnit, div_eq_mul_inv, map_mul, map_inv]

#print axioms recoverSignedHom_liftBase
end EvenTI.P21Scalar







