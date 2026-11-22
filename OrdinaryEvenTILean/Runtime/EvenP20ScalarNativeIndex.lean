import EvenP8SignedPhysical

set_option autoImplicit false
set_option maxHeartbeats 120000

namespace EvenTI.P20Scalar
open EvenTI.CellPreparation EvenOrdinaryTI.LiveRows

/-- Positive signed copy of a genuine native source coordinate. -/
def nativePositiveIndex {s : ℕ} (v : Fin s) : Fin (s*2+1) :=
  (signedVariableOrder s).symm (some (v,false))

theorem nativePositiveIndex_val {s : ℕ} (v : Fin s) :
    (nativePositiveIndex v).val=2*v.val+1 := by
  change (((finSuccEquiv (s*2)).symm (some (finProdFinEquiv (v,(0 : Fin 2))))).val)=2*v.val+1
  rw [finSuccEquiv_symm_some]
  change 0+2*v.val+1=2*v.val+1
  omega

theorem nativePinIndex_val (s : ℕ) :
    ((signedVariableOrder s).symm none).val=0 := rfl

/-- The physical network reserves its initial segment for original signed
source variables, so no auxiliary-prefix offset is added to the native slot. -/
def nativePositivePhysicalSlot {s : ℕ} (t d : ℕ) (v : Fin s) :
    Fin (VarCount (s*2+1) (t+s+1) (d+2)) :=
  varIndex (.inl (nativePositiveIndex v))

theorem nativePositivePhysicalSlot_val {s : ℕ} (t d : ℕ) (v : Fin s) :
    (nativePositivePhysicalSlot t d v).val=2*v.val+1 := by
  change (nativePositiveIndex v).val=2*v.val+1
  exact nativePositiveIndex_val v

#print axioms nativePositiveIndex_val
#print axioms nativePositivePhysicalSlot_val
end EvenTI.P20Scalar