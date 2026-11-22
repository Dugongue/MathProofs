import EvenP6SharedModes
import EvenP20ScalarNativeIndex
import EvenP19ScalarFrameMeaning

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace EvenTI.P20Scalar
open Matrix EvenTI.Part8 EvenTI.CellPreparation EvenOrdinaryTI.LiveRows

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The common normalization pin is itself an original signed source
variable; auxiliary prefix variables occur after it and the signed copies. -/
def nativePinPhysicalSlot (s t d : ℕ) :
    Fin (VarCount (s*2+1) (t+s+1) (d+2)) :=
  varIndex (.inl ((signedVariableOrder s).symm none))

theorem nativePinPhysicalSlot_val (s t d : ℕ) :
    (nativePinPhysicalSlot s t d).val=0 := rfl

/-- Actual `commonKey` values: none is the fixed/pinned block; a present
native variable uses its positive signed copy. Dual sites share this index. -/
def nativeSourcePhysicalSlot {s : ℕ} (t d : ℕ) : Option (Fin s) →
    Fin (VarCount (s*2+1) (t+s+1) (d+2))
  | none => nativePinPhysicalSlot s t d
  | some v => nativePositivePhysicalSlot t d v

theorem nativeSourcePhysicalSlot_val {s : ℕ} (t d : ℕ) (key : Option (Fin s)) :
    (nativeSourcePhysicalSlot t d key).val=
      key.elim 0 (fun v => 2*v.val+1) := by
  cases key with
  | none => exact nativePinPhysicalSlot_val s t d
  | some v => exact nativePositivePhysicalSlot_val t d v

/-- Literal source block numbering used by the actual shared-mode decoder.
Repeated dual modes share one variable; nonfree blocks use the pin. -/
def sharedBlockPhysicalSlot {c modes : ℕ} {width : Fin c → ℕ}
    (physical : Fin modes → Fin c) (free : ∀ p, Fin (width p) → Bool)
    (t d : ℕ) (i : Fin modes) (v : Fin (width (physical i))) :=
  nativeSourcePhysicalSlot t d (commonKey physical free i v)

theorem sharedBlockPhysicalSlot_val {c modes : ℕ} {width : Fin c → ℕ}
    (physical : Fin modes → Fin c) (free : ∀ p, Fin (width p) → Bool)
    (t d : ℕ) (i : Fin modes) (v : Fin (width (physical i))) :
    (sharedBlockPhysicalSlot physical free t d i v).val=
      if free (physical i) v then 2*(sharedSlot (physical i) v).val+1 else 0 := by
  unfold sharedBlockPhysicalSlot commonKey
  cases hf : free (physical i) v <;>
    simp [hf,nativeSourcePhysicalSlot,nativePositivePhysicalSlot_val,nativePinPhysicalSlot_val]
/-- Exact scalar-crop bridge for the pin-normalized native CRT action.
It is enough to compare the actual positive-copy residue words; the common
pin is cancelled, rather than incorrectly treating normalized units as the
unmodified source residue. The eigenaction is an explicit remaining input
port to be instantiated from recovered native projector/source banks. -/
theorem scalarCrop_iff_nativePositiveWords
    {r p s t d : ℕ} {I : Type}
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (N : Matrix (Fin r) (Fin r) K) (X : I → Matrix (Fin r) (Fin r) K)
    (L : BaseUnitLog K) (site : I → Option (Fin s)) (negative : Bool)
    (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (reference : I) (hRef : X reference*P ≠ 0)
    (hLeft : Q*P=1) (hInvariant : N*P=P*(Q*N*P))
    (hSpan : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hEigen : ∀ i, X i*N=(L.decode
            (if negative then -(z (nativeSourcePhysicalSlot t d (site i))-z (nativePinPhysicalSlot s t d))
        else z (nativeSourcePhysicalSlot t d (site i))-z (nativePinPhysicalSlot s t d)) : K) • X i) :
    (∃ a : K, Q*N*P=a • (1 : Matrix (Fin p) (Fin p) K)) ↔
      ∀ i, X i*P ≠ 0 →
        (z (nativeSourcePhysicalSlot t d (site i))).val=
          (z (nativeSourcePhysicalSlot t d (site reference))).val := by
  letI : NeZero (Fintype.card K-1) :=
    ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩
  let act (v : ZMod (Fintype.card K-1)) :=
    if negative then -(v-z (nativePinPhysicalSlot s t d))
    else v-z (nativePinPhysicalSlot s t d)
  let x (v : Fin (VarCount (s*2+1) (t+s+1) (d+2))) := act (z v)
  have hAct : Function.Injective act := by
    intro u v huv
    have hs : u-z (nativePinPhysicalSlot s t d)=v-z (nativePinPhysicalSlot s t d) := by
      cases negative
      · exact huv
      · exact neg_injective huv
    simpa only [sub_add_cancel] using congrArg (fun w => w+z (nativePinPhysicalSlot s t d)) hs
  have h := EvenTI.P19Scalar.scalarCrop_iff_supportedFrameWords P Q N X L
    (fun i => nativeSourcePhysicalSlot t d (site i)) x
    reference hRef hLeft hInvariant hSpan hEigen
  apply h.trans
  constructor
  · intro hall i hi
    have he := ZMod.val_injective _ (hall i hi)
    exact congrArg ZMod.val (hAct he)
  · intro hall i hi
    have he := ZMod.val_injective _ (hall i hi)
    exact congrArg ZMod.val (congrArg act he)
#print axioms nativePinPhysicalSlot_val
#print axioms scalarCrop_iff_nativePositiveWords
end EvenTI.P20Scalar