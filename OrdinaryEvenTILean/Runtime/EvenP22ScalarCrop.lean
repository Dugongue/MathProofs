import EvenP21ScalarFiber
import EvenP21ScalarOrdinary

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace EvenTI.P22Scalar
open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.PrimaryAlignment EvenTI.LiveAlgebra EvenTI.CellProducer
open EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar EvenTI.P21Scalar EvenTI.P12Scalar
open EvenOrdinaryTI.LiveRows
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (T S : Dense K l n)
variable (order : Fin ((l+1)+(l+1)) ≃ Fin ((l+1)+(l+1)))

/-- The ordinary crop only permutes modes. Its scalar verdict can be taken
on the literal physical site array before undoing that permutation. -/
theorem ordinaryCrop_scalar_iff (G : OrdinarySiteUnits order T S) (hn : 0 < n) :
    rawScalarModes (fun i => (recoverOrdinaryChanges order T S G i).val)=true ↔
      ∀ i, ∃ c : K, (G i).val=c • 1 := by
  rw [rawScalarModes_iff_exists _ hn]
  change (∀ j : Fin ((l+1)+(l+1)), ∃ c : K, (recoverOrdinaryChanges order T S G j).val=c • 1) ↔
    ∀ i : Fin (l+l+2), ∃ c : K, (G i).val=c • 1
  let e := (ordinarySiteOrder l).trans order
  constructor
  · intro h i
    have hi := h (e i)
    change (∃ c : K, (G (e.symm (e i))).val=c • 1) at hi
    rwa [Equiv.symm_apply_apply] at hi
  · intro h i
    exact h (e.symm i)

/-- Exact scalar verdict on a reciprocal trial of the original input. -/
theorem reciprocalSourceCrop_scalar_iff
    (a b : HigherModes l → Matrix (Fin n) (Fin n) K)
    (G : OrdinarySiteUnits (reciprocalPhysicalOrder l) T S) (hn : 0 < n) :
    rawScalarModes (sourceTrialCrop T S (.reciprocal a) (.reciprocal b)
      (ordinaryTrialWords (reciprocalPhysicalOrder l) T S) rfl G)=true ↔
      ∀ i, ∃ c : K, (G i).val=c • 1 :=
  ordinaryCrop_scalar_iff T S (reciprocalPhysicalOrder l) G hn

/-- Exact scalar verdict on a higher-order singular trial. -/
theorem higherSourceCrop_scalar_iff
    (p q : CutFormPair K (l+1) (l+1) n)
    (a b : Fin (l+1) × Bool → Matrix (Fin n) (Fin n) K)
    (G : OrdinarySiteUnits (singularPhysicalOrder l) T S) (hn : 0 < n) :
    rawScalarModes (sourceTrialCrop T S (.higher p a) (.higher q b)
      (ordinaryTrialWords (singularPhysicalOrder l) T S) rfl G)=true ↔
      ∀ i, ∃ c : K, (G i).val=c • 1 :=
  ordinaryCrop_scalar_iff T S (singularPhysicalOrder l) G hn

section Native

variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
variable {t : ℕ} (Y : Fin t → Type)
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Fintype (Y j)]

/-- The ordinary scalar predicate consumes exactly one shared word per
native origin. It is independent of the chosen physical gauges. -/
theorem allUnpaddedSites_scalar_iff
    (h : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n=w.width p)
    (U : ModeUnits K (fun j => Fin (ModeSize w m j))) (L : BaseUnitLog K)
    (z : Fin (VarCount ((∑ p, CodeWidth w m p)*2+1)
      (t+(∑ p, CodeWidth w m p)+1) (w.sites+2)) → ZMod (Fintype.card K-1)) :
    (∀ i, ∃ c : K, (recoverTrialSites w m h hw U U (nativeBaseAssignment w m Y L z) i).val=c • 1) ↔
      ∀ i (v u : Fin (CodeWidth w m (w.mode i))),
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) :=
  forall_congr' (unpaddedMode_scalar_iff_signedSites w m Y h hw U L z)

end Native

#print axioms ordinaryCrop_scalar_iff
#print axioms reciprocalSourceCrop_scalar_iff
#print axioms higherSourceCrop_scalar_iff
#print axioms allUnpaddedSites_scalar_iff
end EvenTI.P22Scalar

