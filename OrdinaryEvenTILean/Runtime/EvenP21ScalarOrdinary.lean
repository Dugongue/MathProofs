import EvenP21ScalarOccurrence

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace EvenTI.P21Scalar
open scoped BigOperators
open Matrix EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar
open EvenTI.CellPreparation EvenTI.CellProducer EvenOrdinaryTI.LiveRows
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.LiveAlgebra

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance scalarWordLaws (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance scalarWordField (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "S" => (∑ p, CodeWidth w m p)
local notation "X" => (SharedField (CodeField w m))
local notation "keyOf" => (commonKey w.mode (branchIsFree w m))

variable {t : ℕ} (Y : Fin t → Type) [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
variable [targetFinite : ∀ j, Fintype (Y j)]
include targetFinite

local instance scalarSharedFinite (v : Fin S) : Fintype (X v) :=
  inferInstanceAs (Fintype (CodeField w m (finSigmaFinEquiv.symm v).1 (finSigmaFinEquiv.symm v).2))

local instance scalarSignedSource (v : Fin (S*2+1)) : Fintype (SignedSource (K:=K) X v) := by
  unfold SignedSource
  generalize signedVariableOrder _ v = a
  cases a with
  | none => exact inferInstanceAs (Fintype K)
  | some q => exact inferInstanceAs (Fintype (X q.1))

local instance scalarSignedTarget (j : Fin (t+S+1)) : Fintype (SignedTarget (K:=K) X Y j) := by
  unfold SignedTarget
  generalize signedCellOrder _ _ j = a
  rcases a with _ | (r | v)
  · exact inferInstanceAs (Fintype K)
  · exact inferInstanceAs (Fintype (Y r))
  · exact inferInstanceAs (Fintype (X v))

local notation "Coords" => (Fin (VarCount (S*2+1) (t+S+1) (w.sites+2)) → ZMod (Fintype.card K-1))

noncomputable def nativeBaseAssignment (L : BaseUnitLog K) (z : Coords) : BranchAssignment w m :=
  recoverSignedHom (d:=w.sites) X Y
    (liftBaseCoordinates (d:=w.sites+2) (SignedSource (K:=K) X) (SignedTarget (K:=K) X Y)
      L (Multiplicative.ofAdd z))

/-- The native branch's regular block action sees the actual CRT bank word
at its own physical shared or pinned slot. -/
theorem branchOccurrenceUnits_baseAssignment (L : BaseUnitLog K) (z : Coords)
    (i : Fin (w.sites+2)) (v : Fin (CodeWidth w m (w.mode i))) :
    branchOccurrenceUnits w m (nativeBaseAssignment w m Y L z) i v =
      baseUnit (L.decode (occurrenceExponent (K:=K) z (keyOf i v) (w.minus i))) := by
  exact occurrence_units_liftBase (K:=K) (s:=S) (t:=t) (d:=w.sites) X Y L z (keyOf i v) (w.minus i)
    (sharedLink (K:=K) (CodeField w m) w.mode (branchIsFree w m) i v)


/-- Raw word equality reflects equality of base scalars on any support set. -/
theorem supportedOccurrences_scalar_iff_signedSites (L : BaseUnitLog K) (z : Coords)
    (i : Fin (w.sites+2)) (support : Fin (CodeWidth w m (w.mode i)) → Prop) :
    (∃ c : K, ∀ v, support v →
      (branchOccurrenceUnits w m (nativeBaseAssignment w m Y L z) i v).val=c • (1 : CodeField w m (w.mode i) v)) ↔
      ∀ v u, support v → support u →
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) := by

  let E := fun v : Fin (CodeWidth w m (w.mode i)) => occurrenceExponent (K:=K) z (keyOf i v) (w.minus i)
  let unit := fun v : Fin (CodeWidth w m (w.mode i)) => L.decode (E v)
  have word (v : Fin (CodeWidth w m (w.mode i))) (c : K) :
      (branchOccurrenceUnits w m (nativeBaseAssignment w m Y L z) i v).val=c • 1 ↔
      (unit v : K)=c := by
    rw [branchOccurrenceUnits_baseAssignment]
    change algebraMap K (CodeField w m (w.mode i) v) (unit v : K)=c • 1 ↔ _
    rw [← Algebra.algebraMap_eq_smul_one c]
    exact (algebraMap K (CodeField w m (w.mode i) v)).injective.eq_iff
  have cmp (v u : Fin (CodeWidth w m (w.mode i))) :
      (unit v : K)=(unit u : K) ↔
      z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) := by
    have inject : Function.Injective (fun k : ZMod (Fintype.card K-1) => (L.decode k : K)) :=
      fun _ _ h => congrArg Multiplicative.toAdd (L.mulEquiv.injective (Units.ext h))
    exact inject.eq_iff.trans (occurrenceExponent_eq_iff (K:=K) z _ _ _)
  constructor
  · rintro ⟨c,hc⟩ v u hv hu
    exact (cmp v u).mp (((word v c).mp (hc v hv)).trans ((word u c).mp (hc u hu)).symm)
  · intro all
    classical
    by_cases hS : ∃ u, support u
    · obtain ⟨u,hu⟩ := hS
      exact ⟨(unit u : K),fun v hv => (word v _).mpr ((cmp v u).mpr (all v u hv hu))⟩
    · exact ⟨0,fun v hv => (hS ⟨v,hv⟩).elim⟩

/-- In a complete mode every block is supported. -/
theorem unpaddedMode_scalar_iff_signedSites (h : ∀ p, ModeLayout (m p))
    (hw : ∀ p, (m p).n=w.width p)
    (U : ModeUnits K (fun j => Fin (ModeSize w m j)))
    (L : BaseUnitLog K) (z : Coords) (i : Fin (w.sites+2)) :
    (∃ c : K, (recoverTrialSites w m h hw U U (nativeBaseAssignment w m Y L z) i).val=c • 1) ↔
      ∀ v u : Fin (CodeWidth w m (w.mode i)),
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) := by
  simp only [EvenTI.P20Scalar.Unpadded.recoverTrialSites_scalar_iff]
  simpa using supportedOccurrences_scalar_iff_signedSites w m Y L z i (fun _ => True)

#print axioms branchOccurrenceUnits_baseAssignment
#print axioms supportedOccurrences_scalar_iff_signedSites
#print axioms unpaddedMode_scalar_iff_signedSites
end EvenTI.P21Scalar






