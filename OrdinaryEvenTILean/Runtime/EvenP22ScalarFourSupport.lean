import EvenP21PadNamed
import EvenP21ScalarOrdinary
import EvenP21ScalarFiber

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1250000
set_option maxRecDepth 14000

namespace EvenTI.P22Scalar
open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.CellProducer EvenTI.Part8 EvenTI.P15Scalar
open EvenTI.P20Scalar EvenTI.P21Scalar EvenOrdinaryTI.LiveRows
open EvenTI.PrimaryAlignment EvenTI.P20Pad EvenTI.P21Pad EvenTI.P16Recover EvenTI.P12Scalar

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable (layout : ∀ p, ModeLayout (m p))
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance words (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance fields (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

variable {t : ℕ} (Y : Fin t → Type)
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Fintype (Y j)]

local notation "S" => (∑ p, CodeWidth w m p)
local notation "Coords" => (Fin (VarCount (S*2+1) (t+S+1) (w.sites+2)) → ZMod (Fintype.card K-1))

/-- Geometric support for the actual crop. It depends solely on the source
frame and the mode widths, so a single installed mask serves every probe. -/
def fourNativeSupport (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m)
    {n : ℕ} (ell rho : Coord 2 n → K) (e : Fin (w.sites+2) ≃ Fin 4)
    (width : ∀ i, w.width (w.mode i)=fourRecoveryWidth ell rho (e i))
    (i : Fin (w.sites+2)) : Fin (CodeWidth w m (w.mode i)) → Prop :=
  inverseBlockSupported (fourSiteOrder (e i)).2 (siteCutoff ell rho (e i))
    ((physicalNativeOrder w m layout hw i).trans (finCongr (width i)))
    (transportMatrixUnit (finCongr (width i)) (physicalSourceChartUnit w m hw U i)).inv

/-- A homogeneous order-four crop is scalar in every original mode exactly
when its supported CRT sites agree. One and the same support is used across
all assignments, including both occurrences of a padded physical mode. -/
theorem allFourSites_scalar_iff
    (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m) (L : BaseUnitLog K) (z : Coords)
    {n : ℕ} (ell rho : Coord 2 n → K) (T : Tensor K 4 n) (G : FourNumericUnits ell rho)
    (hn : 0 < n) (hRank : rawRetainedFullRank (l:=3) T=true)
    (hAction : wordAction (fun j => (G j).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (e : Fin (w.sites+2) ≃ Fin 4)
    (width : ∀ i, w.width (w.mode i)=fourRecoveryWidth ell rho (e i))
    (hG : ∀ i, G (e i)=transportMatrixUnit (finCongr (width i))
      (recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z) i)) :
    rawScalarModes (recoverFourMatrices ell rho ell rho rfl rfl G)=true ↔
      ∀ i v u, fourNativeSupport w m layout hw U ell rho e width i v →
        fourNativeSupport w m layout hw U ell rho e width i u →
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) := by
  let x := nativeBaseAssignment w m Y L z
  rw [rawScalarModes_iff_exists _ hn]
  suffices each : ∀ i, (∃ c : K, recoverFourMatrices ell rho ell rho rfl rfl G (e i)=c • 1) ↔
      ∀ v u, fourNativeSupport w m layout hw U ell rho e width i v →
        fourNativeSupport w m layout hw U ell rho e width i u →
        z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i v)=
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i u) by
    constructor
    · intro hs i
      exact (each i).mp (hs (e i))
    · intro hs j
      obtain ⟨i,rfl⟩ := e.surjective j
      exact (each i).mpr (hs i)
  intro i
  refine (exists_congr (fun c => orderFour_cropScalar_iff_recoveredMode
    w m layout hw U x i ell rho (e i) G T hRank hAction (width i) (hG i) c)).trans ?_
  exact supportedOccurrences_scalar_iff_signedSites w m Y L z i
    (fourNativeSupport w m layout hw U ell rho e width i)

#print axioms allFourSites_scalar_iff
end EvenTI.P22Scalar
