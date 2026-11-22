import EvenP21PadClosure
import EvenP21PadExtras

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 18000

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover
open EvenTI.P20Pad

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable (h : ∀ p, ModeLayout (m p))
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance wordLaws (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance wordField (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

theorem recoverTrialSites_transportedConjugate {k : ℕ}
    (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m)
    (x : BranchAssignment w m) (i : Fin (w.sites+2)) (e : Fin (w.width (w.mode i)) ≃ Fin k) :
    let V := transportMatrixUnit e (physicalSourceChartUnit w m hw U i)
    let f := (physicalNativeOrder w m h hw i).trans e
    let B := liveActionMatrix (branchTables w m) (branchDecode w m) i
      (fun v => (branchOccurrenceUnits w m x i v).val)
    (transportMatrixUnit e (recoverTrialSites w m h hw U U x i)).val =
      V.val*B.submatrix f.symm f.symm*V.inv := by
  dsimp only
  let V := physicalSourceChartUnit w m hw U i
  let f := physicalNativeOrder w m h hw i
  let B := liveActionMatrix (branchTables w m) (branchDecode w m) i
    (fun v => (branchOccurrenceUnits w m x i v).val)
  let M := Matrix.reindexAlgEquiv K K e
  change M (recoverTrialSites w m h hw U U x i).val =
    M V.val * B.submatrix (f.trans e).symm (f.trans e).symm * M V.inv
  have hC := recoverTrialSites_nativeConjugate w m h hw U x i
  change (recoverTrialSites w m h hw U U x i).val=V.val*B.submatrix f.symm f.symm*V.inv at hC
  rw [hC,map_mul,map_mul] <;> rfl

/-- All chart words here come from the actual selected recovered mode.
The caller's width equality pins the word reindexing to the literal
order-four site and can be reflexive when both orders use the same port. -/
theorem orderFour_cropScalar_iff_recoveredMode
    (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m)
    (x : BranchAssignment w m) (i : Fin (w.sites+2))
    {n : ℕ} (ell rho : Coord 2 n → K) (j : Fin (2+2))
    (G : FourNumericUnits ell rho) (T : Tensor K 4 n)
    (hRank : rawRetainedFullRank (l:=3) T=true)
    (hAction : wordAction (fun j => (G j).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (hwSite : w.width (w.mode i)=fourRecoveryWidth ell rho j)
    (hUnit : G j=transportMatrixUnit (finCongr hwSite) (recoverTrialSites w m h hw U U x i))
    (c : K) :
    let e := (physicalNativeOrder w m h hw i).trans (finCongr hwSite)
    let V := transportMatrixUnit (finCongr hwSite) (physicalSourceChartUnit w m hw U i)
    recoverFourMatrices ell rho ell rho rfl rfl G j=c • 1 ↔
      ∀ v, inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j) e V.inv v →
        (branchOccurrenceUnits w m x i v).val=c • (1 : CodeField w m (w.mode i) v) := by
  dsimp only
  let e := (physicalNativeOrder w m h hw i).trans (finCongr hwSite)
  let V := transportMatrixUnit (finCongr hwSite) (physicalSourceChartUnit w m hw U i)
  let a : ∀ v : Fin (CodeWidth w m (w.mode i)), CodeField w m (w.mode i) v :=
    fun v => (branchOccurrenceUnits w m x i v).val
  have hMove :
      (G j).val=V.val*(liveActionMatrix (branchTables w m) (branchDecode w m) i a).submatrix
        e.symm e.symm*V.inv :=
    (congrArg Units.val hUnit).trans (recoverTrialSites_transportedConjugate w m h hw U x i (finCongr hwSite))
  exact orderFour_cropScalar_ofBlockConjugacy
    (width:=fun k => CodeWidth w m (w.mode k))
    (dim:=fun k v => numberedDegree (m (w.mode k)) v)
    (A:=fun k v => CodeField w m (w.mode k) v)
    ell rho G T hRank hAction j i (branchTables w m) (branchDecode w m)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) a e V hMove c

#print axioms recoverTrialSites_transportedConjugate
#print axioms orderFour_cropScalar_iff_recoveredMode
end EvenTI.P21Pad
