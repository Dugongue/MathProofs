import EvenP22ScalarFourCrop
import EvenP8Dechart
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 10000
namespace EvenTI.P22Scalar
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open Mathproof.EvenOrdinaryTISingular.EnlargedCut
variable {K : Type} [Field K] [DecidableEq K] {n : ℕ}
variable {ell rho : Coord 2 n → K} {T : Tensor K 4 n} {target : FourTargetGrid ell rho}
variable {w : TrialWords K}
attribute [local irreducible] rawFrameWidth rawNormalFrame rawEnlargedWords

/-- The actual crop uses the physical site order of the padded trial. -/
def fourCompiledSiteOrder (hW : w=sourceFourTrialWords ell rho T target) :
    Fin (w.sites+2) ≃ Fin 4 :=
  finCongr (congrArg (fun s : TrialWords K => s.sites+2) hW)

theorem fourCompiledWidth (hW : w=sourceFourTrialWords ell rho T target)
    (i : Fin (w.sites+2)) :
    w.width (w.mode i) = fourModeWidth ell rho (fourSiteMode (fourCompiledSiteOrder hW i)) := by
  subst w
  rfl

def fourCompiledUnits (hW : w=sourceFourTrialWords ell rho T target) (G : TrialSiteUnits w) :
    FourNumericUnits ell rho :=
  cast (congrArg (fun u : TrialWords K => TrialSiteUnits u) hW) G

theorem fourCompiledUnits_at (hW : w=sourceFourTrialWords ell rho T target)
    (G : TrialSiteUnits w) (i : Fin (w.sites+2)) :
    fourCompiledUnits hW G (fourCompiledSiteOrder hW i) =
      transportMatrixUnit (finCongr (fourCompiledWidth hW i)) (G i) := by
  subst w
  apply Units.ext
  ext r c
  rfl

theorem fourCompiledUnits_fixes (hW : w=sourceFourTrialWords ell rho T target)
    (G : TrialSiteUnits w) (hG : wordAction (fun i => (G i).val) w.source=w.source) :
    wordAction (fun j => (fourCompiledUnits hW G j).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T) := by
  subst w
  simpa only [fourCompiledUnits,cast_eq] using hG

section ActualPair
variable [Fintype K]

/-- The compiled payload preserves the original crop for a distinct target. -/
theorem fourCompiledSourceCrop_eq (T S : Dense K 1 n) (p q : CutFormPair K 2 2 n)
    (a : Matrix (RawEnlargedIndex p.1) (RawEnlargedIndex p.1) K)
    (b : Matrix (RawEnlargedIndex p.2) (RawEnlargedIndex p.2) K)
    (c : Matrix (RawEnlargedIndex q.1) (RawEnlargedIndex q.1) K)
    (d : Matrix (RawEnlargedIndex q.2) (RawEnlargedIndex q.2) K)
    (hL : rawFrameWidth q.1=rawFrameWidth p.1) (hR : rawFrameWidth q.2=rawFrameWidth p.2)
    (target : FourTargetGrid p.1 p.2)
    (hPair : pairedTrialWords T S (.orderFour rfl p a b) (.orderFour rfl q c d)=some w)
    (hW : w=sourceFourTrialWords p.1 p.2 T target) (G : TrialSiteUnits w) :
    sourceTrialCrop T S (.orderFour rfl p a b) (.orderFour rfl q c d) w hPair G =
      recoverFourMatrices p.1 p.2 p.1 p.2 rfl rfl (fourCompiledUnits hW G) := by
  subst w
  simpa only [fourCompiledUnits,cast_eq] using fourSourceCrop_eq T S p q a b c d hL hR target hPair G

end ActualPair

#print axioms fourCompiledUnits_at
#print axioms fourCompiledUnits_fixes
#print axioms fourCompiledSourceCrop_eq
end EvenTI.P22Scalar


