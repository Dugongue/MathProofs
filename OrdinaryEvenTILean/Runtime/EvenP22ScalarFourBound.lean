import EvenP22ScalarFourTransport
import EvenP22ScalarFourSupport

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 11000

namespace EvenTI.P22Scalar

open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar EvenTI.P21Scalar
open EvenTI.PrimaryAlignment EvenTI.P12Scalar EvenOrdinaryTI.LiveRows
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
variable (layout : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n=w.width p)
variable (U : SiteUnits w m)
variable {t : ℕ} (Y : Fin t → Type)
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Fintype (Y j)]

attribute [local irreducible] rawFrameWidth rawNormalFrame rawEnlargedWords

local notation "Modes" => (∑ p, CodeWidth w m p)
local notation "Words" => (Fin (VarCount (Modes*2+1) (t+Modes+1) (w.sites+2)) → ZMod (Fintype.card K-1))

/-- The exact crop of the original compiled enlarged trial obeys the
same one-time inverse-bank support test for every homogeneous CRT word. -/
theorem compiledFourCrop_scalar_iff
    (T S : Dense K 1 n) (p q : CutFormPair K 2 2 n)
    (a : Matrix (RawEnlargedIndex p.1) (RawEnlargedIndex p.1) K)
    (b : Matrix (RawEnlargedIndex p.2) (RawEnlargedIndex p.2) K)
    (c : Matrix (RawEnlargedIndex q.1) (RawEnlargedIndex q.1) K)
    (d : Matrix (RawEnlargedIndex q.2) (RawEnlargedIndex q.2) K)
    (P : pairedTrialWords T S (.orderFour rfl p a b) (.orderFour rfl q c d)=some w)
    (target : FourTargetGrid p.1 p.2) (hW : w=sourceFourTrialWords p.1 p.2 T target)
    (hn : 0 < n) (hRank : rawRetainedFullRank (l:=3) T=true)
    (L : BaseUnitLog K) (z : Words)
    (hAction : let G := recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z)
      wordAction (fun i => (G i).val) w.source=w.source) :

      let act := fourNativeSupport w m layout hw U p.1 p.2
        (fourCompiledSiteOrder hW) (fourCompiledWidth hW)
      rawScalarModes (sourceTrialCrop T S (.orderFour rfl p a b) (.orderFour rfl q c d) w P
        (recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z)))=true ↔
        ∀ i j k, act i j → act i k →
          z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i j)=
            z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites i k) := by
  dsimp only
  have hL : rawFrameWidth q.1=rawFrameWidth p.1 := by
    by_contra hnL
    simpa only [pairedTrialWords,dif_neg hnL,reduceCtorEq] using P
  have hR : rawFrameWidth q.2=rawFrameWidth p.2 := by
    by_contra hnR
    simpa only [pairedTrialWords,dif_pos hL,dif_neg hnR,reduceCtorEq] using P
  let G := recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z)
  rw [fourCompiledSourceCrop_eq T S p q a b c d hL hR target P hW G]
  exact allFourSites_scalar_iff w m layout Y hw U L z p.1 p.2 T (fourCompiledUnits hW G)
    hn hRank (fourCompiledUnits_fixes hW G hAction) (fourCompiledSiteOrder hW)
    (fourCompiledWidth hW) (fourCompiledUnits_at hW G)

#print axioms compiledFourCrop_scalar_iff
end EvenTI.P22Scalar

