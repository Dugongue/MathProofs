import EvenP17ScalarSelfMeaning
import EvenP21ScalarBranch
import EvenP22ScalarCrop
import EvenP6PrimaryRestriction
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

set_option autoImplicit false
set_option maxHeartbeats 1250000
namespace EvenTI.P22Scalar
open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar EvenTI.P21Scalar
open EvenTI.PrimaryAlignment EvenTI.P12Scalar EvenOrdinaryTI.LiveRows
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (T S : Dense K l n) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
variable (layout : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n=w.width p)
variable (U : SiteUnits w m) {t : ℕ} (Y : Fin t → Type)
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Fintype (Y j)]
variable (L : BaseUnitLog K)
local notation "kS" => (∑ p, CodeWidth w m p)
local notation "Words" => (Fin (VarCount (kS*2+1) (t+kS+1) (w.sites+2)) → ZMod (Fintype.card K-1))
local notation "slots" => (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites)
local notation "recovered" => (fun z : Words => recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z))

/-- The successful reciprocal paired trial fixes the exact native slots. -/
theorem compiledReciprocalCrop_scalar_iff (a b : HigherModes l → Matrix (Fin n) (Fin n) K)
    (hPair : pairedTrialWords T S (.reciprocal a) (.reciprocal b)=some w)
    (hn : 0 < n) (z : Words) :
    rawScalarModes (sourceTrialCrop T S (.reciprocal a) (.reciprocal b) w hPair (recovered z))=true ↔
      ∀ i v u, z (slots i v)=z (slots i u) := by
  have hW : ordinaryTrialWords (reciprocalPhysicalOrder l) T S = w := Option.some.inj hPair
  subst w
  apply (reciprocalSourceCrop_scalar_iff T S a b _ hn).trans
  exact allUnpaddedSites_scalar_iff _ m Y layout hw U L z

/-- Exact native CRT meaning of the original higher-order singular branch. -/
theorem compiledHigherCrop_scalar_iff (p q : CutFormPair K (l+1) (l+1) n)
    (a b : Fin (l+1) × Bool → Matrix (Fin n) (Fin n) K)
    (hPair : pairedTrialWords T S (.higher p a) (.higher q b)=some w)
    (hn : 0 < n) (z : Words) :
    rawScalarModes (sourceTrialCrop T S (.higher p a) (.higher q b) w hPair (recovered z))=true ↔
      ∀ i v u, z (slots i v)=z (slots i u) := by
  have hW : ordinaryTrialWords (singularPhysicalOrder l) T S = w := Option.some.inj hPair
  subst w
  apply (higherSourceCrop_scalar_iff T S p q a b _ hn).trans
  exact allUnpaddedSites_scalar_iff _ m Y layout hw U L z

#print axioms compiledReciprocalCrop_scalar_iff
#print axioms compiledHigherCrop_scalar_iff
end EvenTI.P22Scalar


set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
set_option maxRecDepth 14000

namespace EvenTI.P22Scalar

open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.P21Scalar EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (D : FieldEncoding K) (F : FieldPresentation K)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})
local instance clauseModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i

local macro "compiledBranch" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.branchOfCompiled))
local notation "A" => (BranchAssignment out.words out.modes)
local notation "run" => (branchSignedAction out.words out.modes out.layout)
local notation "src" => (sourceCoefficients out.words out.modes out.capacities b.1.left)
local notation "dst" => (targetCoefficients out.words out.modes out.capacities b.1.right)
local notation "sites" => (recoverTrialSites out.words out.modes out.layout out.capacities)
local notation "hWords" => (compiledTrialWords_eq D T T P Q out hOut)
local notation "raw" => (recoverRawMatrices T T P Q out.words hWords)
local notation "crop" => (sourceTrialCrop T T P Q out.words hWords)
local notation "SrcGauge" => b.1.left
local notation "DstGauge" => b.1.right
local notation "ho" => (compiledBranch D T P Q out hOut b)
local notation "cap" => (nativeBranchKernelCap D out.words out.modes out.layout out.capacities b.1 ho)
local notation "verdict" => (nativePrefixSmithBit D out.words out.modes out.layout out.capacities F b.1 ho)
local notation "scan" => (scanNativeRecoveryProbes D out.words out.modes out.layout out.capacities b.1)
local notation "nativeScan" => (scanNativePrefixGenerators D out.words out.modes out.layout out.capacities b.1)

/-- A paid source-only scan after one accepted affine witness decides the
original branch. The affine CRT driver may return any feasible witness. -/
theorem sourceProbe_eq_exactBranch (L : BaseUnitLog K) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true)
    (hv : verdict=true) (hc : cap=true) (x : A)
    (hx : run src x=dst) (hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true) :
    scan L (fun k => rawScalarModes (crop (sites SrcGauge SrcGauge k))) =
      matrixSelfBranch D F T P Q out hOut b := by
  have hh := matrixSelf_branch_via_verified_CRT_witness D F T P Q out hOut b L
    hn hRank hv hc x hx
  rw [hs,Bool.true_and] at hh
  exact (sourceProbeScan_eq_affine D T P Q out hOut b L hn hRank hc x hx hs).trans hh

#print axioms sourceProbe_eq_exactBranch
end EvenTI.P22Scalar
