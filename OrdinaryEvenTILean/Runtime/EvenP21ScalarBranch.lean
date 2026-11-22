import EvenP21ScalarFiber
import EvenP17ScalarSelfMeaning

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2350000
set_option maxRecDepth 14000

namespace EvenTI.P21Scalar

open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar
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

/-- Replace affine transporters with homogeneous source crop tests. Both
finite scans are evaluated against the same checked subgroup of the actual
native kernel, so arbitrary valid CRT choices give the same decision. -/
theorem sourceProbeScan_eq_affine (L : BaseUnitLog K) (hn : 0<n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true)
    (hc : cap=true) (x : A) (hx : run src x=dst)
    (hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true) :
    scan L (fun k => rawScalarModes (crop (sites SrcGauge SrcGauge k))) =
      scan L (fun k => rawScalarModes (raw (sites SrcGauge DstGauge (x*k)))) := by
  let affine := fun k : A => rawScalarModes (raw (sites SrcGauge DstGauge (x*k)))
  let source := fun k : A => rawScalarModes (crop (sites SrcGauge SrcGauge k))
  obtain ⟨R,hR⟩ := matrixSelfProbe_isSubgroup D (Fintype.equivFin Kˣ).symm T P Q out hOut b
    hn hRank x hx hs
  have hSource (k : A) (hk : run src k=src) : source k=true ↔ k∈R := by
    change rawScalarModes (crop (sites SrcGauge SrcGauge k))=true ↔ k∈R
    rw [← affineProbe_scalar_eq_source D T P Q out hOut b hn hRank x k hx hk hs]
    exact hR k hk
  change scan L source=scan L affine
  rw [scanNativeRecoveryProbes_eq D out.words out.modes out.layout out.capacities b.1 L ho hc source R hSource,
    scanNativeRecoveryProbes_eq D out.words out.modes out.layout out.capacities b.1 L ho hc affine R hR]
  apply Bool.eq_iff_iff.mpr
  rw [scanNativePrefixGenerators_iff D out.words out.modes out.layout out.capacities b.1 ho hc source R hSource,
    scanNativePrefixGenerators_iff D out.words out.modes out.layout out.capacities b.1 ho hc affine R hR]


noncomputable def matrixSelfBranchSourceProbes (L : BaseUnitLog K) : Bool :=
  if verdict then cap &&
    match EvenTI.P15Recover.recoverNativeBranchCRT D out.words out.modes out.layout
        out.capacities F b.1 ho with
    | none => false
    | some x => rawScalarModes (raw (sites SrcGauge DstGauge x)) &&
        scan L (fun k => rawScalarModes (crop (sites SrcGauge SrcGauge k)))
  else true

theorem matrixSelfBranchSourceProbes_eq (L : BaseUnitLog K) (hn : 0<n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true) :
    matrixSelfBranchSourceProbes D F T P Q out hOut b L =
      matrixSelfBranchViaComparison D F T P Q out hOut b L := by
  unfold matrixSelfBranchSourceProbes matrixSelfBranchViaComparison
  by_cases hv : verdict=true
  · simp only [if_pos hv]
    by_cases hc : cap=true
    · simp only [hc,Bool.true_and]
      cases hx : EvenTI.P15Recover.recoverNativeBranchCRT D out.words out.modes out.layout
          out.capacities F b.1 ho with
      | none => rfl
      | some x =>
        by_cases hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true
        · have hAct := EvenTI.P15Recover.recoverNativeBranchCRT_sound D out.words out.modes out.layout
            out.capacities F b.1 ho hx
          simp only [hs,Bool.true_and]
          exact sourceProbeScan_eq_affine D T P Q out hOut b L hn hRank hc x hAct hs
        · have hFalse := Bool.eq_false_iff.mpr hs
          simp only [hFalse,Bool.false_and]
    · have hFalse := Bool.eq_false_iff.mpr hc
      simp only [hFalse,Bool.false_and]
  · simp only [if_neg hv]

#print axioms sourceProbeScan_eq_affine
#print axioms matrixSelfBranchSourceProbes_eq

section Request
open EvenTI.Comparison EvenTI.P10Scan EvenTI.P10Oracle
variable {q : ℕ}

/-- The original prepared self request agrees with the branch controller
that checks one affine representative and then probes the source only. -/
theorem preparedSelfWords_eq_sourceProbes
    (D : FieldEncoding K) (F : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (L : BaseUnitLog K)
    (words : List ℕ) (p : ParsedPair K) (hp : decodePair D words=some p)
    (h : p.d=(cutHalf p.d+1)+(cutHalf p.d+1))
    (pair : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n)
    (out : BankedTrial D)
    (hOut : compileTrialBanks D (castDense (cutHalf p.d) h p.source)
      (castDense (cutHalf p.d) h p.source) pair.1 pair.2=some out)
    (hn : 0<p.n)
    (hRank : rawRetainedFullRank (l:=(cutHalf p.d+1)+cutHalf p.d)
      (castDense (cutHalf p.d) h p.source)=true) :
    preparedSelfWords D F enum
      (pairW words (pairW (preparedTrialWords D pair.1) (preparedTrialWords D pair.2))) =
      if out.branches.attach.all (fun b => matrixSelfBranchSourceProbes D F
        (castDense (cutHalf p.d) h p.source) pair.1 pair.2 out hOut b L)
      then [1] else [0] := by
  rw [EvenTI.P17Scalar.preparedSelfWords_encode_eq_comparisonCRT D F enum L words p hp h pair out hOut hn hRank]
  have he : (fun b => matrixSelfBranchViaComparison D F
      (castDense (cutHalf p.d) h p.source) pair.1 pair.2 out hOut b L) =
      (fun b => matrixSelfBranchSourceProbes D F
        (castDense (cutHalf p.d) h p.source) pair.1 pair.2 out hOut b L) := by
    funext b
    exact (matrixSelfBranchSourceProbes_eq D F _ pair.1 pair.2 out hOut b L hn hRank).symm
  rw [he]

#print axioms preparedSelfWords_eq_sourceProbes
end Request
end EvenTI.P21Scalar



