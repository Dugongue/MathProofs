import EvenP21ScalarKernel
import EvenP21ScalarOrdinary
import EvenP21ScalarScanMeaning
import EvenP21ScalarScanSelected

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2100000
set_option maxRecDepth 14000

namespace EvenTI.P22Scalar
open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.CellProducer EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar EvenTI.P15Recover
open EvenTI.P20Scalar EvenTI.P21Scalar EvenTI.P21ScalarScan EvenOrdinaryTI.LiveRows
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (D : FieldEncoding K) (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

private local instance models (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i
private local instance words (p) (v : Fin (CodeWidth out.words out.modes p)) :
    WordTable.Laws (numberedTable (out.modes p) v) := numberedWordLaws (out.modes p) v
private local instance fields (p) (v : Fin (CodeWidth out.words out.modes p)) :
    WordFieldCertificate (numberedTable (out.modes p) v) := numberedFieldCertificate (out.modes p) v

local notation "w" => out.words
local notation "m" => out.modes
local notation "h" => out.layout
local notation "hw" => out.capacities
local notation "SrcGauge" => b.1.left
local notation "DstGauge" => b.1.right
local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
private local instance liveWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ x y => wordDecode_mul _ x y)
private local instance liveReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ x y => wordDecode_mul _ x y)
private local instance liveCompact :
    ∀ j : Fin (rawCells D.symm AC).length, CellFieldCertificate AC ((rawCells D.symm AC).get j) :=
  liveCellCertificate BT D.symm BE

local notation "src" => (sourceCoefficients w m hw SrcGauge)
local notation "dst" => (targetCoefficients w m hw DstGauge)
local notation "AF" => (LiveActiveField BT D.symm BE src)
local notation "S" => (∑ p, CodeWidth w m p)
local notation "C" => ((activeCells (compactProductPack D.symm AC (liveOperand BT BE src))).card)
local notation "Dg" => ((w).sites+2)
local notation "NC" => (VarCount (S*2+1) (C+S+1) Dg)
local notation "NR" => (RowCount (C+S+1) Dg)
local notation "BaseModulus" => (Fintype.card K-1)
local notation "inc" => (physicalSrc (nativeSignedOrigins D w m h hw SrcGauge))
local notation "actB" => (branchSignedAction w m h)
local notation "hWords" => (compiledTrialWords_eq D T T P Q out hOut)
local notation "raw" => (recoverRawMatrices T T P Q w hWords)
local notation "crop" => (sourceTrialCrop T T P Q w hWords)
local notation "sites" => (recoverTrialSites w m h hw)
local notation "coords" => (Fin NC → ZMod BaseModulus)
local notation "mat" => (incidenceMatrix BaseModulus inc)
local notation "A" => (BranchAssignment w m)
local notation "B" => (fun i : Fin Dg => Fin (CodeWidth w m ((w).mode i)))
local notation "physicalWord" => (sharedBlockPhysicalSlot (w).mode (branchIsFree w m) C (w).sites)

private local instance baseOrder : NeZero BaseModulus :=
  ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

/-- One installed chart record covers exactly the active native source sites. -/
structure ChartCoverage {W N : ℕ} {J : Type}
    (plan : ScanModeInput W N) (slot : J → Fin N) (active : J → Prop) : Prop where
  fromChart : ∀ k : Fin plan.L, plan.chart.getD k.val 0 ≠ plan.zero →
    ∃ j, active j ∧ plan.site k = slot j
  toChart : ∀ j, active j →
    ∃ k : Fin plan.L, plan.chart.getD k.val 0 ≠ plan.zero ∧ plan.site k = slot j
  reference : ∀ k : Fin plan.L, plan.chart.getD k.val 0 ≠ plan.zero →
    ∃ j, active j ∧ plan.reference = slot j

/-- Actual scanner execution for one already loaded native branch.
Chart coverage and original-mode scalarity attach to the exact original
incidence bank. The imperative scan and all its calls are paid here. -/
theorem runNativeSourceProbe {W c d : ℕ} {s : Env}
    (L : BaseUnitLog K) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true)
    (x : A) (hx : actB src x=dst) (hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true)
    (plan : Fin Dg → ScanModeInput W NC)
    (active : ∀ i, B i → Prop)
    (covered : ∀ i, ChartCoverage (plan i) (physicalWord i) (active i))
    (cropMeaning : ∀ z : coords, (mat).mulVec z=0 →
      (rawScalarModes (crop (sites SrcGauge SrcGauge (nativeBaseAssignment w m AF L z)))=true ↔
        ∀ i v u, active i v → active i u →
          z (physicalWord i v)=z (physicalWord i u)))
    (hW : 4*BaseModulus*BaseModulus+4*BaseModulus+10 < W) (hRows : 3*NR < W)
    (hLayout : (NR+NC+1)+NC+(NR+NC+1)*NC+(NR+NC+1)*(NR+NC+1)+4 < W)
    (hNM : NC*BaseModulus < W) (hCount : s.vars scanModeCount=Dg) (hModes : Dg < W)
    (hTables : SelectorData plan c d s) (hShared : SharedScanInput BaseModulus W c inc s) :
    ∃ t, Run W (scanAcrossModes prepareSelectedScanMode) s t
      ((20*c+20*d+69+scanInstalledModeCost BaseModulus NR NC c+14)*Dg+8) ∧
      Frame (scanAcrossModes prepareSelectedScanMode) s t ∧
      SelectorData plan c d t ∧ SharedScanInput BaseModulus W c inc t ∧ t.vars scanAllAnswer ≤ 1 ∧
      (t.vars scanAllAnswer=1 ↔
        scanNativeRecoveryProbes D w m h hw b.1 L
          (fun k => rawScalarModes (crop (sites SrcGauge SrcGauge k)))=true) := by
  obtain ⟨u,r,f,ht,hc,hb,hVerdict⟩ :=
    scanSelectedModes_run inc plan hW hRows hLayout hNM hCount hModes hTables hShared
  refine ⟨u,r,f,ht,hc,hb,hVerdict.trans ?_⟩
  have hK := scanSourceProbes_iff_incidence D T P Q out hOut b L hn hRank x hx hs
  rw [hK]
  change (∀ i, (plan i).scalar (M:=BaseModulus) inc) ↔
    ∀ z : coords, (mat).mulVec z=0 →
      rawScalarModes (crop (sites SrcGauge SrcGauge (nativeBaseAssignment w m AF L z)))=true
  have eqAt (i) := (plan i).scalar_iff_supportedSites (M:=BaseModulus) inc (physicalWord i) (active i)
    (covered i).fromChart (covered i).toChart (covered i).reference
  constructor
  · intro hy z hz
    exact (cropMeaning z hz).mpr (fun i => (eqAt i).mp (hy i) z hz)
  · intro hz i
    exact (eqAt i).mpr (fun z hz' => (cropMeaning z hz').mp (hz z hz') i)

#print axioms runNativeSourceProbe
end EvenTI.P22Scalar

