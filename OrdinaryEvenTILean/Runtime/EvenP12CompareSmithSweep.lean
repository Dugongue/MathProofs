import EvenP11PaidSmithVerdict
import EvenP11DenseCost
import EvenP6RawBankBound
import EvenP10ScanCompare

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open EvenTI.LiveAlgebra EvenTI.PrimaryAlignment EvenTI.CellProducer
open EvenOrdinaryTI.LiveRows EvenOrdinaryTI.LiveRows.Physical
open Lax13Proofs.Imp Lax13Proofs.Reasoning EvenTI.Part7
open Lax51.BinaryWordEncoding
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 1000000

section Native

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  (F : FieldEncoding K) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n = w.width p)
  [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
  (b : BankedBranch F w m h hw)

local instance compareSmithLocalWords (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v

local instance compareSmithLocalField (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
local notation "Coeff" => (sourceCoefficients w m hw b.left)

local instance compareSmithLocalJointWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)

local instance compareSmithLocalReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)

local instance compareSmithLocalCompact :
    ∀ j : Fin (rawCells F.symm AC).length, CellFieldCertificate AC ((rawCells F.symm AC).get j) :=
  liveCellCertificate BT F.symm BE

local notation "SX" => (NativeSignedSources w m)
local notation "SY" => (NativeSignedTargets F w m h hw b.left)
local notation "SRC" => (nativeSignedSourceView w m)
local notation "DST" => (nativeSignedTargetView F w m h hw b.left)
local notation "s" => (∑ p, CodeWidth w m p)
local notation "t" => ((activeCells (compactProductPack F.symm AC (liveOperand BT BE Coeff))).card)
local notation "V" => (VarCount (s * 2 + 1) (t + s + 1) (w.sites + 2))
local notation "J" => (RowCount (t + s + 1) (w.sites + 2))

/-- Charge the actual executed register work, summed over the installed
reference calls of a live comparison branch. -/
noncomputable def observedNativeSmithCost (FP : FieldPresentation K)
    (ho : ActualBankedBranch F w m h hw b) : ℕ :=
  let src := nativeSignedOrigins F w m h hw b.left
  let maps := nativeSignedIncidence F w m h hw b.left
  let constants := nativeSignedRatios F w m h hw b.left b.output
  let exactBank := nativePrefixBanksExact F w m h hw b.left b.right b.output ho
  let B (i : Fin (V + J)) := prefixKernelWordBound SX SY FP SRC DST (finSumFinEquiv.symm i)
  let T (i : Fin (V + J)) := prefixKernelFuel SX SY FP SRC DST (finSumFinEquiv.symm i)
  let σ (i : Fin (V + J)) := prefixKernelState SX SY src maps F.symm FP SRC DST
    constants b.output.2 exactBank (finSumFinEquiv.symm i)
  ∑ i : Fin (V + J), ((evalBounded (B i) (T i) (installThenSmith FP) (σ i)).map Prod.snd).getD 0

theorem observedNativeSmithCost_le (FP : FieldPresentation K) (L : ℕ)
    (ho : ActualBankedBranch F w m h hw b)
    (hPaid : PaidNativeSmithVerdict F w m h hw b FP L ho) :
    observedNativeSmithCost F w m h hw b FP ho ≤
      nativeReferenceCapacity L * physicalSmithFuelBound FP (nativeReferenceCapacity L) := by
  unfold PaidNativeSmithVerdict at hPaid
  dsimp only at hPaid
  obtain ⟨outputs,costs,hExact,hCost,_⟩ := hPaid
  unfold observedNativeSmithCost
  dsimp only
  refine le_trans ?_ hCost
  exact le_of_eq (Finset.sum_congr rfl (fun i _ => by rw [hExact i]; rfl))

end Native

section Raw

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

/-- Sweep all branches of a successful compiled pair. This upper bounds
the work when the actual search exits on its first successful branch. -/
noncomputable def compiledPairSmithCost (F : FieldEncoding K) (FP : FieldPresentation K)
    (T S : Dense K l n) (P Q : PreparedTrial K l n) : ℕ :=
  match ho : compileTrialBanks F T S P Q with
  | none => 0
  | some out =>
    letI := out.models
    ∑ i : Fin out.branches.length,
      observedNativeSmithCost F out.words out.modes out.layout out.capacities
        (out.branches.get i) FP
        (actualCompiledBranch F T S P Q out ho (out.branches.get i) (List.get_mem _ _))

def installedSmithSweepBound (FP : FieldPresentation K) (L : ℕ) : ℕ :=
  nativeReferenceCapacity (16 * L) * physicalSmithFuelBound FP (nativeReferenceCapacity (16 * L))

theorem compiledPairSmithCost_le (F : FieldEncoding K) (FP : FieldPresentation K)
    (T S : Dense K l n) (P Q : PreparedTrial K l n)
    (hn : 2 ≤ n) (L : ℕ) (hL : n ^ ((l + 1) + (l + 1)) ≤ L) :
    compiledPairSmithCost F FP T S P Q ≤ L * installedSmithSweepBound FP L := by
  unfold compiledPairSmithCost
  split
  · omega
  · rename_i out ho
    letI := out.models
    have hcount : out.branches.length ≤ L :=
      (compileTrialBanks_bounded F T S P Q out ho hn).1.trans
        ((EvenTI.LiveSpectral.choiceCap_le_inputEntries l n hn).trans hL)
    calc
      _ ≤ ∑ _ : Fin out.branches.length, installedSmithSweepBound FP L := by
        apply Finset.sum_le_sum
        intro i _
        let b := out.branches.get i
        have hb : b ∈ out.branches := List.get_mem _ _
        exact observedNativeSmithCost_le F out.words out.modes out.layout out.capacities b FP
          (16 * L) (actualCompiledBranch F T S P Q out ho b hb)
          (compiledTrial_paidSmithVerdict F FP T S P Q out ho b hb hn L hL)
      _ = out.branches.length * installedSmithSweepBound FP L := by
        simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcount

/-- Total live Smith register cost across the same source-major trial-pair
enumeration used by comparison. -/
noncomputable def preparedCompareSmithCost (F : FieldEncoding K) (FP : FieldPresentation K)
    (T S : Dense K l n) : ℕ :=
  ((prepareTrials F T ×ˢ prepareTrials F S).map fun b =>
    compiledPairSmithCost F FP T S b.1 b.2).sum

private theorem mapped_sum_le {α : Type} (xs : List α) (cost : α → ℕ) (N : ℕ)
    (h : ∀ a ∈ xs, cost a ≤ N) : (xs.map cost).sum ≤ xs.length * N := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (List.mem_cons_of_mem a hx))) |>.trans_eq
      (Nat.add_comm _ _)

theorem preparedCompareSmithCost_le (F : FieldEncoding K) (FP : FieldPresentation K)
    (T S : Dense K l n) (hn : 2 ≤ n) (L : ℕ) (hL : n ^ ((l + 1) + (l + 1)) ≤ L) :
    preparedCompareSmithCost F FP T S ≤ L ^ 3 * installedSmithSweepBound FP L := by
  have hcount : (prepareTrials F T ×ˢ prepareTrials F S).length ≤ L ^ 2 := by
    rw [List.length_product, pow_two]
    exact Nat.mul_le_mul
      ((EvenTI.LiveSpectral.preparedTrialCount_le_inputEntries F T hn).trans hL)
      ((EvenTI.LiveSpectral.preparedTrialCount_le_inputEntries F S hn).trans hL)
  unfold preparedCompareSmithCost
  calc
    _ ≤ (prepareTrials F T ×ˢ prepareTrials F S).length *
        (L * installedSmithSweepBound FP L) := mapped_sum_le _ _ _ fun b _ =>
          compiledPairSmithCost_le F FP T S b.1 b.2 hn L hL
    _ ≤ L ^ 2 * (L * installedSmithSweepBound FP L) := Nat.mul_le_mul_right _ hcount
    _ = L ^ 3 * installedSmithSweepBound FP L := by ring

end Raw

#print axioms preparedCompareSmithCost_le
end EvenTI.CellPreparation
