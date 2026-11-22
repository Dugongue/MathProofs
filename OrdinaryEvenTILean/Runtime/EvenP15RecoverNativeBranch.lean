import EvenP15RecoverPrefixCRT
import EvenP8Attempt

namespace EvenTI.P15Recover

open scoped BigOperators
open EvenTI.Part8 EvenTI.Action EvenTI.Contract EvenTI.LiveAlgebra
open EvenTI.PrimaryAlignment EvenTI.CellProducer EvenTI.CellPreparation EvenOrdinaryTI.LiveRows
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option maxHeartbeats 4500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  (F : FieldEncoding K) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n = w.width p)
  [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
  (FP : FieldPresentation K) (b : BankedBranch F w m h hw)

local instance recoveryWords (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance recoveryFields (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
local notation "WS" => (SharedField (CodeField w m))

local instance recoveryJointWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)
local instance recoveryReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)
local instance recoveryCompact :
    ∀ j : Fin (rawCells F.symm AC).length, CellFieldCertificate AC ((rawCells F.symm AC).get j) :=
  liveCellCertificate BT F.symm BE

local notation "Coef" => (sourceCoefficients w m hw b.left)
local notation "Target" => (targetCoefficients w m hw b.right)
local notation "AF" => (LiveActiveField BT F.symm BE Coef)
local notation "Operand" => (liveOperand BT BE Coef)
local notation "Mode" => (liveMode BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ => wordDecode_mul _))
local notation "Key" => (commonKey w.mode (branchIsFree w m))
local notation "Neg" => (fun i _ => w.minus i)
local notation "Link" => (sharedLink (K := K) (CodeField w m) w.mode (branchIsFree w m))
local notation "O" => (joinedOrigin F.symm AC Mode Key Operand)
local notation "N" => (joinedNegative F.symm AC Mode Neg Operand)
local notation "E" => (joinedEmbedding F.symm AC Mode WS Key Link Operand)

local notation "SX" => (NativeSignedSources w m)
local notation "SY" => (NativeSignedTargets F w m h hw b.left)
local notation "ORIG" => (nativeSignedOrigins F w m h hw b.left)
local notation "INC" => (nativeSignedIncidence F w m h hw b.left)
local notation "SRC" => (nativeSignedSourceView w m)
local notation "DST" => (nativeSignedTargetView F w m h hw b.left)
local notation "C" => (nativeSignedRatios F w m h hw b.left b.output)

noncomputable def recoverNativeBranchCRT (ho : ActualBankedBranch F w m h hw b) :
    Option (BranchAssignment w m) :=
  (recoverLivePrefixCRT SX SY ORIG INC F.symm FP SRC DST C b.output.2
    (nativePrefixBanksExact F w m h hw b.left b.right b.output ho)).map
      (recoverSignedVariables (d := w.sites) WS AF)

theorem recoverNativeBranchCRT_available (ho : ActualBankedBranch F w m h hw b) :
    (recoverNativeBranchCRT F w m h hw FP b ho).isSome =
      (recoverNativeBranch F w m h hw FP b ho).isSome := by
  simpa only [recoverNativeBranchCRT,recoverNativeBranch,Option.isSome_map] using
    recoverLivePrefixCRT_available SX SY ORIG INC F.symm FP SRC DST C b.output.2
      (nativePrefixBanksExact F w m h hw b.left b.right b.output ho)

private theorem actual_ratios (ho : ActualBankedBranch F w m h hw b) :
    rawRatios F.symm AC Operand (liveOperand BT BE Target) = some b.output.1 := by
  unfold ActualBankedBranch compileModeBanks compileRawPrefix at ho
  obtain ⟨ratios,hr,hout⟩ := Option.map_eq_some_iff.mp ho
  exact hr.trans (congrArg some (congrArg Prod.fst hout))

theorem recoverNativeBranchCRT_sound (ho : ActualBankedBranch F w m h hw b)
    {x : BranchAssignment w m} (hx : recoverNativeBranchCRT F w m h hw FP b ho = some x) :
    branchSignedAction w m h Coef x = Target := by
  unfold recoverNativeBranchCRT at hx
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp hx
  apply (liveSignedCells_iff BT F.symm BE (branchDecode w m)
    (fun _ _ => wordDecode_one _) (fun _ _ => wordDecode_mul _) WS Key Link Neg Coef Target _).mpr
  refine ⟨b.output.1,actual_ratios F w m h hw b ho,?_⟩
  exact recoverSignedVariables_exact WS AF O E N z b.output.1
    (recoverLivePrefixCRT_sound SX SY ORIG INC F.symm FP SRC DST C b.output.2
      (nativePrefixBanksExact F w m h hw b.left b.right b.output ho) hz)

#print axioms recoverNativeBranchCRT_available
#print axioms recoverNativeBranchCRT_sound

end EvenTI.P15Recover
