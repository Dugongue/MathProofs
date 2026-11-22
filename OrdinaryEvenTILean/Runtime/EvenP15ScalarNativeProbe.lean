import EvenP15ScalarPrefixProbe
import EvenP9NativeGenerators
import EvenP9BaseKernelScan
import EvenP9AffineMultiplication

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.Part8 EvenTI.Action EvenTI.Contract EvenTI.LiveAlgebra EvenTI.PrimaryAlignment EvenTI.CellProducer
open EvenOrdinaryTI.LiveRows
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 1600000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  (F : FieldEncoding K) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n = w.width p)
  [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
  (b : BankedBranch F w m h hw)

local instance p15GeneratorWords (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance p15GeneratorFields (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
local notation "WS" => (SharedField (CodeField w m))

local instance p15GeneratorJointWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)

local instance p15GeneratorReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)

local instance p15GeneratorCompact :
    ∀ j : Fin (rawCells F.symm AC).length, CellFieldCertificate AC ((rawCells F.symm AC).get j) :=
  liveCellCertificate BT F.symm BE

local notation "Coef" => (sourceCoefficients w m hw b.left)
local notation "AF" => (LiveActiveField BT F.symm BE Coef)
local notation "Operand" => (liveOperand BT BE Coef)

local notation "SX" => (NativeSignedSources w m)
local notation "SY" => (NativeSignedTargets F w m h hw b.left)
local notation "ORIG" => (nativeSignedOrigins F w m h hw b.left)
local notation "INC" => (nativeSignedIncidence F w m h hw b.left)
local notation "SRC" => (nativeSignedSourceView w m)
local notation "DST" => (nativeSignedTargetView F w m h hw b.left)

local macro "decodeHomogeneous" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9NativeGenerators
    `EvenTI.CellPreparation.decodeNativeHomogeneous))

private local instance recoveryBaseOrder :
    NeZero (Fintype.card K - 1) := ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

/-- Use the same modular residual matrix as native recovery. Array
production and CRT recovery can use the already checked B/U driver. -/
noncomputable def scanNativeRecoveryProbes (L : BaseUnitLog K) (test : BranchAssignment w m → Bool) : Bool :=
  EvenTI.P15Scalar.scanRecoveryKernelProbes (baseEquationMatrix (K := K) ORIG)
    (fun z => test (recoverSignedHom (K := K) (d := w.sites) WS AF
      (EvenTI.P15Scalar.liftBaseCoordinates (d := w.sites+2) SX SY L (Multiplicative.ofAdd z))))

/-- Recovery probes have the literal existing native generator verdict
for every valid subgroup test, even when the chosen matrix differs. -/
theorem scanNativeRecoveryProbes_eq (L : BaseUnitLog K)
    (ho : ActualBankedBranch F w m h hw b)
    (hCap : nativeBranchKernelCap F w m h hw b ho = true)
    (test : BranchAssignment w m → Bool) (Q : Subgroup (BranchAssignment w m))
    (hTest : ∀ a, branchSignedAction w m h Coef a = Coef → (test a = true ↔ a ∈ Q)) :
    scanNativeRecoveryProbes F w m h hw b L test = scanNativePrefixGenerators F w m h hw b test := by
  let decode := recoverSignedHom (K := K) (d := w.sites) WS AF
  let testPhys := test ∘ decode
  let Qphys := Q.comap decode
  have hTestPhys (a : PhysicalAssignment (d := w.sites+2) SX SY)
      (ha : prefixEvaluation SX SY ORIG INC a = 1) :
      testPhys a = true ↔ a ∈ Qphys :=
    hTest _ (decodeHomogeneous F w m h hw b a ha)
  have hv :
      0 < VarCount ((∑ p, CodeWidth w m p)*2+1)
        ((activeCells (compactProductPack F.symm AC Operand)).card + (∑ p, CodeWidth w m p)+1)
        (w.sites+2) +
      RowCount ((activeCells (compactProductPack F.symm AC Operand)).card + (∑ p, CodeWidth w m p)+1)
        (w.sites+2) := by unfold VarCount; omega
  have hExp : ∀ a : PhysicalAssignment (d := w.sites+2) SX SY,
      prefixEvaluation SX SY ORIG INC a = 1 → a ^ (Fintype.card K-1) = 1 :=
    (prefixKernelCap_iff SX SY ORIG INC F.symm SRC DST b.output.2
      (nativePrefixBanksExact F w m h hw b.left b.right b.output ho) hv).mp hCap
  exact EvenTI.P15Scalar.scanRecoveryBaseProbes_eq SX SY ORIG INC L F.symm testPhys Qphys hTestPhys hExp

#print axioms scanNativeRecoveryProbes_eq
end EvenTI.CellPreparation