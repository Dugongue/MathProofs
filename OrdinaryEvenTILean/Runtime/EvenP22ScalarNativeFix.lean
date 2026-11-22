import EvenP21ScalarBranch
import EvenP15RecoverIncidenceTriple

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 750000
set_option maxRecDepth 14000

namespace EvenTI.P22Scalar

open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.CellProducer EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar EvenTI.P15Recover
open EvenOrdinaryTI.LiveRows
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (D : FieldEncoding K) (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

local instance kernelModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i
local instance kernelWords (p) (v : Fin (CodeWidth out.words out.modes p)) :
    WordTable.Laws (numberedTable (out.modes p) v) := numberedWordLaws (out.modes p) v
local instance kernelFields (p) (v : Fin (CodeWidth out.words out.modes p)) :
    WordFieldCertificate (numberedTable (out.modes p) v) :=
  numberedFieldCertificate (out.modes p) v

local notation "w" => out.words
local notation "m" => out.modes
local notation "h" => out.layout
local notation "hw" => out.capacities
local notation "SrcGauge" => b.1.left
local notation "DstGauge" => b.1.right
local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
local instance liveWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ x y => wordDecode_mul _ x y)
local instance liveReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ x y => wordDecode_mul _ x y)
local instance liveCompact :
    ∀ j : Fin (rawCells D.symm AC).length, CellFieldCertificate AC ((rawCells D.symm AC).get j) :=
  liveCellCertificate BT D.symm BE

local notation "src" => (sourceCoefficients w m hw SrcGauge)
local notation "dst" => (targetCoefficients w m hw DstGauge)
local notation "AF" => (LiveActiveField BT D.symm BE src)
local notation "WS" => (SharedField (CodeField w m))
local notation "SX" => (NativeSignedSources w m)
local notation "SY" => (NativeSignedTargets D w m h hw SrcGauge)
local notation "OR" => (nativeSignedOrigins D w m h hw SrcGauge)
local notation "EM" => (nativeSignedIncidence D w m h hw SrcGauge)
local notation "actB" => (branchSignedAction w m h)
local notation "hWords" => (compiledTrialWords_eq D T T P Q out hOut)
local notation "raw" => (recoverRawMatrices T T P Q w hWords)
local notation "crop" => (sourceTrialCrop T T P Q w hWords)
local notation "sites" => (recoverTrialSites w m h hw)
local notation "decode" => (recoverSignedHom (d := (w).sites) WS AF)
local notation "lift" => (liftBaseCoordinates (d := (w).sites+2) SX SY)
local notation "A" => (BranchAssignment w m)
local notation "mat" => (incidenceMatrix (Fintype.card K-1) (physicalSrc OR))

local macro "decodeHomogeneous" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9NativeGenerators
    `EvenTI.CellPreparation.decodeNativeHomogeneous))

private local instance baseOrder : NeZero (Fintype.card K-1) :=
  ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩


/-- The actual numeric incidence bank certifies that its decoded CRT vector
fixes the compiled source coefficients. -/
theorem numericKernel_fixes_action (L : BaseUnitLog K)
    (z : Fin (VarCount ((∑ p, CodeWidth w m p)*2+1)
      ((activeCells (compactProductPack D.symm AC (liveOperand BT BE src))).card+
        (∑ p, CodeWidth w m p)+1) ((w).sites+2)) → ZMod (Fintype.card K-1))
    (hz : (mat).mulVec z=0) :
    actB src (decode (lift L (Multiplicative.ofAdd z)))=src := by
  have hBase : (baseEquationMatrix (K:=K) OR).mulVec z=0 := hz
  exact decodeHomogeneous D w m h hw b.1 _ ((liftBaseCoordinates_kernel_iff SX SY OR EM L z).mpr hBase)

#print axioms numericKernel_fixes_action
end EvenTI.P22Scalar
