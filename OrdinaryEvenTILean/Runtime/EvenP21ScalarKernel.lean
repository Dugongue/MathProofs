import EvenP21ScalarBranch
import EvenP15RecoverIncidenceTriple

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

namespace EvenTI.P21Scalar

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


/-- Characterize the exact branch probe by the kernel of the numeric
incidence bank used by the paid machine. -/
theorem scanSourceProbes_iff_incidence (L : BaseUnitLog K) (hn : 0<n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true)
    (x : A) (hx : actB src x=dst) (hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true) :
    scanNativeRecoveryProbes D w m h hw b.1 L (fun k => rawScalarModes (crop (sites SrcGauge SrcGauge k)))=true ↔
      ∀ z, (mat).mulVec z=0 →
        rawScalarModes (crop (sites SrcGauge SrcGauge (decode (lift L (Multiplicative.ofAdd z)))))=true := by
  obtain ⟨R,hR⟩ := matrixSelfProbe_isSubgroup D (Fintype.equivFin Kˣ).symm T P Q out hOut b
    hn hRank x hx hs
  let phys := (decode).comp (lift L)
  let test := fun z => rawScalarModes (crop (sites SrcGauge SrcGauge (phys (Multiplicative.ofAdd z))))
  let Q₀ : AddSubgroup _ :=
    { carrier := {z | phys (Multiplicative.ofAdd z) ∈ R}
      zero_mem' := by change phys 1 ∈ R; rw [map_one]; exact R.one_mem
      add_mem' := by
        intro a c ha hc
        change phys (Multiplicative.ofAdd a * Multiplicative.ofAdd c) ∈ R
        rw [map_mul]; exact R.mul_mem ha hc
      neg_mem' := by
        intro a ha
        change phys (Multiplicative.ofAdd a)⁻¹ ∈ R
        rw [map_inv]; exact R.inv_mem ha }
  have good (z) (hz : (mat).mulVec z=0) : test z=true ↔ z∈Q₀ := by
    have hBase : (baseEquationMatrix (K:=K) OR).mulVec z=0 := hz
    have fixed := decodeHomogeneous D w m h hw b.1 _ ((liftBaseCoordinates_kernel_iff SX SY OR EM L z).mpr hBase)
    let k : A := phys (Multiplicative.ofAdd z)
    change rawScalarModes (crop (sites SrcGauge SrcGauge k))=true ↔ k∈R
    rw [← affineProbe_scalar_eq_source D T P Q out hOut b hn hRank x k hx fixed hs]
    exact hR k fixed
  change scanRecoveryKernelProbes mat test=true ↔ ∀ z, (mat).mulVec z=0 → test z=true
  rw [scanRecoveryKernelProbes_iff mat test Q₀ good]
  exact ⟨fun hg z hz => (good z hz).mpr (hg z hz),fun hg z hz => (good z hz).mp (hg z hz)⟩

#print axioms scanSourceProbes_iff_incidence
end EvenTI.P21Scalar




