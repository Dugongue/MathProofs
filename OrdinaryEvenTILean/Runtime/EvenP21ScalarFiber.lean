import EvenP15ScalarBranchCRT

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

namespace EvenTI.P21Scalar

open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n d : ℕ}

theorem rawScalarModes_iff_exists (W : Fin d → Matrix (Fin n) (Fin n) K) (hn : 0 < n) :
    rawScalarModes W=true ↔ ∀ i, ∃ c : K, W i=c • 1 := by
  simp only [rawScalarModes,dif_pos hn,List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq]
  constructor
  · intro h i
    exact ⟨_,h i⟩
  · intro h i
    obtain ⟨c,hc⟩ := h i
    have hAt : W i ⟨0,hn⟩ ⟨0,hn⟩=c := by
      rw [hc]
      simp [Matrix.smul_apply]
    rwa [hAt]

private theorem scalarMul_iff (M C : Matrix (Fin n) (Fin n) K) (a : K)
    (ha : a≠0) (h : M=a • 1) :
    (∃ c : K, M*C=c • 1) ↔ ∃ c : K, C=c • 1 := by
  rw [h,Matrix.smul_mul,Matrix.one_mul]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨a⁻¹*c,?_⟩
    have q := congrArg (fun X : Matrix (Fin n) (Fin n) K => a⁻¹ • X) hc
    simpa only [smul_smul,inv_mul_cancel₀ ha,one_smul] using q
  · rintro ⟨c,hc⟩
    exact ⟨a*c,by rw [hc,smul_smul]⟩

variable (D : FieldEncoding K)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

local instance branchModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) := out.models p i

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


/-- The affine representative is checked once. Each later homogeneous
probe can test the source crop alone. -/
theorem affineProbe_scalar_eq_source (hn : 0 < n)
    (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true)
    (x k : A) (hx : run src x=dst) (hk : run src k=src)
    (hs : rawScalarModes (raw (sites SrcGauge DstGauge x))=true) :
    rawScalarModes (raw (sites SrcGauge DstGauge (x*k)))=
      rawScalarModes (crop (sites SrcGauge SrcGauge k)) := by
  obtain ⟨g,hg⟩ := recoverOriginalTransporter_of_fullModeRank D T T P Q out hOut SrcGauge DstGauge x hRank hx
  have hM := recoverOriginalTransporter_matrices D T T P Q out hOut SrcGauge DstGauge x g hg
  have hS := (rawScalarModes_iff_exists _ hn).mp hs
  have hFix := recoverTrialSites_homogeneous_action out.words out.modes out.layout out.capacities SrcGauge k hk
  have hProduct (i : Fin ((l+1)+(l+1))) :
      raw (sites SrcGauge DstGauge (x*k)) i=raw (sites SrcGauge DstGauge x) i*crop (sites SrcGauge SrcGauge k) i := by
    rw [recoverTrialSites_affine_mul]
    exact recoverRawMatrices_affine T T P Q out.words hWords _ _ hRank hFix i
  have point (i : Fin ((l+1)+(l+1))) : (∃ c : K, raw (sites SrcGauge DstGauge (x*k)) i=c • 1) ↔
      ∃ c : K, crop (sites SrcGauge SrcGauge k) i=c • 1 := by
    obtain ⟨a,ha⟩ := hS i
    have hNonzero : a≠0 := by
      intro h
      letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
      apply Units.ne_zero (g.1 i)
      rw [congrFun hM i,ha,h,zero_smul]
    rw [hProduct]
    exact scalarMul_iff _ _ a hNonzero ha
  apply Bool.eq_iff_iff.mpr
  rw [rawScalarModes_iff_exists _ hn,rawScalarModes_iff_exists _ hn]
  exact forall_congr' point

#print axioms rawScalarModes_iff_exists
#print axioms affineProbe_scalar_eq_source
end EvenTI.P21Scalar

