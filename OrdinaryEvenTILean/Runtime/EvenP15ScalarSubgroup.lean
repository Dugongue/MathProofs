import EvenP15ScalarBranchSemantics

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option linter.unusedSectionVars false
set_option quotPrecheck false

namespace EvenTI.P15Scalar

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P12Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n q : ℕ}
variable (D : FieldEncoding K) (enum : Fin q ≃ Kˣ)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

private local instance subgroupModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i

local macro "mixedScalar" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9SelfBranchSound `EvenTI.CellPreparation.mixedScalar_iff))
local macro "cropHom" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9RawAffine `EvenTI.CellPreparation.sourceCropHom))
local macro "cropUnits" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9RawAffine `EvenTI.CellPreparation.homogeneousCropUnits))
local macro "cropValue" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9RawAffine `EvenTI.CellPreparation.homogeneousCropUnits_val))
local macro "actsHomogen" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9RawAffine `EvenTI.CellPreparation.homogeneousActs))

local notation "A" => (BranchAssignment out.words out.modes)
local notation "run" => (branchSignedAction out.words out.modes out.layout)
local notation "src" => (sourceCoefficients out.words out.modes out.capacities b.1.left)
local notation "dst" => (targetCoefficients out.words out.modes out.capacities b.1.right)
local notation "sites" => (recoverTrialSites out.words out.modes out.layout out.capacities)
local notation "hWords" => (compiledTrialWords_eq D T T P Q out hOut)
local notation "raw" => (recoverRawMatrices T T P Q out.words hWords)
local notation "Fix" => (nativeSourceFix D out b)
local notation "left" => b.1.left
local notation "right" => b.1.right

include enum in
/-- Once a feasible representative passes, each homogeneous probe is a
membership test in one subgroup. Any complete generating system for the
kernel gives the self-branch verdict. -/
theorem matrixSelfProbe_isSubgroup (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true)
    (x : A) (hx : run src x = dst) (hScalar : rawScalarModes (raw (sites left right x)) = true) :
    ∃ S : Subgroup A, ∀ k : A, run src k = src →
      (rawScalarModes (raw (sites left right (x*k))) = true ↔ k ∈ S) := by
  let rho := cropHom D T P Q out hOut b hRank
  let scalarUnits := (scalarMap (K := K) (d := (l+1)+(l+1)) (n := n)).range
  let S := (scalarUnits.comap rho).map (Fix).subtype
  obtain ⟨g,hg⟩ := recoverOriginalTransporter_of_fullModeRank D T T P Q out hOut left right x hRank hx
  have he := (branchScalarBit_eq_matrix_scan D enum T P Q out hOut b hn hRank x hx).trans hScalar
  change (match recoverOriginalTransporter D T T P Q out hOut left right x with
    | none => false
    | some y => onlyScalarModes enum y.1) = true at he
  rw [hg] at he
  have hs : g.1 ∈ scalarUnits := scalarMap_mem_range.mpr ((onlyScalarModes_iff enum g.1).mp he)
  have hMix (k : Fix) (i : Fin ((l+1)+(l+1))) :
      raw (sites left right (x*k.1)) i = raw (sites left right x) i * (rho k i).val := by
    have h := recoverRawMatrices_affine T T P Q out.words hWords
      (sites left right x) (sites left left k.1) hRank (actsHomogen D out b k) i
    rw [recoverTrialSites_affine_mul]
    change raw (sites left right x * sites left left k.1) i =
      raw (sites left right x) i * (cropUnits D T P Q out hOut b hRank k i).val
    rw [cropValue D T P Q out hOut b hRank k i]
    exact h
  refine ⟨S,?_⟩
  intro k hk
  let z : Fix := ⟨k,hk⟩
  have hSol : run src (x*k) = dst := by rw [branchSignedAction_mul,hk]; exact hx
  have hQ : k ∈ S ↔ rho z ∈ scalarUnits := by
    change (∃ y : Fix, rho y ∈ scalarUnits ∧ (y : A) = k) ↔ _
    constructor
    · rintro ⟨y,hy,eq⟩
      exact (Subtype.ext eq : y=z) ▸ hy
    · intro h
      exact ⟨z,h,rfl⟩
  rw [← branchScalarBit_eq_matrix_scan D enum T P Q out hOut b hn hRank (x*k) hSol]
  exact (mixedScalar D enum T P Q out hOut b hRank x hx g hg hs rho hMix z).trans hQ.symm

#print axioms matrixSelfProbe_isSubgroup
end EvenTI.P15Scalar