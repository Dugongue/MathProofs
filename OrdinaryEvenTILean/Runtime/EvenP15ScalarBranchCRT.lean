import EvenP15ScalarNativeProbe
import EvenP15ScalarSubgroup
import EvenP15RecoverNativeBranch

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
set_option linter.unusedSectionVars false
set_option quotPrecheck false

namespace EvenTI.P15Scalar

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P12Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (D : FieldEncoding K) (F : FieldPresentation K)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

local instance models (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i
local macro "compiledBranch" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.branchOfCompiled))

local notation "A" => (BranchAssignment out.words out.modes)
local notation "run" => (branchSignedAction out.words out.modes out.layout)
local notation "src" => (sourceCoefficients out.words out.modes out.capacities b.1.left)
local notation "sites" => (recoverTrialSites out.words out.modes out.layout out.capacities b.1.left b.1.right)
local notation "raw" => (recoverRawMatrices T T P Q out.words (compiledTrialWords_eq D T T P Q out hOut))
local notation "ho" => (compiledBranch D T P Q out hOut b)
local notation "verdict" => (nativePrefixSmithBit D out.words out.modes out.layout out.capacities F b.1 ho)
local notation "cap" => (nativeBranchKernelCap D out.words out.modes out.layout out.capacities b.1 ho)

/-- The scalar branch driven only by the ordinary CRT recovery interface.
The tests use raw matrices, and the generator selection does not require
an executable right Smith transformation. -/
noncomputable def matrixSelfBranchCRT (L : BaseUnitLog K) : Bool :=
  if verdict then
    cap && match recoverNativeBranch D out.words out.modes out.layout out.capacities F b.1 ho with
      | none => false
      | some x => rawScalarModes (raw (sites x)) &&
        scanNativeRecoveryProbes D out.words out.modes out.layout out.capacities b.1 L
          (fun k => rawScalarModes (raw (sites (x*k))))
  else true

/-- This implementation target preserves the existing scalar decision on
every feasible self branch of a source passing the retained-rank test. -/
theorem matrixSelfBranchCRT_exact (L : BaseUnitLog K) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true) :
    matrixSelfBranchCRT D F T P Q out hOut b L = matrixSelfBranch D F T P Q out hOut b := by
  unfold matrixSelfBranchCRT matrixSelfBranch
  change (if verdict = true then cap && _ else true) =
    (if verdict = true then cap && _ else true)
  by_cases hv : verdict = true
  · simp only [if_pos hv]
    by_cases hc : cap = true
    · simp only [hc,Bool.true_and]
      obtain ⟨x,hx,hxAct⟩ := recoverNativeBranch_complete_of_cap D out.words out.modes
        out.layout out.capacities F b.1 ho hc hv
      rw [hx]
      by_cases hS : rawScalarModes (raw (sites x)) = true
      · let enum : Fin (Fintype.card Kˣ) ≃ Kˣ := (Fintype.equivFin Kˣ).symm
        obtain ⟨R,hR⟩ := matrixSelfProbe_isSubgroup D enum T P Q out hOut b hn hRank x hxAct hS
        simp only [hS,Bool.true_and]
        exact scanNativeRecoveryProbes_eq D out.words out.modes out.layout out.capacities b.1 L
          ho hc (fun k => rawScalarModes (raw (sites (x*k)))) R hR
      · have hf : rawScalarModes (raw (sites x)) = false := Bool.eq_false_iff.mpr hS
        simp only [hf,Bool.false_and]
    · have hf : cap = false := Bool.eq_false_iff.mpr hc
      simp only [hf,Bool.false_and]
  · simp only [if_neg hv]

/-- A feasible witness from any implementation gives the same scalar
decision. The scalar test can therefore share comparison's physical
coordinate recovery, including any admissible root choices. -/
theorem matrixSelf_branch_via_verified_CRT_witness (L : BaseUnitLog K) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true)
    (hv : verdict = true) (hc : cap = true)
    (x : A)
    (hx : run src x = targetCoefficients out.words out.modes out.capacities b.1.right) :
    (rawScalarModes (raw (sites x)) &&
      scanNativeRecoveryProbes D out.words out.modes out.layout out.capacities b.1 L
        (fun k => rawScalarModes (raw (sites (x*k))))) =
      matrixSelfBranch D F T P Q out hOut b := by
  let e : Fin (Fintype.card Kˣ) ≃ Kˣ := (Fintype.equivFin Kˣ).symm
  let target := targetCoefficients out.words out.modes out.capacities b.1.right
  let test (k : A) := rawScalarModes (raw (sites (x*k)))
  have hOld := matrixSelfBranch_iff_all_solutions D F T P Q out hOut b e hn hRank hv hc
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true,hOld]
  constructor
  · rintro ⟨hS,hProbes⟩ y hy
    obtain ⟨R,hR⟩ := matrixSelfProbe_isSubgroup D e T P Q out hOut b hn hRank x hx hS
    have hScan := scanNativeRecoveryProbes_eq D out.words out.modes out.layout out.capacities b.1 L
      ho hc test R hR
    have hOldScan : scanNativePrefixGenerators D out.words out.modes
        out.layout out.capacities b.1 test = true := hScan.symm.trans hProbes
    have hAll := (scanNativePrefixGenerators_iff D out.words out.modes out.layout out.capacities
      b.1 ho hc test R hR).mp hOldScan
    obtain ⟨k,hk,he⟩ := (branchSignedAction_fiber out.words out.modes out.layout
      src target x hx y).mp hy
    rw [he]
    exact (hR k hk).mpr (hAll _ hk)
  · intro hAll
    have hS := hAll x hx
    obtain ⟨R,hR⟩ := matrixSelfProbe_isSubgroup D e T P Q out hOut b hn hRank x hx hS
    have hScan := scanNativeRecoveryProbes_eq D out.words out.modes out.layout out.capacities b.1 L
      ho hc test R hR
    refine ⟨hS,hScan.trans ?_⟩
    apply scanNativePrefixGenerators_of_tests
    intro k hk
    exact hAll (x*k) (by rw [branchSignedAction_mul,hk]; exact hx)


/-- Reuse comparison's proved CRT recovery for the affine representative,
then test only the small homogeneous residue probes. -/
noncomputable def matrixSelfBranchViaComparison (L : BaseUnitLog K) : Bool :=
  if verdict then
    cap && match EvenTI.P15Recover.recoverNativeBranchCRT D out.words out.modes out.layout
        out.capacities F b.1 ho with
      | none => false
      | some x => rawScalarModes (raw (sites x)) &&
        scanNativeRecoveryProbes D out.words out.modes out.layout out.capacities b.1 L
          (fun k => rawScalarModes (raw (sites (x*k))))
  else true

/-- Arbitrary root choices in comparison's verified recovery have no
effect on the raw self-branch decision. -/
theorem matrixSelfBranchViaComparison_exact (L : BaseUnitLog K) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true) :
    matrixSelfBranchViaComparison D F T P Q out hOut b L =
      matrixSelfBranch D F T P Q out hOut b := by
  by_cases hv : verdict = true
  · by_cases hc : cap = true
    · obtain ⟨y,hy,_⟩ := recoverNativeBranch_complete_of_cap D out.words out.modes
        out.layout out.capacities F b.1 ho hc hv
      have hSome : (EvenTI.P15Recover.recoverNativeBranchCRT D out.words out.modes out.layout
          out.capacities F b.1 ho).isSome = true :=
        (EvenTI.P15Recover.recoverNativeBranchCRT_available D out.words out.modes out.layout
          out.capacities F b.1 ho).trans (by rw [hy]; rfl)
      cases hx : EvenTI.P15Recover.recoverNativeBranchCRT D out.words out.modes
          out.layout out.capacities F b.1 ho with
      | none => simp [hx] at hSome
      | some x =>
        have hAct := EvenTI.P15Recover.recoverNativeBranchCRT_sound D out.words out.modes
          out.layout out.capacities F b.1 ho hx
        simp only [matrixSelfBranchViaComparison,if_pos hv,hc,Bool.true_and,hx]
        exact matrixSelf_branch_via_verified_CRT_witness D F T P Q out hOut b L hn hRank hv hc x hAct
    · have hf : cap = false := Bool.eq_false_iff.mpr hc
      simp only [matrixSelfBranchViaComparison,matrixSelfBranch,if_pos hv,hf,Bool.false_and]
  · simp only [matrixSelfBranchViaComparison,matrixSelfBranch,if_neg hv]

#print axioms matrixSelfBranchViaComparison_exact

#print axioms matrixSelfBranchCRT_exact
#print axioms matrixSelf_branch_via_verified_CRT_witness
end EvenTI.P15Scalar