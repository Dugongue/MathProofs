import EvenP12ScalarProbe
import EvenP9RawAffine

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
variable (D : FieldEncoding K) (F : FieldPresentation K) (enum : Fin q ≃ Kˣ)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
variable (b : {b // b ∈ out.branches})

local instance branchModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i

local macro "compiledBranch" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.branchOfCompiled))
local macro "branchBit" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.checkRawBranchScalar))

local notation "A" => (BranchAssignment out.words out.modes)
local notation "run" => (branchSignedAction out.words out.modes out.layout)
local notation "src" => (sourceCoefficients out.words out.modes out.capacities b.1.left)
local notation "dst" => (targetCoefficients out.words out.modes out.capacities b.1.right)
local notation "sites" => (recoverTrialSites out.words out.modes out.layout out.capacities b.1.left b.1.right)
local notation "raw" => (recoverRawMatrices T T P Q out.words (compiledTrialWords_eq D T T P Q out hOut))
local notation "ho" => (compiledBranch D T P Q out hOut b)
local notation "verdict" => (nativePrefixSmithBit D out.words out.modes out.layout out.capacities F b.1 ho)
local notation "cap" => (nativeBranchKernelCap D out.words out.modes out.layout out.capacities b.1 ho)

omit enum in
/-- On a feasible capped branch, the checked scanner tests scalarity of the
entire transporter fibre. In particular, its result is independent of the
particular verified representative or complete generating family used. -/
theorem matrixSelfBranch_iff_all_solutions (e : Fin q ≃ Kˣ) (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true)
    (hVerdict : verdict = true) (hCap : cap = true) :
    matrixSelfBranch D F T P Q out hOut b = true ↔
      ∀ x : A, run src x = dst → rawScalarModes (raw (sites x)) = true := by
  constructor
  · intro h x hx
    have hh : checkSelfBranch D F e T P Q out hOut b = true :=
      (matrixSelfBranch_exact D F e T P Q out hOut b hn hRank).symm.trans h
    obtain ⟨g,hg,hgScalar⟩ := checkSelfBranch_sound D F e T P Q out hOut b hRank hh x hx
    rw [← branchScalarBit_eq_matrix_scan D e T P Q out hOut b hn hRank x hx]
    change (match recoverOriginalTransporter D T T P Q out hOut b.1.left b.1.right x with
      | none => false
      | some y => onlyScalarModes e y.1) = true
    rw [hg]
    exact (onlyScalarModes_iff e g.1).mpr hgScalar
  · intro h
    obtain ⟨x,hx,hxAct⟩ := recoverNativeBranch_complete_of_cap D out.words out.modes
      out.layout out.capacities F b.1 ho hCap hVerdict
    unfold matrixSelfBranch
    change (if verdict = true then cap && _ else true) = true
    rw [if_pos hVerdict,hCap,Bool.true_and,hx,Bool.and_eq_true]
    refine ⟨h x hxAct,?_⟩
    apply scanNativePrefixGenerators_of_tests
    intro k hk
    exact h (x*k) (by rw [branchSignedAction_mul,hk]; exact hxAct)

#print axioms matrixSelfBranch_iff_all_solutions
end EvenTI.P15Scalar