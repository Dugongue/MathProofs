import EvenP9SelfBranchSound

namespace EvenTI.P12Scalar

open Matrix EvenTI.Action EvenTI.TrialProducer EvenTI.Contract
open EvenTI.CellPreparation EvenTI.LiveAlgebra EvenTI.Part8
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n q d : ℕ}

/-- A mode is scalar exactly when its literal matrix equals its first
entry times the identity. The `n = 0` path is outside the guarded scan. -/
def rawScalarModes (W : Fin d → Matrix (Fin n) (Fin n) K) : Bool :=
  if hn : 0 < n then
    (List.finRange d).all (fun i =>
      decide (W i = W i ⟨0,hn⟩ ⟨0,hn⟩ • (1 : Matrix (Fin n) (Fin n) K)))
  else false

theorem rawScalarModes_of_units (enum : Fin q ≃ Kˣ) (G : Changes K d n) (hn : 0 < n) :
    rawScalarModes (fun i => (G i).val) = onlyScalarModes enum G := by
  apply Bool.eq_iff_iff.mpr
  rw [onlyScalarModes_iff]
  simp only [rawScalarModes, dif_pos hn, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq]
  let j : Fin n := ⟨0,hn⟩
  constructor
  · intro h
    letI : Nonempty (Fin n) := ⟨j⟩
    have hnz i : (G i).val j j ≠ 0 := by
      intro hz
      exact Units.ne_zero (G i) ((h i).trans (by simp [j,hz]))
    refine ⟨fun i => Units.mk0 _ (hnz i),?_⟩
    funext i
    apply Units.ext
    exact (h i).trans (scalar_val (n := n) (Units.mk0 _ (hnz i))).symm
  · rintro ⟨u, rfl⟩ i
    simp [scalars, scalar_val, Matrix.smul_apply, Matrix.one_apply]

private theorem all_tabs_congr {v u : ℕ} (f g : Fin v → Fin u → Bool)
    (H : (List.ofFn (fun i : Fin v =>
      (List.ofFn (fun j : Fin u => decide (f i j = g i j))).all id)).all id = true) :
    (List.ofFn (fun i : Fin v => (List.ofFn (f i)).all id)).all id =
      (List.ofFn (fun i : Fin v => (List.ofFn (g i)).all id)).all id := by
  have h : f = g := by
    funext i j
    have hi : (List.ofFn (fun j : Fin u => decide (f i j = g i j))).all id = true :=
      (List.all_eq_true (p := id)).mp H _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have hj : decide (f i j = g i j) = true :=
      (List.all_eq_true (p := id)).mp hi _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    exact of_decide_eq_true hj
  rw [h]

local macro "branchScalarBit" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.checkRawBranchScalar))
local macro "compiledSelfBranch" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP9DenseSelfScanner
    `EvenTI.CellPreparation.branchOfCompiled))

variable (F : FieldEncoding K) (FP : FieldPresentation K) (enum : Fin q ≃ Kˣ)
variable (T : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial F) (hOut : compileTrialBanks F T T P Q = some out)
variable (b : {b // b ∈ out.branches})

local instance scalarCompiledModels (p) (i) : Fact (((out.modes p).blocks.get i).HasFieldModel) :=
  out.models p i

local notation "A" => (BranchAssignment out.words out.modes)
local notation "run" => (branchSignedAction out.words out.modes out.layout)
local notation "src" => (sourceCoefficients out.words out.modes out.capacities b.1.left)
local notation "dst" => (targetCoefficients out.words out.modes out.capacities b.1.right)
local notation "Raw" => (recoverRawMatrices T T P Q out.words
  (compiledTrialWords_eq F T T P Q out hOut))
local notation "sites" => (recoverTrialSites out.words out.modes out.layout out.capacities)

/-- Inside a verified native affine branch, the raw witness construction
is guaranteed to consist of units with the right action. The scalar probe
can inspect its literal matrices directly. -/
theorem branchScalarBit_eq_matrix_scan (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true)
    (x : A) (hx : run src x = dst) :
    branchScalarBit F enum T P Q out hOut b x =
      rawScalarModes (Raw (sites b.1.left b.1.right x)) := by
  obtain ⟨g,hg⟩ := recoverOriginalTransporter_of_fullModeRank F T T P Q out hOut
    b.1.left b.1.right x hRank hx
  have hm := recoverOriginalTransporter_matrices F T T P Q out hOut b.1.left b.1.right x g hg
  change (match recoverOriginalTransporter F T T P Q out hOut b.1.left b.1.right x with
    | none => false
    | some y => onlyScalarModes enum y.1) = _
  rw [hg, ← hm, rawScalarModes_of_units enum g.1 hn]

/-- The exact branch gate retains the checked Smith and homogeneous
kernel tests, and tests entries of the physically recovered matrices. -/
noncomputable def matrixSelfBranch : Bool :=
  let ho := compiledSelfBranch F T P Q out hOut b
  if nativePrefixSmithBit F out.words out.modes out.layout out.capacities FP b.1 ho then
    nativeBranchKernelCap F out.words out.modes out.layout out.capacities b.1 ho &&
      match recoverNativeBranch F out.words out.modes out.layout out.capacities FP b.1 ho with
      | none => false
      | some x => rawScalarModes (Raw (sites b.1.left b.1.right x)) &&
        scanNativePrefixGenerators F out.words out.modes out.layout out.capacities b.1
          (fun k => rawScalarModes (Raw (sites b.1.left b.1.right (x*k))))
  else true

theorem matrixSelfBranch_exact (hn : 0 < n)
    (hRank : rawRetainedFullRank (l := (l+1)+l) T = true) :
    matrixSelfBranch F FP T P Q out hOut b = checkSelfBranch F FP enum T P Q out hOut b := by
  let ho := compiledSelfBranch F T P Q out hOut b
  let bit := nativePrefixSmithBit F out.words out.modes out.layout out.capacities FP b.1 ho
  let cap := nativeBranchKernelCap F out.words out.modes out.layout out.capacities b.1 ho
  unfold matrixSelfBranch checkSelfBranch
  change (if bit = true then cap && _ else true) = (if bit = true then cap && _ else true)
  by_cases hbit : bit = true
  · simp only [if_pos hbit]
    by_cases hcap : cap = true
    · simp only [hcap, Bool.true_and]
      obtain ⟨x,hx,hs⟩ := recoverNativeBranch_complete_of_cap F out.words out.modes
        out.layout out.capacities FP b.1 ho hcap hbit
      simp only [hx]
      rw [branchScalarBit_eq_matrix_scan F enum T P Q out hOut b hn hRank x hs]
      apply congrArg ((rawScalarModes (Raw (sites b.1.left b.1.right x))) && ·)
      have hSame : scanNativePrefixGenerators F out.words out.modes out.layout out.capacities b.1
          (fun k => decide (rawScalarModes (Raw (sites b.1.left b.1.right (x*k))) =
            branchScalarBit F enum T P Q out hOut b (x*k))) = true := by
        apply scanNativePrefixGenerators_of_tests
        intro k hk
        have hxk : run src (x*k) = dst := by rw [branchSignedAction_mul, hk]; exact hs
        simp only [branchScalarBit_eq_matrix_scan F enum T P Q out hOut b hn hRank (x*k) hxk,
          decide_eq_true_eq]
      unfold scanNativePrefixGenerators scanPrefixBaseColumns at hSame ⊢
      exact all_tabs_congr _ _ hSame
    · have hf : cap = false := Bool.eq_false_iff.mpr hcap
      simp only [hf, Bool.false_and]
  · simp only [if_neg hbit]

#print axioms rawScalarModes_of_units
#print axioms branchScalarBit_eq_matrix_scan
#print axioms matrixSelfBranch_exact

end EvenTI.P12Scalar
