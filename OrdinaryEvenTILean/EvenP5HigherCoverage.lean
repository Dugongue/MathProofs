import EvenP5TrialList
import EvenP4Shape

namespace EvenTI.TrialProducer

open scoped BigOperators Matrix
open Matrix Module EvenTI.Action EvenTI.Contract
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenTI.Singular.Coverage
open Mathproof.Problem17RepeatedBudget

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

noncomputable def physicalBudget (A : Fin (l + 1) × Bool → Matrix (Fin n) (Fin n) K) : ℕ :=
  ∑ i, repeatedBudget (A i).charpoly

theorem physicalBudget_eq {R S : Submodule K (Coord (l + 1) n → K)}
    (p : GoodPair R S) (A : DenseKernelFiber R S) :
    physicalBudget (rawHigherSingularAnchors p.ell p.rho A.val) = singularBudget p A := by
  simp only [physicalBudget, singularBudget, rawHigherSingularAnchors_eq]

theorem rawHigherSingularAnchors_follow (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (ell rho : Coord (l + 1) n → K)
    (i : Fin (l + 1) × Bool) :
    let P := if i.2 then rightModes g i.1 else leftModes g i.1
    rawHigherSingularAnchors (moveLeftForm g ell) (moveRightForm g rho) (act g T) i =
      P.val * rawHigherSingularAnchors ell rho T i * P.inv := by
  rcases i with ⟨i, b⟩
  have h := literalSingularAnchors_act i i ell rho T g
  cases b
  · simpa only [rawHigherSingularAnchors, rawPhysicalAnchors_eq, if_false,
      Bool.false_eq_true] using congrArg Prod.fst h
  · simpa only [rawHigherSingularAnchors, rawPhysicalAnchors_eq, if_true] using
      congrArg Prod.snd h

theorem physicalBudget_follow (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (ell rho : Coord (l + 1) n → K) :
    physicalBudget
        (rawHigherSingularAnchors (moveLeftForm g ell) (moveRightForm g rho) (act g T)) =
      physicalBudget (rawHigherSingularAnchors ell rho T) := by
  unfold physicalBudget
  apply Finset.sum_congr rfl
  intro i _
  rw [rawHigherSingularAnchors_follow, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Units.inv_val, Matrix.one_mul]

/-- Recover a source trial witnessing the previously checked higher-order
spectral gate, together with its matching target trial. -/
theorem higherSingular_accepted_follow (F : FieldEncoding K) (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (hl : 2 ≤ l)
    (hd : (flatten (l := l + 1) (r := l + 1) T).det = 0)
    (h : singularShapeAccepted T) :
    ∃ (p : CutFormPair K (l + 1) (l + 1) n),
      higherTrial T p ∈ prepareTrials F T ∧
      higherTrial (act g T) (moveLeftForm g p.1, moveRightForm g p.2) ∈
        prepareTrials F (act g T) ∧
      Fintype.card K ^ physicalBudget (rawHigherSingularAnchors p.1 p.2 T) ≤
        n ^ ((l + 1) + (l + 1)) := by
  obtain ⟨k, A, hAT, hgate, p, hbudget⟩ := h
  subst T
  have hL : (leftCutKernel A.val).ker = k.2 := by
    simpa only [leftCutKernel, ← Matrix.toLin'_apply'] using A.property.2
  have hR : (rightCutKernel A.val).ker = k.1 := by
    simpa only [rightCutKernel, ← Matrix.toLin'_apply'] using A.property.1
  have hp : (p.ell, p.rho) ∈ rawFullRankCutForms F A.val := by
    apply (mem_rawCutBankForms F _ _ _ _ _).mpr
    have hLell : leftCutKernel A.val p.ell = 0 := (left_mem_iff_fiber A p.ell).mp p.ell_mem
    have hRrho : rightCutKernel A.val p.rho = 0 := (right_mem_iff_fiber A p.rho).mp p.rho_mem
    refine ⟨⟨⟨hLell, ?_⟩, p.ell_ne_zero, (rawRetainedFullRank_spec _).mpr p.ell_rank⟩,
      ⟨⟨hRrho, ?_⟩, p.rho_ne_zero, (rawRetainedFullRank_spec _).mpr p.rho_rank⟩⟩
    · have hdim := congrArg (fun U : Submodule K (Coord (l + 1) n → K) => finrank K U) hL
      rw [hdim, ← fiber_coranks_eq A]
      exact hgate
    · have hdim := congrArg (fun U : Submodule K (Coord (l + 1) n → K) => finrank K U) hR
      rw [hdim]
      exact hgate
  have hnunit : ¬ IsUnit (flatten (l := l + 1) (r := l + 1) A.val) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact not_isUnit_zero
  obtain ⟨hs, ht⟩ := higherTrials_follow F A.val g (by omega) hnunit (p.ell, p.rho) hp
  exact ⟨(p.ell, p.rho), hs, ht, by simpa only [physicalBudget_eq p A] using hbudget⟩

#print axioms physicalBudget_follow
#print axioms higherSingular_accepted_follow

end EvenTI.TrialProducer
