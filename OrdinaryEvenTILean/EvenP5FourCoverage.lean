import EvenP5TrialList
import EvenP5TransportRawEnlarged
import EvenP3SingularCoverage

namespace EvenTI.TrialProducer

open Matrix Module EvenTI.Action EvenTI.Contract
open Mathproof.EvenOrdinaryTISingular.EnlargedCut
open Mathproof.EvenTI.Singular.Coverage Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenTI.OrderFour Mathproof.Problem17RepeatedBudget

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

/-- The exact form pair from the order-four acceptance proof is present
in the raw scan. Its transported pair is present in the target scan. -/
theorem fourSingular_accepted_forms (F : FieldEncoding K) (T : Dense K 1 n)
    (g : Changes K (2 + 2) n) (hd : (flatten (l := 2) (r := 2) T).det = 0)
    (h : singularOrderFourAccepted T) :
    ∃ p : CutFormPair K 2 2 n,
      fourTrial rfl T p ∈ prepareTrials F T ∧
      fourTrial rfl (act g T)
        (moveLeftForm (l := 2) (r := 2) g p.1, moveRightForm (l := 2) (r := 2) g p.2) ∈
        prepareTrials F (act g T) ∧
      Fintype.card K ^ (repeatedBudget (rawEnlargedLeftPoly p.1 p.2 T) +
        repeatedBudget (rawEnlargedRightPoly p.1 p.2 T)) ≤ n := by
  obtain ⟨ell, rho, hneL, hneR, he, hr, hgate, hbudget⟩ := h
  have hL : (leftCutKernel T).ker = (exactKernels T).2 := by
    simp only [exactKernels, leftCutKernel, Matrix.toLin'_apply']
  have hR : (rightCutKernel T).ker = (exactKernels T).1 := by
    simp only [exactKernels, rightCutKernel, Matrix.toLin'_apply']
  have he' : leftCutKernel T ell = 0 := LinearMap.mem_ker.mp (hL.symm ▸ he)
  have hr' : rightCutKernel T rho = 0 := LinearMap.mem_ker.mp (hR.symm ▸ hr)
  have hp : (ell, rho) ∈ rawUnfilteredCutForms F T := by
    apply (mem_rawCutBankForms F _ _ _ _ _).mpr
    refine ⟨⟨⟨he', ?_⟩, hneL, rfl⟩, ⟨⟨hr', ?_⟩, hneR, rfl⟩⟩
    · have hdim := congrArg (fun U : Submodule K (Coord 2 n → K) => finrank K U) hL
      rw [hdim, ← fiber_coranks_eq (withExactKernels T)]
      exact hgate
    · have hdim := congrArg (fun U : Submodule K (Coord 2 n → K) => finrank K U) hR
      rw [hdim]
      exact hgate
  have hnu : ¬ IsUnit (flatten (l := 2) (r := 2) T) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact not_isUnit_zero
  obtain ⟨hs, ht⟩ := fourTrials_follow F T g hnu (ell, rho) hp
  exact ⟨(ell, rho), hs, ht, hbudget⟩

noncomputable def enlargedBudget (ell rho : Coord 2 n → K) (T : Dense K 1 n) : ℕ :=
  let A := rawEnlargedAnchors ell rho T
  repeatedBudget A.1.charpoly + repeatedBudget A.2.charpoly

theorem enlargedBudget_follow (T : Dense K 1 n) (g : Changes K (2 + 2) n) (ell rho : Coord 2 n → K) :
    enlargedBudget (moveLeftForm (l := 2) (r := 2) g ell)
      (moveRightForm (l := 2) (r := 2) g rho) (act g T) =
      enlargedBudget ell rho T := by
  have h := rawEnlargedAnchors_charpolys_transport g T ell rho
  exact congrArg (fun p => repeatedBudget p.1 + repeatedBudget p.2) h

/-- Run the exact order-four singular trial preparation on both tensors.
The output includes the transported form pair and the executable enlarged
anchors meet the budget used by the checked shape theorem. -/
theorem fourSingular_accepted_follow (F : FieldEncoding K) (T : Dense K 1 n)
    (g : Changes K (2 + 2) n) (hd : (flatten (l := 2) (r := 2) T).det = 0)
    (h : singularOrderFourAccepted T) :
    ∃ p : CutFormPair K 2 2 n,
      fourTrial rfl T p ∈ prepareTrials F T ∧
      fourTrial rfl (act g T)
        (moveLeftForm (l := 2) (r := 2) g p.1, moveRightForm (l := 2) (r := 2) g p.2) ∈
        prepareTrials F (act g T) ∧
      Fintype.card K ^ enlargedBudget p.1 p.2 T ≤ n ∧
      enlargedBudget (moveLeftForm (l := 2) (r := 2) g p.1)
        (moveRightForm (l := 2) (r := 2) g p.2) (act g T) =
        enlargedBudget p.1 p.2 T := by
  obtain ⟨p, hs, ht, hb⟩ := fourSingular_accepted_forms F T g hd h
  have hp := rawEnlargedAnchors_eq_measured_polys p.1 p.2 T
  have he := congrArg (fun p => repeatedBudget p.1 + repeatedBudget p.2) hp
  change enlargedBudget p.1 p.2 T = _ at he
  refine ⟨p, hs, ht, ?_, enlargedBudget_follow T g p.1 p.2⟩
  rw [he]
  exact hb

#print axioms fourSingular_accepted_forms
#print axioms enlargedBudget_follow
#print axioms fourSingular_accepted_follow

end EvenTI.TrialProducer
