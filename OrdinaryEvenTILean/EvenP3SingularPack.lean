import EvenP3SingularActual
import EvenP3Padding
import EvenP3FormMoment
import EvenP2FormsFiber

namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped BigOperators TensorProduct Matrix Polynomial
open Matrix Module Polynomial EvenTI.Action EvenTI.AnchorCovariance EvenTI.Primary
open Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget
open Mathproof.EvenOrdinaryTISingular.RectPolar
open Mathproof.EvenTI.OrderFour Mathproof.EvenTI.Singular.Forms
noncomputable section

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
variable {ell rho : Coord 2 n → K}

abbrev formWidth (ell : Coord 2 n → K) := (retainedForm (0 : Fin 2) ell).rank

def chosenNormal (ell : Coord 2 n → K) :
    NormalPair ell (formWidth ell) (formDefect ell) :=
  Classical.choice (by simpa only [asMatrix_rank_eq_retainedForm, formDefect] using normalPair_nonempty ell)

def rawEnlargedLeftPoly (ell rho : Coord 2 n → K) (A : Tensor K 4 n) : K[X] :=
  (partialTraceLeft (rawEnlarged (chosenNormal ell) (chosenNormal rho) A ^ 2)).charpoly

def rawEnlargedRightPoly (ell rho : Coord 2 n → K) (A : Tensor K 4 n) : K[X] :=
  (partialTraceRight (rawEnlarged (chosenNormal ell) (chosenNormal rho) A ^ 2)).charpoly

def rawLiveLeftPoly (ell rho : Coord 2 n → K) (A : Tensor K 4 n) : K[X] :=
  (partialTraceLeft (liveMatrix (chosenNormal ell) (chosenNormal rho)
    (matrixTensorEquiv K _ _ (flatten (l := 2) (r := 2) A)) ^ 2)).charpoly

def rawLiveRightPoly (ell rho : Coord 2 n → K) (A : Tensor K 4 n) : K[X] :=
  (partialTraceRight (liveMatrix (chosenNormal ell) (chosenNormal rho)
    (matrixTensorEquiv K _ _ (flatten (l := 2) (r := 2) A)) ^ 2)).charpoly

theorem rawEnlarged_polys_eq_padded (ell rho : Coord 2 n → K) (A : Tensor K 4 n) :
    rawEnlargedLeftPoly ell rho A = rawLiveLeftPoly ell rho A * X^(2*formDefect ell) ∧
    rawEnlargedRightPoly ell rho A = rawLiveRightPoly ell rho A * X^(2*formDefect rho) := by
  let L := chosenNormal ell
  let R := chosenNormal rho
  let U := matrixTensorEquiv K (Coord 2 n) (Coord 2 n) (flatten (l:=2) (r:=2) A)
  have h := quadratic_charpoly_padding (enlargedMatrix L R U) (enlargedMatrix_supported L R U)
  rw [enlargedMatrix_crop] at h
  exact ⟨h.1.trans (mul_comm _ _),h.2.trans (mul_comm _ _)⟩

private instance {T S : Submodule K (Coord 2 n → K)} :
    Fintype (DenseKernelFiber T S) := Fintype.ofFinite _

/-- The unpadded live covariants have bounded characteristic-polynomial
budgets on a specified exact fiber of the raw square cut. -/
theorem raw_live_fiber_primary_means
    {T S : Submodule K (Coord 2 n → K)} (A₀ : DenseKernelFiber T S)
    (he : ell ∈ S) (hr : rho ∈ T) (hn : 1024 ≤ n)
    (hc : Fintype.card K ^ finrank K T ≤ n)
    (hw : n ≤ 3 * min (formWidth ell) (formWidth rho)) :
    mean (fun A : DenseKernelFiber T S => (repeatedBudget (rawLiveLeftPoly ell rho A.val) : ℝ)) ≤
        4 * (budgetConstant K + 1) ∧
    mean (fun A : DenseKernelFiber T S => (repeatedBudget (rawLiveRightPoly ell rho A.val) : ℝ)) ≤
        4 * (budgetConstant K + 1) := by
  let L := chosenNormal ell
  let R := chosenNormal rho
  let pL := liveProjection ell L
  let pR := liveProjection rho R
  have hS := cropImage_trace_codim S ell he pL
    (liveProjection_surjective ell L) (liveProjection_trace ell L)
  have hT := cropImage_trace_codim T rho hr pR
    (liveProjection_surjective rho R) (liveProjection_trace rho R)
  let J := liveJoint pL pR hS.1 hT.1
  have hu : formWidth ell ≤ n := by
    rw [formWidth, ← asMatrix_rank_eq_retainedForm]
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_height (asMatrix n ell)
  have hv : formWidth rho ≤ n := by
    rw [formWidth, ← asMatrix_rank_eq_retainedForm]
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_height (asMatrix n rho)
  have hmean := live_primary_means_le pL pR hS.1 hT.1 A₀ _ hn hu hv hw hc
    (hS.2.trans_eq (fiber_coranks_eq A₀).symm) hT.2
  have hL' (A : DenseKernelFiber T S) :
      rawLiveLeftPoly ell rho A.val = (leftCoordinate (J A)).charpoly := by
    exact congrArg Matrix.charpoly (congrArg Prod.fst (liveMatrix_eq_liveJoint L R S T hS.1 hT.1 A))
  have hR' (A : DenseKernelFiber T S) :
      rawLiveRightPoly ell rho A.val = (rightCoordinate (J A)).charpoly := by
    exact congrArg Matrix.charpoly (congrArg Prod.snd (liveMatrix_eq_liveJoint L R S T hS.1 hT.1 A))
  rw [show (fun A : DenseKernelFiber T S => (repeatedBudget (rawLiveLeftPoly ell rho A.val) : ℝ)) =
      (fun A => (repeatedBudget (leftCoordinate (J A)).charpoly : ℝ)) from funext (fun A => by rw [hL']),
    show (fun A : DenseKernelFiber T S => (repeatedBudget (rawLiveRightPoly ell rho A.val) : ℝ)) =
      (fun A => (repeatedBudget (rightCoordinate (J A)).charpoly : ℝ)) from funext (fun A => by rw [hR'])]
  exact hmean

/-- Fixed-fiber control on the two enlarged anchors from any chosen raw
kernel forms of sufficient rank, without any supplied normalization. -/
theorem raw_enlarged_fiber_primary_means
    {T S : Submodule K (Coord 2 n → K)} (A₀ : DenseKernelFiber T S)
    (he : ell ∈ S) (hr : rho ∈ T) (hn : 1024 ≤ n)
    (hc : Fintype.card K ^ finrank K T ≤ n)
    (hw : n ≤ 3 * min (formWidth ell) (formWidth rho)) :
    mean (fun A : DenseKernelFiber T S =>
      (repeatedBudget (rawEnlargedLeftPoly ell rho A.val) : ℝ)) ≤
        8 * (budgetConstant K + 1) + 2 + 8 * ((formDefect ell)^2 : ℕ) ∧
    mean (fun A : DenseKernelFiber T S =>
      (repeatedBudget (rawEnlargedRightPoly ell rho A.val) : ℝ)) ≤
        8 * (budgetConstant K + 1) + 2 + 8 * ((formDefect rho)^2 : ℕ) := by
  have hmean := raw_live_fiber_primary_means A₀ he hr hn hc hw
  letI : Nonempty (DenseKernelFiber T S) := ⟨A₀⟩
  have hcard : (Fintype.card (DenseKernelFiber T S) : ℝ) ≠ 0 := by positivity
  have step (F G : DenseKernelFiber T S → K[X]) (k : ℕ)
      (hs : ∀ A, G A = F A * X^(2*k)) (hF : ∀ A, F A ≠ 0)
      (h : mean (fun A => (repeatedBudget (F A) : ℝ)) ≤ 4*(budgetConstant K+1)) :
      mean (fun A => (repeatedBudget (G A) : ℝ)) ≤
        8 * (budgetConstant K+1) + 2 + 8 * (k^2 : ℕ) := by
    have hpoint (A : DenseKernelFiber T S) :
        (repeatedBudget (G A) : ℝ) ≤ 2*(repeatedBudget (F A) : ℝ) + (2 + 8*(k^2 : ℕ)) := by
      rw [hs]
      exact_mod_cast repeatedBudget_zero_padding (hF A) k
    have hmono := mean_mono hpoint
    have hcomp : mean (fun A : DenseKernelFiber T S =>
        2*(repeatedBudget (F A) : ℝ) + (2 + 8*(k^2 : ℕ))) =
        2 * mean (fun A => (repeatedBudget (F A) : ℝ)) + (2 + 8*(k^2 : ℕ)) := by
      simp [mean, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc, hcard]
    rw [hcomp] at hmono
    exact hmono.trans (by linarith only [h])
  exact ⟨step _ _ _ (fun A => (rawEnlarged_polys_eq_padded ell rho A.val).1)
      (fun A => (Matrix.charpoly_monic _).ne_zero) hmean.1,
    step _ _ _ (fun A => (rawEnlarged_polys_eq_padded ell rho A.val).2)
      (fun A => (Matrix.charpoly_monic _).ne_zero) hmean.2⟩

end
end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.rawEnlarged_polys_eq_padded
#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.raw_live_fiber_primary_means
#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.raw_enlarged_fiber_primary_means





