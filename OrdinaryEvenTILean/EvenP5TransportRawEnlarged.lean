import EvenP5TransportFrames
import EvenP5EnlargedExecution
import EvenP3SingularPack

namespace EvenTI.TrialProducer

open scoped Matrix
open Matrix EvenTI.Action EvenTI.AnchorCovariance
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [DecidableEq K] {n : ℕ}

theorem rawFrameWidth_move (g : Changes K 2 n) (ell : Coord 2 n → K) :
    rawFrameWidth (moveCutForm (productUnit g) ell) = rawFrameWidth ell := by
  rw [rawFrameWidth_eq, rawFrameWidth_eq, asMatrix_rank_eq_retainedForm,
    asMatrix_rank_eq_retainedForm, retainedForm_rank_move]

/-- Conjugate actual enlarged anchors using the same expanded index types. -/
theorem enlargedAnchorsFor_transport
    {a b k m : ℕ} {ell rho : Coord 2 n → K}
    (g : Changes K (2 + 2) n) (A : Tensor K 4 n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm (l := 2) (r := 2) g ell) a k) (R' : NormalPair (moveRightForm (l := 2) (r := 2) g rho) b m) :
    ∃ U : (Matrix (Index a k) (Index a k) K)ˣ,
      ∃ V : (Matrix (Index b m) (Index b m) K)ˣ,
        enlargedAnchorsFor L' R' (act g A) =
          (U.val * (enlargedAnchorsFor L R A).1 * U.inv,
           V.val * (enlargedAnchorsFor L R A).2 * V.inv) := by
  obtain ⟨U, V, h⟩ := rawEnlarged_transport g A L R L' R'
  refine ⟨U, V, ?_⟩
  rw [enlargedAnchorsFor_eq, enlargedAnchorsFor_eq, h]
  obtain ⟨hL, hR⟩ := quadratic_covariant _ U.val U.inv V.val V.inv U.inv_val V.inv_val
  exact Prod.ext hL hR

/-- Identify the computed index types after checking equality of rank and
radical dimension. -/
def enlargedIndexEquiv {a k a' k' : ℕ} (h₁ : a' = a) (h₂ : k' = k) : Index a k ≃ Index a' k' := by
  subst a'
  subst k'
  exact Equiv.refl _

private theorem enlargedAnchorsFor_transport_dims
    {a b k m a' b' k' m' : ℕ} {ell rho : Coord 2 n → K}
    (g : Changes K (2 + 2) n) (A : Tensor K 4 n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm (l := 2) (r := 2) g ell) a' k') (R' : NormalPair (moveRightForm (l := 2) (r := 2) g rho) b' m')
    (ha : a' = a) (hb : b' = b) (hk : k' = k) (hm : m' = m) :
    let e := enlargedIndexEquiv ha hk
    let f := enlargedIndexEquiv hb hm
    ∃ U : (Matrix (Index a k) (Index a k) K)ˣ,
      ∃ V : (Matrix (Index b m) (Index b m) K)ˣ,
        ((enlargedAnchorsFor L' R' (act g A)).1.submatrix e e,
         (enlargedAnchorsFor L' R' (act g A)).2.submatrix f f) =
          (U.val * (enlargedAnchorsFor L R A).1 * U.inv,
           V.val * (enlargedAnchorsFor L R A).2 * V.inv) := by
  subst a'
  subst b'
  subst k'
  subst m'
  simpa only [enlargedIndexEquiv, Equiv.coe_refl, Matrix.submatrix_id_id] using
    enlargedAnchorsFor_transport g A L R L' R'

/-- The computed order-four enlarged anchors are conjugate after identifying
their equal index dimensions. -/
theorem rawEnlargedAnchors_transport
    (g : Changes K (2 + 2) n) (A : Tensor K 4 n) (ell rho : Coord 2 n → K) :
    let hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) ell
    let hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) rho
    let e := enlargedIndexEquiv hL (congrArg (fun d => n - d) hL)
    let f := enlargedIndexEquiv hR (congrArg (fun d => n - d) hR)
    ∃ U : (Matrix (RawEnlargedIndex ell) (RawEnlargedIndex ell) K)ˣ,
      ∃ V : (Matrix (RawEnlargedIndex rho) (RawEnlargedIndex rho) K)ˣ,
        ((rawEnlargedAnchors (moveLeftForm (l := 2) (r := 2) g ell) (moveRightForm (l := 2) (r := 2) g rho) (act g A)).1.submatrix e e,
         (rawEnlargedAnchors (moveLeftForm (l := 2) (r := 2) g ell) (moveRightForm (l := 2) (r := 2) g rho) (act g A)).2.submatrix f f) =
          (U.val * (rawEnlargedAnchors ell rho A).1 * U.inv,
           V.val * (rawEnlargedAnchors ell rho A).2 * V.inv) := by
  have hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) ell
  have hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) rho
  exact enlargedAnchorsFor_transport_dims g A (rawNormalFrame ell) (rawNormalFrame rho)
    (rawNormalFrame (moveLeftForm (l := 2) (r := 2) g ell)) (rawNormalFrame (moveRightForm (l := 2) (r := 2) g rho))
    hL hR (congrArg (fun d => n - d) hL) (congrArg (fun d => n - d) hR)

private theorem rawEnlarged_charpoly_dimensions
    {a b k m a' b' k' m' : ℕ} {ell rho : Coord 2 n → K}
    (g : Changes K (2 + 2) n) (A : Tensor K 4 n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm (l := 2) (r := 2) g ell) a' k') (R' : NormalPair (moveRightForm (l := 2) (r := 2) g rho) b' m')
    (ha : a' = a) (hb : b' = b) (hk : k' = k) (hm : m' = m) :
    (partialTraceLeft (rawEnlarged L' R' (act g A) ^ 2)).charpoly =
        (partialTraceLeft (rawEnlarged L R A ^ 2)).charpoly ∧
      (partialTraceRight (rawEnlarged L' R' (act g A) ^ 2)).charpoly =
        (partialTraceRight (rawEnlarged L R A ^ 2)).charpoly := by
  subst a'
  subst b'
  subst k'
  subst m'
  exact rawEnlarged_charpolys_transport g A L R L' R'

/-- The actual order-four singular anchor computation preserves the pair
of characteristic polynomials under exact transport of the kernel forms. -/
theorem rawEnlargedAnchors_charpolys_transport
    (g : Changes K (2 + 2) n) (A : Tensor K 4 n) (ell rho : Coord 2 n → K) :
    Prod.map Matrix.charpoly Matrix.charpoly
        (rawEnlargedAnchors (moveLeftForm (l := 2) (r := 2) g ell) (moveRightForm (l := 2) (r := 2) g rho) (act g A)) =
      Prod.map Matrix.charpoly Matrix.charpoly (rawEnlargedAnchors ell rho A) := by
  have hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) ell
  have hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) rho
  obtain ⟨ha, hb⟩ := rawEnlarged_charpoly_dimensions g A
    (rawNormalFrame ell) (rawNormalFrame rho)
    (rawNormalFrame (moveLeftForm (l := 2) (r := 2) g ell)) (rawNormalFrame (moveRightForm (l := 2) (r := 2) g rho))
    hL hR (congrArg (fun d => n - d) hL) (congrArg (fun d => n - d) hR)
  rw [rawEnlargedAnchors_eq, rawEnlargedAnchors_eq]
  exact Prod.ext ha hb

private theorem frame_choice_dims
    {a b k m a' b' k' m' : ℕ} {ell rho : Coord 2 n → K}
    (A : Tensor K 4 n) (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair ell a' k') (R' : NormalPair rho b' m')
    (ha : a' = a) (hb : b' = b) (hk : k' = k) (hm : m' = m) :
    (partialTraceLeft (rawEnlarged L' R' A ^ 2)).charpoly =
        (partialTraceLeft (rawEnlarged L R A ^ 2)).charpoly ∧
      (partialTraceRight (rawEnlarged L' R' A ^ 2)).charpoly =
        (partialTraceRight (rawEnlarged L R A ^ 2)).charpoly := by
  subst a'
  subst b'
  subst k'
  subst m'
  exact rawEnlarged_charpolys_frame_choice A L L' R R'

/-- The actual normal-frame generator reproduces both characteristic
polynomials of the order-four coverage theorem. -/
theorem rawEnlargedAnchors_eq_measured_polys [Fintype K]
    (ell rho : Coord 2 n → K) (A : Tensor K 4 n) :
    Prod.map Matrix.charpoly Matrix.charpoly (rawEnlargedAnchors ell rho A) =
      (rawEnlargedLeftPoly ell rho A, rawEnlargedRightPoly ell rho A) := by
  have hL : rawFrameWidth ell = formWidth ell := by
    rw [rawFrameWidth_eq, asMatrix_rank_eq_retainedForm]
  have hR : rawFrameWidth rho = formWidth rho := by
    rw [rawFrameWidth_eq, asMatrix_rank_eq_retainedForm]
  have hkL : n - rawFrameWidth ell = Mathproof.EvenTI.OrderFour.formDefect ell :=
    congrArg (fun d => n - d) hL
  have hkR : n - rawFrameWidth rho = Mathproof.EvenTI.OrderFour.formDefect rho :=
    congrArg (fun d => n - d) hR
  obtain ⟨ha, hb⟩ := frame_choice_dims A (chosenNormal ell) (chosenNormal rho)
    (rawNormalFrame ell) (rawNormalFrame rho) hL hR hkL hkR
  rw [rawEnlargedAnchors_eq]
  exact Prod.ext ha hb

#print axioms rawFrameWidth_move
#print axioms enlargedAnchorsFor_transport
#print axioms rawEnlargedAnchors_transport
#print axioms rawEnlargedAnchors_charpolys_transport
#print axioms rawEnlargedAnchors_eq_measured_polys

end EvenTI.TrialProducer
