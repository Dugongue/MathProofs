import EvenP6EnlargedWords
import EvenP6AlignNumbered

namespace EvenTI.CellPreparation

open scoped Matrix
open Matrix EvenTI.Action EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.AnchorCovariance
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [DecidableEq K] {n a b k m a' b' k' m' : ℕ}
variable {ell rho : Coord 2 n → K}

/-- Keep the actual enlarged comparison and its two anchor conjugacies
under the same units. A separate existential for each anchor would not
suffice to reconstruct a candidate for the original comparison. -/
theorem enlarged_match_common_units
    (g : Changes K 4 n) (T : Tensor K 4 n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm (l := 2) (r := 2) g ell) a' k')
    (R' : NormalPair (moveRightForm (l := 2) (r := 2) g rho) b' m')
    (ha : a' = a) (hb : b' = b) (hk : k' = k) (hm : m' = m) :
    let e := enlargedIndexEquiv ha hk
    let f := enlargedIndexEquiv hb hm
    let ep := Equiv.prodCongr e f
    ∃ U : (Matrix (Index a k) (Index a k) K)ˣ,
      ∃ V : (Matrix (Index b m) (Index b m) K)ˣ,
        ((enlargedAnchorsFor L' R' (act g T)).1.submatrix e e =
          U.val * (enlargedAnchorsFor L R T).1 * U.inv) ∧
        ((enlargedAnchorsFor L' R' (act g T)).2.submatrix f f =
          V.val * (enlargedAnchorsFor L R T).2 * V.inv) ∧
        wordAction (conjugationWords U V) (enlargedGrid (rawEnlarged L R T)) =
          enlargedGrid ((rawEnlarged L' R' (act g T)).submatrix ep ep) := by
  subst a'
  subst b'
  subst k'
  subst m'
  obtain ⟨U, V, h⟩ := rawEnlarged_transport g T L R L' R'
  obtain ⟨hL, hR⟩ := quadratic_covariant _ U.val U.inv V.val V.inv U.inv_val V.inv_val
  refine ⟨U, V, ?_, ?_, ?_⟩
  · simpa only [enlargedIndexEquiv, Equiv.coe_refl, Matrix.submatrix_id_id,
      enlargedAnchorsFor_eq, h] using hL
  · simpa only [enlargedIndexEquiv, Equiv.coe_refl, Matrix.submatrix_id_id,
      enlargedAnchorsFor_eq, h] using hR
  · rw [enlargedGrid_conjugation, h]
    rfl

theorem raw_enlarged_match_common_units
    (g : Changes K 4 n) (T : Tensor K 4 n) (ell rho : Coord 2 n → K) :
    let hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) ell
    let hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) rho
    let e := enlargedIndexEquiv hL (congrArg (fun d => n - d) hL)
    let f := enlargedIndexEquiv hR (congrArg (fun d => n - d) hR)
    let L' := moveLeftForm (l := 2) (r := 2) g ell
    let R' := moveRightForm (l := 2) (r := 2) g rho
    ∃ U : (Matrix (RawEnlargedIndex ell) (RawEnlargedIndex ell) K)ˣ,
      ∃ V : (Matrix (RawEnlargedIndex rho) (RawEnlargedIndex rho) K)ˣ,
        ((rawEnlargedAnchors L' R' (act g T)).1.submatrix e e =
          U.val * (rawEnlargedAnchors ell rho T).1 * U.inv) ∧
        ((rawEnlargedAnchors L' R' (act g T)).2.submatrix f f =
          V.val * (rawEnlargedAnchors ell rho T).2 * V.inv) ∧
        wordAction (conjugationWords U V) (rawEnlargedWords ell rho T) =
          enlargedGrid
            ((rawEnlarged (rawNormalFrame L') (rawNormalFrame R') (act g T)).submatrix
              (Equiv.prodCongr e f) (Equiv.prodCongr e f)) := by
  let hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) ell
  let hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) rho
  rw [rawEnlargedWords_eq]
  exact enlarged_match_common_units g T (rawNormalFrame ell) (rawNormalFrame rho)
    (rawNormalFrame (moveLeftForm (l := 2) (r := 2) g ell)) (rawNormalFrame (moveRightForm (l := 2) (r := 2) g rho))
    hL hR (congrArg (fun d => n - d) hL) (congrArg (fun d => n - d) hR)

#print axioms enlarged_match_common_units
#print axioms raw_enlarged_match_common_units

end EvenTI.CellPreparation
