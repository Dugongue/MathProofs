import EvenP5Diagonal
import EvenP3SingularNormalPair
import Mathlib.Data.Fintype.Sort

namespace EvenTI.TrialProducer

open Matrix Matrix.TransvectionStruct EvenTI.Action
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [DecidableEq K] {n : ℕ}

/-- Compose the actual transvections together with their computable inverses. -/
def elementaryUnit (p : List (TransvectionStruct (Fin n) K)) :
    (Matrix (Fin n) (Fin n) K)ˣ where
  val := (p.map toMatrix).prod
  inv := (p.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
  val_inv := prod_mul_reverse_inv_prod p
  inv_val := reverse_inv_prod_mul_prod p

private def normalizeScale (d : Fin n → K) (i : Fin n) : K :=
  if d i = 0 then 1 else (d i)⁻¹

private def scaleUnit (d : Fin n → K) : (Matrix (Fin n) (Fin n) K)ˣ where
  val := diagonal (normalizeScale d)
  inv := diagonal (fun i => if d i = 0 then 1 else d i)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : d i = 0 <;> simp [normalizeScale, h]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : d i = 0 <;> simp [normalizeScale, h]

def liveSet (d : Fin n → K) : Finset (Fin n) :=
  Finset.univ.filter (fun i => d i ≠ 0)

private theorem normalRank {M : Matrix (Fin n) (Fin n) K} {p : Elementary K (Fin n)}
    {D : Fin n → K} (h : applyElementary p M = diagonal D) :
    (liveSet D).card = M.rank := by
  let L := elementaryUnit p.1
  let R := elementaryUnit p.2
  have hdL := (Matrix.isUnit_iff_isUnit_det L.val).mp L.isUnit
  have hdR := (Matrix.isUnit_iff_isUnit_det R.val).mp R.isUnit
  change L.val * M * R.val = diagonal D at h
  rw [← rank_mul_eq_right_of_isUnit_det L.val M hdL,
    ← rank_mul_eq_left_of_isUnit_det R.val (L.val * M) hdR, h, rank_diagonal]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [liveSet]))

private theorem diagonalize_output (M : Matrix (Fin n) (Fin n) K) :
    applyElementary (diagonalize M) M =
      diagonal (applyElementary (diagonalize M) M).diag := by
  let X := applyElementary (diagonalize M) M
  have h : ∃ D, X = diagonal D := diagonalize_spec M
  obtain ⟨D, hD⟩ := h
  change X = diagonal X.diag
  rw [hD, diag_diagonal]

def rawFrameWidth (ell : Coord 2 n → K) : ℕ :=
  let M := asMatrix n ell
  (liveSet (applyElementary (diagonalize M) M).diag).card

theorem rawFrameWidth_eq (ell : Coord 2 n → K) :
    rawFrameWidth ell = (asMatrix n ell).rank :=
  normalRank (diagonalize_output (asMatrix n ell))

/-- An actual canonical coordinate choice from transvections and sorted
nonzero diagonal positions, with no search over physical basis changes. -/
def rawNormalFrame (ell : Coord 2 n → K) :
    NormalPair ell (rawFrameWidth ell) (n - rawFrameWidth ell) := by
  let M := asMatrix n ell
  let p := diagonalize M
  let d := (applyElementary p M).diag
  have h : applyElementary p M = diagonal d := diagonalize_output M
  let s := liveSet d
  have hs : s.card = rawFrameWidth ell := rfl
  have hc : sᶜ.card = n - rawFrameWidth ell := by
    rw [Finset.card_compl, Fintype.card_fin, hs]
  let e : Fin (rawFrameWidth ell) ⊕ Fin (n - rawFrameWidth ell) ≃ Fin n :=
    finSumEquivOfFinset hs hc
  let L := elementaryUnit p.1
  let R := elementaryUnit p.2
  refine ⟨scaleUnit d * L, R, e.symm, ?_⟩
  have h' : L.val * M * R.val = diagonal d := h
  change ((diagonal (normalizeScale d) * L.val) * M * R.val).submatrix e e = _
  have hscaled :
      (diagonal (normalizeScale d) * L.val) * M * R.val =
        diagonal (normalizeScale d) * diagonal d := by
    rw [← h']
    simp only [Matrix.mul_assoc]
  rw [hscaled, diagonal_mul_diagonal, Matrix.submatrix_diagonal_equiv]
  rw [normalPair, ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal]
  congr 1
  funext i
  cases i with
  | inl i =>
    have hi : e (Sum.inl i) ∈ s := (s.orderIsoOfFin hs i).property
    have hd : d (e (Sum.inl i)) ≠ 0 := by simpa [s, liveSet] using hi
    simp [normalizeScale, hd]
  | inr i =>
    have hi : e (Sum.inr i) ∈ sᶜ := (sᶜ.orderIsoOfFin hc i).property
    have hd : d (e (Sum.inr i)) = 0 := by simpa [s, liveSet] using hi
    simp [normalizeScale, hd]

#print axioms rawNormalFrame
#print axioms rawFrameWidth_eq

end EvenTI.TrialProducer
