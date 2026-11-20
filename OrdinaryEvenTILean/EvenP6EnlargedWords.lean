import EvenP6Reframe
import EvenP5EnlargedExecution

namespace EvenTI.CellPreparation

open scoped BigOperators Matrix
open Matrix EvenTI.TrialProducer EvenTI.Action
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K A B : Type} [Field K] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

abbrev FourSite := Bool × Bool

abbrev fourWidth (A B : Type) (i : FourSite) : Type :=
  match i.1 with
  | false => A
  | true => B

instance (i : FourSite) : Fintype (fourWidth A B i) := by
  rcases i with ⟨a,b⟩
  cases a <;> infer_instance

instance (i : FourSite) : DecidableEq (fourWidth A B i) := by
  rcases i with ⟨a,b⟩
  cases a <;> infer_instance

/-- Identify the two conjugated endomorphism factors with four physical
coordinate factors, each primal factor followed by its dual. -/
def enlargedGridOrder : ((i : FourSite) → fourWidth A B i) ≃ (A × B) × (A × B) where
  toFun p := ((p (false,false), p (true,false)), (p (false,true), p (true,true)))
  invFun p
    | (false, false) => p.1.1
    | (true, false) => p.1.2
    | (false, true) => p.2.1
    | (true, true) => p.2.2
  left_inv p := by
    funext i
    rcases i with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  right_inv _ := rfl

def enlargedGrid (Z : Matrix (A × B) (A × B) K) : Grid K (fourWidth A B) :=
  fun p => Z (enlargedGridOrder p).1 (enlargedGridOrder p).2

def conjugationWords (P : (Matrix A A K)ˣ) (Q : (Matrix B B K)ˣ) :
    ModeMatrices K (fourWidth A B)
  | (false,false) => P.val
  | (false,true) => P.invᵀ
  | (true,false) => Q.val
  | (true,true) => Q.invᵀ

theorem enlargedGrid_conjugation (P : (Matrix A A K)ˣ) (Q : (Matrix B B K)ˣ)
    (Z : Matrix (A × B) (A × B) K) :
    wordAction (conjugationWords P Q) (enlargedGrid Z) =
      enlargedGrid (Matrix.kronecker P.val Q.val * Z * Matrix.kronecker P.inv Q.inv) := by
  funext p
  unfold wordAction enlargedGrid
  rw [← (enlargedGridOrder (A := A) (B := B)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [enlargedGridOrder, conjugationWords, Fintype.prod_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply]
  ring

section Raw

variable [DecidableEq K] {n : ℕ}

/-- Compute the actual enlarged tensor words by the same finite coordinate
projection that supplied the Part 5 singular anchors. -/
def rawEnlargedWords (ell rho : Coord 2 n → K) (T : Tensor K 4 n) :
    Grid K (fourWidth (RawEnlargedIndex ell) (RawEnlargedIndex rho)) :=
  enlargedGrid (coordinateProjection
    (enlargedProjection ell (rawNormalFrame ell))
    (enlargedProjection rho (rawNormalFrame rho)) (flatten (l := 2) (r := 2) T))

theorem rawEnlargedWords_eq (ell rho : Coord 2 n → K) (T : Tensor K 4 n) :
    rawEnlargedWords ell rho T =
      enlargedGrid (rawEnlarged (rawNormalFrame ell) (rawNormalFrame rho) T) := by
  unfold rawEnlargedWords
  rw [coordinateProjection_eq]
  rfl

end Raw

#print axioms enlargedGrid_conjugation
#print axioms rawEnlargedWords_eq

end EvenTI.CellPreparation
