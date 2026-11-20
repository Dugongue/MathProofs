import EvenP6TensorWords
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace EvenTI.CellPreparation

open scoped BigOperators
open Matrix

variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]
  {N : I → Type} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]

abbrev Grid (K : Type) (N : I → Type) := ((i : I) → N i) → K
abbrev ModeMatrices (K : Type) (N : I → Type) := ∀ i, Matrix (N i) (N i) K
abbrev ModeUnits (K : Type) [Field K] (N : I → Type)
    [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)] := ∀ i, (Matrix (N i) (N i) K)ˣ

def gridMatrix (M : ModeMatrices K N) : Matrix ((i : I) → N i) ((i : I) → N i) K :=
  fun p q => ∏ i, M i (p i) (q i)

theorem gridMatrix_mul (A B : ModeMatrices K N) :
    gridMatrix (fun i => A i * B i) = gridMatrix A * gridMatrix B := by
  ext p q
  simp only [gridMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem gridMatrix_one : gridMatrix (fun i => (1 : Matrix (N i) (N i) K)) = 1 := by
  ext p q
  simp only [gridMatrix, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem wordAction_mul (A B : ModeMatrices K N) (T : Grid K N) :
    wordAction A (wordAction B T) = wordAction (fun i => A i * B i) T := by
  change (gridMatrix A).mulVec ((gridMatrix B).mulVec T) =
    (gridMatrix (fun i => A i * B i)).mulVec T
  rw [Matrix.mulVec_mulVec, gridMatrix_mul]

theorem wordAction_one (T : Grid K N) :
    wordAction (fun i => (1 : Matrix (N i) (N i) K)) T = T := by
  change (gridMatrix (fun i => (1 : Matrix (N i) (N i) K))).mulVec T = T
  rw [gridMatrix_one, Matrix.one_mulVec]

/-- Change into the verified source frame and apply the selected repeated
intertwiners. The remaining multiplication operators act on these words. -/
def branchSourceWords (U R : ModeUnits K N) (T : Grid K N) : Grid K N :=
  wordAction (fun i => (R i).val * (U i).inv) T

def branchTargetWords (V : ModeUnits K N) (S : Grid K N) : Grid K N :=
  wordAction (fun i => (V i).inv) S

theorem branchWords_equation_iff (U V R : ModeUnits K N) (M : ModeMatrices K N)
    (T S : Grid K N) :
    wordAction M (branchSourceWords U R T) = branchTargetWords V S ↔
      wordAction (fun i => (V i).val * M i * (R i).val * (U i).inv) T = S := by
  have h₁ : ∀ A B : Grid K N,
      wordAction (fun i => (V i).val) A = wordAction (fun i => (V i).val) B ↔ A = B := by
    intro A B
    constructor
    · intro he
      have hh := congrArg (wordAction (fun i => (V i).inv)) he
      simpa only [wordAction_mul, Units.inv_val, wordAction_one] using hh
    · exact congrArg _
  rw [← h₁]
  unfold branchSourceWords branchTargetWords
  simp only [wordAction_mul, Units.val_inv, wordAction_one, Matrix.mul_assoc]

#print axioms wordAction_mul
#print axioms branchWords_equation_iff

end EvenTI.CellPreparation
