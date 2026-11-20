import EvenP6Reframe
import EvenPhysicalAction

namespace EvenTI.CellPreparation

set_option maxHeartbeats 700000

open scoped BigOperators
open Matrix EvenTI.Action

variable {K I J : Type} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : I → Type} {D : J → Type}
  [∀ i, Fintype (N i)] [∀ j, Fintype (D j)]

def reindexWords (e : I ≃ J) (w : ∀ i, N i ≃ D (e i)) (T : Grid K D) : Grid K N :=
  T ∘ e.piCongr w

def reindexModes (e : I ≃ J) (w : ∀ i, N i ≃ D (e i)) (M : ModeMatrices K D) :
    ModeMatrices K N :=
  fun i => (M (e i)).submatrix (w i) (w i)

theorem reindexWords_action (e : I ≃ J) (w : ∀ i, N i ≃ D (e i))
    (M : ModeMatrices K D) (T : Grid K D) :
    wordAction (reindexModes e w M) (reindexWords e w T) =
      reindexWords e w (wordAction M T) := by
  funext p
  unfold wordAction reindexWords reindexModes
  simp only [Function.comp_apply, Matrix.submatrix_apply]
  apply Fintype.sum_equiv (e.piCongr w)
  intro q
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply]
theorem reindexWords_injective (e : I ≃ J) (w : ∀ i, N i ≃ D (e i)) :
    Function.Injective (reindexWords (K := K) e w) :=
  fun _ _ h => funext fun p => by
    obtain ⟨q, rfl⟩ := (e.piCongr w).surjective p
    exact congrFun h q

/-- The numbered comparison acts on the original dense coefficients. -/
theorem reindexWords_act {a n : ℕ} (e : I ≃ Fin a)
    (w : ∀ i, N i ≃ Fin n) (g : Changes K a n) (T : Tensor K a n) :
    wordAction (reindexModes e w (fun i => (g i).val)) (reindexWords e w T) =
      reindexWords e w (act g T) :=
  reindexWords_action e w (fun i => (g i).val) T

#print axioms reindexWords_action
#print axioms reindexWords_injective
#print axioms reindexWords_act

end EvenTI.CellPreparation
