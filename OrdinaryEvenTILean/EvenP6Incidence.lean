import EvenCellsBlocks
import Mathlib.Data.List.FinRange

namespace EvenTI.CellPreparation

open EvenOrdinaryTI.CellVariables

variable {K B : Type} [Field K] [Field B] [DecidableEq B] [Algebra K B]
variable {m : ℕ} {A : Fin m → Type} [∀ i, Field (A i)] [∀ i, Algebra K (A i)]

/-- Read the active block label using the given order of block idempotents. -/
def findActiveBlock (f : (∀ i, A i) →ₐ[K] B) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (f (Pi.single i 1) = 1)

theorem findActiveBlock_total (f : (∀ i, A i) →ₐ[K] B) :
    (findActiveBlock f).isSome = true := by
  obtain ⟨i, hi, _⟩ := exists_unique_active_coordinate f.toRingHom
  cases hf : findActiveBlock f with
  | some j => rfl
  | none =>
    exact False.elim (List.find?_eq_none.mp hf i (List.mem_finRange _) (by simpa using hi))

def activeBlock (f : (∀ i, A i) →ₐ[K] B) : Fin m :=
  (findActiveBlock f).get (findActiveBlock_total f)

theorem activeBlock_spec (f : (∀ i, A i) →ₐ[K] B) :
    f (Pi.single (activeBlock f) 1) = 1 := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (findActiveBlock_total f)
  rw [activeBlock, Option.get_of_eq_some _ hi]
  have hm := List.find?_some hi
  exact of_decide_eq_true hm

private theorem coordinate_mul (i : Fin m) (a b : A i) :
    Pi.single i (a * b) = Pi.single i a * Pi.single i b := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

private theorem coordinate_restrict (i : Fin m) (a : ∀ j, A j) :
    Pi.single i (a i) = Pi.single i 1 * a := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

/-- Evaluate the actual field embedding by inserting the value into the
selected primary coordinate and applying the cell map. -/
def activeFieldEmbedding (f : (∀ i, A i) →ₐ[K] B) : A (activeBlock f) →ₐ[K] B where
  toFun a := f (Pi.single (activeBlock f) a)
  map_zero' := by simp
  map_one' := activeBlock_spec f
  map_add' a b := by rw [Pi.single_add, map_add]
  map_mul' a b := by rw [coordinate_mul, map_mul]
  commutes' c := by
    change f (Pi.single (activeBlock f) ((algebraMap K (∀ i, A i) c) (activeBlock f))) = _
    rw [coordinate_restrict, map_mul, activeBlock_spec, one_mul, f.commutes]

theorem activeFieldEmbedding_spec (f : (∀ i, A i) →ₐ[K] B) (x : ∀ i, A i) :
    f x = activeFieldEmbedding f (x (activeBlock f)) := by
  change f x = f (Pi.single (activeBlock f) (x (activeBlock f)))
  rw [coordinate_restrict, map_mul, activeBlock_spec, one_mul]

#print axioms findActiveBlock_total
#print axioms activeFieldEmbedding_spec

end EvenTI.CellPreparation
