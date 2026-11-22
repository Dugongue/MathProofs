import EvenP17ScalarActiveWords
import EvenP17ScalarActiveLoop

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace EvenTI.P17Scalar

open EvenTI.Part8 Matrix

variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The whole predicate computed by the paid ordered-slot loop is exactly
raw cropped scalarity when the installed list covers precisely the active
chart rows. Repeated slots and multiple rows with the same site are allowed. -/
theorem activeResidueWords_iff_scalarCrop
    (P : Matrix I J K) (Q : Matrix J I K) (N : Matrix I I K)
    (U : (Matrix I I K)ˣ) (L : BaseUnitLog K) {c : ℕ}
    (slot : I → Fin c) (x : Fin c → ZMod (Fintype.card K-1))
    (reference : I) (hRef : ∃ j, (U.inv*P) reference j ≠ 0)
    (hLeft : Q*P=1)
    (hConj : N=U.val*Matrix.diagonal (fun i => (L.decode (x (slot i)) : K))*U.inv)
    (hInvariant : N*P=P*(Q*N*P))
    (coords slots : List ℕ)
    (hRead : ∀ i : Fin c, coords.getD i.val 0=(x i).val)
    (hSound : ∀ a ∈ slots, ∃ i, (∃ j, (U.inv*P) i j ≠ 0) ∧ a=(slot i).val)
    (hFull : ∀ i, (∃ j, (U.inv*P) i j ≠ 0) → (slot i).val ∈ slots) :
    (∀ j < slots.length, coords.getD (slots.getD j 0) 0 =
      coords.getD (slot reference).val 0) ↔
      ∃ a : K, Q*N*P=a • (1 : Matrix J J K) := by
  have he :
      (∀ j < slots.length, coords.getD (slots.getD j 0) 0 =
        coords.getD (slot reference).val 0) ↔
      ∀ i, (∃ j, (U.inv*P) i j ≠ 0) →
        (x (slot i)).val=(x (slot reference)).val := by
    constructor
    · intro h i hi
      obtain ⟨j,hj,hEq⟩ := List.mem_iff_getElem.mp (hFull i hi)
      have hh := h j hj
      rw [List.getD_eq_getElem _ _ hj,hEq,hRead,hRead] at hh
      exact hh
    · intro h j hj
      obtain ⟨i,hi,hEq⟩ := hSound slots[j] (List.getElem_mem hj)
      rw [List.getD_eq_getElem _ _ hj,hEq,hRead,hRead]
      exact h i hi
  exact he.trans (scalarCrop_iff_activeExponentWords P Q N U L slot x
    reference hRef hLeft hConj hInvariant).symm

#print axioms activeResidueWords_iff_scalarCrop
end EvenTI.P17Scalar
