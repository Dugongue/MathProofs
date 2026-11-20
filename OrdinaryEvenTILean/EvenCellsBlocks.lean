import EvenCells
import Mathlib.Algebra.Group.Pi.Units

/-! Algebraic reduction of a split mode algebra to shared variables across all cells. -/

open scoped BigOperators TensorProduct

namespace EvenOrdinaryTI.CellVariables

variable {L B : Type*} [Fintype L] [DecidableEq L] [Field B]
    {C : L → Type*} [∀ i, Field (C i)]

/-- A field-valued map on product coordinates selects a single coordinate.
The remaining map is a field embedding. -/
theorem exists_coordinate (f : (∀ i, C i) →+* B) :
    ∃ i, ∃ g : C i →+* B, ∀ x, f x = g (x i) := by
  classical
  have hs : (∑ i : L, Pi.single i (1 : C i)) = 1 := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj.symm]
    · simp
  have hi : ∃ i : L, f (Pi.single i (1 : C i)) ≠ 0 := by
    by_contra h
    have hz (i : L) : f (Pi.single i (1 : C i)) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    have hf := congrArg f hs
    rw [map_sum] at hf
    simp [hz] at hf
  obtain ⟨i, hi⟩ := hi
  have hmul (a b : C i) : Pi.single i (a * b) = Pi.single i a * Pi.single i b := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  have hone : f (Pi.single i (1 : C i)) = 1 := by
    have he : f (Pi.single i (1 : C i)) =
        f (Pi.single i (1 : C i)) * f (Pi.single i (1 : C i)) := by
      simpa only [one_mul, map_mul] using congrArg f (hmul 1 1)
    have h' := mul_left_cancel₀ hi (show f (Pi.single i (1 : C i)) * 1 =
        f (Pi.single i (1 : C i)) * f (Pi.single i (1 : C i)) by simpa using he)
    exact h'.symm
  let g : C i →+* B := {
    toFun := fun x => f (Pi.single i x)
    map_one' := hone
    map_zero' := by simp
    map_mul' := fun a b => by rw [hmul, map_mul]
    map_add' := fun a b => by rw [Pi.single_add, map_add] }
  refine ⟨i, g, fun x => ?_⟩
  have hx : Pi.single i (x i) = Pi.single i 1 * x := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  change f x = f (Pi.single i (x i))
  rw [hx, map_mul, hone, one_mul]



/-- An incidence can be found by applying the cell map to the coordinate idempotents. -/
theorem exists_unique_active_coordinate (f : (∀ i, C i) →+* B) :
    ∃! i, f (Pi.single i (1 : C i)) = 1 := by
  classical
  obtain ⟨i, g, hg⟩ := exists_coordinate f
  refine ⟨i, ?_, fun j hj => ?_⟩
  · simp [hg]
  · by_contra hji
    have : f (Pi.single j (1 : C j)) = 0 := by
      rw [hg]
      simp [Pi.single_eq_of_ne (Ne.symm hji)]
    exact zero_ne_one (this.symm.trans hj)

section Network

variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]
    {L : I → Type*} [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
    {C : ∀ i, L i → Type*} [∀ i l, Field (C i l)] [∀ i l, Algebra K (C i l)]
    {F : J → Type*} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

open EvenOrdinaryTI.Cells

/-- A common variable is indexed by its physical mode and its primary block.
The equations may choose a different block in each mode and cell. -/
theorem transport_iff_shared_variable_network
    (E : (⨂[K] i, (∀ l, C i l)) ≃ₐ[K] (∀ j, F j))
    (T S : ⨂[K] i, (∀ l, C i l))
    (pick : J → ∀ i, L i) (φ : ∀ j i, C i (pick j i) →+* F j)
    (he : ∀ j i (x : ∀ l, C i l), embedding E j i x = φ j i (x (pick j i))) :
    (∃ x : ∀ i, (∀ l, C i l)ˣ,
      PiTensorProduct.tprod K (fun i => (x i : ∀ l, C i l)) * T = S) ↔
    ∃ h : ∀ j, E T j = 0 ↔ E S j = 0,
      ∃ y : ∀ a : Sigma L, (C a.1 a.2)ˣ, ∀ j : {j // E T j ≠ 0},
        (∏ i, Units.map (φ j.1 i).toMonoidHom (y ⟨i, pick j.1 i⟩)) =
          ratio (E T) (E S) j h := by
  classical
  have hmap (j : J) (i : I) (x : (∀ l, C i l)ˣ) :
      Units.map (embedding E j i).toMonoidHom x =
        Units.map (φ j i).toMonoidHom (MulEquiv.piUnits x (pick j i)) := by
    apply Units.ext
    exact he j i (x : ∀ l, C i l)
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h, hx⟩ := (transport_iff_cell_ratios E T S x).mp hx
    refine ⟨h, fun a => MulEquiv.piUnits (x a.1) a.2, fun j => ?_⟩
    simpa only [hmap] using hx j
  · rintro ⟨h, y, hy⟩
    let x (i : I) : (∀ l, C i l)ˣ := MulEquiv.piUnits.symm (fun l => y ⟨i, l⟩)
    refine ⟨x, (transport_iff_cell_ratios E T S x).mpr ⟨h, fun j => ?_⟩⟩
    simpa only [hmap, x, MulEquiv.apply_symm_apply] using hy j

/-- Every field-cell presentation yields the shared incidence graph from its algebra maps. -/
theorem exists_shared_variable_network
    (E : (⨂[K] i, (∀ l, C i l)) ≃ₐ[K] (∀ j, F j))
    (T S : ⨂[K] i, (∀ l, C i l)) :
    ∃ (pick : J → ∀ i, L i) (φ : ∀ j i, C i (pick j i) →+* F j),
      (∃ x : ∀ i, (∀ l, C i l)ˣ,
        PiTensorProduct.tprod K (fun i => (x i : ∀ l, C i l)) * T = S) ↔
      ∃ h : ∀ j, E T j = 0 ↔ E S j = 0,
        ∃ y : ∀ a : Sigma L, (C a.1 a.2)ˣ, ∀ j : {j // E T j ≠ 0},
          (∏ i, Units.map (φ j.1 i).toMonoidHom (y ⟨i, pick j.1 i⟩)) =
            ratio (E T) (E S) j h := by
  classical
  have h : ∀ j i, ∃ l, ∃ f : C i l →+* F j,
      ∀ x, embedding E j i x = f (x l) :=
    fun j i => exists_coordinate (embedding E j i)
  let pick (j : J) (i : I) : L i := Classical.choose (h j i)
  let φ (j : J) (i : I) : C i (pick j i) →+* F j :=
    Classical.choose (Classical.choose_spec (h j i))
  have he (j : J) (i : I) (x : ∀ l, C i l) :
      embedding E j i x = φ j i (x (pick j i)) :=
    Classical.choose_spec (Classical.choose_spec (h j i)) x
  exact ⟨pick, φ, transport_iff_shared_variable_network E T S pick φ he⟩

end Network
end EvenOrdinaryTI.CellVariables

#print axioms EvenOrdinaryTI.CellVariables.exists_coordinate

#print axioms EvenOrdinaryTI.CellVariables.transport_iff_shared_variable_network
#print axioms EvenOrdinaryTI.CellVariables.exists_shared_variable_network
#print axioms EvenOrdinaryTI.CellVariables.exists_unique_active_coordinate
