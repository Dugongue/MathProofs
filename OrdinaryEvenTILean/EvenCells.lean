import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Variable-order exact field-cell equations for ordinary tensor isomorphism.
Primary coordinates and a cell decomposition serve as inputs to these identities.
-/

open scoped TensorProduct BigOperators
open Module

namespace EvenOrdinaryTI.Cells

section TensorCells

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    {F : J → Type*} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

private theorem pure_eq_prod [DecidableEq I] (x : ∀ i, A i) :
    PiTensorProduct.tprod K x =
      ∏ i, PiTensorProduct.singleAlgHom (R := K) i (x i) := by
  have h : (∏ i, MonoidHom.mulSingle A i (x i)) = x := by
    funext j
    rw [Fintype.prod_apply]
    simp only [MonoidHom.mulSingle_apply]
    exact Fintype.prod_pi_mulSingle ..
  conv_lhs => rw [← h]
  exact map_prod (PiTensorProduct.tprodMonoidHom K)
    (fun i => MonoidHom.mulSingle A i (x i)) Finset.univ

noncomputable def embedding [DecidableEq I]
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) (j : J) (i : I) :
    A i →+* F j :=
  (Pi.evalRingHom F j).comp (E.toRingHom.comp
    (PiTensorProduct.singleAlgHom (R := K) (A := A) i).toRingHom)

theorem cell_multiplication [DecidableEq I]
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) (x : ∀ i, A i)
    (T : ⨂[K] i, A i) (j : J) :
    E (PiTensorProduct.tprod K x * T) j =
      (∏ i, embedding E j i (x i)) * E T j := by
  rw [map_mul, Pi.mul_apply, pure_eq_prod]
  let f : (⨂[K] i, A i) →+* F j := (Pi.evalRingHom F j).comp E.toRingHom
  change f (∏ i, PiTensorProduct.singleAlgHom (R := K) i (x i)) * E T j = _
  rw [map_prod]
  rfl

noncomputable def ratio (a b : ∀ j, F j) (j : {j // a j ≠ 0})
    (h : ∀ j, a j = 0 ↔ b j = 0) : (F j.1)ˣ :=
  Units.mk0 (b j.1 / a j.1)
    (div_ne_zero (fun hz => j.2 ((h j.1).mpr hz)) j.2)

theorem transport_iff_cell_ratios [DecidableEq I]
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) (T S : ⨂[K] i, A i)
    (x : ∀ i, (A i)ˣ) :
    PiTensorProduct.tprod K (fun i => (x i : A i)) * T = S ↔
      ∃ h : ∀ j, E T j = 0 ↔ E S j = 0,
        ∀ j : {j // E T j ≠ 0},
          (∏ i, Units.map (embedding E j.1 i).toMonoidHom (x i)) =
            ratio (E T) (E S) j h := by
  classical
  have hm (j : J) :
      (↑(∏ i, Units.map (embedding E j i).toMonoidHom (x i)) : F j) =
        ∏ i, embedding E j i (x i : A i) := by simp
  constructor
  · intro h
    have he (j : J) := (cell_multiplication E (fun i => (x i : A i)) T j).symm.trans
      (congrArg (fun t => E t j) h)
    have hSupp (j : J) : E T j = 0 ↔ E S j = 0 := by
      rw [← he j, ← hm j]
      exact ⟨fun hz => by simp [hz], fun hz => (mul_eq_zero.mp hz).resolve_left (Units.ne_zero _)⟩
    refine ⟨hSupp, fun j => Units.ext ?_⟩
    change (↑(∏ i, Units.map (embedding E j.1 i).toMonoidHom (x i)) : F j.1) =
      E S j.1 / E T j.1
    rw [hm j.1, eq_div_iff j.2]
    exact he j.1
  · rintro ⟨hSupp, h⟩
    apply E.injective
    funext j
    rw [cell_multiplication]
    by_cases hj : E T j = 0
    · simp [hj, (hSupp j).mp hj]
    · have he := congrArg (fun u : (F j)ˣ => (u : F j)) (h ⟨j, hj⟩)
      change (↑(∏ i, Units.map (embedding E j i).toMonoidHom (x i)) : F j) =
        E S j / E T j at he
      rw [hm j] at he
      exact (eq_div_iff hj).mp he

theorem cell_dimensions [∀ i, Module.Finite K (A i)] [∀ j, Module.Finite K (F j)]
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) :
    (∑ j, Module.finrank K (F j)) = ∏ i, Module.finrank K (A i) := by
  classical
  let b : ∀ i, Module.Basis (Fin (Module.finrank K (A i))) K (A i) :=
    fun i => Module.finBasis K (A i)
  calc
    (∑ j, Module.finrank K (F j)) = Module.finrank K (∀ j, F j) :=
      (Module.finrank_pi_fintype K).symm
    _ = Module.finrank K (⨂[K] i, A i) := E.toLinearEquiv.finrank_eq.symm
    _ = ∏ i, Module.finrank K (A i) := by
      rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi]
      simp

end TensorCells

section Recovery

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Once the coordinate powers of an actual preimage have been extracted, every root
choice leaves a correction in the bounded torsion of the source group. -/
theorem solution_iff_torsionCorrection (f : G →* H) (h : ℕ) (x₀ : G) (y : H)
    (hpower : ∀ x, f x = y → x ^ h = x₀ ^ h) :
    (∃ x, f x = y) ↔ ∃ z : G, z ^ h = 1 ∧ f z = y / f x₀ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / x₀, ?_, by rw [map_div, hx]⟩
    rw [div_pow, hpower x hx, div_self']
  · rintro ⟨z, -, hz⟩
    exact ⟨z * x₀, by simp [map_mul, hz]⟩

/-- A supplied row character giving the (h)-power of a coordinate simultaneously
pins this power on every preimage and bounds the kernel in that coordinate. -/
theorem coordinate_power_of_character (f : G →* H) {X : Type*} [CommGroup X]
    (c : G →* X) (χ : H →* X) (h : ℕ)
    (hchar : ∀ x, χ (f x) = c x ^ h) (x : G) (y : H) (hy : f x = y) :
    c x ^ h = χ y := by
  rw [← hchar, hy]

end Recovery

end EvenOrdinaryTI.Cells

#print axioms EvenOrdinaryTI.Cells.transport_iff_cell_ratios
#print axioms EvenOrdinaryTI.Cells.cell_dimensions
#print axioms EvenOrdinaryTI.Cells.solution_iff_torsionCorrection
#print axioms EvenOrdinaryTI.Cells.coordinate_power_of_character
