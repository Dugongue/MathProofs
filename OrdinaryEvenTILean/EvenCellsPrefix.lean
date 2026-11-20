import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Reduce arbitrary-arity field-cell rows to the three incidences used by the
existing CRT/Smith network. All new variables for a row live in that row's field.
-/

open scoped BigOperators

namespace EvenOrdinaryTI.CellPrefix

variable {G : Type*} [CommGroup G]

/-- The three slots of the existing network have signs (+,-,-). -/
def ternary (a b c : G) : G := a * b⁻¹ * c⁻¹

theorem ternary_eq_one_iff (a b c : G) : ternary a b c = 1 ↔ a = b * c := by
  rw [ternary, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, mul_comm c b]

theorem pin_iff (a b : G) : ternary a a a = b⁻¹ ↔ a = b := by
  simp [ternary, inv_inj]

/-- There are two boundary rows and one transition row per original incidence. -/
structure Rows (x : ℕ → G) (d : ℕ) (c : G) (y : ℕ → G) : Prop where
  start : ternary (y 0) (y 0) (y 0) = 1
  finish : ternary (y d) (y d) (y d) = c⁻¹
  step : ∀ i, i < d → ternary (y (i + 1)) (y i) (x i) = 1

def prefixProd (x : ℕ → G) (i : ℕ) : G := ∏ j ∈ Finset.range i, x j


theorem prefix_mul (x z : ℕ → G) (i : ℕ) :
    prefixProd (fun j => x j * z j) i = prefixProd x i * prefixProd z i := by
  exact Finset.prod_mul_distrib

theorem prefix_rows (x : ℕ → G) (d : ℕ) (c : G) (h : prefixProd x d = c) :
    Rows x d c (prefixProd x) := by
  constructor
  · simp [ternary, prefixProd]
  · exact (pin_iff _ _).mpr h
  · intro i _
    exact (ternary_eq_one_iff _ _ _).mpr (Finset.prod_range_succ x i)

theorem rows_unique_on_prefix (x : ℕ → G) (d : ℕ) (c : G) {y : ℕ → G}
    (h : Rows x d c y) (i : ℕ) (hi : i ≤ d) : y i = prefixProd x i := by
  induction i with
  | zero =>
    have hs : ternary (y 0) (y 0) (y 0) = (1 : G)⁻¹ := by simpa only [inv_one] using h.start
    simpa [prefixProd] using (pin_iff _ _).mp hs
  | succ i ih =>
    have hlt : i < d := Nat.lt_of_succ_le hi
    have hrec := (ternary_eq_one_iff _ _ _).mp (h.step i hlt)
    rw [hrec, ih hlt.le]
    exact (Finset.prod_range_succ x i).symm

theorem rows_iff_product (x : ℕ → G) (d : ℕ) (c : G) :
    (∃ y, Rows x d c y) ↔ (∏ j ∈ Finset.range d, x j) = c := by
  constructor
  · rintro ⟨y, hy⟩
    exact (rows_unique_on_prefix x d c hy d le_rfl).symm.trans ((pin_iff _ _).mp hy.finish)
  · intro h
    exact ⟨prefixProd x, prefix_rows x d c h⟩

/-- Apply the same bounded-arity replacement independently to each output cell.
The original variables can still be shared by any number of cells. -/
theorem cell_network_iff_rows {J : Type*} {F : J → Type*} [∀ j, CommGroup (F j)]
    (x : ∀ j, ℕ → F j) (c : ∀ j, F j) (d : ℕ) :
    (∀ j, (∏ i ∈ Finset.range d, x j i) = c j) ↔
      ∃ y : ∀ j, ℕ → F j, ∀ j, Rows (x j) d (c j) (y j) := by
  constructor
  · intro h
    exact ⟨fun j => prefixProd (x j), fun j => prefix_rows (x j) d (c j) (h j)⟩
  · rintro ⟨y, hy⟩ j
    exact (rows_iff_product (x j) d (c j)).mp ⟨y j, hy j⟩

end EvenOrdinaryTI.CellPrefix

#print axioms EvenOrdinaryTI.CellPrefix.rows_unique_on_prefix
#print axioms EvenOrdinaryTI.CellPrefix.rows_iff_product
#print axioms EvenOrdinaryTI.CellPrefix.cell_network_iff_rows
#print axioms EvenOrdinaryTI.CellPrefix.prefix_mul
