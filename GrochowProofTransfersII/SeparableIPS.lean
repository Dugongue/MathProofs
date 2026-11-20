import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic

namespace SeparableIPS

variable {R : Type*} [Semiring R]

/-- Sum of the products obtained by taking exactly one marked factor. -/
def markedProduct : List (R × R) → R
  | [] => 0
  | (ordinary, marked) :: tail =>
    marked * (tail.map Prod.fst).prod + ordinary * markedProduct tail

/-- The two states at a layer boundary hold the ordinary and marked products. -/
def sweep : List (R × R) → R → R → R × R
  | [], ordinary, marked => (ordinary, marked)
  | (a, b) :: tail, ordinary, marked =>
    sweep tail (ordinary * a) (marked * a + ordinary * b)

theorem sweep_eq_marked_product (layers : List (R × R)) (ordinary marked : R) :
    sweep layers ordinary marked =
      (ordinary * (layers.map Prod.fst).prod,
        marked * (layers.map Prod.fst).prod + ordinary * markedProduct layers) := by
  induction layers generalizing ordinary marked with
  | nil =>
    simp [sweep, markedProduct]
  | cons head tail ih =>
    obtain ⟨a, b⟩ := head
    simp [sweep, markedProduct, ih, add_mul, mul_add, mul_assoc, add_assoc]

theorem sweep_from_empty_mark (layers : List (R × R)) :
    sweep layers (1 : R) 0 = ((layers.map Prod.fst).prod, markedProduct layers) := by
  simp [sweep_eq_marked_product]

/-- An intervening coordinate lane permits the marker to be read separately. -/
def ordinaryLayer (states : R × R) (a q : R) : R × R × R :=
  (states.1 * a, states.1 * q, states.2 * a)

def markerLayer (states : R × R × R) (z : R) : R × R :=
  (states.1, states.2.2 + states.2.1 * z)

theorem split_layer (states : R × R) (a q z : R) :
    markerLayer (ordinaryLayer states a q) z =
      (states.1 * a, states.2 * a + states.1 * (q * z)) := by
  simp [ordinaryLayer, markerLayer, mul_assoc]

end SeparableIPS
