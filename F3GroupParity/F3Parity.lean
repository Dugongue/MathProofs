import Mathlib.Data.Bool.Basic

namespace F3Parity

def rails (odd : Bool) : Bool × Bool := (!odd, odd)

def combine (a b : Bool × Bool) : Bool × Bool :=
  (a.1 && b.1 || a.2 && b.2, a.1 && b.2 || a.2 && b.1)

theorem combine_rails (a b : Bool) :
    combine (rails a) (rails b) = rails (Bool.xor a b) := by
  cases a <;> cases b <;> rfl

inductive SignTree where
  | leaf (odd : Bool)
  | branch (left right : SignTree)

def SignTree.odd : SignTree → Bool
  | .leaf odd => odd
  | .branch left right => Bool.xor left.odd right.odd

def SignTree.evaluate : SignTree → Bool × Bool
  | .leaf odd => rails odd
  | .branch left right => combine left.evaluate right.evaluate

theorem parity_tree_exact (t : SignTree) :
    t.evaluate = rails t.odd := by
  induction t with
  | leaf odd => rfl
  | branch left right left_ih right_ih =>
    simp only [SignTree.evaluate, SignTree.odd, left_ih, right_ih, combine_rails]

theorem centroid_maps_commute_on_brackets {X Z : Type*}
    (β : X → X → Z) (a b : X → X) (c d : Z → Z)
    (ha₂ : ∀ x y, β x (a y) = c (β x y))
    (hb₁ : ∀ x y, β (b x) y = d (β x y)) (x y : X) :
    c (d (β x y)) = d (c (β x y)) := by
  calc
    c (d (β x y)) = c (β (b x) y) := by rw [hb₁]
    _ = β (b x) (a y) := (ha₂ _ _).symm
    _ = d (β x (a y)) := hb₁ _ _
    _ = d (c (β x y)) := by rw [ha₂]

end F3Parity
