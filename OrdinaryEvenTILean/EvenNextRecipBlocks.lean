import EvenReciprocalShear
import Mathlib.Data.Fintype.BigOperators

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators Matrix
open Matrix
open Mathproof.EvenTI.Reciprocal

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]

abbrev Restricted (K H L J : Type*) := J → H → L → K

/-- Only shear entries from the distinguished low-mode column to a
nondistinguished high-mode row are allowed to vary. -/
private def sparseShear (x : Restricted K H L J) :
    UpperShear K H L (Option J) :=
  fun p q => match p.2, q.2 with
    | some u, none => x u p.1 q.1
    | _, _ => 0

def includeShear : Restricted K H L J →ₗ[K] UpperShear K H L (Option J) where
  toFun := sparseShear
  map_add' x y := by
    ext p q
    change sparseShear (x + y) p q = sparseShear x p q + sparseShear y p q
    rcases p with ⟨a, u⟩
    rcases q with ⟨b, t⟩
    cases u <;> cases t <;> simp [sparseShear]
  map_smul' k x := by
    ext p q
    change sparseShear (k • x) p q = k * sparseShear x p q
    rcases p with ⟨a, u⟩
    rcases q with ⟨b, t⟩
    cases u <;> cases t <;> simp [sparseShear]
@[simp] theorem includeShear_some_none (x : Restricted K H L J) (a : H) (b : L) (u : J) :
    includeShear x (a, some u) (b, none) = x u a b := rfl

@[simp] theorem includeShear_some_some (x : Restricted K H L J) (a : H) (b : L) (u t : J) :
    includeShear x (a, some u) (b, some t) = 0 := rfl

@[simp] theorem includeShear_none (x : Restricted K H L J) (a : H) (q : L × Option J) :
    includeShear x (a, none) q = 0 := by rcases q with ⟨b, t⟩; cases t <;> rfl

@[simp] theorem includeShear_right_some (x : Restricted K H L J) (p : H × Option J)
    (b : L) (t : J) : includeShear x p (b, some t) = 0 := by
  rcases p with ⟨a, u⟩; cases u <;> rfl

variable (U : (Sum H L × Option J) → Matrix I B K)
variable (V : (Sum H L × Option J) → Matrix B I K)

/-- The independently controlled row of blocks in the nondistinguished sector. -/
def oneRow (x : H → L → K) (t : J) (i j : I) : K :=
  ∑ a : H, ∑ b : L, x a b * (U (.inr b, none) * V (.inl a, some t)) i j

theorem delta_some_some (x : Restricted K H L J) (u t : J) (i j : I) :
    delta U V (includeShear x) (some u, i) (some t, j) = oneRow U V (x u) t i j := by
  simp [delta, oneRow, Fintype.sum_prod_type, Fintype.sum_option]

theorem delta_none_some (x : Restricted K H L J) (u : J) (i j : I) :
    delta U V (includeShear x) (none, i) (some u, j) = 0 := by
  simp [delta, Fintype.sum_prod_type, Fintype.sum_option]

theorem delta_none_none (x : Restricted K H L J) (i j : I) :
    delta U V (includeShear x) (none, i) (none, j) =
      -(∑ t, oneRow U V (x t) t i j) := by
  simp [delta, oneRow, Fintype.sum_prod_type, Fintype.sum_option]
  congr 1
  let f (t : J) (a : H) (b : L) :=
    x t a b * (U (.inr b, none) * V (.inl a, some t)) i j
  change (∑ b, ∑ a, ∑ t, f t a b) = ∑ t, ∑ a, ∑ b, f t a b
  calc
    _ = ∑ a, ∑ b, ∑ t, f t a b := Finset.sum_comm
    _ = ∑ a, ∑ t, ∑ b, f t a b := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- The selected shear has a full square sector and one forced trace-sum
block. Its lower off-diagonal sector is zero, so the other off-diagonal
sector cannot contribute to the diagonal of a product. -/
theorem delta_triangular_blocks (x : Restricted K H L J) :
    (∀ (u t : J) (i j : I), delta U V (includeShear x) (some u,i) (some t,j) =
      oneRow U V (x u) t i j) ∧
    (∀ (t : J) (i j : I), delta U V (includeShear x) (none,i) (some t,j) = 0) ∧
    (∀ i j : I, delta U V (includeShear x) (none,i) (none,j) =
      -(∑ t, oneRow U V (x t) t i j)) :=
  ⟨delta_some_some U V x, delta_none_some U V x, delta_none_none U V x⟩

#print axioms delta_triangular_blocks
end Mathproof.EvenTI.Reciprocal.Next
