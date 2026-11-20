import EvenLiveRowLayout
import Mathlib.Algebra.Group.Pi.Basic

/-! Introducing prefix variables preserves the exponent test on actual
field-unit assignments. -/
namespace EvenOrdinaryTI.LiveRows

open scoped BigOperators
open EvenOrdinaryTI.CellPrefix

variable {s t d : Nat}
variable (X : Fin s → Type) (Y : Fin t → Type) [∀ i, Field (X i)] [∀ j, Field (Y j)]
  (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →+* Y j)

private theorem factors_one (j : Fin t) (i : Nat) :
    factors X Y orig emb 1 j i = 1 := by
  by_cases hi : i < d <;> simp [factors, hi, Pi.one_apply]

private theorem factors_pow (x : ∀ i, (X i)ˣ) (j : Fin t) (i m : Nat) :
    factors X Y orig emb (x ^ m) j i = factors X Y orig emb x j i ^ m := by
  by_cases hi : i < d <;> simp [factors, hi, Pi.pow_apply]

theorem liftOriginal_one :
    liftOriginal X Y orig emb 1 = 1 := by
  funext v
  rcases v with i | ⟨j, k⟩
  · rfl
  · change prefixProd (factors X Y orig emb 1 j) k.val = (1 : (Y j)ˣ)
    simp [prefixProd, factors_one X Y orig emb]

theorem liftOriginal_pow (x : ∀ i, (X i)ˣ) (m : Nat) :
    liftOriginal X Y orig emb (x ^ m) = liftOriginal X Y orig emb x ^ m := by
  funext v
  rcases v with i | ⟨j, k⟩
  · rfl
  · change prefixProd (factors X Y orig emb (x ^ m) j) k.val =
      prefixProd (factors X Y orig emb x j) k.val ^ m
    simp [prefixProd, Finset.prod_pow, factors_pow X Y orig emb]

theorem liftOriginal_pow_eq_one_iff (x : ∀ i, (X i)ˣ) (m : Nat) :
    liftOriginal X Y orig emb x ^ m = 1 ↔ x ^ m = 1 := by
  rw [← liftOriginal_pow]
  constructor
  · intro h
    funext i
    exact congrFun h (.inl i)
  · intro h
    rw [h, liftOriginal_one]

#print axioms liftOriginal_pow_eq_one_iff

end EvenOrdinaryTI.LiveRows
