import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Init.Data.List.OfFn

namespace EvenTI.CellPreparation

open scoped BigOperators

/-- Use the existing mixed-radix equivalence to enumerate dependent choices
without materializing lists of rejected or duplicate prefixes. -/
def finiteChoices {n : ℕ} (count : Fin n → ℕ) : List (∀ i, Fin (count i)) :=
  List.ofFn (finPiFinEquiv (n := count)).symm

theorem mem_finiteChoices {n : ℕ} (count : Fin n → ℕ) (p : ∀ i, Fin (count i)) :
    p ∈ finiteChoices count :=
  List.mem_ofFn.mpr ⟨finPiFinEquiv p, finPiFinEquiv.symm_apply_apply p⟩

theorem finiteChoices_length {n : ℕ} (count : Fin n → ℕ) :
    (finiteChoices count).length = ∏ i, count i :=
  List.length_ofFn

theorem finiteChoices_length_le {n : ℕ} (count cap : Fin n → ℕ)
    (h : ∀ i, count i ≤ cap i) :
    (finiteChoices count).length ≤ ∏ i, cap i := by
  rw [finiteChoices_length]
  exact Finset.prod_le_prod' (fun i _ => h i)

#print axioms mem_finiteChoices
#print axioms finiteChoices_length_le

/-- Collect values in their original dependent index order. A missing
value discards the candidate and never shifts later indices. -/
def collectSites {n : ℕ} {A : Fin n → Type} (read : ∀ i, Option (A i)) :
    Option (∀ i, A i) :=
  if h : ∀ i, (read i).isSome then some (fun i => (read i).get (h i)) else none

theorem collectSites_some {n : ℕ} {A : Fin n → Type} (read : ∀ i, Option (A i))
    (a : ∀ i, A i) (ha : ∀ i, read i = some (a i)) :
    collectSites read = some a := by
  have hc (i : Fin n) : (read i).isSome := by rw [ha i]; rfl
  unfold collectSites
  rw [dif_pos hc]
  congr 1
  funext i
  exact Option.get_of_eq_some (hc i) (ha i)

#print axioms collectSites_some
end EvenTI.CellPreparation
