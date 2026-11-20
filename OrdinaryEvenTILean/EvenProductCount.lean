import Init.Data.Vector.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard


open scoped BigOperators

namespace EvenTI.Counting

variable {G : Type*} [CommGroup G] [DecidableEq G] {q : Nat}

@[simp] private theorem tabulate_get {f : Fin q → Nat} (j : Fin q) :
    (Vector.ofFn f).get j = f j := by
  change (Vector.ofFn f)[j.val] = f j
  exact Vector.getElem_ofFn j.isLt

/-- A table has one entry for every element in the given group enumeration. -/
def productTable (enumerate : Fin q ≃ G) :
    (d : Nat) → (Fin d → G → Bool) → Vector Nat q
  | 0, _ => Vector.ofFn (fun j => if enumerate j = 1 then 1 else 0)
  | d + 1, allowed =>
    let tail := productTable enumerate d (fun i => allowed i.succ)
    Vector.ofFn fun j => ∑ k : Fin q,
      if allowed 0 (enumerate k) then
        tail.get (enumerate.symm ((enumerate k)⁻¹ * enumerate j))
      else 0

/-- Specification sums over complete tuples, independent of the implementation. -/
def specification [Fintype G] {d : Nat} (allowed : Fin d → G → Bool) (z : G) : Nat :=
  ∑ u : Fin d → G,
    if (∀ i, allowed i (u i) = true) ∧ (∏ i, u i) = z then 1 else 0

theorem specification_succ [Fintype G] {d : Nat}
    (allowed : Fin (d + 1) → G → Bool) (z : G) :
    specification allowed z = ∑ a : G, if allowed 0 a then
      specification (fun i : Fin d => allowed i.succ) (a⁻¹ * z) else 0 := by
  classical
  unfold specification
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => G)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases ha : allowed 0 a with
  | false =>
    simp [Fin.consEquiv, Fin.forall_fin_succ, ha]
  | true =>
    simp only [Fin.consEquiv_apply, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.prod_univ_succ, ha, true_and, if_true]
    apply Finset.sum_congr rfl
    intro u _
    simp only [eq_inv_mul_iff_mul_eq]

theorem productTable_correct [Fintype G] (enumerate : Fin q ≃ G) (d : Nat)
    (allowed : Fin d → G → Bool) (j : Fin q) :
    (productTable enumerate d allowed).get j = specification allowed (enumerate j) := by
  induction d generalizing j with
  | zero =>
    classical
    by_cases h : enumerate j = 1
    · simp [productTable, specification, tabulate_get, h]
    · simp [productTable, specification, tabulate_get, h, Ne.symm h]
  | succ d ih =>
    rw [specification_succ]
    simp only [productTable, tabulate_get, ih, Equiv.apply_symm_apply]
    exact enumerate.sum_comp (fun a : G => if allowed 0 a then
      specification (fun i : Fin d => allowed i.succ) (a⁻¹ * enumerate j) else 0)

theorem specification_eq_card [Fintype G] {d : Nat} (allowed : Fin d → G → Bool) (z : G) :
    specification allowed z =
      Nat.card {u : Fin d → G // (∀ i, allowed i (u i) = true) ∧ (∏ i, u i) = z} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [specification]

theorem productTable_counts [Fintype G] (enumerate : Fin q ≃ G) (d : Nat)
    (allowed : Fin d → G → Bool) (j : Fin q) :
    (productTable enumerate d allowed).get j =
      Nat.card {u : Fin d → G //
        (∀ i, allowed i (u i) = true) ∧ (∏ i, u i) = enumerate j} :=
  (productTable_correct enumerate d allowed j).trans (specification_eq_card allowed _)

theorem productTable_entry_le [Fintype G] (enumerate : Fin q ≃ G) (d : Nat)
    (allowed : Fin d → G → Bool) (j : Fin q) :
    (productTable enumerate d allowed).get j ≤ q ^ d := by
  rw [productTable_counts]
  calc
    _ ≤ Nat.card (Fin d → G) := by
      classical
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = q ^ d := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Fintype.card_congr enumerate,
        Fintype.card_fin]

#print axioms productTable_counts
#print axioms productTable_entry_le

end EvenTI.Counting
