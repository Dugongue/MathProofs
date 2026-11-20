import EvenStabilizerUnion
import Mathlib.Algebra.Order.Field.Basic

namespace EvenTI.Action
open scoped Classical

private theorem order_margin (n l : Nat) (hn : 5 ≤ n) (hl : 3 ≤ l) :
    l + 2 ≤ n ^ (l - 2) := by
  induction l, hl using Nat.le_induction with
  | base => simpa using hn
  | succ l hl ih =>
    have h : l + 1 - 2 = (l - 2) + 1 := by omega
    rw [h, pow_succ]
    calc
      l + 1 + 2 ≤ (l + 2) * 2 := by omega
      _ ≤ _ := Nat.mul_le_mul ih (by omega)

variable {K : Type*} [Field K] [Fintype K]

/-- A uniform bound on the nonscalar-stabilizer exception for all orders
at least four and all side lengths at least five. -/
theorem nonscalar_bad_count_uniform (n l : Nat) (hn : 5 ≤ n) (hl : 3 ≤ l) :
    nonscalarBadCount K l n * Fintype.card K ^ (n ^ 2) ≤
      Fintype.card (Tensor K (l + 1) n) := by
  let q := Fintype.card K
  let a := nonscalarBadCount K l n
  let b := Fintype.card (Tensor K (l + 1) n)
  let large := (l + 1) * n ^ 2
  have hsum : large + n ^ 2 ≤ n ^ l := by
    calc
      _ = (l + 2) * n ^ 2 := by dsimp [large]; ring
      _ ≤ n ^ (l - 2) * n ^ 2 := Nat.mul_le_mul_right _ (order_margin n l hn hl)
      _ = n ^ l := by rw [← pow_add]; congr 1; omega
  have hlarge : 0 < q ^ large := pow_pos Fintype.card_pos _
  have hfixed : a * q ^ (n ^ l) ≤ q ^ large * b :=
    nonscalar_bad_count_le (K := K) (l := l) (by omega : 0 < n)
  have hle : (a * q ^ (n ^ 2)) * q ^ large ≤ b * q ^ large := by
    rw [Nat.mul_assoc, ← pow_add]
    calc
      _ ≤ a * q ^ (n ^ l) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (Fintype.card_pos (α := K)) (by omega))
      _ ≤ _ := by simpa only [Nat.mul_comm] using hfixed
  exact Nat.le_of_mul_le_mul_right hle hlarge

private theorem exists_bad_stabilizer_iff (T : Tensor K (l + 1) n) :
    (∃ a : Changes K (l + 1) n, act a T = T ∧ ∃ i, ¬∃ u : Kˣ, a i = scalar u) ↔
      ¬ (∀ a : Changes K (l + 1) n, act a T = T → ∃ u, a = scalars u) := by
  constructor
  · rintro ⟨a, ha, i, hi⟩ good
    obtain ⟨u, hu⟩ := good a ha
    exact hi ⟨u i, congrFun hu i⟩
  · intro bad
    by_contra no
    apply bad
    intro a ha
    have h : ∀ i, ∃ u : Kˣ, a i = scalar u := by
      intro i
      by_contra hi
      exact no ⟨a, ha, i, hi⟩
    choose u hu using h
    exact ⟨u, funext hu⟩

/-- The mathematical scalar-only predicate has an exponentially small
exception uniformly in the tensor order. -/
theorem scalar_only_failure_card (n l : Nat) (hn : 5 ≤ n) (hl : 3 ≤ l) :
    let bad := ((Finset.univ : Finset (Tensor K (l + 1) n)).filter (fun T =>
        ¬ (∀ a : Changes K (l + 1) n, act a T = T → ∃ u, a = scalars u))).card
    bad * Fintype.card K ^ (n ^ 2) ≤ Fintype.card (Tensor K (l + 1) n) := by
  classical
  dsimp
  have h : ((Finset.univ : Finset (Tensor K (l + 1) n)).filter (fun T =>
        ¬ (∀ a : Changes K (l + 1) n, act a T = T → ∃ u, a = scalars u))).card =
        nonscalarBadCount K l n := by
    unfold nonscalarBadCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro T _
    exact (exists_bad_stabilizer_iff T).symm
  rw [h]
  exact nonscalar_bad_count_uniform n l hn hl

#print axioms nonscalar_bad_count_uniform
#print axioms scalar_only_failure_card

end EvenTI.Action
