import EvenStabilizerCount

namespace EvenTI.Action

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] {n l : Nat}

theorem changes_count_le :
    Nat.card (Changes K (l + 1) n) ≤ Fintype.card K ^ ((l + 1) * n ^ 2) := by
  classical
  letI : Fintype (Changes K (l + 1) n) := Fintype.ofFinite _
  let enc : Changes K (l + 1) n → (Fin (l + 1) → Fin n → Fin n → K) := fun a i => (a i).val
  have henc : Function.Injective enc := by
    intro a b h
    funext i
    apply Units.ext
    exact congrFun h i
  calc
    _ = Fintype.card (Changes K (l + 1) n) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Fin (l + 1) → Fin n → Fin n → K) :=
      Fintype.card_le_of_injective enc henc
    _ = _ := by simp [Fintype.card_fun, ← pow_mul, pow_two, Nat.mul_comm, Nat.mul_left_comm]

noncomputable def nonscalarBadCount (K : Type*) [Field K] [Fintype K] (l n : Nat) : Nat := by
  classical
  exact (Finset.univ.filter fun T : Tensor K (l + 1) n =>
    ∃ a : Changes K (l + 1) n, act a T = T ∧
      ∃ i, ¬ ∃ u : Kˣ, a i = scalar u).card

theorem nonscalar_bad_count_le (hn : 0 < n) :
    nonscalarBadCount K l n * Fintype.card K ^ (n ^ l) ≤
      Fintype.card K ^ ((l + 1) * n ^ 2) * Fintype.card (Tensor K (l + 1) n) := by
  classical
  letI : Fintype (Changes K (l + 1) n) := Fintype.ofFinite _
  let badChanges := (Finset.univ : Finset (Changes K (l + 1) n)).filter
    (fun a => ∃ i, ¬ ∃ u : Kˣ, a i = scalar u)
  let fixed (a : Changes K (l + 1) n) := (Finset.univ : Finset (Tensor K (l + 1) n)).filter
    (fun T => act a T = T)
  have hb : nonscalarBadCount K l n = (badChanges.biUnion fixed).card := by
    unfold nonscalarBadCount
    apply congrArg Finset.card
    ext T
    simp only [badChanges, fixed, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun _ => and_comm
  have hbad : badChanges.card ≤ Fintype.card K ^ ((l + 1) * n ^ 2) := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact changes_count_le
  calc
    _ ≤ (∑ a ∈ badChanges, (fixed a).card) * Fintype.card K ^ (n ^ l) := by
      rw [hb]
      exact Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ a ∈ badChanges, (fixed a).card * Fintype.card K ^ (n ^ l) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _a ∈ badChanges, Fintype.card (Tensor K (l + 1) n) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨i, hi⟩ := (Finset.mem_filter.mp ha).2
      have hcard : Nat.card {T : Tensor K (l + 1) n // act a T = T} = (fixed a).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [← hcard]
      exact nonscalar_fixed_count a i hn hi
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ hbad

#print axioms changes_count_le
#print axioms nonscalar_bad_count_le

end EvenTI.Action
