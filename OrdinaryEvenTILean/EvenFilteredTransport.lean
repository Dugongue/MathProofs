import EvenPhysicalAction
import EvenProductCount

open scoped BigOperators

namespace EvenTI

open Action Counting

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d n q : Nat}

/-- Count with independently decidable per-mode filters, from a single transporter. -/
def countWithTransporter (enumerate : Fin q ≃ Kˣ) (g : Changes K d n)
    (allowed : Fin d → (Matrix (Fin n) (Fin n) K)ˣ → Bool) : Nat :=
  (productTable enumerate d (fun i u => allowed i (g i * scalar u))).get
    (enumerate.symm 1)

theorem countWithTransporter_correct (enumerate : Fin q ≃ Kˣ) (hn : 0 < n)
    {T S : Tensor K d n} (hT : T ≠ 0)
    (g : Changes K d n) (hg : act g T = S)
    (scalarOnly : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u)
    (allowed : Fin d → (Matrix (Fin n) (Fin n) K)ˣ → Bool) :
    countWithTransporter enumerate g allowed =
      Nat.card {a : Changes K d n // (∀ i, allowed i (a i) = true) ∧ act a T = S} := by
  unfold countWithTransporter
  rw [productTable_counts, Equiv.apply_symm_apply]
  exact Nat.card_congr (filteredTransportEquiv hn hT g hg scalarOnly (fun a i => allowed i a = true))

/-- The zero case comes from the exact no-transporter verdict of the search routine. -/
def countFromSearch (enumerate : Fin q ≃ Kˣ) (found : Option (Changes K d n))
    (allowed : Fin d → (Matrix (Fin n) (Fin n) K)ˣ → Bool) : Nat :=
  match found with
  | none => 0
  | some g => countWithTransporter enumerate g allowed

theorem countFromSearch_correct (enumerate : Fin q ≃ Kˣ) (hn : 0 < n)
    {T S : Tensor K d n} (hT : T ≠ 0)
    (found : Option (Changes K d n))
    (valid : ∀ g, found = some g → act g T = S)
    (noMatch : found = none → ∀ g, act g T ≠ S)
    (scalarOnly : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u)
    (allowed : Fin d → (Matrix (Fin n) (Fin n) K)ˣ → Bool) :
    countFromSearch enumerate found allowed =
      Nat.card {a : Changes K d n // (∀ i, allowed i (a i) = true) ∧ act a T = S} := by
  cases found with
  | none =>
    haveI : IsEmpty {a : Changes K d n //
        (∀ i, allowed i (a i) = true) ∧ act a T = S} :=
      ⟨fun a => noMatch rfl a.val a.property.2⟩
    exact (Nat.card_eq_zero.mpr (Or.inl inferInstance)).symm
  | some g =>
    exact countWithTransporter_correct enumerate hn hT g (valid g rfl) scalarOnly allowed

/-- Product-one scalar tuples are determined by all but their first entry. -/
def scalarTupleEquiv (K : Type*) [Field K] (m : Nat) :
    {u : Fin (m + 1) → Kˣ // (∏ i, u i) = 1} ≃ (Fin m → Kˣ) where
  toFun u i := u.val i.succ
  invFun u := ⟨Fin.cons (∏ i, u i)⁻¹ u, by
    simp [Fin.prod_univ_succ]⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      have h := u.property
      rw [Fin.prod_univ_succ] at h
      exact (eq_inv_of_mul_eq_one_left h).symm
    | succ i => rfl
  right_inv u := by
    funext i
    rfl

theorem unfilteredTransport_card (hn : 0 < n) {m : Nat}
    {T S : Tensor K (m + 1) n} (hT : T ≠ 0)
    (g : Changes K (m + 1) n) (hg : act g T = S)
    (scalarOnly : ∀ a : Changes K (m + 1) n, act a T = T → ∃ u, a = scalars u) :
    Nat.card {a : Changes K (m + 1) n // act a T = S} =
      (Fintype.card K - 1) ^ m := by
  let scalarsFiltered := filteredTransportEquiv hn hT g hg scalarOnly (fun _ _ => True)
  let transportForget :
      {a : Changes K (m + 1) n // (∀ _ : Fin (m + 1), True) ∧ act a T = S} ≃
        {a : Changes K (m + 1) n // act a T = S} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  let scalarsForget :
      {u : Fin (m + 1) → Kˣ // (∀ _ : Fin (m + 1), True) ∧ (∏ i, u i) = 1} ≃
        {u : Fin (m + 1) → Kˣ // (∏ i, u i) = 1} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = Nat.card (Fin m → Kˣ) := Nat.card_congr (transportForget.symm.trans
      (scalarsFiltered.symm.trans (scalarsForget.trans (scalarTupleEquiv K m))))
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_units]

#print axioms unfilteredTransport_card
#print axioms countWithTransporter_correct
#print axioms countFromSearch_correct

end EvenTI
