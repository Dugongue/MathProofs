import EvenNextSmithBanks
import Mathlib.Data.Fintype.Sort

namespace EvenTI.CellPreparation

variable {m : ℕ} {Y : Fin m → Type}
  [∀ j, Field (Y j)] [∀ j, DecidableEq (Y j)]

def activeCells (a : ∀ j, Y j) : Finset (Fin m) :=
  Finset.univ.filter (fun j => a j ≠ 0)

def activeOrder (a : ∀ j, Y j) : Fin (activeCells a).card ≃ ↥(activeCells a) :=
  ((activeCells a).orderIsoOfFin rfl).toEquiv

abbrev activeIndex (a : ∀ j, Y j) (j : Fin (activeCells a).card) : Fin m :=
  (activeOrder a j).val

theorem activeIndex_ne_zero (a : ∀ j, Y j) (j : Fin (activeCells a).card) :
    a (activeIndex a j) ≠ 0 :=
  (Finset.mem_filter.mp (activeOrder a j).property).2

def equalSupport (a b : ∀ j, Y j) : Bool :=
  (List.finRange m).all (fun j => decide (a j = 0 ↔ b j = 0))

theorem equalSupport_spec (a b : ∀ j, Y j) :
    equalSupport a b = true ↔ ∀ j, a j = 0 ↔ b j = 0 := by
  simp [equalSupport, List.all_eq_true]

def liveRatios (a b : ∀ j, Y j) :
    Option (∀ j : Fin (activeCells a).card, (Y (activeIndex a j))ˣ) :=
  if h : equalSupport a b = true then
    some fun j => Units.mk0 (b (activeIndex a j) / a (activeIndex a j))
      (div_ne_zero
        (fun hzero => activeIndex_ne_zero a j (((equalSupport_spec a b).mp h _).mpr hzero))
        (activeIndex_ne_zero a j))
  else none

theorem liveRatios_none_iff (a b : ∀ j, Y j) :
    liveRatios a b = none ↔ ¬ (∀ j, a j = 0 ↔ b j = 0) := by
  rw [← equalSupport_spec a b]
  unfold liveRatios
  split <;> simp_all

theorem liveRatios_correct (a b : ∀ j, Y j)
    {c : ∀ j : Fin (activeCells a).card, (Y (activeIndex a j))ˣ}
    (hc : liveRatios a b = some c) :
    (∀ j, a j = 0 ↔ b j = 0) ∧ ∀ j, (c j).val * a (activeIndex a j) = b (activeIndex a j) := by
  unfold liveRatios at hc
  split at hc
  next h =>
    cases hc
    exact ⟨(equalSupport_spec a b).mp h, fun j =>
      div_mul_cancel₀ (b _) (activeIndex_ne_zero a j)⟩
  next => contradiction

theorem activeCells_card_le (a : ∀ j, Y j) : (activeCells a).card ≤ m := by
  unfold activeCells
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := Finset.univ) (p := fun j => a j ≠ 0)

end EvenTI.CellPreparation

#print axioms EvenTI.CellPreparation.liveRatios_correct
#print axioms EvenTI.CellPreparation.liveRatios_none_iff
