import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Defs

open scoped BigOperators

namespace TerminalProfiles

theorem arithmetic_or_eq_one_iff {R ι : Type*} [CommRing R] [IsDomain R]
    (s : Finset ι) (f : ι → R) :
    1 - (∏ i ∈ s, (1 - f i)) = 1 ↔ ∃ i ∈ s, f i = 1 := by
  rw [sub_eq_self, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, hi, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨i, hi, hone⟩
    exact ⟨i, hi, sub_eq_zero.mpr hone.symm⟩

end TerminalProfiles
