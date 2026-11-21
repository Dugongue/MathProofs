import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LocalizationSpectrum

variable {ι G : Type*} [DecidableEq ι] [CommGroup G]

theorem selector_product (s : Finset ι) (i : ι) (a : G) (z : ι → ℤ) :
    (∏ j ∈ s, if j = i then a ^ z j else 1) =
      if i ∈ s then a ^ z i else 1 := by
  classical
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    calc
      (∏ j ∈ s, if j = i then a ^ z j else 1) =
          (if i = i then a ^ z i else 1) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [hji]
        · intro h
          exact (h hi).elim
      _ = a ^ z i := by simp
  · rw [if_neg hi]
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [hji]

theorem selector_attainable (s : Finset ι) (i : ι) (a : G) (ha : a ≠ 1) :
    (∃ z : ι → ℤ, (∏ j ∈ s, if j = i then a ^ z j else 1) = a) ↔
      i ∈ s := by
  constructor
  · rintro ⟨z, hz⟩
    by_contra h
    rw [selector_product, if_neg h] at hz
    exact ha hz.symm
  · intro hi
    use fun _ => 1
    rw [selector_product, if_pos hi, zpow_one]

end LocalizationSpectrum
