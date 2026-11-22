import Mathlib.RingTheory.Ideal.Basic

theorem successive_residuals_force_membership {R : Type*} [CommRing R] (I : Ideal R)
    (a : ℕ → R) (start : a 0 ∈ I)
    (step : ∀ i, a (i + 1) - a (i + 1) * a i ∈ I) :
    ∀ i, a i ∈ I := by
  intro i
  induction i with
  | zero => exact start
  | succ i ih =>
    have product : a (i + 1) * a i ∈ I := I.mul_mem_left _ ih
    have sum := I.add_mem (step i) product
    simpa only [sub_add_cancel] using sum
