import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

theorem mixedCubeMem {R : Type*} [CommRing R] (I : Ideal R) (x y : R)
    (h : x ^ 2 * y ∈ I ∨ x * y ^ 2 ∈ I) : (x * y) ^ 3 ∈ I := by
  rcases h with h | h
  · rw [show (x * y) ^ 3 = (x * y ^ 2) * (x ^ 2 * y) by ring]
    exact I.mul_mem_left _ h
  · rw [show (x * y) ^ 3 = (x ^ 2 * y) * (x * y ^ 2) by ring]
    exact I.mul_mem_left _ h
