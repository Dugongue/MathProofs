import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Logic.Function.Iterate

open scoped BigOperators
open Function

namespace TensorSymmetryTransfer

theorem transfer_iterate {X : Type*} (A B : X → X) (x : X)
    (commutes : Function.Commute A B) (transfers : A x = B x) (n : ℕ) :
    A^[n] x = B^[n] x := by
  exact commutes.iterate_eq_of_map_eq n transfers

theorem transfers_commute_at_state {X : Type*} (A₁ A₃ B₁ B₂ : X → X) (t : X)
    (hA : A₁ t = A₃ t) (hB : B₁ t = B₂ t)
    (h₁ : Function.Commute A₁ B₂) (h₂ : Function.Commute A₃ B₂)
    (h₃ : Function.Commute A₃ B₁) : A₁ (B₁ t) = B₁ (A₁ t) := by
  calc
    A₁ (B₁ t) = A₁ (B₂ t) := congrArg A₁ hB
    _ = B₂ (A₁ t) := h₁ t
    _ = B₂ (A₃ t) := congrArg B₂ hA
    _ = A₃ (B₂ t) := (h₂ t).symm
    _ = A₃ (B₁ t) := congrArg A₃ hB.symm
    _ = B₁ (A₃ t) := h₃ t
    _ = B₁ (A₁ t) := congrArg B₁ hA.symm

theorem normalized_label_sum {K I : Type*} [Field K] [Fintype I] (x : I → K) (v : K)
    (h : ∀ i, x i = v) (nonzero : (Fintype.card I : K) ≠ 0) :
    (∑ i, x i) / (Fintype.card I : K) = v := by
  classical
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀ _ nonzero]

theorem square_zero_prime_multiple_power {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
    (prime_ge_two : 2 ≤ p) (x t : R) (square_zero : t ^ 2 = 0) (n : ℕ) :
    (x + t) ^ (p * n) = x ^ (p * n) := by
  have hp : t ^ p = 0 := pow_eq_zero_of_le prime_ge_two square_zero
  rw [pow_mul, pow_mul, add_pow_expChar, hp, add_zero]

end TensorSymmetryTransfer
