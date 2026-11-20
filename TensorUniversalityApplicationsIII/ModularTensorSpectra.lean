import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Abel

open scoped BigOperators

namespace ModularTensorSpectra

/-- A sum over fixed-size characteristic orbits keeps only singleton fibers. -/
theorem collapse_fiber_sum {I O K : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    [CommSemiring K] (p : ℕ) [CharP K p] (tag : I → O) (fixed : O → Bool)
    (coefficient : O → K)
    (single : ∀ o, fixed o = true → (Finset.univ.filter (fun i => tag i = o)).card = 1)
    (vanish : ∀ o, fixed o = false → p ∣ (Finset.univ.filter (fun i => tag i = o)).card) :
    (∑ i, coefficient (tag i)) = ∑ o, if fixed o then coefficient o else 0 := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ tag coefficient]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.sum_const, nsmul_eq_mul]
  cases h : fixed o with
  | false =>
    have hz : ((Finset.univ.filter (fun i => tag i = o)).card : K) = 0 :=
      (CharP.cast_eq_zero_iff K p _).mpr (vanish o h)
    simp [hz]
  | true => simp [single o h]

/-- Intermediate binomial orbit sizes disappear at prime order. -/
theorem mixed_binomial_cast_zero {K : Type*} [CommSemiring K] (p i : ℕ) [CharP K p]
    (hp : p.Prime) (hi₀ : i ≠ 0) (hi : i < p) : (p.choose i : K) = 0 := by
  exact (CharP.cast_eq_zero_iff K p _).mpr (hp.dvd_choose_self hi₀ hi)

/-- Compensation of a pure-power map by its binary addition defects. -/
theorem cumulative_defect {A B : Type*} [AddCommMonoid A] [AddCommGroup B]
    (power : A → B) (hzero : power 0 = 0) (x : ℕ → A) (n : ℕ) :
    power (∑ i ∈ Finset.range n, x i) =
      (∑ i ∈ Finset.range n, power (x i)) +
      ∑ i ∈ Finset.range n,
        (power ((∑ j ∈ Finset.range i, x j) + x i) -
          power (∑ j ∈ Finset.range i, x j) - power (x i)) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih]
    abel

end ModularTensorSpectra
