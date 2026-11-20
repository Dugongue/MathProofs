import RepeatedBudget
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators Polynomial Classical

namespace EvenTI.Primary

open Polynomial UniqueFactorizationMonoid Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

abbrev DegreeIrreducible (K : Type*) [Field K] (d : ℕ) :=
  {p : K[X] // p.Monic ∧ Irreducible p ∧ p.natDegree = d}

private def coeffs (d : ℕ) (p : DegreeIrreducible K d) : Fin d → K :=
  fun i => p.val.coeff i

private theorem coeffs_injective (d : ℕ) : Function.Injective (coeffs (K := K) d) := by
  intro a b he
  apply Subtype.ext
  apply Polynomial.ext
  intro i
  by_cases hi : i < d
  · exact congrFun he ⟨i, hi⟩
  by_cases hei : i = d
  · have ha := a.property.1.coeff_natDegree
    have hb := b.property.1.coeff_natDegree
    rw [a.property.2.2] at ha
    rw [b.property.2.2] at hb
    rw [hei, ha, hb]
  · have hai : a.val.natDegree < i := by rw [a.property.2.2]; omega
    have hbi : b.val.natDegree < i := by rw [b.property.2.2]; omega
    rw [coeff_eq_zero_of_natDegree_lt hai, coeff_eq_zero_of_natDegree_lt hbi]

instance (d : ℕ) : Fintype (DegreeIrreducible K d) := by
  classical
  exact Fintype.ofInjective (coeffs d) (coeffs_injective d)

theorem degreeIrreducible_card_le (d : ℕ) :
    Fintype.card (DegreeIrreducible K d) ≤ Fintype.card K ^ d := by
  calc
    _ ≤ Fintype.card (Fin d → K) := Fintype.card_le_of_injective _ (coeffs_injective d)
    _ = _ := by simp

def mean {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ x, X x) / Fintype.card Ω

def event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact mean fun x => if P x then 1 else 0

theorem mean_mono {Ω : Type*} [Fintype Ω] {X Y : Ω → ℝ} (h : ∀ x, X x ≤ Y x) :
    mean X ≤ mean Y :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (X : Ω → ℝ) :
    mean (fun x => c * X x) = c * mean X := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_sum {Ω J : Type*} [Fintype Ω] (s : Finset J) (X : J → Ω → ℝ) :
    mean (fun x => ∑ j ∈ s, X j x) = ∑ j ∈ s, mean (X j) := by
  classical
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem event_eq_card {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    event P = (Nat.card {x : Ω // P x} : ℝ) / Nat.card Ω := by
  classical
  simp [event, mean, Nat.card_eq_fintype_card, Fintype.card_subtype]

def thresholdWeight (d k : ℕ) : ℝ := d * (2*k+3 : ℕ)^2

/-- Charge a repeated factor of multiplicity m to the even threshold
2 * (m / 2). The square weight rounds m up by at most one. -/
theorem budget_le_threshold_sum (f : K[X]) (hf : f ≠ 0) (n : ℕ) (hn : f.natDegree ≤ n) :
    (repeatedBudget f : ℝ) ≤
      ∑ d : Fin (n+1), ∑ p : DegreeIrreducible K d, ∑ k ∈ Finset.range (n+1),
        if p.val ^ (2*(k+1)) ∣ f then thresholdWeight d k else 0 := by
  classical
  let S := (normalizedFactors f).toFinset
  let D := Σ d : Fin (n+1), DegreeIrreducible K d
  have hP (p : S) : Irreducible p.val ∧ p.val.Monic ∧ p.val ∣ f :=
    (Polynomial.mem_normalizedFactors_iff hf).mp (Multiset.mem_toFinset.mp p.property)
  have hdeg (p : S) : p.val.natDegree ≤ n :=
    (natDegree_le_of_dvd (hP p).2.2 hf).trans hn
  let ix (p : S) : D :=
    ⟨⟨p.val.natDegree, Nat.lt_succ_of_le (hdeg p)⟩, ⟨p.val, (hP p).2.1, (hP p).1, rfl⟩⟩
  let w (x : D) := ∑ k ∈ Finset.range (n+1),
    if x.2.val ^ (2*(k+1)) ∣ f then thresholdWeight x.1 k else 0
  have hw (x : D) : 0 ≤ w x := by
    apply Finset.sum_nonneg
    intro k _
    split <;> first | exact le_rfl | (unfold thresholdWeight; positivity)
  have hx (p : S) :
      ((if 2 ≤ (normalizedFactors f).count p.val then
        p.val.natDegree * ((normalizedFactors f).count p.val)^2 else 0 : ℕ) : ℝ) ≤ w (ix p) := by
    let m := (normalizedFactors f).count p.val
    by_cases hm : 2 ≤ m
    · have hpow : p.val ^ m ∣ f :=
        (power_dvd_iff_count (k := m) (hP p).1 (hP p).2.1 hf).mpr le_rfl
      have hmul := (natDegree_le_of_dvd hpow hf).trans hn
      rw [natDegree_pow] at hmul
      have hmn : m ≤ n := calc
        m = m * 1 := (Nat.mul_one _).symm
        _ ≤ m * p.val.natDegree := Nat.mul_le_mul_left _ (hP p).1.natDegree_pos
        _ ≤ n := hmul
      let k := m / 2 - 1
      have hk : k ∈ Finset.range (n+1) := Finset.mem_range.mpr (by dsimp [k]; omega)
      have hkpow : 2 * (k+1) ≤ m := by dsimp [k]; omega
      have hkup : m ≤ 2*k+3 := by dsimp [k]; omega
      have hdvd : p.val ^ (2*(k+1)) ∣ f := (pow_dvd_pow _ hkpow).trans hpow
      change ((if 2 ≤ m then p.val.natDegree * m^2 else 0 : ℕ) : ℝ) ≤ w (ix p)
      rw [if_pos hm]
      calc
        _ ≤ thresholdWeight p.val.natDegree k := by
          unfold thresholdWeight
          push_cast
          gcongr
          exact_mod_cast hkup
        _ = (if (ix p).2.val ^ (2*(k+1)) ∣ f then thresholdWeight (ix p).1 k else 0) := by
          change _ = (if p.val ^ (2*(k+1)) ∣ f then thresholdWeight p.val.natDegree k else 0)
          rw [if_pos hdvd]
        _ ≤ w (ix p) := by
          exact Finset.single_le_sum
            (f := fun i => if (ix p).2.val ^ (2*(i+1)) ∣ f then thresholdWeight (ix p).1 i else 0)
            (fun i _ => by split <;> first | exact le_rfl | (unfold thresholdWeight; positivity)) hk
    · change ((if 2 ≤ m then p.val.natDegree * m^2 else 0 : ℕ) : ℝ) ≤ w (ix p)
      simpa [hm] using hw (ix p)
  calc
    (repeatedBudget f : ℝ) =
      ∑ p : S, ((if 2 ≤ (normalizedFactors f).count p.val then
        p.val.natDegree * ((normalizedFactors f).count p.val)^2 else 0 : ℕ) : ℝ) := by
      rw [repeatedBudget, Nat.cast_sum]
      exact (Finset.sum_attach S _).symm
    _ ≤ ∑ p : S, w (ix p) := Finset.sum_le_sum fun p _ => hx p
    _ = ∑ p ∈ (Finset.univ : Finset S).image ix, w p := by
      symm
      apply Finset.sum_image
      intro a _ b _ h
      apply Subtype.ext
      exact congrArg (fun z : D => z.2.val) h
    _ ≤ ∑ p : D, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun p _ _ => hw p)
    _ = _ := Fintype.sum_sigma _

variable {Ω : Type*} [Fintype Ω]

theorem mean_budget_le_threshold_events (f : Ω → K[X]) (n : ℕ)
    (hne : ∀ x, f x ≠ 0) (hdeg : ∀ x, (f x).natDegree ≤ n) :
    mean (fun x => (repeatedBudget (f x) : ℝ)) ≤
      ∑ d : Fin (n+1), ∑ p : DegreeIrreducible K d, ∑ k ∈ Finset.range (n+1),
        thresholdWeight d k * event (fun x => p.val ^ (2*(k+1)) ∣ f x) := by
  classical
  refine (mean_mono fun x => budget_le_threshold_sum (f x) (hne x) n (hdeg x)).trans ?_
  simp only [mean_sum]
  refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun k _ => ?_
  rw [event, ← mean_mul]
  apply mean_mono
  intro x
  by_cases hx : p.val ^ (2 * (k + 1)) ∣ f x <;> simp [hx]

/-- Maximum average budget controls a total-budget gate irrespective of dependencies. -/
theorem event_sum_budget_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (hX : ∀ i x, 0 ≤ X i x)
    (B t : ℝ) (ht : 0 < t) (hB : ∀ i, mean (X i) ≤ B) :
    event (fun x => (Fintype.card ι : ℝ) * t < ∑ i, X i x) ≤ B / t := by
  classical
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by positivity
  have hNt : 0 < N*t := mul_pos hN ht
  apply (le_div_iff₀ ht).mpr
  apply le_of_mul_le_mul_left _ hN
  calc
    N * (event (fun x => N*t < ∑ i, X i x) * t) =
        mean (fun x => (N*t) * (if N*t < ∑ i, X i x then (1 : ℝ) else 0)) := by
      rw [mean_mul, event]
      ring
    _ ≤ mean (fun x => ∑ i, X i x) := by
      apply mean_mono
      intro x
      split_ifs with h
      · simpa using h.le
      · exact (by simpa using Finset.sum_nonneg (fun i _ => hX i x))
    _ ≤ N * B := by
      rw [mean_sum]
      simpa [N] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hB i)

#print axioms budget_le_threshold_sum
#print axioms mean_budget_le_threshold_events
#print axioms event_sum_budget_le

end
end EvenTI.Primary
