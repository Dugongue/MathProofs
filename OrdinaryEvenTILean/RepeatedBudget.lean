import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace Mathproof.Problem17RepeatedBudget
open scoped BigOperators Polynomial
open Polynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K]

noncomputable def repeatedBudget (f : K[X]) : ℕ := by
  classical
  let fs := normalizedFactors f
  exact ∑ p ∈ fs.toFinset, if 2 ≤ fs.count p then p.natDegree * (fs.count p)^2 else 0

theorem power_dvd_iff_count {p f : K[X]} {k : ℕ}
    (hi : Irreducible p) (hm : p.Monic) (hf : f ≠ 0) [DecidableEq K] :
    p ^ k ∣ f ↔ k ≤ (normalizedFactors f).count p := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hi.ne_zero) hf,
    normalizedFactors_of_irreducible_pow hi,
    (Polynomial.normalize_eq_self_iff_monic hi.ne_zero).mpr hm, Multiset.le_count_iff_replicate_le]

theorem degree_bounded_finite [Finite K] (E : ℕ) :
    Set.Finite {f : K[X] | f.natDegree ≤ E} := by
  let g (f : {f : K[X] // f.natDegree ≤ E}) (i : Fin (E + 1)) := f.val.coeff i
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply Polynomial.ext
    intro i
    by_cases hi : i < E + 1
    · exact congrFun h ⟨i, hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt a.property (by omega)),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt b.property (by omega))]
  have : Finite {f : K[X] // f.natDegree ≤ E} := Finite.of_injective g hg
  exact @Set.toFinite (K[X]) {f : K[X] | f.natDegree ≤ E} (Finite.of_injective g hg)

theorem budget_le_of_cutoffs [Finite K] (E m : ℕ) :
    ∃ B : ℕ, ∀ f : K[X], f ≠ 0 →
      (∀ p : K[X], p.Monic → Irreducible p → E < p.natDegree → ¬ p ^ 2 ∣ f) →
      (∀ p : K[X], p.Monic → Irreducible p → ¬ p ^ (m + 1) ∣ f) →
      repeatedBudget f ≤ B := by
  classical
  let S := (degree_bounded_finite (K := K) E).toFinset
  refine ⟨S.card * (E * m^2), fun f hf hE hm => ?_⟩
  let F := (normalizedFactors f).toFinset.filter fun p => 2 ≤ (normalizedFactors f).count p
  have ht (p : K[X]) (hp : p ∈ F) :
      p ∈ S ∧ p.natDegree * ((normalizedFactors f).count p)^2 ≤ E * m^2 := by
    obtain ⟨hp, hk⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi, hmon, -⟩ := (Polynomial.mem_normalizedFactors_iff hf).mp
      (Multiset.mem_toFinset.mp hp)
    have hc := power_dvd_iff_count (k := 2) hi hmon hf
    have hd : p.natDegree ≤ E := Nat.le_of_not_gt (fun h => hE p hmon hi h (hc.mpr hk))
    have hm' : (normalizedFactors f).count p ≤ m := by
      by_contra! h
      exact hm p hmon hi ((power_dvd_iff_count hi hmon hf).mpr h)
    refine ⟨(Set.Finite.mem_toFinset _).mpr hd, ?_⟩
    gcongr
  have hsub : F ⊆ S := fun p hp => (ht p hp).1
  calc
    repeatedBudget f = ∑ p ∈ F, p.natDegree * ((normalizedFactors f).count p)^2 := by
      simp only [repeatedBudget, F, Finset.sum_filter]
    _ ≤ ∑ _p ∈ F, E * m^2 := Finset.sum_le_sum fun p hp => (ht p hp).2
    _ = F.card * (E * m^2) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)

end Mathproof.Problem17RepeatedBudget

#print axioms Mathproof.Problem17RepeatedBudget.budget_le_of_cutoffs

