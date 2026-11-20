import EvenP2Mean
import EvenPrimaryMoment
import EvenPrimaryGate

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Classical Polynomial Matrix
open Polynomial Matrix EvenTI.Primary Mathproof.EvenOrdinaryTISingular
open Mathproof.Problem17RepeatedBudget UniqueFactorizationMonoid

noncomputable section

theorem repeatedBudget_le_degree_sq {K : Type*} [Field K]
    {p : K[X]} (hp : p.Monic) : repeatedBudget p ≤ p.natDegree ^ 2 := by
  let F := normalizedFactors p
  have hm (g : K[X]) (hg : g ∈ F) : g.Monic := by
    exact ((Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hg).2.1
  have hprod : F.prod = p := by
    change (normalizedFactors p).prod = p
    rw [prod_normalizedFactors_eq hp.ne_zero, (Polynomial.normalize_eq_self_iff_monic hp.ne_zero).mpr hp]
  have hdeg : (∑ f ∈ F.toFinset, F.count f * f.natDegree) = p.natDegree := by
    calc
      _ = (F.map Polynomial.natDegree).sum :=
        (Finset.sum_multiset_map_count F Polynomial.natDegree).symm
      _ = _ := by rw [← natDegree_multiset_prod_of_monic _ hm, hprod]
  change (∑ f ∈ F.toFinset, if 2 ≤ F.count f then f.natDegree * (F.count f)^2 else 0) ≤ _
  calc
    _ ≤ ∑ f ∈ F.toFinset, (F.count f * f.natDegree) * p.natDegree := by
      apply Finset.sum_le_sum
      intro f hf
      split_ifs with h
      · have hmF := Multiset.mem_toFinset.mp hf
        obtain ⟨hi, hMonic, _⟩ := (Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hmF
        have hn := natDegree_le_of_dvd
          ((power_dvd_iff_count hi hMonic hp.ne_zero).mpr (show F.count f ≤ F.count f from le_rfl))
          hp.ne_zero
        rw [natDegree_pow] at hn
        have hfn : 1 ≤ f.natDegree := Nat.succ_le_of_lt hi.natDegree_pos
        have hmult : F.count f ≤ p.natDegree := by
          calc
            _ = 1 * F.count f := by simp
            _ ≤ f.natDegree * F.count f := Nat.mul_le_mul_right _ hfn
            _ ≤ _ := by simpa [Nat.mul_comm] using hn
        rw [pow_two, ← mul_assoc, mul_comm f.natDegree (F.count f)]
        exact Nat.mul_le_mul_left _ hmult
      · exact Nat.zero_le _
    _ = _ := by rw [← Finset.sum_mul, hdeg, pow_two]

theorem primary_pointwise_cap {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    (repeatedBudget A.charpoly : ℝ) ≤ (n^2 : ℕ) := by
  have h := repeatedBudget_le_degree_sq A.charpoly_monic
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  exact_mod_cast h

theorem square_mul_field_decay {K : Type*} [Field K] [Fintype K] (n : ℕ)
    (hn : 2 ≤ n) :
    (n^2 : ℕ) * ((Fintype.card K : ℝ)^(n^2))⁻¹ ≤ 1 := by
  let q := Fintype.card K
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hb (k : ℕ) : k ≤ q^k := by
    induction k with
    | zero => simp
    | succ k hk =>
      have hp : 0 < q^k := pow_pos (by omega) _
      rw [pow_succ]
      have hm := Nat.mul_le_mul_left (q^k) hq
      omega
  have hcast : (↑(n^2) : ℝ) ≤ (q : ℝ)^(n^2) := by exact_mod_cast hb (n^2)
  rw [← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr hcast

theorem spectral_gate_of_mode_means {K Ω J : Type*} [Field K] [Fintype K]
    [Fintype Ω] [Fintype J] [Nonempty J] {n : ℕ} (hn : 2 ≤ n)
    (A : J → Ω → Matrix (Fin n) (Fin n) K) (C : ℝ)
    (hMean : ∀ j, mean (fun x => (repeatedBudget (A j x).charpoly : ℝ)) ≤ C) :
    uniformFraction Ω (fun x => n^(Fintype.card J) <
      (Fintype.card K)^(∑ j, repeatedBudget (A j x).charpoly)) ≤
        C * Real.log (Fintype.card K) / Real.log n := by
  rw [← event_as_fraction]
  exact event_pow_gate_le (fun j x => repeatedBudget (A j x).charpoly) C hMean _ _
    Fintype.one_lt_card hn

#print axioms repeatedBudget_le_degree_sq
#print axioms square_mul_field_decay
#print axioms spectral_gate_of_mode_means

end
end Mathproof.EvenTI.Singular.Coverage
