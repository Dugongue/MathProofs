import EvenP2SpectralBasic

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical Polynomial
open Polynomial UniqueFactorizationMonoid Mathproof.Problem17RepeatedBudget

noncomputable section

private def multiplicityCost (d m : ℕ) : ℕ := if 2 ≤ m then d * m^2 else 0

private theorem zero_padding_term (m k : ℕ) :
    multiplicityCost 1 (m+2*k) ≤ 2 * multiplicityCost 1 m + (2+8*k^2) := by
  have hu : multiplicityCost 1 (m+2*k) ≤ (m+2*k)^2 := by
    unfold multiplicityCost
    split <;> simp
  have hq : (m+2*k)^2 ≤ 2*m^2+8*k^2 := by
    exact_mod_cast (show ((m : ℤ)+2*k)^2 ≤ 2*(m : ℤ)^2+8*(k : ℤ)^2 from
      by nlinarith [sq_nonneg ((m : ℤ)-2*k)])
  apply hu.trans
  apply hq.trans
  by_cases h : 2 ≤ m
  · simp [multiplicityCost, h]
  · have hm : m^2 ≤ 1 := by
      have hm' : m ≤ 1 := by omega
      simpa using Nat.pow_le_pow_left hm' 2
    simp [multiplicityCost, h]
    omega

variable {K : Type*} [Field K]

private theorem factors_X_even (k : ℕ) :
    normalizedFactors ((X : K[X])^(2*k)) = Multiset.replicate (2*k) X := by
  rw [normalizedFactors_of_irreducible_pow Polynomial.irreducible_X,
    (Polynomial.normalize_eq_self_iff_monic Polynomial.X_ne_zero).mpr Polynomial.monic_X]

private def term (S : Multiset K[X]) (f : K[X]) : ℕ :=
  multiplicityCost f.natDegree (S.count f)

/-- Adding a radical of width k pads the live characteristic polynomial
by X^(2k) and costs only a quadratic allowance in k. -/
theorem repeatedBudget_zero_padding {p : K[X]} (hp : p ≠ 0) (k : ℕ) :
    repeatedBudget (p * X^(2*k)) ≤ 2 * repeatedBudget p + (2+8*k^2) := by
  let F := normalizedFactors p
  let G := normalizedFactors (p * X^(2*k))
  let U := insert X F.toFinset
  let C := 2+8*k^2
  have hG : G = F + Multiset.replicate (2*k) X := by
    exact (normalizedFactors_mul hp (pow_ne_zero _ Polynomial.X_ne_zero)).trans
      (congrArg (F + ·) (factors_X_even k))
  have hsub : G.toFinset ⊆ U := by
    intro f hf
    rw [hG, Multiset.mem_toFinset, Multiset.mem_add] at hf
    rcases hf with h | h
    · exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
    · obtain rfl := Multiset.eq_of_mem_replicate h
      exact Finset.mem_insert_self _ _
  have ht (f : K[X]) : term G f ≤ 2*term F f + if f=X then C else 0 := by
    unfold term
    rw [hG, Multiset.count_add, Multiset.count_replicate]
    by_cases hf : f = X
    · subst f
      simpa [C, Polynomial.natDegree_X] using zero_padding_term (F.count X) k
    · simp only [hf, Ne.symm hf, if_false, add_zero]
      omega
  have hbase : (∑ f ∈ U, term F f) = ∑ f ∈ F.toFinset, term F f := by
    classical
    by_cases hX : X ∈ F.toFinset
    · simp [U, hX]
    · have hcount : F.count X = 0 := Multiset.count_eq_zero.mpr (by simpa using hX)
      simp [U, Finset.sum_insert hX, term, multiplicityCost, hcount]
  change (∑ f ∈ G.toFinset, term G f) ≤ 2*(∑ f ∈ F.toFinset, term F f)+C
  calc
    _ ≤ ∑ f ∈ U, term G f := Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ f ∈ U, (2*term F f + if f=X then C else 0) :=
      Finset.sum_le_sum fun f _ => ht f
    _ = _ := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hbase, U]

#print axioms repeatedBudget_zero_padding

end
end Mathproof.EvenTI.OrderFour
