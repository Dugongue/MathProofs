import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Mathproof.MinimumGeneration.RankIsolation

open Polynomial

/-- Distinct element weights isolate a minimum in a finite family with directed
basis exchange. The exchange direction is the one that inserts the given
element of the first basis into the second basis. -/
theorem exists_unique_minimum_basis_weight
    {ι : Type*} [LinearOrder ι] (bases : Finset (Finset ι)) (w : ι → ℕ)
    (hw : StrictMono w) (hne : bases.Nonempty)
    (hcard : ∀ I ∈ bases, ∀ J ∈ bases, I.card = J.card)
    (hex : ∀ I ∈ bases, ∀ J ∈ bases, ∀ i ∈ I, i ∉ J →
      ∃ j ∈ J, j ∉ I ∧ insert i (J.erase j) ∈ bases) :
    ∃ I ∈ bases, ∀ J ∈ bases, J ≠ I → (∑ i ∈ I, w i) < ∑ j ∈ J, w j := by
  classical
  let weight (I : Finset ι) := ∑ i ∈ I, w i
  obtain ⟨I, hI, hmin⟩ := Finset.exists_min_image bases weight hne
  refine ⟨I, hI, ?_⟩
  intro J hJ hJI
  change weight I < weight J
  by_contra! hnot
  have hminJ : ∀ K ∈ bases, weight J ≤ weight K :=
    fun K hK => hnot.trans (hmin K hK)
  have shift (P Q : Finset ι) (hP : P ∈ bases) (hQ : Q ∈ bases)
      (hqmin : ∀ K ∈ bases, weight Q ≤ weight K) (i : ι) (hi : i ∈ P \ Q)
      (hij : ∀ j ∈ Q \ P, i ≤ j) : False := by
    obtain ⟨hip, hiq⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨j, hjq, hjp, hchange⟩ := hex P hP Q hQ i hip hiq
    have hlt : w i < w j := hw (lt_of_le_of_ne (hij j (Finset.mem_sdiff.mpr ⟨hjq, hjp⟩))
      (fun heq => hjp (heq ▸ hip)))
    have hni : i ∉ Q.erase j := fun hh => hiq (Finset.mem_of_mem_erase hh)
    have hwq := hqmin _ hchange
    change (∑ a ∈ Q, w a) ≤ ∑ a ∈ insert i (Q.erase j), w a at hwq
    rw [Finset.sum_insert hni, ← Finset.sum_erase_add _ _ hjq] at hwq
    omega
  have hd₁ : (I \ J).Nonempty := by
    by_contra he
    have hs : I ⊆ J := by
      intro i hi
      by_contra hj
      exact he ⟨i, Finset.mem_sdiff.mpr ⟨hi, hj⟩⟩
    exact hJI (Finset.eq_of_subset_of_card_le hs (hcard I hI J hJ).ge).symm
  have hd₂ : (J \ I).Nonempty := by
    by_contra he
    have hs : J ⊆ I := by
      intro i hi
      by_contra hj
      exact he ⟨i, Finset.mem_sdiff.mpr ⟨hi, hj⟩⟩
    exact hJI (Finset.eq_of_subset_of_card_le hs (hcard I hI J hJ).le)
  by_cases hc : (I \ J).min' hd₁ ≤ (J \ I).min' hd₂
  · exact shift I J hI hJ hminJ _ (Finset.min'_mem _ _) (fun j hj =>
      hc.trans (Finset.min'_le _ _ hj))
  · exact shift J I hJ hI hmin _ (Finset.min'_mem _ _) (fun j hj =>
      (le_of_not_ge hc).trans (Finset.min'_le _ _ hj))

/-- An isolated nonzero monomial in a polynomial sum guarantees a nonzero
evaluation on any field grid larger than the maximum exponent. -/
theorem has_nonzero_evaluation_of_isolated_term
    {ι K : Type*} [Field K] [Fintype K]
    (terms : Finset ι) (exponent : ι → ℕ) (value : ι → K)
    (d : ℕ) (hdegree : ∀ i ∈ terms, exponent i ≤ d)
    (hfield : d < Fintype.card K) (i : ι) (hi : i ∈ terms) (hvalue : value i ≠ 0)
    (hiso : ∀ j ∈ terms, j ≠ i → exponent j = exponent i → value j = 0) :
    ∃ t : K, (∑ j ∈ terms, Polynomial.monomial (exponent j) (value j)).eval t ≠ 0 := by
  classical
  let P := ∑ j ∈ terms, Polynomial.monomial (exponent j) (value j)
  have hcoeff : P.coeff (exponent i) = value i := by
    dsimp [P]
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp only [Polynomial.coeff_monomial]
      split
      · exact hiso j hj hji (by assumption)
      · rfl
    · exact fun hn => (hn hi).elim
  have hp : P ≠ 0 := by
    intro hz
    exact hvalue (by simpa [hz] using hcoeff.symm)
  have hPd : P.natDegree ≤ d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    dsimp [P]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j hj
    simp [Polynomial.coeff_monomial, Nat.ne_of_lt ((hdegree j hj).trans_lt hn)]
  exact Polynomial.exists_eval_ne_zero_of_natDegree_lt_card P hp
    (by simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hPd.trans_lt hfield)

end Mathproof.MinimumGeneration.RankIsolation
