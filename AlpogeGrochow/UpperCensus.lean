import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Preorder.Finite

open scoped BigOperators

namespace EtaleOrbitCertificate

/-- Weighted fixed-point counts obtained by evaluating at subgroup generators. -/
noncomputable def upperCensus {ι : Type*} [Fintype ι] [PartialOrder ι]
    (weight : ι → ℤ) (multiplicity : ι → ℤ) (i : ι) : ℤ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j => i ≤ j), weight j * multiplicity j

theorem upperCensus_injective {ι : Type*} [Fintype ι] [PartialOrder ι]
    (weight : ι → ℤ) (nonzero : ∀ i, weight i ≠ 0) :
    Function.Injective (upperCensus weight) := by
  classical
  intro a b equal
  by_contra different
  let differing := Finset.univ.filter (fun i => a i ≠ b i)
  have existsDifferent : differing.Nonempty := by
    by_contra empty
    apply different
    funext i
    by_contra hi
    exact empty ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, maximal⟩ := differing.exists_maximal existsDifferent
  have hi : a i ≠ b i := (Finset.mem_filter.mp maximal.1).2
  let tail := Finset.univ.filter (fun j => i ≤ j)
  have htail : ∑ j ∈ tail, (weight j * a j - weight j * b j) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun equal i)
  have hsingle :
      ∑ j ∈ tail, (weight j * a j - weight j * b j) =
        weight i * a i - weight i * b i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hjle : i ≤ j := (Finset.mem_filter.mp hj).2
      have hab : a j = b j := by
        by_contra hne
        have hjmem : j ∈ differing := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
        exact hji (le_antisymm (maximal.2 hjmem hjle) hjle)
      rw [hab, sub_self]
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_rfl⟩)).elim
  rw [hsingle] at htail
  exact hi (Int.eq_of_mul_eq_mul_left (nonzero i) (sub_eq_zero.mp htail))

end EtaleOrbitCertificate
