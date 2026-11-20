import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.BigOperators

open scoped BigOperators

namespace TISLNegativeAtlas

theorem coset_sum_of_normalized_integer_weights
    {ι G : Type*} [AddCommGroup G] (s : Finset ι) (H : AddSubgroup G)
    (c : G) (v : ι → G) (a : ι → ℤ)
    (hv : ∀ i ∈ s, v i - c ∈ H)
    (ha : (∑ i ∈ s, a i) = 1) :
    (∑ i ∈ s, a i • v i) - c ∈ H := by
  have hs : (∑ i ∈ s, a i • (v i - c)) ∈ H := by
    exact sum_mem fun i hi => H.zsmul_mem (hv i hi) (a i)
  have hsum (t : Finset ι) : (∑ i ∈ t, a i • c) = (∑ i ∈ t, a i) • c := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t h it => simp [Finset.sum_insert h, it, add_zsmul]
  simp_rw [zsmul_sub] at hs
  rw [Finset.sum_sub_distrib, hsum s, ha, one_zsmul] at hs
  exact hs

theorem multiple_weights_act_trivially
    {G : Type*} [AddCommGroup G] (m k : ℤ) (v : G)
    (h : m • v = 0) : (m * k) • v = 0 := by
  rw [mul_comm, mul_zsmul, h, zsmul_zero]

end TISLNegativeAtlas
