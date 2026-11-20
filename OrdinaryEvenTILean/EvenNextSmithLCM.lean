import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! The LCM image-membership interface from Problem 1.7's
`Problem17LCMProjection`, replayed with narrow Mathlib imports. -/

open scoped BigOperators
/-! For a homomorphism of commutative groups, test image membership by
projecting to the torsion orders in a finite list. This is the group-theoretic
LCM reduction used in the ongoing Problem 1.7 comparator formalization. -/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace EvenOrdinaryTI.LCMProjection


variable {I : Type*} [Fintype I]

def commonOrder (m : I → ℕ) : ℕ := Finset.univ.lcm m

theorem order_dvd_common (m : I → ℕ) (i : I) : m i ∣ commonOrder m :=
  Finset.dvd_lcm (Finset.mem_univ i)

theorem commonOrder_pos (m : I → ℕ) (hm : ∀ i, 0 < m i) : 0 < commonOrder m := by
  have h : commonOrder m ∣ ∏ i, m i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem m hi
  exact Nat.pos_of_dvd_of_pos h (Finset.prod_pos fun i _ => hm i)

theorem commonOrder_dvd_quotients (m : I → ℕ) (hm : ∀ i, 0 < m i)
    {d : ℕ} (hd : d ∣ commonOrder m) (hE : ∀ i, d ∣ commonOrder m/m i) : d = 1 := by
  have hp := commonOrder_pos m hm
  have hdpos := Nat.pos_of_dvd_of_pos hd hp
  have h : commonOrder m ∣ commonOrder m/d := Finset.lcm_dvd fun i _ => by
    have hh : m i*d ∣ commonOrder m := (Nat.dvd_div_iff_mul_dvd (order_dvd_common m i)).mp (hE i)
    exact (Nat.dvd_div_iff_mul_dvd hd).mpr (by simpa [Nat.mul_comm] using hh)
  have h' := Nat.div_pos (Nat.le_of_dvd hp hd) hdpos
  have hle := Nat.le_of_dvd h' h
  by_contra! hne
  exact (Nat.not_lt_of_ge hle) (Nat.div_lt_self hp (by omega))

theorem lcm_projection_iff {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (m : I → ℕ) (hm : ∀ i, 0 < m i) (c : H)
    (hg : ∀ g : G, g ^ commonOrder m = 1) (hc : c ^ commonOrder m = 1) :
    (∃ g, f g = c) ↔
      ∀ i, ∃ g, g ^ m i = 1 ∧ f g = c ^ (commonOrder m/m i) := by
  constructor
  · rintro ⟨g,h⟩ i
    refine ⟨g ^ (commonOrder m/m i),?_,by rw [map_pow,h]⟩
    rw [← pow_mul,Nat.div_mul_cancel (order_dvd_common m i),hg]
  · intro h
    let q := QuotientGroup.mk' f.range
    let D := orderOf (q c)
    have hD : D ∣ commonOrder m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,hc,map_one])
    have hE (i : I) : D ∣ commonOrder m/m i := by
      obtain ⟨x,_,hx⟩ := h i
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow,← hx]
      exact (QuotientGroup.eq_one_iff (f x)).mpr ⟨x,rfl⟩
    have hD1 := commonOrder_dvd_quotients m hm hD hE
    have hq : q c = 1 := by
      have hh := pow_orderOf_eq_one (q c)
      change (q c)^D = 1 at hh
      rwa [hD1,pow_one] at hh
    exact (QuotientGroup.eq_one_iff c).mp hq

#print axioms lcm_projection_iff
end EvenOrdinaryTI.LCMProjection
