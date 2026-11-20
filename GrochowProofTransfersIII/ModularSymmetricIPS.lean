
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open MulAction

namespace ModularSymmetricIPS

/-- A monomial or marking orbit contributes in characteristic p exactly when
it contains a representative fixed by the chosen Sylow subgroup. -/
theorem orbit_prime_to_p_iff_contains_sylow_fixed
    {G A : Type*} [Group G] [Finite G] [MulAction G A]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (a : A) :
    (¬ p ∣ Nat.card (orbit G a)) ↔
      ∃ b : orbit G a, ∀ g : P.toSubgroup, g • (b : A) = b := by
  constructor
  · intro hn
    obtain ⟨b, hb⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (orbit G a) hn
    refine ⟨b, fun g => ?_⟩
    exact congrArg Subtype.val (mem_fixedPoints.mp hb g)
  · rintro ⟨b, hb⟩
    have le_stab : P.toSubgroup ≤ stabilizer G (b : A) := by
      intro g hg
      exact mem_stabilizer_iff.mpr (hb ⟨g, hg⟩)
    have horbit : orbit G (b : A) = orbit G a := orbit_eq_iff.mpr b.property
    rw [← horbit, Nat.card_congr (orbitEquivQuotientStabilizer G (b : A))]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_stab))

/-- Any coefficient can be produced by a constant assignment on an orbit
of length prime to p. This is the normalization used in the equivariant lift. -/
theorem orbit_sum_normalization
    {K A : Type*} [Field K] [Fintype A] {p : ℕ} [CharP K p]
    (c : K) (h : ¬ p ∣ Fintype.card A) :
    (∑ _a : A, c / (Fintype.card A : K)) = c := by
  classical
  have hn : (Fintype.card A : K) ≠ 0 :=
    fun hz => h ((CharP.cast_eq_zero_iff K p _).mp hz)
  simp [nsmul_eq_mul, hn, mul_div_cancel₀]


/-- The formula obtained by interpolating the four assignments in the 2-to-1
pigeonhole equations and correcting the residual by Boolean equations. -/
def phpTwoCertificate {K : Type*} [CommRing K]
    (x y row₁ row₂ collision grid₁ grid₂ : K) : K :=
  (1 - x) * (1 - y) * row₁ * row₂ -
    x * (1 - y) * row₂ - (1 - x) * y * row₁ +
    x * y * collision - ((1 + y) * grid₁ + (1 + x) * grid₂ + 2 * grid₁ * grid₂)

theorem phpTwoCertificate_zero {K : Type*} [CommRing K] (x y : K) :
    phpTwoCertificate x y 0 0 0 0 0 = 0 := by
  simp [phpTwoCertificate]

theorem phpTwoCertificate_substitute {K : Type*} [CommRing K] (x y : K) :
    phpTwoCertificate x y (x - 1) (y - 1) (x * y) (x ^ 2 - x) (y ^ 2 - y) = 1 := by
  unfold phpTwoCertificate
  ring

theorem phpTwoCertificate_swap {K : Type*} [CommRing K]
    (x y row₁ row₂ collision grid₁ grid₂ : K) :
    phpTwoCertificate x y row₁ row₂ collision grid₁ grid₂ =
      phpTwoCertificate y x row₂ row₁ collision grid₂ grid₁ := by
  unfold phpTwoCertificate
  ring

end ModularSymmetricIPS
