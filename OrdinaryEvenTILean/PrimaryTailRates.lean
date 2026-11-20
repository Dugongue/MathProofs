import PrimaryTailAllWeights

namespace Mathproof.Problem17PrimaryTail
open Module LinearMap Polynomial Matrix
noncomputable section

variable {K : Type*} [Field K] [Fintype K]

abbrev SquareMatrix (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K

omit [Fintype K] in
theorem matrix_event_card (p : K[X] → Prop) (n : ℕ) :
    Nat.card {A : SquareMatrix K n // p A.charpoly} =
      Nat.card (PolyEvent p (Coord K n)) :=
  Nat.card_congr (Matrix.toLin'.toEquiv.subtypeEquiv fun A => by
    change p A.charpoly ↔ p A.toLin'.charpoly
    rw [Matrix.charpoly_toLin'])

theorem matrix_card (n : ℕ) : Nat.card (SquareMatrix K n) = Nat.card K^(n*n) := by
  rw [Nat.card_congr (Matrix.toLin'.toEquiv : SquareMatrix K n ≃ End K (Coord K n)), end_card]

theorem matrix_power_event_probability_le (f : K[X]) (hf : f.Monic) (hi : Irreducible f) (k n : ℕ) :
    (Nat.card {A : SquareMatrix K n // f^k ∣ A.charpoly} : ℝ) / Nat.card (SquareMatrix K n) ≤
      (((Nat.card K : ℝ)^f.natDegree - 1)^k)⁻¹ := by
  let q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have hqd : 2 ≤ q^f.natDegree := by
    exact (show 2 ≤ q^1 by simpa using hq).trans (Nat.pow_le_pow_right (by omega) hi.natDegree_pos)
  have hpos : (0:ℝ) < (q:ℝ)^f.natDegree - 1 := by
    exact sub_pos.mpr (show (1:ℝ) < (q:ℝ)^f.natDegree by exact_mod_cast (show 1 < q^f.natDegree by omega))
  have hcard := power_event_card_le f hf hi k n
  change Nat.card (powerEvent f k n) * (q ^ f.natDegree - 1)^k ≤ q^(n*n) at hcard
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (show 1 ≤ q^f.natDegree by omega), Nat.cast_one] at hcast
  rw [matrix_event_card, matrix_card, Nat.cast_pow]
  change (Nat.card (powerEvent f k n) : ℝ) / (q:ℝ)^(n*n) ≤ (((q:ℝ)^f.natDegree - 1)^k)⁻¹
  apply (div_le_iff₀ (by positivity)).mpr
  rw [mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hpos _)).mpr hcast

theorem matrix_even_power_event_probability_le (f : K[X]) (hf : f.Monic) (hi : Irreducible f) (k n : ℕ) :
    (Nat.card {A : SquareMatrix K n // f^(2*k) ∣ A.charpoly} : ℝ) / Nat.card (SquareMatrix K n) ≤
      (2/3:ℝ)^k := by
  have hcard := even_power_event_card_le f hf hi k n
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [matrix_event_card, matrix_card, Nat.cast_pow]
  change (Nat.card (powerEvent f (2*k) n) : ℝ) / (Nat.card K:ℝ)^(n*n) ≤ (2/3:ℝ)^k
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  rw [div_pow, div_le_div_iff₀ (pow_pos hq _) (by positivity)]
  exact hcast

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.matrix_power_event_probability_le
#print axioms Mathproof.Problem17PrimaryTail.matrix_even_power_event_probability_le
