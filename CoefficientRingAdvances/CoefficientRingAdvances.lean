import Mathlib.Tactic
import Mathlib.Algebra.CharP.Lemmas

namespace CoefficientRingAdvances

theorem binaryPrecision {R : Type*} [CommRing R] (x y : R) (s : ℕ) (hs : 1 ≤ s)
    (h : (2 : R) ^ s ∣ x - y) (r : ℕ) :
    (2 : R) ^ (s + r) ∣ x ^ (2 ^ r) - y ^ (2 ^ r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    obtain ⟨a, ha⟩ := ih
    have hs' : 1 ≤ s + r := by omega
    obtain ⟨k, hk⟩ : ∃ k, s + r = k + 1 := ⟨s + r - 1, by omega⟩
    have ha' : x ^ (2 ^ r) - y ^ (2 ^ r) = 2 * (2 ^ k * a) := by
      rw [ha, hk, pow_succ]
      ring
    have hb : x ^ (2 ^ r) + y ^ (2 ^ r) = 2 * (y ^ (2 ^ r) + 2 ^ k * a) := by
      linear_combination ha'
    refine ⟨a * (y ^ (2 ^ r) + 2 ^ k * a), ?_⟩
    rw [pow_succ (2 : ℕ), pow_mul, pow_mul, Nat.add_succ, pow_succ (2 : R)]
    calc
      _ = (x ^ (2 ^ r) - y ^ (2 ^ r)) * (x ^ (2 ^ r) + y ^ (2 ^ r)) := by ring
      _ = _ := by rw [ha, hb]; ring

theorem primePrecision {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime)
    (x y : R) (s : ℕ) (hs : 1 ≤ s)
    (h : (p : R) ^ s ∣ x - y) (r : ℕ) :
    (p : R) ^ (s + r) ∣ x ^ (p ^ r) - y ^ (p ^ r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    obtain ⟨a, ha⟩ := ih
    let X := x ^ (p ^ r)
    let Y := y ^ (p ^ r)
    let z := (p : R) ^ (s + r) * a
    have hxy : X = Y + z := by
      change x ^ (p ^ r) = y ^ (p ^ r) + (p : R) ^ (s + r) * a
      linear_combination ha
    obtain ⟨b, hb⟩ := exists_add_pow_prime_eq hp Y z
    have hbd := Nat.mul_le_mul_left (s + r) hp.two_le
    let k := (s + r) * p - (s + r + 1)
    have hk : (s + r) * p = (s + r + 1) + k := by
      dsimp [k]
      omega
    have hz : z ^ p = (p : R) ^ (s + r + 1) * ((p : R) ^ k * a ^ p) := by
      dsimp only [z]
      rw [mul_pow, ← pow_mul, hk, pow_add]
      ring
    refine ⟨(p : R) ^ k * a ^ p + Y * a * b, ?_⟩
    rw [Nat.add_succ, pow_succ p r, pow_mul, pow_mul]
    change X ^ p - Y ^ p = (p : R) ^ (s + r + 1) * ((p : R) ^ k * a ^ p + Y * a * b)
    rw [hxy, hb, hz, pow_succ (p : R)]
    dsimp only [z]
    ring

theorem scalingFrobenius {R : Type*} [CommRing R] (p r : ℕ)
    [ExpChar R p] (z : R) :
    (1 + z) ^ (p ^ r) = 1 + z ^ (p ^ r) := by
  rw [add_pow_expChar_pow, one_pow]

theorem layerDisplacement {M : Type*} [AddCommGroup M]
    (g h : M →+ M) (v : M) (hfix : g (h v - v) = h v - v) :
    g (h v) - v = (g v - v) + (h v - v) := by
  calc
    g (h v) - v = (g v - v) + (g (h v) - g v) := by abel
    _ = (g v - v) + (h v - v) := by rw [← map_sub, hfix]

end CoefficientRingAdvances
