import Mathlib.Tactic

namespace FaithfulActionAdvances

theorem orbitSplitCost (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a + b ≤ a * b := by
  have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (2 : ℤ) ≤ b := by exact_mod_cast hb
  have h : (a : ℤ) + b ≤ (a : ℤ) * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')]
  exact_mod_cast h

theorem hyperplaneFanoutBound (p d : ℕ) (hp : 2 ≤ p) :
    d ≤ p ^ (d - 1) := by
  cases d with
  | zero => exact Nat.zero_le _
  | succ d =>
    simp only [Nat.succ_sub_one]
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ]
      calc
        d.succ.succ ≤ 2 * d.succ := by omega
        _ ≤ p * p ^ d := Nat.mul_le_mul hp ih
        _ = p ^ d * p := Nat.mul_comm _ _

theorem detectorZeroOnSpan {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (mark : V →ₗ[F] F) (generators : Set V)
    (h : ∀ x ∈ generators, mark x = 0) {v : V}
    (hv : v ∈ Submodule.span F generators) : mark v = 0 := by
  have hle : Submodule.span F generators ≤ LinearMap.ker mark :=
    Submodule.span_le.mpr (by
      intro x hx
      exact LinearMap.mem_ker.mpr (h x hx))
  exact LinearMap.mem_ker.mp (hle hv)

theorem normalizedDetector {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (mark : V →ₗ[F] F) (v : V) (h : mark v ≠ 0) :
    mark ((mark v)⁻¹ • v) = 1 := by
  simp [h]

theorem syndromeCoordinateStep {F : Type*} [Field F] (x c d a b : F) :
    (a, b) + x • ((c, d) : F × F) = (a + x * c, b + x * d) := by
  rfl

theorem offsetRemovedFromThreshold (v e alpha k : ℕ)
    (ha : alpha ≤ v) (hk : k ≤ v) :
    v + e - alpha ≤ v + e - k ↔ k ≤ alpha := by
  omega

end FaithfulActionAdvances
