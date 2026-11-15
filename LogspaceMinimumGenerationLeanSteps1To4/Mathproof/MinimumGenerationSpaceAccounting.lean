import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

namespace Mathproof.MinimumGeneration

private theorem pow_sum_log_le_prod (kernels : List ℕ)
    (positive : ∀ a ∈ kernels, a ≠ 0) :
    2 ^ (kernels.map Nat.log2).sum ≤ kernels.prod := by
  induction kernels with
  | nil => simp
  | cons a ks ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Nat.pow_add]
    exact Nat.mul_le_mul
      ((Nat.le_log2 (positive a (by simp))).1 le_rfl)
      (ih (fun k hk => positive k (by simp [hk])))

/-- Logarithmic labels from successive kernel cardinalities fit in one
logarithm of the ambient order when the kernel sizes multiply to at most it. -/
theorem kernelLabelWidths_le (kernels : List ℕ) (order : ℕ)
    (positive : ∀ a ∈ kernels, a ≠ 0) (hprod : kernels.prod ≤ order) :
    (kernels.map Nat.log2).sum ≤ Nat.log2 order := by
  have hpow := (pow_sum_log_le_prod kernels positive).trans hprod
  have hp := Nat.pow_pos (n := (kernels.map Nat.log2).sum) (by decide : 0 < 2)
  exact (Nat.le_log2 (show order ≠ 0 by omega)).2 hpow

/-- If each parked frame has one kernel-sized label and a common index budget,
the total charged width splits into one ambient label and the index budget. -/
theorem parkedWidths_le (kernels : List ℕ) (order extra : ℕ)
    (positive : ∀ a ∈ kernels, a ≠ 0) (hprod : kernels.prod ≤ order) :
    (kernels.map (fun a => Nat.log2 a + extra)).sum ≤
      Nat.log2 order + kernels.length * extra := by
  have hsum (ks : List ℕ) :
      (ks.map (fun a => Nat.log2 a + extra)).sum =
        (ks.map Nat.log2).sum + ks.length * extra := by
    induction ks with
    | nil => simp
    | cons a ks ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, ih]
      omega
  rw [hsum]
  exact Nat.add_le_add_right (kernelLabelWidths_le kernels order positive hprod) _

end Mathproof.MinimumGeneration
