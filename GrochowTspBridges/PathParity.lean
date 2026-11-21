import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace ShortcutTree

theorem path_edge_parity_constant (m : ℕ → ℕ) (last : ℕ)
    (h : ∀ i < last, (m i + m (i + 1)) % 2 = 0) :
    m 0 % 2 = m last % 2 := by
  induction last with
  | zero => rfl
  | succ k ih =>
      have hprefix : ∀ i < k, (m i + m (i + 1)) % 2 = 0 := by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi)
      have hlast := h k (Nat.lt_succ_self k)
      have hstep : m k % 2 = m (k + 1) % 2 := by omega
      exact (ih hprefix).trans hstep

end ShortcutTree
