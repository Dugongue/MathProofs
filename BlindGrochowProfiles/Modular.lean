import Mathlib

namespace ModularProfiles

open scoped BigOperators

def Grid (I : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => I × Grid I n

def mass {I : Type*} [Fintype I] : (n : ℕ) → (Grid I n → ℤ) → ℤ
  | 0, f => |f PUnit.unit|
  | n + 1, f => ∑ i, mass n (fun x => f (i, x))

def balanced {I : Type*} [Fintype I] : (n : ℕ) → (Grid I n → ℤ) → Prop
  | 0, _ => True
  | n + 1, f => (∀ i, balanced n (fun x => f (i, x))) ∧
      ∀ x, ∑ i, f (i, x) = 0

theorem line_bound {I : Type*} [Fintype I] (g : I → ℤ) (i : I)
    (hz : ∑ j, g j = 0) : 2 * |g i| ≤ ∑ j, |g j| := by
  classical
  have he := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
  have ha := Finset.sum_erase_add Finset.univ (fun j => |g j|) (Finset.mem_univ i)
  have he' : ∑ j ∈ Finset.univ.erase i, g j = -g i := by linarith
  have ht := Finset.abs_sum_le_sum_abs g (Finset.univ.erase i)
  rw [he', abs_neg] at ht
  linarith

theorem grid_bound {I : Type*} [Fintype I] (n : ℕ) (f : Grid I n → ℤ)
    (hb : balanced n f) (x : Grid I n) : 2 ^ n * |f x| ≤ mass n f := by
  induction n with
  | zero => cases x; simp [mass]
  | succ n ih =>
    obtain ⟨i, y⟩ := x
    have h := line_bound (fun j => f (j, y)) i (hb.2 y)
    calc
      (2 : ℤ) ^ (n + 1) * |f (i, y)| = 2 ^ n * (2 * |f (i, y)|) := by ring
      _ ≤ 2 ^ n * ∑ j, |f (j, y)| := by gcongr
      _ = ∑ j, (2 : ℤ)^n * |f (j, y)| := Finset.mul_sum ..
      _ ≤ mass (n+1) f := Finset.sum_le_sum (fun j _ => ih _ (hb.1 j) y)

end ModularProfiles
