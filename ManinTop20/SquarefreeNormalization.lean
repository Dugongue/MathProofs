import Mathlib.Data.Nat.Squarefree

theorem absEqOneOfSquarefreeMul (u t z : ℤ)
    (hs : Squarefree (u * t).natAbs) (h : t ^ 2 = u * z) : u.natAbs = 1 := by
  have hs' : Squarefree (u.natAbs * t.natAbs) := by
    simpa only [Int.natAbs_mul] using hs
  have ht : u.natAbs ∣ t.natAbs ^ 2 :=
    ⟨z.natAbs, by simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h⟩
  have hc := (Nat.coprime_of_squarefree_mul hs').pow_right 2
  exact (Nat.gcd_eq_left ht).symm.trans hc
