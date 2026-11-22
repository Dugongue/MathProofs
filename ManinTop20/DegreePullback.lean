import Mathlib.Tactic

theorem degreePullbackInjective {V W V' W' : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    (P : V → W → ℚ) (Q : V' → W' → ℚ) (hP : ∀ x, (∀ y, P x y = 0) → x = 0)
    (F : V →+ V') (G : W →+ W') (hQ : ∀ y, Q 0 y = 0) (d : ℚ) (hd : d ≠ 0)
    (h : ∀ x y, Q (F x) (G y) = d * P x y) : Function.Injective F := by
    intro x y hxy
    have hker : ∀ z : V, F z = 0 → z = 0 := by
      intro z hz
      apply hP z
      intro w
      have he : d * P z w = 0 := by simpa [hz, hQ] using (h z w).symm
      exact (mul_eq_zero.mp he).resolve_left hd
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hxy, sub_self]
