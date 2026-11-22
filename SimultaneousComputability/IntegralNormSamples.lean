import Mathlib.Algebra.Polynomial.Roots

theorem norm_polynomial_eq_one_of_samples
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : Polynomial R) (n : ℕ)
    (degree_bound : P.natDegree ≤ n)
    (samples : ∀ i : ℕ, i ≤ n → P.eval (i : R) = 1) :
    P = 1 := by
  classical
  by_contra h
  let Q := P - 1
  have qzero : Q ≠ 0 := sub_ne_zero.mpr h
  have qdegree : Q.natDegree ≤ n := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le degree_bound (by simp))
  let tests := (Finset.range (n + 1)).image (fun i : ℕ => (i : R))
  have tests_card : tests.card = n + 1 := by
    change ((Finset.range (n + 1)).image (fun i : ℕ => (i : R))).card = n + 1
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have test_roots : tests ⊆ Q.roots.toFinset := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots qzero).mpr
    change (P - 1).eval (i : R) = 0
    simp [samples i hi']
  have hc := (Finset.card_le_card test_roots).trans
    (le_trans (Multiset.toFinset_card_le Q.roots) ((Polynomial.card_roots' Q).trans qdegree))
  exact (Nat.not_succ_le_self n) (by simpa only [tests_card] using hc)
