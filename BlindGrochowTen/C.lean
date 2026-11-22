import Mathlib

namespace BlindGrochowTen

section Isotopy

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]

/-- All three independent transports of unital associative multiplication are
specified by an algebra equivalence and two units. -/
theorem multiplication_isotopy_normal_form (X Y Z : A ≃ₗ[R] B) :
    (∀ x y : A, Z (x * y) = X x * Y y) ↔
      ∃ (a b : Bˣ) (σ : A ≃ₐ[R] B),
        (∀ x, X x = (a : B) * σ x) ∧
        (∀ x, Y x = σ x * (b : B)) ∧
        (∀ x, Z x = (a : B) * σ x * (b : B)) := by
  constructor
  · intro h
    have hx (x : A) : Z x = X x * Y 1 := by simpa using h x 1
    have hy (x : A) : Z x = X 1 * Y x := by simpa using h 1 x
    have injA : Function.Injective (fun x : B => X 1 * x) := by
      intro x y he
      obtain ⟨x, rfl⟩ := Y.surjective x
      obtain ⟨y, rfl⟩ := Y.surjective y
      exact congrArg Y (Z.injective (by simpa only [hy] using he))
    have injB : Function.Injective (fun x : B => x * Y 1) := by
      intro x y he
      obtain ⟨x, rfl⟩ := X.surjective x
      obtain ⟨y, rfl⟩ := X.surjective y
      exact congrArg X (Z.injective (by simpa only [hx] using he))
    obtain ⟨t, ht⟩ := Z.surjective 1
    have hta : X 1 * Y t = 1 := (hy t).symm.trans ht
    have htb : X t * Y 1 = 1 := (hx t).symm.trans ht
    let a : Bˣ := ⟨X 1, Y t, hta, injA (by dsimp; rw [← mul_assoc, hta, one_mul, mul_one])⟩
    let b : Bˣ := ⟨Y 1, X t, injB (by dsimp; rw [mul_assoc, htb, mul_one, one_mul]), htb⟩
    let L := (Z.trans ((a⁻¹).mulLeftLinearEquiv R B)).trans ((b⁻¹).mulRightLinearEquiv R)
    have hL (x : A) : L x = (↑(a⁻¹) : B) * Z x * (↑(b⁻¹) : B) := rfl
    have ha : (a : B) * (↑(a⁻¹) : B) = 1 := a.val_inv
    have ha' : (↑(a⁻¹) : B) * (a : B) = 1 := a.inv_val
    have hb : (b : B) * (↑(b⁻¹) : B) = 1 := b.val_inv
    have hb' : (↑(b⁻¹) : B) * (b : B) = 1 := b.inv_val
    have hX (x : A) : (a : B) * L x = X x := by
      calc
        (a : B) * L x = Z x * (↑(b⁻¹) : B) := by
          rw [hL]
          simp only [← mul_assoc, ha, one_mul]
        _ = X x := by
          rw [hx]
          change (X x * (b : B)) * (↑(b⁻¹) : B) = X x
          rw [mul_assoc, hb, mul_one]
    have hY (x : A) : L x * (b : B) = Y x := by
      calc
        L x * (b : B) = (↑(a⁻¹) : B) * Z x := by
          rw [hL, mul_assoc ((↑(a⁻¹) : B) * Z x), hb', mul_one]
        _ = Y x := by
          rw [hy]
          change (↑(a⁻¹) : B) * ((a : B) * Y x) = Y x
          rw [← mul_assoc, ha', one_mul]
    have h_one : L 1 = 1 := by
      rw [hL, hx]
      change (↑(a⁻¹) : B) * ((a : B) * (b : B)) * (↑(b⁻¹) : B) = 1
      rw [← mul_assoc (↑(a⁻¹) : B) (a : B), ha', one_mul, hb]
    have h_mul (x y : A) : L (x * y) = L x * L y := by
      rw [hL, h, ← hX x, ← hY y]
      have e₁ : (↑(a⁻¹) : B) * ((a : B) * L x) = L x := by
        rw [← mul_assoc, ha', one_mul]
      have e₂ : (L y * (b : B)) * (↑(b⁻¹) : B) = L y := by
        rw [mul_assoc, hb, mul_one]
      rw [← mul_assoc (↑(a⁻¹) : B) ((a : B) * L x), mul_assoc, e₁, e₂]
    let σ := AlgEquiv.ofLinearEquiv L h_one h_mul
    refine ⟨a, b, σ, fun x => (hX x).symm, fun x => (hY x).symm, fun x => ?_⟩
    change Z x = (a : B) * L x * (b : B)
    rw [hX, hx]
  · rintro ⟨a, b, σ, hX, hY, hZ⟩ x y
    simp only [hX, hY, hZ, map_mul, mul_assoc]

end Isotopy

section Trace

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]

/-- A common change of basis between weighted trace tensors exists exactly
when an algebra equivalence transports the weights up to a unit cube. -/
theorem weighted_trace_equiv_iff_unit_cube
    (hB : (Algebra.traceForm R B).Nondegenerate) (a : Aˣ) (b : Bˣ) :
    (∃ T : A ≃ₗ[R] B, ∀ x y z : A,
      Algebra.trace R A ((a : A) * (x * y * z)) =
        Algebra.trace R B ((b : B) * (T x * T y * T z))) ↔
    ∃ (σ : A ≃ₐ[R] B) (u : Bˣ), σ (a : A) = (b : B) * (u : B) ^ 3 := by
  constructor
  · rintro ⟨T, h⟩
    have sep (c d : B)
        (e : ∀ z, Algebra.trace R B (c * z) = Algebra.trace R B (d * z)) :
        c = d := by
      apply sub_eq_zero.mp
      apply hB.1
      intro z
      rw [Algebra.traceForm_apply, sub_mul, map_sub, e, sub_self]
    have ht (x y : A) : T x * T y = T 1 * T (x * y) := by
      apply (b.mulLeftLinearEquiv R B).injective
      apply sep
      intro z
      obtain ⟨t, rfl⟩ := T.surjective z
      change Algebra.trace R B (((b : B) * (T x * T y)) * T t) =
        Algebra.trace R B (((b : B) * (T 1 * T (x * y))) * T t)
      calc
        _ = Algebra.trace R B ((b : B) * (T x * T y * T t)) := by rw [mul_assoc]
        _ = Algebra.trace R B ((b : B) * (T (x * y) * T 1 * T t)) := by
          rw [← h x y t, ← h (x * y) 1 t, mul_one]
        _ = _ := by congr 1; ac_rfl
    obtain ⟨v, hv⟩ := T.surjective 1
    have hunit : IsUnit (T 1) :=
      isUnit_iff_exists_inv.mpr ⟨T (v * v), by rw [← ht, hv, one_mul]⟩
    obtain ⟨u, hu⟩ := hunit
    let L := T.trans ((u⁻¹).mulLeftLinearEquiv R B)
    have hL (x : A) : L x = (↑(u⁻¹) : B) * T x := rfl
    have hi : (↑(u⁻¹) : B) * (u : B) = 1 := u.inv_val
    have hi' : (u : B) * (↑(u⁻¹) : B) = 1 := u.val_inv
    have h_one : L 1 = 1 := by rw [hL, ← hu, hi]
    have h_mul (x y : A) : L (x * y) = L x * L y := by
      calc
        L (x * y) = ((↑(u⁻¹) : B) * (u : B)) * ((↑(u⁻¹) : B) * T (x * y)) := by
          rw [hi, one_mul, hL]
        _ = ((↑(u⁻¹) : B) * (↑(u⁻¹) : B)) * (T 1 * T (x * y)) := by
          rw [← hu]
          ac_rfl
        _ = L x * L y := by rw [← ht, hL, hL]; ac_rfl
    let σ := AlgEquiv.ofLinearEquiv L h_one h_mul
    have hT (x : A) : T x = (u : B) * σ x := by
      change T x = (u : B) * L x
      rw [hL, ← mul_assoc, hi', one_mul]
    refine ⟨σ, u, ?_⟩
    apply sep
    intro z
    obtain ⟨x, rfl⟩ := σ.surjective z
    rw [← map_mul σ (a : A) x, Algebra.trace_eq_of_algEquiv]
    calc
      _ = Algebra.trace R B ((b : B) * (T x * T 1 * T 1)) := by simpa using h x 1 1
      _ = _ := by rw [hT x, ← hu]; congr 1; ring
  · rintro ⟨σ, u, h⟩
    let T := σ.toLinearEquiv.trans (u.mulLeftLinearEquiv R B)
    refine ⟨T, fun x y z => ?_⟩
    change Algebra.trace R A ((a : A) * (x * y * z)) =
      Algebra.trace R B ((b : B) * (((u : B) * σ x) * ((u : B) * σ y) * ((u : B) * σ z)))
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul σ, map_mul σ, map_mul σ, h]
    congr 1
    ring

end Trace

end BlindGrochowTen
