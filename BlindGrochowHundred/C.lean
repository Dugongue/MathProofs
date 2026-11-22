import Mathlib

namespace BlindGrochowHundred.C

section Regular

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem regular_intertwiner_iff (f : A →ₐ[R] B) (T : A →ₗ[R] B) :
    (∀ a x, T (a * x) = f a * T x) ↔ ∀ x, T x = f x * T 1 := by
  constructor
  · intro h x
    simpa using h x 1
  · intro h a x
    rw [h (a * x), h x, map_mul, mul_assoc]

theorem regular_bimodule_intertwiner_iff (f : A →ₐ[R] B) (T : A →ₗ[R] B) :
    (∀ a x, T (a * x) = f a * T x ∧ T (x * a) = T x * f a) ↔
      (∀ x, T x = f x * T 1) ∧ ∀ a, f a * T 1 = T 1 * f a := by
  constructor
  · intro h
    have shape := (regular_intertwiner_iff f T).mp (fun a x => (h a x).1)
    exact ⟨shape, fun a => (shape a).symm.trans (by simpa using (h a 1).2)⟩
  · rintro ⟨shape, commute⟩ a x
    refine ⟨(regular_intertwiner_iff f T).mpr shape a x, ?_⟩
    rw [shape (x * a), shape x, map_mul, mul_assoc, commute a, ← mul_assoc]

theorem regular_double_commutant_iff (T : A →ₗ[R] A) :
    (∀ U : A →ₗ[R] A, (∀ a x, U (a * x) = a * U x) →
        ∀ x, T (U x) = U (T x)) ↔ ∀ x, T x = T 1 * x := by
  constructor
  · intro h x
    have eq := h (LinearMap.mulRight R x) (fun a y => mul_assoc a y x) 1
    change T (1 * x) = T 1 * x at eq
    simpa using eq
  · intro shape U comm x
    have normal (z : A) : U z = z * U 1 := by simpa using comm z 1
    calc
      T (U x) = T 1 * (x * U 1) := by rw [shape (U x), normal x]
      _ = U (T x) := by rw [normal (T x), shape x, mul_assoc]

theorem regular_intertwiner_from_generators (f : A →ₐ[R] B)
    (T : A →ₗ[R] B) (S : Set A) (hS : Algebra.adjoin R S = ⊤)
    (h : ∀ a ∈ S, ∀ x, T (a * x) = f a * T x) :
    ∀ a x, T (a * x) = f a * T x := by
  have step (a : A) (ha : a ∈ Algebra.adjoin R S) :
      ∀ x, T (a * x) = f a * T x := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact h a ha
    | algebraMap r =>
      intro x
      rw [f.commutes, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add a b ha hb ia ib =>
      intro x
      simp only [add_mul, map_add, ia, ib]
    | mul a b ha hb ia ib =>
      intro x
      rw [mul_assoc, ia, ib, map_mul, mul_assoc]
  intro a
  apply step
  rw [hS]
  trivial

theorem regular_conjugacy_recovers_algebra (P T : A ≃ₗ[R] B)
    (h : ∀ a x, T (a * x) = P a * T x) :
    ∃ σ : A ≃ₐ[R] B, (∀ a, σ a = P a) ∧ ∀ x, T x = σ x * T 1 := by
  obtain ⟨v, hv⟩ := T.surjective 1
  have hone : P 1 = 1 := by simpa only [one_mul, hv, mul_one] using (h 1 v).symm
  have hmul (a b : A) : P (a * b) = P a * P b := by
    calc
      P (a * b) = T ((a * b) * v) := by rw [h, hv, mul_one]
      _ = P a * P b := by rw [mul_assoc, h, h, hv, mul_one]
  let σ := AlgEquiv.ofLinearEquiv P hone hmul
  refine ⟨σ, fun _ => rfl, fun x => ?_⟩
  change T x = P x * T 1
  simpa only [mul_one] using h x 1

theorem independently_fixed_output_isotopy (X Y : A ≃ₗ[R] A) :
    (∀ x y, x * y = X x * Y y) ↔
      ∃ u : Aˣ, (∀ x, X x = x * (u : A)) ∧ ∀ y, Y y = (↑u⁻¹ : A) * y := by
  constructor
  · intro h
    have hl (x : A) : x = X x * Y 1 := by simpa using h x 1
    have hr (y : A) : y = X 1 * Y y := by simpa using h 1 y
    have ab : X 1 * Y 1 = 1 := (hl 1).symm
    have hh (s t : A) (e : s * Y 1 = t * Y 1) : s = t := by
      obtain ⟨s, rfl⟩ := X.surjective s
      obtain ⟨t, rfl⟩ := X.surjective t
      exact congrArg X ((hl s).trans (e.trans (hl t).symm))
    have ba : Y 1 * X 1 = 1 := by
      apply hh
      rw [mul_assoc, ab, mul_one, one_mul]
    let u : Aˣ := ⟨X 1, Y 1, ab, ba⟩
    refine ⟨u, ?_, ?_⟩
    · intro x
      change X x = x * X 1
      calc
        X x = (X x * Y 1) * X 1 := by rw [mul_assoc, ba, mul_one]
        _ = x * X 1 := congrArg (fun a => a * X 1) (hl x).symm
    · intro y
      change Y y = Y 1 * y
      calc
        Y y = Y 1 * (X 1 * Y y) := by rw [← mul_assoc, ba, one_mul]
        _ = Y 1 * y := congrArg (fun a => Y 1 * a) (hr y).symm
  · rintro ⟨u, hu, hv⟩ x y
    rw [hu, hv]
    simp [mul_assoc]

theorem surjective_product_transport_recovers_second_kernel
    (X Y Z : A →ₗ[R] B) (hX : Function.Surjective X)
    (h : ∀ x y, Z (x * y) = X x * Y y) :
    ∀ y, Y y = 0 ↔ ∀ x, Z (x * y) = 0 := by
  intro y
  refine ⟨fun hy x => by simp [h, hy], ?_⟩
  intro hz
  obtain ⟨x, hx⟩ := hX 1
  simpa only [h, hx, one_mul] using hz x

theorem left_regular_invariant_complement_of_central_projection (e : A)
    (he : e * e = e) (hc : ∀ x, e * x = x * e) :
    ∀ x, (e * x = x ↔ ∃ y, x = e * y) ∧
        (e * x = 0 ↔ ∀ y, e * (x * y) = 0 ∧ e * (y * x) = 0) := by
  intro x
  constructor
  · refine ⟨fun h => ⟨x, h.symm⟩, ?_⟩
    rintro ⟨y, rfl⟩
    rw [← mul_assoc, he]
  · constructor
    · intro h y
      constructor
      · rw [← mul_assoc, h, zero_mul]
      · rw [← mul_assoc, hc y, mul_assoc, h, mul_zero]
    · intro h
      simpa using (h 1).1

end Regular

section Frobenius

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]

/-- Multiplication by an element is determined by all of its scalar evaluations. -/
def Separating (φ : A →ₗ[R] R) : Prop :=
  ∀ a b, (∀ z, φ (a * z) = φ (b * z)) → a = b

theorem frobenius_centroid_iff (φ : A →ₗ[R] R) (sep : Separating φ)
    (F : A →ₗ[R] A) :
    (∀ x y z, φ (F x * y * z) = φ (x * F y * z)) ↔
      ∀ x, F x = F 1 * x := by
  constructor
  · intro h x
    apply sep
    intro z
    simpa [mul_comm (F 1) x] using h x 1 z
  · intro h x y z
    rw [h x, h y]
    congr 1
    ac_rfl

theorem frobenius_slice_separating_iff (φ : A →ₗ[R] R) (sep : Separating φ)
    (u : A) :
    (∀ a b, (∀ z, φ (u * a * z) = φ (u * b * z)) → a = b) ↔
      Function.Injective (fun a => u * a) := by
  constructor
  · intro h a b hab
    apply h a b
    intro z
    change u * a = u * b at hab
    rw [hab]
  · intro h a b hab
    exact h (sep (u * a) (u * b) hab)

theorem frobenius_product_at_invertible_slice (φ : A →ₗ[R] R) (sep : Separating φ)
    (u : Aˣ) (m : A → A → A) :
    (∀ x y z, φ ((u : A) * m x y * z) = φ (x * y * z)) ↔
       ∀ x y, m x y = (↑u⁻¹ : A) * (x * y) := by
  constructor
  · intro h x y
    have hp := sep ((u : A) * m x y) (x * y) (h x y)
    have eq := congrArg (fun v : A => (↑u⁻¹ : A) * v) hp
    have unit : (↑u⁻¹ : A) * (u : A) = 1 := u.inv_val
    simpa only [← mul_assoc, unit, one_mul] using eq
  · intro h x y z
    have unit : (u : A) * (↑u⁻¹ : A) = 1 := u.val_inv
    rw [h, ← mul_assoc (u : A), unit, one_mul]

theorem frobenius_transporter_from_two_leg_duality
    (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) (sep : Separating ψ)
    (X Y Z : A ≃ₗ[R] B) (P : A →ₗ[R] B)
    (dual : ∀ w z, φ (w * z) = ψ (P w * Z z)) :
    (∀ x y z, φ (x * y * z) = ψ (X x * Y y * Z z)) ↔
    ∀ x y, P (x * y) = X x * Y y := by
  constructor
  · intro h x y
    apply sep
    intro z
    obtain ⟨w, rfl⟩ := Z.surjective z
    exact (dual (x * y) w).symm.trans (h x y w)
  · intro h x y z
    rw [dual, h]

theorem frobenius_tensor_ext_of_spanning_probes (φ ψ : A →ₗ[R] R)
    (S : Set A) (hS : Submodule.span R S = ⊤)
    (h : ∀ x y z, z ∈ S → φ (x * y * z) = ψ (x * y * z)) :
    ∀ x y z, φ (x * y * z) = ψ (x * y * z) := by
  intro x y
  let left := φ.comp (LinearMap.mulLeft R (x * y))
  let right := ψ.comp (LinearMap.mulLeft R (x * y))
  have eq : left = right := by
    apply LinearMap.ext_on hS
    intro z hz
    exact h x y z hz
  intro z
  exact DFunLike.congr_fun eq z

theorem frobenius_reference_slice_determined_by_tensor (φ : A →ₗ[R] R)
    (ψ : B →ₗ[R] R) (T : A ≃ₗ[R] B)
    (h : ∀ x y z, φ (x * y * z) = ψ (T x * T y * T z)) :
    (∀ x y, φ (x * y) = ψ (T x * T y)) ↔
      (∀ x y, ψ (T 1 * (T x * T y)) = ψ (T x * T y)) := by
  constructor
  · intro hpair x y
    rw [mul_comm (T 1), ← h x y 1, mul_one, hpair]
  · intro hu x y
    rw [← hu x y, mul_comm (T 1), ← h x y 1, mul_one]

private theorem frobenius_orthogonal_product_support (φ : A →ₗ[R] R)
    (e f : A) (orth : e * f = 0) :
    ∀ x y z, φ ((e * x) * (f * y) * z) = 0 := by
  intro x y z
  have eq : (e * x) * (f * y) * z = (e * f) * (x * y * z) := by ac_rfl
  rw [eq, orth, zero_mul, map_zero]

theorem frobenius_orthogonal_blocks_recover_product (φ : A →ₗ[R] R)
    (sep : Separating φ) (e f : A) :
    (∀ x y z, φ ((e * x) * (f * y) * z) = 0) ↔ e * f = 0 := by
  constructor
  · intro h
    apply sep
    intro z
    simpa using h 1 1 z
  · exact frobenius_orthogonal_product_support φ e f

theorem frobenius_radical_computed_by_weight (φ : A →ₗ[R] R)
    (sep : Separating φ) (u : A) :
    ∀ x, (∀ y z, φ (u * (x * y * z)) = 0) ↔ u * x = 0 := by
  intro x
  constructor
  · intro h
    apply sep
    intro z
    simpa only [mul_one, zero_mul, map_zero, mul_assoc] using h 1 z
  · intro h y z
    have eq : u * (x * y * z) = (u * x) * (y * z) := by simp [mul_assoc]
    simp only [eq, h, zero_mul, map_zero]

end Frobenius

section Reconstruction

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]

theorem frobenius_tensor_and_reference_pair_recover_algebra (φ : A →ₗ[R] R)
    (ψ : B →ₗ[R] R) (sep : Separating ψ) (T : A ≃ₗ[R] B)
    (hp : ∀ x y, φ (x * y) = ψ (T x * T y))
    (ht : ∀ x y z, φ (x * y * z) = ψ (T x * T y * T z)) :
    ∃ e : A ≃ₐ[R] B, ∀ x, e x = T x := by
  have hm (x y : A) : T (x * y) = T x * T y := by
    apply sep
    intro z
    obtain ⟨w, rfl⟩ := T.surjective z
    exact (hp (x * y) w).symm.trans (ht x y w)
  obtain ⟨v, hv⟩ := T.surjective 1
  have hone := hm 1 v
  simp only [one_mul, hv, mul_one] at hone
  exact ⟨AlgEquiv.ofLinearEquiv T hone.symm hm, fun _ => rfl⟩

theorem frobenius_weighted_tensor_fixed_transporter_iff
    (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) (sep : Separating ψ)
    (e : A ≃ₐ[R] B) (htrace : ∀ u, ψ (e u) = φ u) (a : A) (b : B) :
    (∀ x y z, φ (a * (x * y * z)) = ψ (b * (e x * e y * e z))) ↔ e a = b := by
  constructor
  · intro h
    apply sep
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, htrace]
    simpa using h w 1 1
  · intro h x y z
    simp only [← htrace (a * (x * y * z)), map_mul e, h]

theorem frobenius_product_pair_separating_iff
    (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) :
    Separating (φ.comp (LinearMap.fst R A B) + ψ.comp (LinearMap.snd R A B)) ↔
      Separating φ ∧ Separating ψ := by
  constructor
  · intro h
    constructor
    · intro a b e
      have eq : (a, (0 : B)) = (b, 0) := by
        apply h
        intro z
        simpa using e z.1
      exact congrArg Prod.fst eq
    · intro a b e
      have eq : ((0 : A), a) = (0, b) := by
        apply h
        intro z
        simpa using e z.2
      exact congrArg Prod.snd eq
  · rintro ⟨ha, hb⟩ a b h
    apply Prod.ext
    · apply ha
      intro z
      simpa using h (z, 0)
    · apply hb
      intro z
      simpa using h (0, z)

theorem frobenius_orthogonal_projection_is_multiplication
    (φ : A →ₗ[R] R) (sep : Separating φ) (P : A →ₗ[R] A)
    (idempotent : ∀ x, P (P x) = P x)
    (orthogonal : ∀ x y z, P y = 0 → φ (P x * y * z) = 0)
    (split : ∀ x, ∃ y, P y = 0 ∧ x = P x + y) :
    ∃ e : A, e * e = e ∧ ∀ x, P x = e * x := by
  have vanishes (x y : A) (hy : P y = 0) : P x * y = 0 := by
    apply sep
    intro z
    simpa using orthogonal x y z hy
  have commute (x y : A) : P x * y = x * P y := by
    obtain ⟨u, hu, hxu⟩ := split x
    obtain ⟨v, hv, hyv⟩ := split y
    calc
      P x * y = P x * (P y + v) := congrArg (fun a => P x * a) hyv
      _ = P x * P y := by rw [mul_add, vanishes x v hv, add_zero]
      _ = (P x + u) * P y := by
        rw [add_mul, mul_comm u, vanishes y u hu, add_zero]
      _ = x * P y := congrArg (fun a => a * P y) hxu.symm
  refine ⟨P 1, ?_, fun x => ?_⟩
  · simpa [idempotent] using (commute (P 1) 1).symm
  · simpa only [mul_one, mul_comm x (P 1)] using commute x 1

theorem frobenius_nilpotence_detected_by_contractions
    (φ : A →ₗ[R] R) (sep : Separating φ) (u : Aˣ) (x : A) (n : ℕ) :
    (∀ z, φ ((u : A) * (x ^ n * z)) = 0) ↔ x ^ n = 0 := by
  constructor
  · intro h
    have eq : (u : A) * x ^ n = 0 := by
      apply sep
      intro z
      simpa only [mul_assoc, zero_mul, map_zero] using h z
    apply (u.mulLeftLinearEquiv R A).injective
    simpa using eq
  · intro h z
    simp [h]

theorem frobenius_normalized_contractions_commute
    (φ : A →ₗ[R] R) (sep : Separating φ) (r : Aˣ)
    (L : A → A → A)
    (recover : ∀ a x y, φ ((r : A) * (L a x * y)) = φ (a * x * y)) :
    ∀ a b x, L a (L b x) = L b (L a x) := by
  have hh (a x : A) : L a x = (↑r⁻¹ : A) * (a * x) := by
    have eq : (r : A) * L a x = a * x :=
      sep _ _ (fun y => by simpa only [mul_assoc] using recover a x y)
    have norm := congrArg (fun t : A => (↑r⁻¹ : A) * t) eq
    have unit : (↑r⁻¹ : A) * (r : A) = 1 := r.inv_val
    simpa only [← mul_assoc, unit, one_mul] using norm
  intro a b x
  rw [hh a, hh b, hh b, hh a]
  ac_rfl

omit [CommSemiring R] in
theorem frobenius_recovered_multiplication_associative
    {V : Type*} (pairing : V → V → R)
    (sep : ∀ a b, (∀ z, pairing a z = pairing b z) → a = b)
    (F : V → V → V → R) (m : V → V → V)
    (symm : ∀ x y z, F x y z = F y x z)
    (recover : ∀ x y z, pairing (m x y) z = F x y z)
    (commute : ∀ x y z, m x (m y z) = m y (m x z)) :
    ∀ x y z, m (m x y) z = m x (m y z) := by
  have comm (x y : V) : m x y = m y x :=
    sep _ _ (fun z => by rw [recover, recover, symm])
  intro x y z
  calc
    m (m x y) z = m z (m x y) := comm _ _
    _ = m x (m z y) := commute _ _ _
    _ = m x (m y z) := congrArg (m x) (comm z y)

end Reconstruction

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem frobenius_good_slices_iff_units [FiniteDimensional K A]
    (φ : A →ₗ[K] K) (sep : Separating φ) (u : A) :
    (∀ a b, (∀ z, φ (u * a * z) = φ (u * b * z)) → a = b) ↔ IsUnit u := by
  rw [frobenius_slice_separating_iff φ sep]
  constructor
  · intro h
    have hinj : Function.Injective (LinearMap.mulLeft K u) := h
    obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
    exact isUnit_iff_exists_inv.mpr ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    exact (v.mulLeftLinearEquiv K A).injective

theorem frobenius_weighted_form_determines_orthogonal_decomposition
    (φ : A →ₗ[K] K) (sep : Separating φ) (u : Aˣ)
    (P : A →ₗ[K] A) (idempotent : ∀ x, P (P x) = P x)
    (mixed : ∀ x y z, φ ((u : A) * (P x * (y - P y) * z)) = 0) :
    ∃ e : A, (e * e = e) ∧ ∀ x, P x = e * x := by
  let ψ := φ.comp (LinearMap.mulLeft K (u : A))
  have sep' : Separating ψ := by
    intro a b h
    apply (u.mulLeftLinearEquiv K A).injective
    apply sep
    intro z
    change φ (((u : A) * a) * z) = φ (((u : A) * b) * z)
    simpa only [ψ, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_assoc] using h z
  apply frobenius_orthogonal_projection_is_multiplication ψ sep' P idempotent
  · intro x y z hy
    simpa [ψ, hy] using mixed x y z
  · intro x
    use x - P x
    rw [map_sub, idempotent, sub_self]
    exact ⟨rfl, by abel⟩

end Field

end BlindGrochowHundred.C
