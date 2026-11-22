import Mathlib

namespace C200

section WeightedProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]

def ProductTransport (a : A) (b : B) (X Y Z : A ≃ₗ[R] B) : Prop :=
  ∀ x y, Z (x * a * y) = X x * b * Y y

private theorem left_bijective_iff (c : A) :
    Function.Bijective (fun x : A => c * x) ↔ IsUnit c := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    obtain ⟨d, hd⟩ := hsurj 1
    change c * d = 1 at hd
    exact ⟨⟨c, d, hd, hinj (by dsimp; rw [← mul_assoc, hd, one_mul, mul_one])⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact u.mulLeft.bijective

private theorem right_bijective_iff (c : A) :
    Function.Bijective (fun x : A => x * c) ↔ IsUnit c := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    obtain ⟨d, hd⟩ := hsurj 1
    change d * c = 1 at hd
    exact ⟨⟨c, d, hinj (by dsimp; rw [mul_assoc, hd, one_mul, mul_one]), hd⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact u.mulRight.bijective

theorem sandwich_identity_iff (a : A) :
    (∃ e : A, ∀ x, e * a * x = x ∧ x * a * e = x) ↔ IsUnit a := by
  constructor
  · rintro ⟨e, h⟩
    have left : e * a = 1 := by simpa using (h 1).1
    have right : a * e = 1 := by simpa using (h 1).2
    exact ⟨⟨a, e, right, left⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨(↑u⁻¹ : A), fun x => ?_⟩
    have left : (↑u⁻¹ : A) * (u : A) = 1 := u.inv_val
    have right : (u : A) * (↑u⁻¹ : A) = 1 := u.val_inv
    exact ⟨by rw [left, one_mul], by rw [mul_assoc, right, mul_one]⟩

theorem sandwich_pivot_characterization (a x y : A) :
    (Function.Bijective (fun z => x * a * z) ↔ IsUnit (x * a)) ∧
      (Function.Bijective (fun z => z * a * y) ↔ IsUnit (a * y)) := by
  refine ⟨left_bijective_iff _, ?_⟩
  simpa only [mul_assoc] using right_bijective_iff (a * y)

theorem sandwich_radicals_transport {a : A} {b : B} (X Y Z : A ≃ₗ[R] B)
    (h : ProductTransport a b X Y Z) :
    (∀ x, x * a = 0 ↔ X x * b = 0) ∧ (∀ y, a * y = 0 ↔ b * Y y = 0) := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := Y.surjective 1
      simpa [hx, ht] using (h x t).symm
    · intro hx
      apply Z.injective
      simpa [hx] using h x 1
  · intro y
    constructor
    · intro hy
      obtain ⟨t, ht⟩ := X.surjective 1
      simpa [mul_assoc, hy, ht] using (h t y).symm
    · intro hy
      apply Z.injective
      simpa [mul_assoc, hy] using h 1 y

theorem sandwich_slice_image_transport {a : A} {b : B} (X Y Z : A ≃ₗ[R] B)
    (h : ProductTransport a b X Y Z) :
    ∀ x y, (∃ t, x * a * t = y) ↔ ∃ t, X x * b * t = Z y := by
  intro x y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Y t, (h x t).symm⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := Y.surjective t
    exact ⟨s, Z.injective ((h x s).trans ht)⟩

theorem sandwich_right_slice_image_transport {a : A} {b : B} (X Y Z : A ≃ₗ[R] B)
    (h : ProductTransport a b X Y Z) :
    ∀ x y, (∃ t, t * a * x = y) ↔ ∃ t, t * b * Y x = Z y := by
  intro x y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨X t, (h t x).symm⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := X.surjective t
    exact ⟨s, Z.injective ((h s x).trans ht)⟩

theorem sandwich_unit_descends {a : A} {b : B} (X Y Z : A ≃ₗ[R] B)
    (h : ProductTransport a b X Y Z) (ha : IsUnit a) : IsUnit b := by
  obtain ⟨u, rfl⟩ := ha
  have left : (fun t => X 1 * b * t) = (Y.symm.trans (u.mulLeftLinearEquiv R A)).trans Z := by
    funext y
    obtain ⟨t, rfl⟩ := Y.surjective y
    simpa using (h 1 t).symm
  have right : (fun t => t * (b * Y 1)) =
      (X.symm.trans (u.mulRightLinearEquiv R)).trans Z := by
    funext x
    obtain ⟨t, rfl⟩ := X.surjective x
    simpa [mul_assoc] using (h t 1).symm
  have bijL : Function.Bijective (fun t => X 1 * b * t) := by rw [left]; exact ((Y.symm.trans (u.mulLeftLinearEquiv R A)).trans Z).bijective
  have bijR : Function.Bijective (fun t => t * (b * Y 1)) := by rw [right]; exact ((X.symm.trans (u.mulRightLinearEquiv R)).trans Z).bijective
  obtain ⟨v, hv⟩ := (left_bijective_iff (X 1 * b)).mp bijL
  obtain ⟨w, hw⟩ := (right_bijective_iff (b * Y 1)).mp bijR
  have l : (↑v⁻¹ : B) * X 1 * b = 1 := by rw [mul_assoc, ← hv]; exact v.inv_val
  have r : b * (Y 1 * (↑w⁻¹ : B)) = 1 := by rw [← mul_assoc, ← hw]; exact w.val_inv
  have eq : (↑v⁻¹ : B) * X 1 = Y 1 * (↑w⁻¹ : B) := by
    calc
      _ = ((↑v⁻¹ : B) * X 1) * (b * (Y 1 * (↑w⁻¹ : B))) := by rw [r, mul_one]
      _ = _ := by rw [← mul_assoc, l, one_mul]
  exact ⟨⟨b, Y 1 * (↑w⁻¹ : B), r, by rwa [← eq]⟩, rfl⟩

theorem sandwich_transport_by_regular_units (a b : A) (u v : Aˣ) :
    ProductTransport a b (u.mulRightLinearEquiv R) (v.mulLeftLinearEquiv R A)
        (LinearEquiv.refl R A) ↔ a = (u : A) * b * (v : A) := by
  constructor
  · intro h
    simpa [ProductTransport] using h 1 1
  · intro h x y
    change x * a * y = (x * (u : A)) * b * ((v : A) * y)
    simp [h, mul_assoc]

theorem sandwich_weighted_algebra_equivalence (a : Aˣ) (b : Bˣ) (T : A ≃ₗ[R] B) :
    ProductTransport (a : A) (b : B) T T T ↔
      ∃ f : A ≃ₐ[R] B, ∀ x, (b : B) * T x = f ((a : A) * x) := by
  let S := ((a⁻¹).mulLeftLinearEquiv R A).trans (T.trans (b.mulLeftLinearEquiv R B))
  have bridge (x : A) : S ((a : A) * x) = (b : B) * T x := by
    change (b : B) * T ((↑a⁻¹ : A) * ((a : A) * x)) = (b : B) * T x
    have unit : (↑a⁻¹ : A) * (a : A) = 1 := a.inv_val
    rw [← mul_assoc, unit, one_mul]
  have mulbridge :
      ProductTransport (a : A) (b : B) T T T ↔
        ∀ x y, S (x * y) = S x * S y := by
    constructor
    · intro h x y
      obtain ⟨x, rfl⟩ := (a.mulLeftLinearEquiv R A).surjective x
      obtain ⟨y, rfl⟩ := (a.mulLeftLinearEquiv R A).surjective y
      change S (((a : A) * x) * ((a : A) * y)) =
        S ((a : A) * x) * S ((a : A) * y)
      have e : ((a : A) * x) * ((a : A) * y) = (a : A) * (x * (a : A) * y) := by
        simp only [mul_assoc]
      rw [e, bridge, bridge, bridge, h x y]
      simp only [mul_assoc]
    · intro h x y
      apply (b.mulLeftLinearEquiv R B).injective
      have e : ((a : A) * x) * ((a : A) * y) = (a : A) * (x * (a : A) * y) := by
        simp only [mul_assoc]
      simpa only [e, bridge, Units.mulLeftLinearEquiv_apply, mul_assoc] using
        h ((a : A) * x) ((a : A) * y)
  rw [mulbridge]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := S.surjective 1
    have h1 : S 1 = 1 := by simpa [hv] using (h 1 v).symm
    exact ⟨AlgEquiv.ofLinearEquiv S h1 h, fun x => (bridge x).symm⟩
  · rintro ⟨f, hf⟩ x y
    have eq (u : A) : S u = f u := by
      obtain ⟨t, rfl⟩ := (a.mulLeftLinearEquiv R A).surjective u
      change S ((a : A) * t) = f ((a : A) * t)
      rw [bridge, hf]
    simp only [eq, map_mul]

end WeightedProduct

section Radical

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

def radical (φ : A →ₗ[R] R) : Ideal A where
  carrier := {a | ∀ x, φ (a * x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    change ∀ x, φ (a * x) = 0 at ha
    change ∀ x, φ (b * x) = 0 at hb
    change φ ((a + b) * x) = 0
    rw [add_mul, map_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb x
    change ∀ x, φ (b * x) = 0 at hb
    change φ ((a * b) * x) = 0
    rw [mul_comm a b, mul_assoc, hb]

def weighted (φ : A →ₗ[R] R) (a : A) : A →ₗ[R] R :=
  φ.comp (LinearMap.mulLeft R a)

private theorem mem_rad (φ : A →ₗ[R] R) (a : A) :
    a ∈ radical φ ↔ ∀ x, φ (a * x) = 0 := Iff.rfl

theorem radical_largest_ideal (φ : A →ₗ[R] R) (I : Ideal A) :
    I ≤ radical φ ↔ ∀ x ∈ I, φ x = 0 := by
  constructor
  · intro h x hx
    simpa using (mem_rad φ x).mp (h hx) 1
  · intro h x hx
    apply (mem_rad φ x).mpr
    intro z
    apply h
    rw [mul_comm]
    exact I.mul_mem_left z hx

theorem radical_vanishes_iff_zero (φ : A →ₗ[R] R) :
    radical φ = ⊤ ↔ φ = 0 := by
  rw [← top_le_iff, radical_largest_ideal]
  simp only [Submodule.mem_top, true_implies]
  constructor
  · intro h
    ext x
    exact h x
  · intro h
    simp [h]

theorem radical_separating_exact (φ : A →ₗ[R] R) :
    radical φ = ⊥ ↔
      ∀ a b, (∀ x, φ (a * x) = φ (b * x)) → a = b := by
  constructor
  · intro h a b hab
    have w : a - b ∈ radical φ := by
      apply (mem_rad _ _).mpr
      intro x
      rw [sub_mul, map_sub, hab, sub_self]
    rw [h, Submodule.mem_bot] at w
    exact sub_eq_zero.mp w
  · intro h
    apply bot_unique
    intro a ha
    rw [Submodule.mem_bot]
    apply h a 0
    intro x
    simpa using (mem_rad _ _).mp ha x

theorem radical_surjective_pullback (f : A →ₐ[R] B) (surj : Function.Surjective f)
    (ψ : B →ₗ[R] R) :
    radical (ψ.comp f.toLinearMap) = (radical ψ).comap f.toRingHom := by
  ext a
  change (∀ x, ψ (f (a * x)) = 0) ↔ ∀ y, ψ (f a * y) = 0
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := surj y
    simpa only [map_mul] using h x
  · intro h x
    rw [map_mul]
    exact h (f x)

theorem weighted_radical_membership (φ : A →ₗ[R] R) (a x : A) :
    x ∈ radical (weighted φ a) ↔ a * x ∈ radical φ := by
  change (∀ y, φ (a * (x * y)) = 0) ↔ ∀ y, φ ((a * x) * y) = 0
  simp only [mul_assoc]

theorem weighted_radical_antitone (φ : A →ₗ[R] R) {a b : A} (h : a ∣ b) :
    radical (weighted φ a) ≤ radical (weighted φ b) := by
  intro x hx
  obtain ⟨c, rfl⟩ := h
  rw [weighted_radical_membership] at hx ⊢
  have eq : (a * c) * x = c * (a * x) := by ac_rfl
  rw [eq]
  exact (radical φ).mul_mem_left c hx

theorem weighted_functional_eq_iff (φ : A →ₗ[R] R) (a b : A) :
    weighted φ a = weighted φ b ↔ a - b ∈ radical φ := by
  change weighted φ a = weighted φ b ↔ ∀ x, φ ((a - b) * x) = 0
  simp only [sub_mul, map_sub, sub_eq_zero]
  exact ⟨fun eq x => DFunLike.congr_fun eq x, fun e => LinearMap.ext e⟩

theorem radical_is_canonical_linear_quotient (φ : A →ₗ[R] R) :
    ∃! ψ : (A ⧸ (radical φ).restrictScalars R) →ₗ[R] R,
      ψ.comp ((radical φ).restrictScalars R).mkQ = φ := by
  let I : Submodule R A := (radical φ).restrictScalars R
  have ker : I ≤ LinearMap.ker φ := by
    intro x hx
    exact LinearMap.mem_ker.mpr (by simpa using (mem_rad φ x).mp hx 1)
  refine ⟨I.liftQ φ ker, I.liftQ_mkQ _ _, ?_⟩
  intro ψ hψ
  apply LinearMap.ext
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective I a
  exact (DFunLike.congr_fun hψ x).trans (Submodule.liftQ_apply I φ x).symm

theorem radical_transfer_product_survives (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (T : A ≃ₗ[R] B)
    (h : ∀ x y, φ (x * y) = ψ (T x * T y)) :
    ∀ x, x ∈ radical φ ↔ T x ∈ radical ψ := by
  intro x
  change (∀ y, φ (x * y) = 0) ↔ ∀ z, ψ (T x * z) = 0
  constructor
  · intro g z
    obtain ⟨y, rfl⟩ := T.surjective z
    rw [← h]
    exact g y
  · intro g y
    rw [h]
    exact g (T y)

theorem radical_equivariant_orthogonal_splitting (φ : A →ₗ[R] R)
    (a b : A) (h : a + b = 1) :
    radical (weighted φ a) ⊓ radical (weighted φ b) = radical φ := by
  ext x
  change (x ∈ radical (weighted φ a) ∧ x ∈ radical (weighted φ b)) ↔ x ∈ radical φ
  rw [weighted_radical_membership, weighted_radical_membership]
  constructor
  · rintro ⟨ha, hb⟩
    have joined := (radical φ).add_mem ha hb
    rw [← add_mul, h, one_mul] at joined
    exact joined
  · intro hx
    exact ⟨(radical φ).mul_mem_left a hx, (radical φ).mul_mem_left b hx⟩

theorem radical_weight_prime_factor (φ : A →ₗ[R] R)
    (h : (radical φ).IsPrime) (a x : A) :
    x ∈ radical (weighted φ a) ↔ a ∈ radical φ ∨ x ∈ radical φ := by
  rw [weighted_radical_membership]
  constructor
  · exact h.mem_or_mem
  · rintro (ha | hx)
    · rw [mul_comm]; exact (radical φ).mul_mem_left x ha
    · exact (radical φ).mul_mem_left a hx

theorem radical_product_functional (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) (x : A × B) :
    x ∈ radical (φ.comp (LinearMap.fst R A B) + ψ.comp (LinearMap.snd R A B)) ↔
      x.1 ∈ radical φ ∧ x.2 ∈ radical ψ := by
  change (∀ z : A × B, φ (x.1 * z.1) + ψ (x.2 * z.2) = 0) ↔
    (∀ t : A, φ (x.1 * t) = 0) ∧ (∀ t : B, ψ (x.2 * t) = 0)
  constructor
  · intro h
    exact ⟨fun t => by simpa using h (t, 0), fun t => by simpa using h (0, t)⟩
  · rintro ⟨ha, hb⟩ z
    rw [ha, hb, zero_add]

theorem radical_of_weight_family (φ : A →ₗ[R] R) (S : Set A) (x : A) :
    (∀ a ∈ S, x ∈ radical (weighted φ a)) ↔
      ∀ a ∈ Ideal.span S, a * x ∈ radical φ := by
  simp only [weighted_radical_membership]
  constructor
  · intro h a ha
    have incl : Ideal.span S ≤ (radical φ).colon ({x} : Set A) :=
      Ideal.span_le.mpr (fun t ht => Submodule.mem_colon_singleton.mpr (h t ht))
    exact Submodule.mem_colon_singleton.mp (incl ha)
  · intro h a ha
    exact h a (Ideal.subset_span ha)

theorem radical_powers_detect_quotient_nilpotence (φ : A →ₗ[R] R) (a : A) :
    IsNilpotent (Ideal.Quotient.mk (radical φ) a) ↔
      ∃ n : ℕ, ∀ x, φ (a ^ n * x) = 0 := by
  change (∃ n : ℕ, (Ideal.Quotient.mk (radical φ) a) ^ n = 0) ↔ _
  simp only [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_rad]

theorem weighted_tensor_perturbation (φ : A →ₗ[R] R) (a b : A) :
    (∀ x y z, φ (a * (x * y * z)) = φ (b * (x * y * z))) ↔
      a - b ∈ radical φ := by
  rw [← weighted_functional_eq_iff]
  constructor
  · intro h
    ext x
    simpa [weighted] using h x 1 1
  · intro h x y z
    exact DFunLike.congr_fun h (x * y * z)

end Radical

section Arity

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

def Arity (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) (T : A ≃ₗ[R] B) : Prop :=
  ∀ (x y z : A) (l : List A), l.length = n →
    φ (x * y * z * l.prod) = ψ (T x * T y * T z * (l.map T).prod)

private theorem prod_map_scale (σ : A ≃ₐ[R] B) (u : B) (l : List A) :
    (l.map (fun x => u * σ x)).prod = u ^ l.length * σ l.prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, map_mul, pow_succ, ih]
    ac_rfl

private theorem arity_from_normal (n : ℕ) (φ : A →ₗ[R] R)
    (ψ : B →ₗ[R] R) (T : A ≃ₗ[R] B) (σ : A ≃ₐ[R] B) (u : Bˣ)
    (hT : ∀ x, T x = (u : B) * σ x)
    (h : ∀ x, φ x = ψ ((u : B) ^ (n + 3) * σ x)) : Arity n φ ψ T := by
  intro x y z l hl
  have hm : l.map (fun x => T x) = l.map (fun x => (u : B) * σ x) := by
    congr 1
    funext t
    exact hT t
  rw [h, hm, prod_map_scale, hl]
  simp only [map_mul σ, hT, pow_add]
  congr 1
  ring

theorem arity_normal_form (n : ℕ) (φ : A →ₗ[R] R)
    (ψ : B →ₗ[R] R) (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) :
    Arity n φ ψ T ↔
      ∃ (σ : A ≃ₐ[R] B) (u : Bˣ),
        (∀ x, T x = (u : B) * σ x) ∧
        ∀ x, φ x = ψ ((u : B) ^ (n + 3) * σ x) := by
  constructor
  · intro h
    have tri (x y z : A) : φ (x * y * z) = ψ ((T 1) ^ n * (T x * T y * T z)) := by
      have e := h x y z (List.replicate n 1) (List.length_replicate ..)
      simpa only [List.map_replicate, List.prod_replicate, one_pow, mul_one, mul_comm ((T 1) ^ n)] using e
    have sepA := (radical_separating_exact φ).mp sep
    have localSep (a b : B) (e : ∀ z, ψ ((T 1) ^ n * (a * z)) = ψ ((T 1) ^ n * (b * z))) :
        a = b := by
      obtain ⟨a, rfl⟩ := T.surjective a
      obtain ⟨b, rfl⟩ := T.surjective b
      apply congrArg T
      apply sepA
      intro z
      calc
        φ (a * z) = ψ ((T 1) ^ n * (T a * (T z * T 1))) := by
          simpa only [mul_one, mul_assoc] using tri a z 1
        _ = ψ ((T 1) ^ n * (T b * (T z * T 1))) := e (T z * T 1)
        _ = φ (b * z) := by simpa only [mul_one, mul_assoc] using (tri b z 1).symm
    have ht (x y : A) : T x * T y = T 1 * T (x * y) := by
      apply localSep
      intro z
      obtain ⟨v, rfl⟩ := T.surjective z
      rw [← tri, mul_comm (T 1), ← tri, mul_one]
    obtain ⟨v, hv⟩ := T.surjective 1
    obtain ⟨u, hu⟩ : IsUnit (T 1) :=
      isUnit_iff_exists_inv.mpr ⟨T (v * v), by rw [← ht, hv, one_mul]⟩
    let L := T.trans ((u⁻¹).mulLeftLinearEquiv R B)
    have hL (x : A) : L x = (↑u⁻¹ : B) * T x := rfl
    have left : (↑u⁻¹ : B) * (u : B) = 1 := u.inv_val
    have right : (u : B) * (↑u⁻¹ : B) = 1 := u.val_inv
    have h_one : L 1 = 1 := by rw [hL, ← hu, left]
    have h_mul (x y : A) : L (x * y) = L x * L y := by
      calc
        L (x * y) = ((↑u⁻¹ : B) * (u : B)) * ((↑u⁻¹ : B) * T (x * y)) := by
          rw [left, one_mul, hL]
        _ = ((↑u⁻¹ : B) * (↑u⁻¹ : B)) * (T 1 * T (x * y)) := by
          rw [← hu]
          ac_rfl
        _ = L x * L y := by rw [← ht, hL, hL]; ac_rfl
    let σ := AlgEquiv.ofLinearEquiv L h_one h_mul
    have hT (x : A) : T x = (u : B) * σ x := by
      change T x = (u : B) * L x
      rw [hL, ← mul_assoc, right, one_mul]
    refine ⟨σ, u, hT, fun x => ?_⟩
    have e := tri x 1 1
    rw [hT x, ← hu, mul_one, mul_one] at e
    rw [e, pow_add]
    congr 1
    ring
  · rintro ⟨σ, u, hT, h⟩
    exact arity_from_normal n φ ψ T σ u hT h

theorem arity_recovers_unit_contraction (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (T : A ≃ₗ[R] B) (h : Arity n φ ψ T) (x : A) :
    φ x = ψ ((T 1) ^ (n + 2) * T x) := by
  have e := h x 1 1 (List.replicate n 1) (List.length_replicate ..)
  simp only [List.map_replicate, List.prod_replicate, one_pow, mul_one] at e
  rw [e, pow_add]
  congr 1
  ring

theorem arity_separation_descends (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (h : Arity n φ ψ T) :
    radical ψ = ⊥ := by
  obtain ⟨σ, u, hT, hφ⟩ := (arity_normal_form n φ ψ sep T).mp h
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨a, rfl⟩ := σ.surjective x
  have ha : a ∈ radical φ := by
    apply (mem_rad _ _).mpr
    intro t
    rw [hφ, map_mul σ]
    have e : (u : B) ^ (n + 3) * (σ a * σ t) = σ a * ((u : B) ^ (n + 3) * σ t) := by ac_rfl
    rw [e]
    exact (mem_rad _ _).mp hx _
  rw [sep, Submodule.mem_bot] at ha
  simp [ha]

theorem arity_extra_degree_iff_unit_power (n k : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (h : Arity n φ ψ T) :
    Arity (n + k) φ ψ T ↔ (T 1) ^ k = 1 := by
  obtain ⟨σ, u, hT, hφ⟩ := (arity_normal_form n φ ψ sep T).mp h
  have hu : T 1 = (u : B) := by simpa using hT 1
  have sepψ := (radical_separating_exact ψ).mp (arity_separation_descends n φ ψ sep T h)
  constructor
  · intro g
    have e (x : A) : ψ ((u : B) ^ (n + 3) * σ x) =
        ψ ((u : B) ^ (n + 3) * ((u : B) ^ k * σ x)) := by
      have hx := arity_recovers_unit_contraction (n + k) φ ψ T g x
      rw [hu, hT x] at hx
      calc
        _ = φ x := (hφ x).symm
        _ = ψ ((u : B) ^ (n + k + 2) * ((u : B) * σ x)) := hx
        _ = ψ ((u : B) ^ (n + k + 2 + 1) * σ x) := by
          rw [pow_succ (u : B) (n + k + 2), mul_assoc]
        _ = _ := by
          rw [show n + k + 2 + 1 = (n + 3) + k by omega, pow_add (u : B) (n + 3) k, mul_assoc]
    rw [hu]
    apply sepψ
    intro y
    obtain ⟨x, hx⟩ := (((u ^ (n + 3)).mulLeftLinearEquiv R B).surjective y)
    obtain ⟨z, rfl⟩ := σ.surjective x
    change (u : B) ^ (n + 3) * σ z = y at hx
    rw [← hx, one_mul]
    have eq : (u : B) ^ k * ((u : B) ^ (n + 3) * σ z) =
        (u : B) ^ (n + 3) * ((u : B) ^ k * σ z) := by ac_rfl
    rw [eq, ← e]
  · intro g
    apply arity_from_normal (n + k) φ ψ T σ u hT
    intro x
    have g' : (u : B) ^ k = 1 := hu ▸ g
    rw [hφ, show n + k + 3 = (n + 3) + k by omega, pow_add (u : B) (n + 3) k, g', mul_one]

theorem arity_consecutive_recovers_actual_algebra (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (hn : Arity n φ ψ T)
    (hs : Arity (n + 1) φ ψ T) :
    ∃ σ : A ≃ₐ[R] B, (∀ x, T x = σ x) ∧ ∀ x, φ x = ψ (σ x) := by
  obtain ⟨σ, u, hT, hφ⟩ := (arity_normal_form n φ ψ sep T).mp hn
  have h1 : T 1 = 1 := by
    simpa using (arity_extra_degree_iff_unit_power n 1 φ ψ sep T hn).mp hs
  have hu : (u : B) = 1 := by simpa [h1] using (hT 1).symm
  exact ⟨σ, fun x => by simpa [hu] using hT x, fun x => by simpa [hu] using hφ x⟩

theorem arity_all_from_two_consecutive (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) :
    (Arity n φ ψ T ∧ Arity (n + 1) φ ψ T) ↔ ∀ k, Arity k φ ψ T := by
  constructor
  · rintro ⟨hn, hn1⟩ k
    obtain ⟨σ, hT, hφ⟩ := arity_consecutive_recovers_actual_algebra n φ ψ sep T hn hn1
    exact arity_from_normal k φ ψ T σ 1 (by simpa using hT) (by simpa using hφ)
  · intro h
    exact ⟨h n, h (n + 1)⟩

theorem arity_transport_locality_lifts (n : ℕ) (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (T : A ≃ₗ[R] B) :
    Arity n φ ψ T ↔
      ∀ l : List A, l.length = n + 3 →
        φ l.prod = ψ (l.map T).prod := by
  constructor
  · intro h l hl
    rcases l with _ | ⟨x, l⟩
    · simp at hl
    rcases l with _ | ⟨y, l⟩
    · simp at hl
    rcases l with _ | ⟨z, l⟩
    · simp at hl
    have hlen : l.length = n := by simp at hl; omega
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using h x y z l hlen
  · intro h x y z l hl
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using
      h (x :: y :: z :: l) (by simp [hl])

end Arity

section Constrained
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]

/-- All three independent transports of unital associative multiplication are
specified by an algebra equivalence and two units. -/
private theorem normalize_product (X Y Z : A ≃ₗ[R] B) :
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


theorem equal_input_isotopy (T Z : A ≃ₗ[R] B) :
    (∀ x y, Z (x * y) = T x * T y) ↔
      ∃ (a : Bˣ) (σ : A ≃ₐ[R] B),
        (∀ v : B, (a : B) * v = v * (a : B)) ∧
        (∀ x, T x = (a : B) * σ x) ∧
        ∀ x, Z x = (a : B) * σ x * (a : B) := by
  constructor
  · intro h
    obtain ⟨a, b, σ, hX, hY, hZ⟩ := (normalize_product T T Z).mp h
    have e : (a : B) = (b : B) := by
      simpa using (hX 1).symm.trans (hY 1)
    have v : a = b := Units.ext e
    subst b
    refine ⟨a, σ, ?_, hX, hZ⟩
    intro t
    obtain ⟨x, rfl⟩ := σ.surjective t
    exact (hX x).symm.trans (hY x)
  · rintro ⟨a, σ, c, hT, hZ⟩ x y
    rw [hZ, hT x, hT y, map_mul σ, c (σ y)]
    simp only [mul_assoc]

theorem coincident_first_and_output_isotopy (X Y : A ≃ₗ[R] B) :
    (∀ x y, X (x * y) = X x * Y y) ↔
      ∃ (a : Bˣ) (σ : A ≃ₐ[R] B), (∀ x, X x = (a : B) * σ x) ∧ ∀ y, Y y = σ y := by
  constructor
  · intro h
    obtain ⟨a, b, σ, hX, hY, hZ⟩ := (normalize_product X Y X).mp h
    have eb : (a : B) = (a : B) * (b : B) := by simpa using (hX 1).symm.trans (hZ 1)
    have hb : (b : B) = 1 := (a.mulLeftLinearEquiv R B).injective (by simpa using eb.symm)
    exact ⟨a, σ, hX, fun y => by simpa [hb] using hY y⟩
  · rintro ⟨a, σ, hX, hY⟩ x y
    simp only [hX, hY, map_mul σ, mul_assoc]

theorem reversing_input_order_classifies_opposite
    (X Y Z : A ≃ₗ[R] B) (h : ∀ x y, Z (x * y) = Y y * X x) :
    Nonempty (A ≃ₐ[R] Bᵐᵒᵖ) := by
  let U : B ≃ₗ[R] Bᵐᵒᵖ := MulOpposite.opLinearEquiv R
  have h' (x y : A) : (Z.trans U) (x * y) = (X.trans U) x * (Y.trans U) y := by
    change MulOpposite.op (Z (x * y)) = MulOpposite.op (Y y * X x)
    exact congrArg MulOpposite.op (h x y)
  obtain ⟨a, b, σ, -⟩ := (normalize_product (X.trans U) (Y.trans U) (Z.trans U)).mp h'
  exact ⟨σ⟩

theorem product_isotopy_from_spanning_grid (X Y Z : A ≃ₗ[R] B)
    (S T : Set A) (hS : Submodule.span R S = ⊤) (hT : Submodule.span R T = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ T, Z (x * y) = X x * Y y) :
    ∃ σ : A ≃ₐ[R] B, ∃ a b : Bˣ, ∀ x, Z x = (a : B) * σ x * (b : B) := by
  have all_right (x : A) (hx : x ∈ S) (y : A) : Z (x * y) = X x * Y y := by
    let L := Z.toLinearMap.comp (LinearMap.mulLeft R x)
    let M := (LinearMap.mulLeft R (X x)).comp Y.toLinearMap
    have e : L = M := LinearMap.ext_on hT (h x hx)
    exact DFunLike.congr_fun e y
  have all_left (x y : A) : Z (x * y) = X x * Y y := by
    let L := Z.toLinearMap.comp (LinearMap.mulRight R y)
    let M := (LinearMap.mulRight R (Y y)).comp X.toLinearMap
    have e : L = M := LinearMap.ext_on hS (fun z hz => all_right z hz y)
    exact DFunLike.congr_fun e x
  obtain ⟨a, b, σ, _, _, hZ⟩ := (normalize_product X Y Z).mp all_left
  exact ⟨σ, a, b, hZ⟩

theorem three_input_isotopy (X Y W Z : A ≃ₗ[R] B) :
    (∀ x y z, Z (x * y * z) = X x * Y y * W z) ↔
      ∃ (a b c : Bˣ) (σ : A ≃ₐ[R] B),
        (∀ x, X x = (a : B) * σ x) ∧
        (∀ y, Y y = σ y * (b : B)) ∧
        (∀ z, W z = (↑b⁻¹ : B) * σ z * (c : B)) ∧
        ∀ x, Z x = (a : B) * σ x * (c : B) := by
  constructor
  · intro h
    have shape (x : A) : Z x = (X x * Y 1) * W 1 := by simpa using h x 1 1
    have hY₁ : IsUnit (Y 1 * W 1) := by
      have e : (fun t => t * (Y 1 * W 1)) = (X.symm.trans Z : B ≃ₗ[R] B) := by
        funext t
        obtain ⟨x, rfl⟩ := X.surjective t
        simpa [mul_assoc] using (shape x).symm
      apply (right_bijective_iff _).mp
      rw [e]
      exact (X.symm.trans Z).bijective
    have hW₁ : IsUnit (W 1) := by
      obtain ⟨q, hq⟩ := hY₁
      have leftInv : (↑q⁻¹ : B) * Y 1 * W 1 = 1 := by
        rw [mul_assoc, ← hq]
        exact q.inv_val
      have inj : Function.Injective (fun t : B => t * W 1) := by
        intro s t est
        have p (b : B) : ∃ x y, X x * Y y = b := by
          obtain ⟨x, hx⟩ := X.surjective b
          obtain ⟨y, hy⟩ := Y.surjective 1
          exact ⟨x, y, by rw [hx, hy, mul_one]⟩
        obtain ⟨x, y, rfl⟩ := p s
        obtain ⟨x', y', rfl⟩ := p t
        have ez : x * y = x' * y' := Z.injective (by simpa using (h x y 1).trans (est.trans (h x' y' 1).symm))
        have ec := (h x y (W.symm 1)).symm.trans (congrArg (fun u => Z (u * W.symm 1)) ez |>.trans (h x' y' (W.symm 1)))
        simpa using ec
      refine ⟨⟨W 1, (↑q⁻¹ : B) * Y 1, ?_, leftInv⟩, rfl⟩
      apply inj
      change W 1 * ((↑q⁻¹ : B) * Y 1) * W 1 = 1 * W 1
      rw [mul_assoc, leftInv, mul_one, one_mul]
    obtain ⟨c, hc⟩ := hW₁
    let P := Z.trans ((c⁻¹).mulRightLinearEquiv R)
    have bin (x y : A) : P (x * y) = X x * Y y := by
      change Z (x * y) * (↑c⁻¹ : B) = X x * Y y
      have eq : Z (x * y) = X x * Y y * (c : B) := by simpa [hc] using h x y 1
      have ci : (c : B) * (↑c⁻¹ : B) = 1 := c.val_inv
      rw [eq, mul_assoc, ci, mul_one]
    obtain ⟨a, d, σ, hX, hY, hP⟩ := (normalize_product X Y P).mp bin
    have hZ (z : A) : Z z = (a : B) * σ z * ((d * c : Bˣ) : B) := by
      have e : Z z * (↑c⁻¹ : B) = (a : B) * σ z * (d : B) := hP z
      have ic : (↑c⁻¹ : B) * (c : B) = 1 := c.inv_val
      simpa only [Units.val_mul, mul_assoc, ic, mul_one] using congrArg (fun v : B => v * (c : B)) e
    refine ⟨a, d, d * c, σ, hX, hY, ?_, hZ⟩
    intro z
    have e : (a : B) * (d : B) * W z = (a : B) * σ z * ((d * c : Bˣ) : B) := by
      simpa [hX 1, hY 1, hZ z] using (h 1 1 z).symm
    have id₁ : (d : B) * (↑d⁻¹ : B) = 1 := d.val_inv
    apply ((a * d).mulLeftLinearEquiv R B).injective
    change (a : B) * (d : B) * W z =
      ((a : B) * (d : B)) * ((↑d⁻¹ : B) * σ z * ((d * c : Bˣ) : B))
    have rd : (d : B) * ((↑d⁻¹ : B) * σ z * ((d * c : Bˣ) : B)) =
        σ z * ((d * c : Bˣ) : B) := by
      simp only [← mul_assoc, id₁, one_mul]
    calc
      _ = (a : B) * σ z * ((d * c : Bˣ) : B) := e
      _ = (a : B) * (σ z * ((d * c : Bˣ) : B)) := mul_assoc ..
      _ = (a : B) * ((d : B) * ((↑d⁻¹ : B) * σ z * ((d * c : Bˣ) : B))) :=
        congrArg (fun t : B => (a : B) * t) rd.symm
      _ = _ := (mul_assoc ..).symm
  · rintro ⟨a, b, c, σ, hX, hY, hW, hZ⟩ x y z
    have e : (b : B) * (↑b⁻¹ : B) = 1 := b.val_inv
    simp only [hX, hY, hW, hZ, map_mul σ, mul_assoc]
    rw [← mul_assoc (b : B), e, one_mul]

end Constrained

section Volume

variable {K A B : Type*} [Field K] [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] [FiniteDimensional K B]

noncomputable def orientedDet (base T : A ≃ₗ[K] B) : Kˣ := LinearEquiv.det (base.symm.trans T)

noncomputable def normL (a : Bˣ) : Kˣ := LinearEquiv.det (a.mulLeftLinearEquiv K B)
noncomputable def normR (a : Bˣ) : Kˣ := LinearEquiv.det (a.mulRightLinearEquiv K)

private theorem detShape (base : A ≃ₗ[K] B) (X Y Z : A ≃ₗ[K] B)
    (a b : Bˣ) (σ : A ≃ₐ[K] B)
    (hx : ∀ x, X x = (a : B) * σ x)
    (hy : ∀ x, Y x = σ x * (b : B))
    (hz : ∀ x, Z x = (a : B) * σ x * (b : B)) :
    orientedDet base X = normL a * orientedDet base σ.toLinearEquiv ∧
    orientedDet base Y = normR b * orientedDet base σ.toLinearEquiv ∧
    orientedDet base Z = normR b * (normL a * orientedDet base σ.toLinearEquiv) := by
  have xeq : X = σ.toLinearEquiv.trans (a.mulLeftLinearEquiv K B) := by ext x; exact hx x
  have yeq : Y = σ.toLinearEquiv.trans (b.mulRightLinearEquiv K) := by ext x; exact hy x
  have zeq : Z = (σ.toLinearEquiv.trans (a.mulLeftLinearEquiv K B)).trans (b.mulRightLinearEquiv K) := by
    ext x; exact hz x
  rw [xeq, yeq, zeq]
  have endomorphism (T : A ≃ₗ[K] B) (E : B ≃ₗ[K] B) :
      orientedDet base (T.trans E) = LinearEquiv.det E * orientedDet base T := by
    change LinearEquiv.det ((base.symm.trans T).trans E) = _
    exact LinearEquiv.det_trans _ _
  simp only [endomorphism, normL, normR, true_and]

theorem product_determinant_fibres (base : A ≃ₗ[K] B) (d e f : Kˣ) :
    (∃ X Y Z : A ≃ₗ[K] B, (∀ x y, Z (x * y) = X x * Y y) ∧
        orientedDet base X = d ∧ orientedDet base Y = e ∧ orientedDet base Z = f) ↔
      ∃ (σ : A ≃ₐ[K] B) (a b : Bˣ),
        normL a * orientedDet base σ.toLinearEquiv = d ∧
        normR b * orientedDet base σ.toLinearEquiv = e ∧
        normR b * (normL a * orientedDet base σ.toLinearEquiv) = f := by
  constructor
  · rintro ⟨X, Y, Z, h, hdx, hdy, hdz⟩
    obtain ⟨a, b, σ, hx, hy, hz⟩ := (normalize_product X Y Z).mp h
    obtain ⟨dx, dy, dz⟩ := detShape base X Y Z a b σ hx hy hz
    exact ⟨σ, a, b, dx.symm.trans hdx, dy.symm.trans hdy, dz.symm.trans hdz⟩
  · rintro ⟨σ, a, b, hd, he, hf⟩
    let X := σ.toLinearEquiv.trans (a.mulLeftLinearEquiv K B)
    let Y := σ.toLinearEquiv.trans (b.mulRightLinearEquiv K)
    let Z := X.trans (b.mulRightLinearEquiv K)
    have hx (x : A) : X x = (a : B) * σ x := rfl
    have hy (x : A) : Y x = σ x * (b : B) := rfl
    have hz (x : A) : Z x = (a : B) * σ x * (b : B) := rfl
    obtain ⟨dx, dy, dz⟩ := detShape base X Y Z a b σ hx hy hz
    exact ⟨X, Y, Z, (normalize_product X Y Z).mpr ⟨a, b, σ, hx, hy, hz⟩,
      dx.trans hd, dy.trans he, dz.trans hf⟩

theorem product_special_linear_iff (base : A ≃ₗ[K] B) :
    (∃ X Y Z : A ≃ₗ[K] B, (∀ x y, Z (x * y) = X x * Y y) ∧
        orientedDet base X = 1 ∧ orientedDet base Y = 1 ∧ orientedDet base Z = 1) ↔
      ∃ σ : A ≃ₐ[K] B, orientedDet base σ.toLinearEquiv = 1 := by
  rw [product_determinant_fibres]
  constructor
  · rintro ⟨σ, a, b, h₁, h₂, h₃⟩
    rw [h₁, mul_one] at h₃
    exact ⟨σ, by simpa [h₃] using h₂⟩
  · rintro ⟨σ, h⟩
    have oneR : (1 : Bˣ).mulRightLinearEquiv K = LinearEquiv.refl K B := by ext x; simp
    exact ⟨σ, 1, 1, by simp [normL, h], by simp [normR, oneR, h], by simp [normL, normR, oneR, h]⟩

theorem determinant_of_recovered_algebra (base X Y Z : A ≃ₗ[K] B)
    (h : ∀ x y, Z (x * y) = X x * Y y) :
    ∃ σ : A ≃ₐ[K] B, orientedDet base σ.toLinearEquiv =
      orientedDet base X * orientedDet base Y / orientedDet base Z := by
  obtain ⟨a, b, σ, hx, hy, hz⟩ := (normalize_product X Y Z).mp h
  obtain ⟨h₁, h₂, h₃⟩ := detShape base X Y Z a b σ hx hy hz
  refine ⟨σ, ?_⟩
  rw [h₁, h₂, h₃]
  apply eq_div_iff_mul_eq'.mpr
  ac_rfl

theorem product_fixed_input_volumes (base : A ≃ₗ[K] B) (output : Kˣ) :
    (∃ X Y Z : A ≃ₗ[K] B, (∀ x y, Z (x * y) = X x * Y y) ∧
      orientedDet base X = 1 ∧ orientedDet base Y = 1 ∧ orientedDet base Z = output) ↔
    (∃ σ : A ≃ₐ[K] B, orientedDet base σ.toLinearEquiv = output⁻¹) ∧
      (∃ a : Bˣ, normL a = output) ∧ (∃ b : Bˣ, normR b = output) := by
  rw [product_determinant_fibres]
  constructor
  · rintro ⟨σ, a, b, h₁, h₂, h₃⟩
    rw [h₁, mul_one] at h₃
    have eq : orientedDet base σ.toLinearEquiv = output⁻¹ := by
      apply mul_left_cancel (a := output)
      simpa only [← h₃, mul_inv_cancel] using h₂
    have e : normL a = output := by
      rw [eq] at h₁
      apply mul_right_cancel (b := output⁻¹)
      simpa using h₁
    exact ⟨⟨σ, eq⟩, ⟨a, e⟩, ⟨b, h₃⟩⟩
  · rintro ⟨⟨σ, hs⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨σ, a, b, by simp [ha, hs], by simp [hb, hs], by simp [ha, hb, hs]⟩

omit [FiniteDimensional K B] in
theorem product_fixed_output_has_det_ratio (X Y : B ≃ₗ[K] B)
    (h : ∀ x y, x * y = X x * Y y) :
    ∃ a : Bˣ, LinearEquiv.det X = normR a ∧ LinearEquiv.det Y = (normL a)⁻¹ := by
  obtain ⟨u, v, σ, hx, hy, hz⟩ :=
    (normalize_product X Y (LinearEquiv.refl K B)).mp h
  have e (x : B) : x = (u : B) * σ x * (v : B) := hz x
  have uv : (u : B) * (v : B) = 1 := by simpa using (e 1).symm
  have hbv : (v : B) = (↑u⁻¹ : B) := by
    apply (u.mulLeftLinearEquiv K B).injective
    change (u : B) * (v : B) = (u : B) * (↑u⁻¹ : B)
    rw [uv]
    exact u.val_inv.symm
  have xeq : X = u.mulRightLinearEquiv K := by
    ext x
    have ui : (↑u⁻¹ : B) * (u : B) = 1 := u.inv_val
    calc
      X x = (u : B) * σ x := hx x
      _ = ((u : B) * σ x * (v : B)) * (u : B) := by rw [hbv, mul_assoc, ui, mul_one]
      _ = x * (u : B) := by rw [← e]
  have yeq : Y = (u⁻¹).mulLeftLinearEquiv K B := by
    ext x
    have ui : (↑u⁻¹ : B) * (u : B) = 1 := u.inv_val
    calc
      Y x = σ x * (v : B) := hy x
      _ = (↑u⁻¹ : B) * ((u : B) * σ x * (v : B)) := by simp only [← mul_assoc, ui, one_mul]
      _ = (↑u⁻¹ : B) * x := by rw [← e]
  refine ⟨u, by rw [xeq]; rfl, ?_⟩
  rw [yeq, normL, ← map_inv, ← map_inv]

end Volume

section ThreeLeg

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]

def ThreeLeg (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R) (X Y Z : A ≃ₗ[R] B) : Prop :=
  ∀ x y z, φ (x * y * z) = ψ (X x * Y y * Z z)

theorem trilinear_radicals_each_leg (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (X Y Z : A ≃ₗ[R] B) (h : ThreeLeg φ ψ X Y Z) :
    (∀ x, x ∈ radical φ ↔ X x ∈ radical ψ) ∧
    (∀ x, x ∈ radical φ ↔ Y x ∈ radical ψ) ∧
    (∀ x, x ∈ radical φ ↔ Z x ∈ radical ψ) := by
  have first (X Y Z : A ≃ₗ[R] B) (e : ThreeLeg φ ψ X Y Z) (x : A) :
      x ∈ radical φ ↔ X x ∈ radical ψ := by
    simp only [mem_rad]
    constructor
    · intro g b
      obtain ⟨y, hy⟩ := Y.surjective b
      obtain ⟨z, hz⟩ := Z.surjective 1
      rw [← hy, ← mul_one (X x * Y y), ← hz, ← e, mul_assoc]
      exact g (y * z)
    · intro g y
      rw [← mul_one (x * y), e, mul_assoc]
      exact g (Y y * Z 1)
  refine ⟨first X Y Z h, first Y X Z (fun x y z => ?_), first Z X Y (fun x y z => ?_)⟩
  · simpa only [mul_comm y x, mul_comm (X y)] using h y x z
  · calc
      φ (x * y * z) = φ (y * z * x) := by congr 1; ac_rfl
      _ = ψ (X y * Y z * Z x) := h y z x
      _ = ψ (Z x * X y * Y z) := by congr 1; ac_rfl

theorem two_legs_determine_third_mod_radical (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (X Y Z W : A ≃ₗ[R] B) (h : ThreeLeg φ ψ X Y Z) :
    ThreeLeg φ ψ X Y W ↔ ∀ z, W z - Z z ∈ radical ψ := by
  constructor
  · intro g z
    have e (b : B) : ψ (W z * b) = ψ (Z z * b) := by
      obtain ⟨x, hx⟩ := X.surjective b
      obtain ⟨y, hy⟩ := Y.surjective 1
      have k := (g x y z).symm.trans (h x y z)
      rw [hx, hy, mul_one] at k
      simpa only [mul_comm] using k
    exact (weighted_functional_eq_iff ψ _ _).mp (LinearMap.ext e)
  · intro g x y z
    have e := (weighted_functional_eq_iff ψ _ _).mpr (g z)
    calc
      _ = ψ (X x * Y y * Z z) := h x y z
      _ = ψ (Z z * (X x * Y y)) := by rw [mul_comm]
      _ = ψ (W z * (X x * Y y)) := (DFunLike.congr_fun e (X x * Y y)).symm
      _ = _ := by rw [mul_comm]

private theorem middle_unit {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [FiniteDimensional K B]
    (φ : A →ₗ[K] K) (ψ : B →ₗ[K] K) (sep : radical φ = ⊥)
    (X Y Z : A ≃ₗ[K] B) (h : ThreeLeg φ ψ X Y Z) : IsUnit (Y 1) := by
  have hinj : Function.Injective (LinearMap.mulRight K (Y 1)) := by
    intro b c eq
    obtain ⟨a, rfl⟩ := X.surjective b
    obtain ⟨a', rfl⟩ := X.surjective c
    apply congrArg X
    apply (radical_separating_exact φ).mp sep
    intro z
    have e := (h a 1 z).trans ((congrArg (fun t : B => ψ (t * Z z)) eq).trans (h a' 1 z).symm)
    simpa only [mul_one] using e
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  exact isUnit_iff_exists_inv'.mpr ⟨b, hb⟩

theorem three_leg_exact_frobenius_transport {K A B : Type*}
    [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K B]
    (φ : A →ₗ[K] K) (ψ : B →ₗ[K] K) (hφ : radical φ = ⊥) (hψ : radical ψ = ⊥)
    (X Y Z : A ≃ₗ[K] B) :
    ThreeLeg φ ψ X Y Z ↔ ∃ (σ : A ≃ₐ[K] B) (a b c : Bˣ),
      (∀ x, X x = (a : B) * σ x) ∧ (∀ x, Y x = (b : B) * σ x) ∧
      (∀ x, Z x = (c : B) * σ x) ∧ ∀ x, φ x = ψ ((a : B) * b * c * σ x) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := middle_unit φ ψ hφ X Y Z h
    obtain ⟨c, hc⟩ : IsUnit (Z 1) := middle_unit φ ψ hφ X Z Y (by
      intro x y z
      convert h x z y using 1 <;> ac_rfl)
    have sep := (radical_separating_exact ψ).mp hψ
    let P := X.trans (u.mulRightLinearEquiv K)
    have bin (x y : A) : P (x * y) = X x * Y y := by
      change X (x * y) * (u : B) = X x * Y y
      apply sep
      intro t
      obtain ⟨z, rfl⟩ := Z.surjective t
      rw [hu, ← h (x * y) 1 z, ← h x y z, mul_one]
    obtain ⟨a, b, σ, hx, hy, hp⟩ := (normalize_product X Y P).mp bin
    have hz (z : A) : Z z = (c : B) * σ z := by
      have eq : X 1 * Z z = X z * Z 1 := by
        apply sep
        intro t
        obtain ⟨y, rfl⟩ := Y.surjective t
        calc
          _ = ψ (X 1 * Y y * Z z) := congrArg ψ (by ring)
          _ = φ (1 * y * z) := (h 1 y z).symm
          _ = φ (z * y * 1) := by congr 1; simp [mul_comm]
          _ = ψ (X z * Y y * Z 1) := h z y 1
          _ = _ := congrArg ψ (by ring)
      rw [hx 1, hx z, map_one, mul_one, ← hc, mul_assoc, mul_comm (σ z)] at eq
      exact (a.mulLeftLinearEquiv K B).injective eq
    have hy' (x : A) : Y x = (b : B) * σ x := (hy x).trans (mul_comm ..)
    refine ⟨σ, a, b, c, hx, hy', hz, fun x => ?_⟩
    have e := h x 1 1
    simp only [hx x, hy' 1, hz 1, map_one, mul_one] at e
    rw [e]
    congr 1
    ac_rfl
  · rintro ⟨σ, a, b, c, hx, hy, hz, h⟩ x y z
    simp only [h, map_mul σ, hx, hy, hz]
    congr 1
    ac_rfl

theorem third_leg_unique_on_observable_tensor (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (hψ : radical ψ = ⊥) (X Y Z W : A ≃ₗ[R] B)
    (hZ : ThreeLeg φ ψ X Y Z) (hW : ThreeLeg φ ψ X Y W) : W = Z := by
  have h := (two_legs_determine_third_mod_radical φ ψ X Y Z W hZ).mp hW
  ext z
  have e := h z
  rw [hψ, Submodule.mem_bot] at e
  exact sub_eq_zero.mp e

theorem trilinear_representatives_mod_radical (φ : A →ₗ[R] R)
    (a b c x y z : A)
    (hx : a - x ∈ radical φ) (hy : b - y ∈ radical φ) (hz : c - z ∈ radical φ) :
    φ (a * b * c) = φ (x * y * z) := by
  have qa := (weighted_functional_eq_iff φ _ _).mpr hx
  have qb := (weighted_functional_eq_iff φ _ _).mpr hy
  have qc := (weighted_functional_eq_iff φ _ _).mpr hz
  have ea : φ (a * (b * c)) = φ (x * (b * c)) := DFunLike.congr_fun qa (b * c)
  have eb : φ (b * (x * c)) = φ (y * (x * c)) := DFunLike.congr_fun qb (x * c)
  have ec : φ (c * (x * y)) = φ (z * (x * y)) := DFunLike.congr_fun qc (x * y)
  calc
    _ = φ (x * b * c) := by simpa only [mul_assoc] using ea
    _ = φ (b * (x * c)) := congrArg φ (by ring)
    _ = φ (y * (x * c)) := eb
    _ = φ (x * y * c) := congrArg φ (by ring)
    _ = φ (c * (x * y)) := congrArg φ (by ring)
    _ = φ (z * (x * y)) := ec
    _ = _ := congrArg φ (by ring)

theorem trilinear_weighted_ideal_probes (φ : A →ₗ[R] R) (a b : A) (I : Ideal A) :
    (∀ x y z, z ∈ I → φ (a * (x * y * z)) = φ (b * (x * y * z))) ↔
    ∀ z ∈ I, (a - b) * z ∈ radical φ := by
  constructor
  · intro h z hz
    apply (mem_rad _ _).mpr
    intro x
    have g := h x 1 z hz
    rw [mul_one] at g
    simpa only [sub_mul, map_sub, mul_assoc, mul_comm z x, sub_eq_zero] using g
  · intro h x y z hz
    have g := (mem_rad _ _).mp (h z hz) (x * y)
    have e : (a - b) * z * (x * y) = (a - b) * (x * y * z) := by ac_rfl
    rw [e, sub_mul, map_sub, sub_eq_zero] at g
    exact g

theorem coprime_weights_recover_original_radical (φ : A →ₗ[R] R) (a b : A)
    (h : IsCoprime a b) :
    radical (weighted φ a) ⊓ radical (weighted φ b) = radical φ := by
  obtain ⟨u, v, huv⟩ := h
  ext x
  change (x ∈ radical (weighted φ a) ∧ x ∈ radical (weighted φ b)) ↔ x ∈ radical φ
  simp only [weighted_radical_membership]
  constructor
  · rintro ⟨ha, hb⟩
    have j := (radical φ).add_mem ((radical φ).mul_mem_left u ha) ((radical φ).mul_mem_left v hb)
    simpa only [← mul_assoc, ← add_mul, huv, one_mul] using j
  · intro h
    exact ⟨(radical φ).mul_mem_left a h, (radical φ).mul_mem_left b h⟩

end ThreeLeg

section Period

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]

theorem arity_single_period_gives_all_multiples (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (n k : ℕ)
    (hn : Arity n φ ψ T) (h : Arity (n + k) φ ψ T) :
    ∀ j, Arity (n + k * j) φ ψ T := by
  intro j
  have eq := (arity_extra_degree_iff_unit_power n k φ ψ sep T hn).mp h
  apply (arity_extra_degree_iff_unit_power n (k * j) φ ψ sep T hn).mpr
  rw [pow_mul, eq, one_pow]

theorem arity_matches_all_when_reference_is_unit (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (n : ℕ)
    (hn : Arity n φ ψ T) (h : T 1 = 1) :
    ∀ m, Arity m φ ψ T := by
  obtain ⟨σ, u, hT, hφ⟩ := (arity_normal_form n φ ψ sep T).mp hn
  have e : (u : B) = 1 := by simpa [h] using (hT 1).symm
  intro m
  apply arity_from_normal m φ ψ T σ u hT
  simpa only [e, one_pow, one_mul] using hφ

theorem arity_periods_closed_under_addition (φ : A →ₗ[R] R) (ψ : B →ₗ[R] R)
    (sep : radical φ = ⊥) (T : A ≃ₗ[R] B) (n k j : ℕ)
    (hn : Arity n φ ψ T) (hk : Arity (n + k) φ ψ T) (hj : Arity (n + j) φ ψ T) :
    Arity (n + (k + j)) φ ψ T := by
  have e := (arity_extra_degree_iff_unit_power n k φ ψ sep T hn).mp hk
  have f := (arity_extra_degree_iff_unit_power n j φ ψ sep T hn).mp hj
  apply (arity_extra_degree_iff_unit_power n (k + j) φ ψ sep T hn).mpr
  rw [pow_add, e, f, one_mul]

end Period

end C200
