import Mathlib

namespace BlindHundredB

section AnchoredActions

variable {G H ι : Type*} [Group G] [Group H]

/-- One invertible anchor trades two unknown basis changes for one, with both
character values retained as exact constraints. -/
theorem anchored_left_right_character (A B : ι → G) (o : ι)
    (χ : G →* H) (u v : H) :
    (∃ x y : G, χ x = u ∧ χ y = v ∧ ∀ i, x * A i = B i * y) ↔
    (∃ x : G, χ x = u ∧ χ ((B o)⁻¹ * x * A o) = v ∧
       ∀ i, x * (A i * (A o)⁻¹) = (B i * (B o)⁻¹) * x) := by
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have he : (B o)⁻¹ * x * A o = y := by
      rw [mul_assoc, h o]
      group
    refine ⟨x, hx, by simpa [he] using hy, ?_⟩
    intro i
    rw [← mul_assoc, h i, ← he]
    group
  · rintro ⟨x, hx, hy, h⟩
    refine ⟨x, (B o)⁻¹ * x * A o, hx, hy, ?_⟩
    intro i
    have he := congrArg (· * A o) (h i)
    calc
      x * A i = (x * (A i * (A o)⁻¹)) * A o := by group
      _ = ((B i * (B o)⁻¹) * x) * A o := he
      _ = B i * ((B o)⁻¹ * x * A o) := by group

/-- Prescribing both changes to the character kernel adds just one anchor
character equality to the normalized single-transporter problem. -/
theorem anchored_special_equivalence (A B : ι → G) (o : ι) (χ : G →* H) :
    (∃ x y : G, χ x = 1 ∧ χ y = 1 ∧ ∀ i, x * A i = B i * y) ↔
    χ (A o) = χ (B o) ∧
    (∃ x : G, χ x = 1 ∧
       ∀ i, x * (A i * (A o)⁻¹) = (B i * (B o)⁻¹) * x) := by
  rw [anchored_left_right_character A B o χ]
  constructor
  · rintro ⟨x, hx, hy, h⟩
    rw [map_mul, map_mul, map_inv, hx, mul_one, inv_mul_eq_one] at hy
    exact ⟨hy.symm, x, hx, h⟩
  · rintro ⟨he, x, hx, h⟩
    exact ⟨x, hx, by simp [hx, he], h⟩

/-- A single congruence equation at an invertible anchor plus simultaneous
conjugacy of normalized slices is equivalent to the whole congruence system. -/
theorem anchored_congruence (σ : G → G) (A B : ι → G) (o : ι) (x : G) :
    (∀ i, x * A i * σ x = B i) ↔
    x * A o * σ x = B o ∧
    (∀ i, x * (A i * (A o)⁻¹) = (B i * (B o)⁻¹) * x) := by
  constructor
  · intro h
    refine ⟨h o, fun i => ?_⟩
    rw [← h i, ← h o]
    group
  · rintro ⟨h₀, h⟩ i
    calc
      x * A i * σ x = x * (A i * (A o)⁻¹) * (A o * σ x) := by group
      _ = ((B i * (B o)⁻¹) * x) * (A o * σ x) := by rw [h i]
      _ = (B i * (B o)⁻¹) * (x * A o * σ x) := by group
      _ = B i := by rw [h₀]; group

/-- A single normalized transporter and a centralizer describe exactly all
character values realized by simultaneous conjugators. -/
theorem transporter_character_coset (A B : ι → G) (χ : G →* H) (x₀ : G)
    (h₀ : ∀ i, x₀ * A i = B i * x₀) (t : H) :
    (∃ x : G, χ x = t ∧ ∀ i, x * A i = B i * x) ↔
    (∃ c : G, χ x₀ * χ c = t ∧ ∀ i, c * A i = A i * c) := by
  constructor
  · rintro ⟨x, hχ, hx⟩
    refine ⟨x₀⁻¹ * x, by rw [← map_mul, ← mul_assoc, mul_inv_cancel, one_mul, hχ], ?_⟩
    intro i
    have he : B i = x₀ * A i * x₀⁻¹ := by
      rw [h₀]
      group
    rw [mul_assoc, hx i, he]
    group
  · rintro ⟨c, hχ, hc⟩
    refine ⟨x₀ * c, by rw [map_mul, hχ], ?_⟩
    intro i
    rw [mul_assoc, hc i, ← mul_assoc, h₀, mul_assoc]

/-- Near an existing left-right transporter, the simultaneous stabilizer of
the normalized source gives the exact two-character feasibility condition. -/
theorem left_right_character_fiber (A B : ι → G) (o : ι) (χ : G →* H)
    (x₀ y₀ : G) (h₀ : ∀ i, x₀ * A i = B i * y₀) (u v : H) :
    (∃ x y : G, χ x = u ∧ χ y = v ∧ ∀ i, x * A i = B i * y) ↔
    (∃ c : G, χ x₀ * χ c = u ∧ χ y₀ * χ ((A o)⁻¹ * c * A o) = v ∧
      ∀ i, c * (A i * (A o)⁻¹) = (A i * (A o)⁻¹) * c) := by
  rw [anchored_left_right_character A B o χ]
  have he : y₀ = (B o)⁻¹ * x₀ * A o := by
    rw [mul_assoc, h₀ o]
    group
  have hN : ∀ i, x₀ * (A i * (A o)⁻¹) = (B i * (B o)⁻¹) * x₀ := by
    intro i
    rw [← mul_assoc, h₀ i, he]
    group
  have hy (c : G) :
      (B o)⁻¹ * (x₀ * c) * A o = y₀ * ((A o)⁻¹ * c * A o) := by
    rw [he]
    group
  constructor
  · rintro ⟨x, hx, hv, h⟩
    let c := x₀⁻¹ * x
    have hxc : x = x₀ * c := by dsimp [c]; group
    rw [hxc, map_mul] at hx
    rw [hxc, hy, map_mul] at hv
    refine ⟨c, hx, hv, ?_⟩
    intro i
    apply mul_left_cancel (a := x₀)
    calc
      x₀ * (c * (A i * (A o)⁻¹)) = (x₀ * c) * (A i * (A o)⁻¹) := (mul_assoc ..).symm
      _ = x * (A i * (A o)⁻¹) := congrArg (· * (A i * (A o)⁻¹)) hxc.symm
      _ = (B i * (B o)⁻¹) * x := h i
      _ = ((B i * (B o)⁻¹) * x₀) * c := by rw [hxc]; group
      _ = x₀ * ((A i * (A o)⁻¹) * c) := by rw [← hN i, mul_assoc]
  · rintro ⟨c, hc, hv, h⟩
    refine ⟨x₀ * c, by rwa [map_mul], by rwa [hy, map_mul], ?_⟩
    intro i
    rw [mul_assoc, h i, ← mul_assoc, hN, mul_assoc]

end AnchoredActions

section Graph

variable {V G H : Type*} [Group G] [Group H]
variable {E : V → V → Type*}

universe uV uE

inductive Path {V : Type uV} (E : V → V → Type uE) : V → V → Type (max uV uE)
  | nil (i : V) : Path E i i
  | step {i j k : V} (e : E i j) (tail : Path E j k) : Path E i k

def Path.weight (A : {i j : V} → E i j → G) {i j : V} : Path E i j → G
  | .nil _ => 1
  | .step e q => A e * q.weight A

/-- Edge gauges transport the weight of every finite directed path through
its two endpoints. -/
theorem path_weight_transport (A B : {i j : V} → E i j → G)
    (g : V → G) (h : ∀ i j (e : E i j), g i * A e = B e * g j)
    {i j : V} (q : Path E i j) :
    g i * q.weight A = q.weight B * g j := by
  induction q with
  | nil => simp [Path.weight]
  | @step i j k e q ih =>
    simp only [Path.weight]
    calc
      g i * (A e * q.weight A) = (g i * A e) * q.weight A := (mul_assoc ..).symm
      _ = (B e * g j) * q.weight A := by rw [h]
      _ = B e * (q.weight B * g k) := by rw [mul_assoc, ih]
      _ = (B e * q.weight B) * g k := (mul_assoc ..).symm

def basedLabel (A : {i j : V} → E i j → G) {o : V}
    (q : ∀ i, Path E o i) {i j : V} (e : E i j) : G :=
  (q i).weight A * A e * ((q j).weight A)⁻¹

/-- One conjugator of the based edge labels lifts to a gauge at all vertices.
The chosen root path at the root is empty. -/
theorem graph_gauge_iff (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o) (z : G) :
    (∃ g : V → G, g o = z ∧ ∀ i j (e : E i j), g i * A e = B e * g j) ↔
    (∀ i j (e : E i j), z * basedLabel A q e = basedLabel B q e * z) := by
  constructor
  · rintro ⟨g, hg, h⟩ i j e
    have hi := path_weight_transport A B g h (q i)
    have hj := path_weight_transport A B g h (q j)
    rw [hg] at hi hj
    simp only [basedLabel]
    calc
      z * ((q i).weight A * A e * ((q j).weight A)⁻¹)
          = (z * (q i).weight A) * A e * ((q j).weight A)⁻¹ := by group
      _ = (q i).weight B * (g i * A e) * ((q j).weight A)⁻¹ := by rw [hi]; group
      _ = (q i).weight B * B e * (g j * ((q j).weight A)⁻¹) := by rw [h]; group
      _ = (q i).weight B * B e * (((q j).weight B)⁻¹ * z) := by
        congr 1
        calc
          g j * ((q j).weight A)⁻¹
              = ((q j).weight B)⁻¹ * ((q j).weight B * g j) * ((q j).weight A)⁻¹ := by group
          _ = ((q j).weight B)⁻¹ * z := by rw [← hj]; group
      _ = (q i).weight B * B e * ((q j).weight B)⁻¹ * z := by group
  · intro h
    let g := fun i => ((q i).weight B)⁻¹ * z * (q i).weight A
    refine ⟨g, by simp [g, hq, Path.weight], ?_⟩
    intro i j e
    have he := congrArg (fun v => ((q i).weight B)⁻¹ * v * (q j).weight A) (h i j e)
    simp only [basedLabel] at he
    calc
      g i * A e =
          ((q i).weight B)⁻¹ * (z * ((q i).weight A * A e *
            ((q j).weight A)⁻¹)) * (q j).weight A := by dsimp [g]; group
      _ = ((q i).weight B)⁻¹ * ((q i).weight B * B e *
            ((q j).weight B)⁻¹ * z) * (q j).weight A := he
      _ = B e * g j := by dsimp [g]; group

/-- If all vertices are reachable from the root, fixing its gauge determines
the gauge uniquely, even when some vertex has many paths from the root. -/
theorem graph_gauge_root_rigid (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (g g' : V → G) (h₀ : g o = g' o)
    (h : ∀ i j (e : E i j), g i * A e = B e * g j)
    (h' : ∀ i j (e : E i j), g' i * A e = B e * g' j) : g = g' := by
  funext i
  apply mul_left_cancel (a := (q i).weight B)
  rw [← path_weight_transport A B g h (q i), ← path_weight_transport A B g' h' (q i), h₀]

/-- Flat based labels are exactly the path-independent edge system that
can be switched to unit labels. -/
theorem graph_flat_iff (A : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o) :
    (∃ g : V → G, g o = 1 ∧ ∀ i j (e : E i j), A e = (g i)⁻¹ * g j) ↔
    (∀ i j (e : E i j), basedLabel A q e = 1) := by
  let B : {i j : V} → E i j → G := fun {_ _} _ => 1
  have wone {i j : V} (p : Path E i j) : p.weight B = 1 := by
    induction p with
    | nil => rfl
    | step e p ih => simp [Path.weight, B, ih]
  rw [show (∀ i j (e : E i j), basedLabel A q e = 1) ↔
      (∀ i j (e : E i j), (1 : G) * basedLabel A q e = basedLabel B q e * 1) by
        simp [basedLabel, B, wone]]
  rw [← graph_gauge_iff A B q hq]
  constructor
  · rintro ⟨g, h₀, h⟩
    refine ⟨g, h₀, fun i j e => ?_⟩
    rw [h]
    simp [B]
  · rintro ⟨g, h₀, h⟩
    refine ⟨g, h₀, fun i j e => ?_⟩
    exact (eq_inv_mul_iff_mul_eq).2 (by simpa [B] using h i j e)

/-- Edge gauges transport a character along paths. This tracks a determinant
budget at every vertex through the character of the chosen path. -/
theorem path_character_budget (A B : {i j : V} → E i j → G)
    (χ : G →* H) (g : V → G)
    (h : ∀ i j (e : E i j), g i * A e = B e * g j) {i j : V} (p : Path E i j) :
    χ (g j) = (χ (p.weight B))⁻¹ * χ (g i) * χ (p.weight A) := by
  have he := congrArg χ (path_weight_transport A B g h p)
  simp only [map_mul] at he
  rw [mul_assoc, he]
  group

end Graph


section Spectral

open Matrix
variable {K n A : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A labelled collection of diagonal anchors imposes an explicit zero pattern
on every linear transporter, even for repeated eigenvalues in each individual
anchor. -/
theorem diagonal_anchor_intertwiner_iff (a b : A → n → K) (X : Matrix n n K) :
    (∀ t, X * diagonal (a t) = diagonal (b t) * X) ↔
    (∀ i j, (∃ t, a t j ≠ b t i) → X i j = 0) := by
  constructor
  · intro h i j ⟨t, ht⟩
    have he := congrArg (fun M : Matrix n n K => M i j) (h t)
    simp only [mul_diagonal, diagonal_mul] at he
    by_contra hz
    apply ht
    apply mul_left_cancel₀ hz
    exact he.trans (mul_comm ..)
  · intro h t
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases ht : a t j = b t i
    · rw [ht, mul_comm]
    · rw [h i j ⟨t, ht⟩, zero_mul, mul_zero]

/-- When labels classify the indices jointly, an invertible transporter
between tuples with the same fixed anchors is precisely a diagonal scaling
operator with nonzero entries satisfying the scaling equations. -/
theorem anchored_diagonal_conjugacy (a : A → n → K)
    (ha : Function.Injective (fun i t => a t i))
    {ι : Type*} (M N : ι → Matrix n n K) :
    (∃ X Y : Matrix n n K, X * Y = 1 ∧ Y * X = 1 ∧
      (∀ t, X * diagonal (a t) = diagonal (a t) * X) ∧
      ∀ t, X * M t = N t * X) ↔
      (∃ d : n → K, (∀ i, d i ≠ 0) ∧ ∀ t i j, d i * M t i j = N t i j * d j) := by
  constructor
  · rintro ⟨X, Y, hXY, _, hX, h⟩
    have zero : ∀ i j, i ≠ j → X i j = 0 := by
      intro i j hij
      apply (diagonal_anchor_intertwiner_iff a a X).mp hX i j
      by_contra hn
      push Not at hn
      exact hij ((ha (funext hn)).symm)
    have he : X = diagonal (fun i => X i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [diagonal_apply_ne _ hij, zero i j hij]
    refine ⟨fun i => X i i, ?_, ?_⟩
    · intro i hi
      have hf := congrArg (fun X : Matrix n n K => X i i) hXY
      rw [he] at hf
      simpa [diagonal_mul, hi] using hf
    · intro t i j
      have hf := congrArg (fun X : Matrix n n K => X i j) (h t)
      rw [he] at hf
      simpa only [diagonal_mul, mul_diagonal] using hf
  · rintro ⟨d, hd, h⟩
    refine ⟨diagonal d, diagonal (fun i => (d i)⁻¹), ?_, ?_, ?_, ?_⟩
    · rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hd i))
    · rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hd i))
    · intro t
      exact (commute_diagonal _ _).eq
    · intro t
      ext i j
      simpa only [diagonal_mul, mul_diagonal] using h t i j

/-- For a complete set of labelled anchors, distinct dimensions of the
matched source and target blocks rule out a transporter in characteristic
where that cardinal difference survives. -/
theorem diagonal_support_trace_certificate (a b : A → n → K) (X Y : Matrix n n K)
    (hx : ∀ t, X * diagonal (a t) = diagonal (b t) * X)
    (hXY : X * Y = 1) (hYX : Y * X = 1)
    (u v : n → K)
    (paired : ∀ i j, (∀ t, a t j = b t i) → u j = v i) :
    (∑ j, u j) = ∑ i, v i := by
  have h : X * diagonal u = diagonal v * X := by
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases h' : ∀ t, a t j = b t i
    · rw [paired i j h', mul_comm]
    · push Not at h'
      rw [(diagonal_anchor_intertwiner_iff a b X).mp hx i j h', zero_mul, mul_zero]
  have he := congrArg Matrix.trace (congrArg (Y * ·) h)
  rw [← Matrix.mul_assoc, hYX, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hXY, Matrix.one_mul] at he
  simpa using he

end Spectral

section Certificates

variable {R : Type*} [Ring R]

/-- Exact cubic certificate for reverse transport from the forward equation and
the two inverse equations. -/
theorem cubic_reverse_transport (x y a b : R) :
    a * y - y * b =
      y * (x * a - b * x) * y - (y * x - 1) * a * y + y * b * (x * y - 1) := by
  noncomm_ring

/-- Two independently measured residuals suffice for a commutator test. -/
theorem commutator_transport_residual (x a b c d : R) :
    x * (a * b - b * a) - (c * d - d * c) * x =
      (x * a - c * x) * b + c * (x * b - d * x)
      - (x * b - d * x) * a - d * (x * a - c * x) := by
  noncomm_ring

/-- A two-sided transporter sends a polynomial identity with a scalar
offset to the corresponding scalar offset. -/
theorem scalar_residual_certificate (x y a b : R) :
    a - b = (1 - y * x) * a + y * (x * a - x * b) + (y * x - 1) * b := by
  noncomm_ring

/-- One-sided inversion is sufficient to transport a polynomial relation
whenever its target vanishes. This identity identifies all individual blocks
of the annihilator certificate. -/
theorem left_inverse_defect_certificate (x y p q : R) :
    p = y * (x * p - q * x) + y * q * x + (1 - y * x) * p := by
  noncomm_ring

/-- Perturbing a common invertible slice does not introduce another unknown in
the normalized intertwining system. The non-anchor slices may be singular. -/
theorem singular_slices_left_right {ι : Type*} (A B : ι → R)
    (a b : Rˣ) (o : ι) (ha : A o = a) (hb : B o = b) (x y : R) :
    (∀ i, x * A i = B i * y) ↔
    y = ↑b⁻¹ * x * ↑a ∧
      ∀ i, x * (A i * ↑a⁻¹) = (B i * ↑b⁻¹) * x := by
  constructor
  · intro h
    have h₀ : x * ↑a = ↑b * y := by simpa [ha, hb] using h o
    have e : y = ↑b⁻¹ * x * ↑a := by
      simpa only [mul_assoc, h₀, ← mul_assoc (↑b⁻¹ : R), Units.inv_mul, one_mul]
    refine ⟨e, ?_⟩
    intro i
    rw [← mul_assoc, h i, e]
    simp only [mul_assoc, ← mul_assoc (↑a : R), Units.mul_inv, mul_one]
  · rintro ⟨rfl, h⟩ i
    have he := congrArg (· * (↑a : R)) (h i)
    simpa only [mul_assoc, Units.inv_mul, mul_one] using he

end Certificates


section Quotients

variable {K S V W O I : Type*} [Ring K]
variable [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] [AddCommGroup O] [Module K O]

private theorem linear_transport (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (hf : Function.Surjective f) (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ T : V →ₗ[K] W, ∀ s, T (f s) = g s := by
  let E := f.quotKerEquivOfSurjective hf
  refine ⟨((LinearMap.ker f).liftQ g h).comp E.symm.toLinearMap, ?_⟩
  intro s
  change (LinearMap.ker f).liftQ g h (E.symm (f s)) = g s
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- A surjective probe family can be sent through a uniquely determined
linear map exactly when the target obeys all source relations. -/
theorem surjective_probe_transport_iff (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (hf : Function.Surjective f) :
    (∃! T : V →ₗ[K] W, ∀ s, T (f s) = g s) ↔ LinearMap.ker f ≤ LinearMap.ker g := by
  constructor
  · rintro ⟨T, hT, _⟩ s hs
    rw [LinearMap.mem_ker] at hs ⊢
    rw [← hT, hs, map_zero]
  · intro h
    obtain ⟨T, hT⟩ := linear_transport f g hf h
    refine ⟨T, hT, fun U hU => ?_⟩
    ext x
    obtain ⟨s, rfl⟩ := hf x
    rw [hU, hT]

/-- The relation kernel of a surjective generator probe is a complete pointed
orbit invariant over an arbitrary scalar ring. -/
theorem relation_kernel_equivalence (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (∃! T : V ≃ₗ[K] W, ∀ s, T (f s) = g s) ↔ LinearMap.ker f = LinearMap.ker g := by
  constructor
  · rintro ⟨T, hT, _⟩
    ext s
    simp only [LinearMap.mem_ker]
    rw [← hT]
    exact ⟨fun hs => by rw [hs, map_zero], fun hs => T.injective (by simpa using hs)⟩
  · intro h
    obtain ⟨T, hT⟩ := linear_transport f g hf h.le
    obtain ⟨U, hU⟩ := linear_transport g f hg h.ge
    have hinj : Function.Injective T := by
      intro x y hx
      obtain ⟨s, rfl⟩ := hf x
      obtain ⟨t, rfl⟩ := hf y
      rw [hT, hT] at hx
      rw [← hU s, ← hU t, hx]
    have hsurj : Function.Surjective T := by
      intro y
      obtain ⟨s, rfl⟩ := hg y
      exact ⟨f s, hT s⟩
    let E := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
    refine ⟨E, hT, fun F hF => ?_⟩
    ext x
    obtain ⟨s, rfl⟩ := hf x
    exact (hF s).trans (hT s).symm

/-- Equality of probe kernels yields the same unique transporter for every
labelled operator induced from a common operator on the probe space. -/
theorem common_probe_simultaneous_equivalence (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (C : I → S →ₗ[K] S) (A : I → V →ₗ[K] V) (B : I → W →ₗ[K] W)
    (hA : ∀ i s, f (C i s) = A i (f s)) (hB : ∀ i s, g (C i s) = B i (g s)) :
    (∃! T : V ≃ₗ[K] W, (∀ s, T (f s) = g s) ∧
      ∀ i x, T (A i x) = B i (T x)) ↔ LinearMap.ker f = LinearMap.ker g := by
  constructor
  · rintro ⟨T, ⟨hT, _⟩, _⟩
    ext s
    simp only [LinearMap.mem_ker]
    rw [← hT]
    exact ⟨fun hs => by rw [hs, map_zero], fun hs => T.injective (by simpa using hs)⟩
  · intro h
    obtain ⟨T, hT, hu⟩ := (relation_kernel_equivalence f g hf hg).2 h
    refine ⟨T, ⟨hT, ?_⟩, fun U hU => hu U hU.1⟩
    intro i x
    obtain ⟨s, rfl⟩ := hf x
    rw [← hA, hT, hB, hT]

/-- Two injective observation maps determine a unique transporter preserving
observations exactly when their observation ranges agree. -/
theorem observation_range_equivalence (f : V →ₗ[K] O) (g : W →ₗ[K] O)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (∃! T : V ≃ₗ[K] W, ∀ x, g (T x) = f x) ↔ LinearMap.range f = LinearMap.range g := by
  constructor
  · rintro ⟨T, hT, _⟩
    ext x
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨T y, hT y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨T.symm y, by rw [← hT, T.apply_symm_apply]⟩
  · intro h
    let e₁ := LinearEquiv.ofInjective f hf
    let e₂ := LinearEquiv.ofInjective g hg
    let T := (e₁.trans (LinearEquiv.ofEq _ _ h)).trans e₂.symm
    have hT (x : V) : g (T x) = f x := by
      simp [T, e₁, e₂]
    refine ⟨T, hT, fun U hU => ?_⟩
    ext x
    exact hg ((hU x).trans (hT x).symm)

/-- Operators observed faithfully in the same ambient system are all
intertwined by the unique equality-of-observations map. -/
theorem common_observation_simultaneous_equivalence
    (f : V →ₗ[K] O) (g : W →ₗ[K] O)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (C : I → O →ₗ[K] O) (A : I → V →ₗ[K] V) (B : I → W →ₗ[K] W)
    (hA : ∀ i v, f (A i v) = C i (f v))
    (hB : ∀ i w, g (B i w) = C i (g w)) :
    (∃! T : V ≃ₗ[K] W, (∀ v, g (T v) = f v) ∧
       ∀ i v, T (A i v) = B i (T v)) ↔ LinearMap.range f = LinearMap.range g := by
  constructor
  · rintro ⟨T, ⟨hT, _⟩, _⟩
    ext x
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨T y, hT y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨T.symm y, by rw [← hT, T.apply_symm_apply]⟩
  · intro h
    obtain ⟨T, hT, hu⟩ := (observation_range_equivalence f g hf hg).2 h
    refine ⟨T, ⟨hT, ?_⟩, fun U hU => hu U hU.1⟩
    intro i x
    apply hg
    rw [hT, hA, hB, hT]

/-- Two probe-observation factorizations of the same map have a unique
state change whenever both factorizations are reachable and observable. -/
theorem minimal_factorization_equivalence
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (u : V →ₗ[K] O) (v : W →ₗ[K] O)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    (∃! T : V ≃ₗ[K] W, (∀ s, T (f s) = g s) ∧ ∀ x, v (T x) = u x) ↔
      u.comp f = v.comp g := by
  constructor
  · rintro ⟨T, ⟨hT, hc⟩, _⟩
    ext s
    change u (f s) = v (g s)
    rw [← hT, hc]
  · intro h
    have he (s : S) : u (f s) = v (g s) := DFunLike.congr_fun h s
    have hk : LinearMap.ker f = LinearMap.ker g := by
      ext s
      simp only [LinearMap.mem_ker]
      constructor
      · intro hs
        apply hv
        rw [← he, hs, map_zero, map_zero]
      · intro hs
        apply hu
        rw [he, hs, map_zero, map_zero]
    obtain ⟨T, hT, hU⟩ := (relation_kernel_equivalence f g hf hg).2 hk
    refine ⟨T, ⟨hT, ?_⟩, fun U hU' => hU U hU'.1⟩
    intro x
    obtain ⟨s, rfl⟩ := hf x
    rw [hT, ← he]

/-- A faithful observation map turns equality of induced effects into an exact
test that a labelled linear tuple descends through a surjective probe. -/
theorem intertwiner_from_probe_observation
    (f : S →ₗ[K] V) (g : W →ₗ[K] O) (T : V →ₗ[K] W)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (A : I → V →ₗ[K] V) (B : I → W →ₗ[K] W) :
    (∀ i s, g (T (A i (f s))) = g (B i (T (f s)))) ↔
    (∀ i x, T (A i x) = B i (T x)) := by
  constructor
  · intro h i x
    obtain ⟨s, rfl⟩ := hf x
    exact hg (h i s)
  · intro h i s
    rw [h]

end Quotients

end BlindHundredB
