import Mathlib

open Matrix

namespace TwoHundredB

section Supports

variable {K n I J : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Two coordinate indices belong to the same component when they are joined
by nonzero entries in the tuple. Orientations are forgotten. -/
def SupportSetoid (A : I → Matrix n n K) : Setoid n where
  r := Relation.EqvGen (fun i j => ∃ t, A t i j ≠ 0)
  iseqv := ⟨Relation.EqvGen.refl, fun h => h.symm _ _, fun h h' => h.trans _ _ _ h'⟩

abbrev Component (A : I → Matrix n n K) := Quotient (SupportSetoid A)

def component (A : I → Matrix n n K) (i : n) : Component A :=
  Quotient.mk _ i

def twist (v : n → K) (A : I → Matrix n n K) (t : I) : Matrix n n K :=
  fun i j => v i / v j * A t i j

def Transport (a : J → n → K) (A B : I → Matrix n n K) (X : Matrix n n K) : Prop :=
  (∀ t, X * diagonal (a t) = diagonal (a t) * X) ∧
    ∀ t, X * A t = B t * X

private theorem component_edge {A : I → Matrix n n K} {i j : n}
    (h : ∃ t, A t i j ≠ 0) : component A i = component A j :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

private theorem diag_form (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (X : Matrix n n K) (h : ∀ t, X * diagonal (a t) = diagonal (a t) * X) :
    X = diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [diagonal_apply_ne _ hij]
    by_contra hz
    apply hij
    apply ha
    funext t
    have hc := congrArg (fun M : Matrix n n K => M i j) (h t)
    simp only [mul_diagonal, diagonal_mul] at hc
    apply mul_left_cancel₀ hz
    exact (hc.trans (mul_comm _ _)).symm

/-- With a jointly separating diagonal anchor family, all transporters
of a weighted tuple are diagonal and normalized diagonals are arbitrary
functions on the support components. Singular transporters are included. -/
theorem component_transport_classification
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (X : Matrix n n K) :
    Transport a A (twist v A) X ↔
      ∃ c : Component A → K, X = diagonal (fun i => v i * c (component A i)) := by
  constructor
  · rintro ⟨hA, hT⟩
    have hd := diag_form a ha X hA
    let d : n → K := fun i => X i i / v i
    have hstep (i j : n) (h : ∃ t, A t i j ≠ 0) : d i = d j := by
      obtain ⟨t, hn⟩ := h
      have he := congrArg (fun M : Matrix n n K => M i j) (hT t)
      rw [hd] at he
      simp only [diagonal_mul, mul_diagonal, twist] at he
      apply mul_right_cancel₀ hn
      dsimp [d]
      calc
        X i i / v i * A t i j = (X i i * A t i j) / v i := by ring
        _ = (v i / v j * A t i j * X j j) / v i := congrArg (· / v i) he
        _ = X j j / v j * A t i j := by field_simp [hv i, hv j] <;> ring
    have hconst (i j : n) (h : (SupportSetoid A).r i j) : d i = d j := by
      change Relation.EqvGen _ i j at h
      induction h with
      | rel i j h => exact hstep i j h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
    let c : Component A → K := Quotient.lift d hconst
    refine ⟨c, hd.trans (?_ : diagonal (fun i => X i i) = _)⟩
    congr 1
    funext i
    change X i i = v i * (X i i / v i)
    field_simp [hv i]
  · rintro ⟨c, rfl⟩
    refine ⟨fun t => (Matrix.commute_diagonal _ _).eq, ?_⟩
    intro t
    ext i j
    simp only [diagonal_mul, mul_diagonal, twist]
    by_cases hz : A t i j = 0
    · simp [hz]
    · rw [component_edge (A := A) ⟨t, hz⟩]
      field_simp [hv j] <;> ring

def detTransport (a : J → n → K) (A B : I → Matrix n n K) (d : K) : Prop :=
  ∃ X : Matrix n n K, X.det = d ∧ Transport a A B X

private theorem component_det (A : I → Matrix n n K) (v : n → K)
    (c : Component A → K) :
    (diagonal (fun i => v i * c (component A i))).det =
      (∏ i, v i) * ∏ i, c (component A i) := by
  rw [det_diagonal, Finset.prod_mul_distrib]

/-- Exact determinant range for any weighted tuple with a separating anchor
family. Component cardinalities enter as multiplicities in the product. -/
theorem component_determinant_range
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (d : K) :
    detTransport a A (twist v A) d ↔
      ∃ c : Component A → K, (∏ i, v i) * (∏ i, c (component A i)) = d := by
  constructor
  · rintro ⟨X, hX, hT⟩
    obtain ⟨c, rfl⟩ := (component_transport_classification a ha A v hv X).mp hT
    exact ⟨c, (component_det A v c).symm.trans hX⟩
  · rintro ⟨c, h⟩
    refine ⟨diagonal (fun i => v i * c (component A i)), (component_det A v c).trans h, ?_⟩
    exact (component_transport_classification a ha A v hv _).mpr ⟨c, rfl⟩

/-- Exact monomial determinant formula indexed once per component. The
individual exponents are the sizes of the corresponding vertex fibres. -/
theorem component_power_range
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (d : K)
    [Fintype (Component A)] [DecidableEq (Component A)] :
    detTransport a A (twist v A) d ↔
      ∃ c : Component A → K,
        (∏ i, v i) * (∏ j, c j ^ ((Finset.univ.filter (fun i => component A i = j)).card)) = d := by
  have hp (c : Component A → K) :
      (∏ j, c j ^ ((Finset.univ.filter (fun i => component A i = j)).card)) =
        ∏ i, c (component A i) := by
    simpa only [Finset.prod_const] using
      Finset.prod_fiberwise_of_maps_to'
        (s := (Finset.univ : Finset n)) (t := Finset.univ)
        (g := component A) (fun i _ => Finset.mem_univ _) c
  simp only [hp, component_determinant_range a ha A v hv]

/-- A singleton support component makes every determinant attainable over
the original field, even when other components admit only power values. -/
theorem singleton_component_removes_determinant_obstruction
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (i₀ : n)
    (hi : ∀ i, component A i = component A i₀ → i = i₀) (d : K) :
    detTransport a A (twist v A) d := by
  classical
  apply (component_determinant_range a ha A v hv d).2
  let c : Component A → K := fun j => if j = component A i₀ then d / ∏ i, v i else 1
  refine ⟨c, ?_⟩
  have he (i : n) :
      c (component A i) = if i = i₀ then d / ∏ i, v i else 1 := by
    by_cases hz : i = i₀
    · subst i
      simp [c]
    · have hf : component A i ≠ component A i₀ := fun hm => hz (hi i hm)
      simp [c, hz, hf]
  simp only [he]
  rw [Fintype.prod_ite_eq']
  field_simp [Finset.prod_ne_zero_iff.2 fun i _ => hv i]

/-- For a connected support, a prescribed determinant is possible exactly
when it is the twist product times a single n-th power. -/
theorem connected_support_power_range
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0)
    (r : n) (hc : ∀ i, component A i = component A r) (d : K) :
    detTransport a A (twist v A) d ↔
      ∃ c : K, (∏ i, v i) * c ^ Fintype.card n = d := by
  rw [component_determinant_range a ha A v hv]
  constructor
  · rintro ⟨c, h⟩
    refine ⟨c (component A r), ?_⟩
    simpa only [hc, Finset.prod_const, Finset.card_univ] using h
  · rintro ⟨c, h⟩
    refine ⟨fun _ => c, ?_⟩
    simpa only [Finset.prod_const, Finset.card_univ] using h

/-- Exact comparison of two twists of the same base tuple, with the quotient
of twist products providing the common determinant offset. -/
theorem relative_twist_range
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v w : n → K) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (d : K) :
    detTransport a (twist v A) (twist w A) d ↔
      ∃ c : Component (twist v A) → K,
        (∏ i, w i / v i) * (∏ i, c (component (twist v A) i)) = d := by
  have he : twist (fun i => w i / v i) (twist v A) = twist w A := by
    funext t
    ext i j
    simp only [twist]
    field_simp [hv i, hv j, hw i, hw j] <;> ring
  rw [← he]
  exact component_determinant_range a ha (twist v A) _ (fun i => div_ne_zero (hw i) (hv i)) d

/-- Adding tuple slices can only shrink the attainable determinant set.
The ambient anchor family and twist are unchanged. -/
theorem concatenated_support_is_determinant_restrictive
    {I' : Type*} (a : J → n → K) (A : I → Matrix n n K) (B : I' → Matrix n n K)
    (v : n → K) (d : K) :
    detTransport a (Sum.elim A B) (twist v (Sum.elim A B)) d →
      detTransport a A (twist v A) d ∧ detTransport a B (twist v B) d := by
  rintro ⟨X, hx, hA, h⟩
  exact ⟨⟨X, hx, hA, fun i => h (.inl i)⟩, ⟨X, hx, hA, fun i => h (.inr i)⟩⟩

/-- If the twist product is one, a determinant-one transporter exists,
regardless of the directed support and number of component sizes. -/
theorem balanced_twist_special (a : J → n → K) (A : I → Matrix n n K)
    (v : n → K) (hv : ∀ i, v i ≠ 0) (hg : (∏ i, v i) = 1) :
    detTransport a A (twist v A) 1 := by
  refine ⟨diagonal v, by rwa [det_diagonal], fun t => (commute_diagonal _ _).eq, ?_⟩
  intro t
  ext i j
  simp only [diagonal_mul, mul_diagonal, twist]
  field_simp [hv j] <;> ring

end Supports


section Characters

variable {G H S : Type*} [Group G] [CommGroup H] [MulAction G S]

/-- The character image of a transporter is one coset of the stabilizer
image. This is independent of the kind of object being transported. -/
theorem action_character_fiber (χ : G →* H) (a b : S) (g : G) (hg : g • a = b) (h : H) :
    (∃ x : G, x • a = b ∧ χ x = h) ↔
      ∃ c : G, c • a = a ∧ χ g * χ c = h := by
  constructor
  · rintro ⟨x, hs, hx⟩
    refine ⟨g⁻¹ * x, ?_, ?_⟩
    · rw [mul_smul, hs, ← hg, inv_smul_smul]
    · rw [← map_mul, ← mul_assoc, mul_inv_cancel, one_mul, hx]
  · rintro ⟨c, hc, hh⟩
    exact ⟨g*c, by rw [mul_smul, hc, hg], by rwa [map_mul]⟩

/-- If the character is surjective on the source stabilizer, every ordinary
orbit element has transporters of every prescribed character. -/
theorem action_all_character_values (χ : G →* H) (a b : S) (g : G) (hg : g • a = b)
    (surj : ∀ h : H, ∃ c : G, c • a = a ∧ χ c = h) (h : H) :
    ∃ x : G, x • a = b ∧ χ x = h := by
  apply (action_character_fiber χ a b g hg h).2
  obtain ⟨c, hs, hc⟩ := surj ((χ g)⁻¹*h)
  exact ⟨c, hs, by rw [hc]; group⟩

/-- If the character has trivial kernel on the stabilizer, every feasible
character specifies a unique transporter. -/
theorem transporter_unique_at_character (χ : G →* H) (a b : S) (h : H)
    (kernel : ∀ c : G, c • a = a → χ c = 1 → c = 1)
    (existsOne : ∃ x : G, x • a = b ∧ χ x = h) :
    ∃! x : G, x • a = b ∧ χ x = h := by
  obtain ⟨x, hx, hc⟩ := existsOne
  refine ⟨x, ⟨hx,hc⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  have hk : x⁻¹*y = 1 := kernel _ (by rw [mul_smul, hy, ← hx, inv_smul_smul])
    (by rw [map_mul, map_inv, hc, hyc, inv_mul_cancel])
  have he := congrArg (x * ·) hk
  simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using he

/-- Stabilizer character images coincide at all points of an orbit. -/
theorem orbit_stabilizer_character_invariant (χ : G →* H) (a b : S)
    (g : G) (hg : g • a = b) (h : H) :
    (∃ x : G, x • a = a ∧ χ x = h) ↔ (∃ x : G, x • b = b ∧ χ x = h) := by
  constructor
  · rintro ⟨x, hx, hc⟩
    refine ⟨g*x*g⁻¹, ?_, ?_⟩
    · rw [mul_smul, ← hg, inv_smul_smul, mul_smul, hx]
    · simp only [map_mul, map_inv, hc]
      rw [mul_comm (χ g) h]
      group
  · rintro ⟨x, hx, hc⟩
    refine ⟨g⁻¹*x*g, ?_, ?_⟩
    · rw [mul_smul, hg, mul_smul, hx, ← hg, inv_smul_smul]
    · simp only [map_mul, map_inv, hc]
      rw [mul_comm (χ g)⁻¹ h]
      group

/-- Two transported points in one ordinary orbit lie in the same kernel
orbit exactly when their character quotient occurs in the source stabilizer. -/
theorem orbit_splitting_by_character (χ : G →* H) (a : S) (g₁ g₂ : G) :
    (∃ x : G, x • (g₁ • a) = g₂ • a ∧ χ x = 1) ↔
      ∃ c : G, c • a = a ∧ χ c = (χ g₂)⁻¹ * χ g₁ := by
  constructor
  · rintro ⟨x, hx, hχ⟩
    refine ⟨g₂⁻¹*x*g₁, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hx, inv_smul_smul]
    · simp [map_mul, map_inv, hχ]
  · rintro ⟨c, hc, hχ⟩
    refine ⟨g₂*c*g₁⁻¹, ?_, ?_⟩
    · rw [mul_smul, inv_smul_smul, mul_smul, hc]
    · simp only [map_mul, map_inv, hχ]
      group

/-- If the stabilizer character image is trivial, the character assigned
to a point of the orbit is independent of its ordinary transporter. -/
theorem orbit_point_character_well_defined (χ : G →* H) (a : S)
    (trivial : ∀ c : G, c • a = a → χ c = 1)
    (g₁ g₂ : G) (he : g₁ • a = g₂ • a) : χ g₁ = χ g₂ := by
  obtain ⟨c,hc,hh⟩ := (orbit_splitting_by_character χ a g₁ g₂).1
    ⟨1,by simpa using he,by simp⟩
  have heq := (trivial c hc).symm.trans hh
  calc
    χ g₁ = χ g₂ * ((χ g₂)⁻¹ * χ g₁) := by group
    _ = χ g₂ := by rw [← heq, mul_one]

/-- The character values on a stabilizer can be computed from any supplied
generating family of that stabilizer. -/
theorem stabilizer_character_generated (χ : G →* H) (a : S) (T : Set G)
    (hT : Subgroup.closure T = MulAction.stabilizer G a) :
    (MulAction.stabilizer G a).map χ = Subgroup.closure (χ '' T) := by
  rw [← hT, MonoidHom.map_closure]

/-- A simultaneous action on two objects has no character obstruction if a
single source correction subgroup fixes both objects and surjects. -/
theorem paired_action_character_correction
    {S' : Type*} [MulAction G S'] (χ : G →* H) (a b : S) (a' b' : S') (g : G)
    (hg : g • a = b) (hg' : g • a' = b')
    (hs : ∀ h : H, ∃ c : G, c • a = a ∧ c • a' = a' ∧ χ c = h) (h : H) :
    ∃ x : G, x • a = b ∧ x • a' = b' ∧ χ x = h := by
  obtain ⟨c, hc, hc', he⟩ := hs ((χ g)⁻¹ * h)
  exact ⟨g*c, by rw [mul_smul,hc,hg], by rw [mul_smul,hc',hg'],
    by rw [map_mul, he]; group⟩

/-- A scalar correction need only provide a power of the required character.
An n-th root suffices when the supplied central corrections realize n-th powers. -/
theorem action_character_root_correction
    (χ : G →* H) (a b : S) (g : G) (hg : g • a = b)
    (k : ℕ) (central : ∀ h : H, ∃ c : G, c • a = a ∧ χ c = h ^ k)
    (v t : H) (hv : χ g * v ^ k = t) :
    ∃ x : G, x • a = b ∧ χ x = t := by
  obtain ⟨c, hc, h⟩ := central v
  exact ⟨g*c, by rw [mul_smul,hc,hg], by rwa [map_mul,h]⟩

/-- For commuting requirements on two source objects, a correcting action
on the first that fixes the second assembles prescribed characters additively
in the product of their character groups. -/
theorem independent_character_constraints
    {H' : Type*} [CommGroup H'] (χ : G →* H) (ψ : G →* H') (a b : S)
    (g : G) (hg : g • a = b)
    (hc : ∀ h : H, ∃ c : G, c • a = a ∧ χ c = h ∧ ψ c = 1)
    (hd : ∀ h : H', ∃ c : G, c • a = a ∧ ψ c = h ∧ χ c = 1)
    (u : H) (v : H') :
    ∃ x : G, x • a = b ∧ χ x = u ∧ ψ x = v := by
  obtain ⟨c, hc₀, hc₁, hc₂⟩ := hc ((χ g)⁻¹*u)
  obtain ⟨d, hd₀, hd₁, hd₂⟩ := hd ((ψ g)⁻¹*v)
  refine ⟨g*(c*d), by rw [mul_smul,mul_smul,hd₀,hc₀,hg], ?_, ?_⟩
  · simp only [map_mul,hc₁,hd₂]
    group
  · simp only [map_mul,hc₂,hd₁]
    group

end Characters

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
private theorem path_weight_transport (A B : {i j : V} → E i j → G)
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
private theorem graph_gauge_iff (A B : {i j : V} → E i j → G)
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

def rootGauge (A B : {i j : V} → E i j → G) {o : V}
    (q : ∀ i, Path E o i) (z : G) (i : V) : G :=
  ((q i).weight B)⁻¹ * z * (q i).weight A

def IsGauge (E : V → V → Type*) (A B : (i j : V) → E i j → G) (g : V → G) : Prop :=
  ∀ i j (e : E i j), g i * A i j e = B i j e * g j

def Based (A B : {i j : V} → E i j → G) {o : V}
    (q : ∀ i, Path E o i) (z : G) : Prop :=
  ∀ i j (e : E i j), z * basedLabel A q e = basedLabel B q e * z

private theorem root_reconstruction
    (A B : {i j : V} → E i j → G) {o : V} (q : ∀ i, Path E o i)
    (g : V → G) (hg : IsGauge E (@A) (@B) g) :
    g = rootGauge A B q (g o) := by
  funext i
  unfold rootGauge
  rw [mul_assoc, path_weight_transport A B g hg (q i)]
  group

/-- Arbitrary global constraints on a gauge reduce to the same constraints
on a specific root reconstruction. They may depend on every vertex jointly. -/
theorem gauge_with_property (A B : {i j : V} → E i j → G) {o : V}
    (q : ∀ i, Path E o i) (hq : q o = Path.nil o) (P : (V → G) → Prop) :
    (∃ g, IsGauge E (@A) (@B) g ∧ P g) ↔
      (∃ z, Based A B q z ∧ P (rootGauge A B q z)) := by
  constructor
  · rintro ⟨g,hg,hP⟩
    refine ⟨g o,(graph_gauge_iff A B q hq (g o)).1 ⟨g,rfl,hg⟩,?_⟩
    rwa [← root_reconstruction A B q g hg]
  · rintro ⟨z,hz,hP⟩
    obtain ⟨g,hgo,hg⟩ := (graph_gauge_iff A B q hq z).2 hz
    refine ⟨g,hg,?_⟩
    rw [root_reconstruction A B q g hg,hgo]
    exact hP

/-- Exact vertex-character constraints reduce to independent character
transport equations and a single based-label problem at the root. -/
theorem gauge_character_vector_iff (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o)
    (χ : G →* H) (b : V → H) :
    (∃ g, IsGauge E (@A) (@B) g ∧ ∀ i, χ (g i) = b i) ↔
      ∃ z, Based A B q z ∧
        ∀ i, (χ ((q i).weight B))⁻¹ * χ z * χ ((q i).weight A) = b i := by
  rw [gauge_with_property A B q hq]
  simp only [rootGauge, map_mul, map_inv]

private theorem root_rearrange {U : Type*} [Group U] (s t x y : U) :
    s⁻¹*x*t = y ↔ x = s*y*t⁻¹ := by
  constructor
  · intro h
    calc
      x = s*(s⁻¹*x*t)*t⁻¹ := by group
      _ = s*y*t⁻¹ := by rw [h]
  · intro h
    rw [h]
    group

/-- Two independently specified characters are handled at the root
simultaneously. This retains all compatibility between the two characters. -/
theorem gauge_joint_characters
    {H' : Type*} [Group H'] (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o)
    (χ : G →* H) (ψ : G →* H') (b : V → H) (d : V → H') :
    (∃ g, IsGauge E (@A) (@B) g ∧ (∀ i, χ (g i) = b i) ∧ ∀ i, ψ (g i) = d i) ↔
      (∃ z, Based A B q z ∧
        (∀ i, χ z = χ ((q i).weight B) * b i * (χ ((q i).weight A))⁻¹) ∧
        ∀ i, ψ z = ψ ((q i).weight B) * d i * (ψ ((q i).weight A))⁻¹) := by
  rw [gauge_with_property A B q hq]
  simp only [rootGauge, map_mul, map_inv]
  constructor
  · rintro ⟨z,hz,hχ,hψ⟩
    exact ⟨z,hz,fun i => (root_rearrange _ _ _ _).1 (hχ i),
      fun i => (root_rearrange _ _ _ _).1 (hψ i)⟩
  · rintro ⟨z,hz,hχ,hψ⟩
    exact ⟨z,hz,fun i => (root_rearrange _ _ _ _).2 (hχ i),
      fun i => (root_rearrange _ _ _ _).2 (hψ i)⟩

/-- The weighted product of vertex characters reduces to one power of the
root character. Vertex multiplicities may be arbitrary natural numbers. -/
theorem gauge_weighted_character_budget
    {H' : Type*} [CommGroup H'] [Fintype V]
    (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o)
    (χ : G →* H') (m : V → ℕ) (d : H') :
    (∃ g, IsGauge E (@A) (@B) g ∧ (∏ i, χ (g i) ^ m i) = d) ↔
      (∃ z, Based A B q z ∧
        χ z ^ (∑ i, m i) *
          (∏ i, (χ ((q i).weight B)⁻¹ * χ ((q i).weight A)) ^ m i) = d) := by
  rw [gauge_with_property A B q hq]
  have he (z : G) :
      (∏ i, χ (rootGauge A B q z i) ^ m i) =
        χ z ^ (∑ i, m i) *
          (∏ i, (χ ((q i).weight B)⁻¹ * χ ((q i).weight A)) ^ m i) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [rootGauge, map_mul, map_inv, ← mul_pow]
    ac_rfl
  simp only [he]

/-- Multiplicative labels on the graph with trivial character weights admit a
kernel-valued gauge exactly when their based labels match by a kernel root. -/
theorem graph_kernel_gauge_iff (A B : {i j : V} → E i j → G)
    {o : V} (q : ∀ i, Path E o i) (hq : q o = Path.nil o)
    (χ : G →* H) (hE : ∀ i j (e : E i j), χ (A e) = χ (B e)) :
    (∃ g, IsGauge E (@A) (@B) g ∧ ∀ i, χ (g i) = 1) ↔
      ∃ z, Based A B q z ∧ χ z = 1 := by
  have hp {i j : V} (w : Path E i j) : χ (w.weight A) = χ (w.weight B) := by
    induction w with
    | nil => rfl
    | step e w ih => simp only [Path.weight, map_mul, ih, hE]
  rw [gauge_character_vector_iff A B q hq]
  constructor
  · rintro ⟨z,hz,h⟩
    refine ⟨z,hz,?_⟩
    simpa [hq,Path.weight] using h o
  · rintro ⟨z,hz,h⟩
    exact ⟨z,hz,fun i => by rw [hp (q i),h,mul_one,inv_mul_cancel]⟩

/-- Once an ordinary gauge is supplied, the roots of all admissible gauges
form the corresponding centralizer cosets for the based labels. -/
theorem known_gauge_special_correction
    (A B : {i j : V} → E i j → G) {o : V} (q : ∀ i, Path E o i)
    (hq : q o = Path.nil o) (χ : G →* H) (g : V → G) (hg : IsGauge E (@A) (@B) g)
    (hE : ∀ i j (e : E i j), χ (A e) = χ (B e)) :
    (∃ k, IsGauge E (@A) (@B) k ∧ ∀ i, χ (k i) = 1) ↔
      ∃ c : G, χ c = (χ (g o))⁻¹ ∧
        (∀ i j (e : E i j), c * basedLabel A q e = basedLabel A q e * c) := by
  rw [graph_kernel_gauge_iff A B q hq χ hE]
  have hb := (graph_gauge_iff A B q hq (g o)).1 ⟨g,rfl,hg⟩
  constructor
  · rintro ⟨z,hz,hχ⟩
    refine ⟨(g o)⁻¹*z,by simp [map_mul,map_inv,hχ],?_⟩
    intro i j e
    have hb' := hb i j e
    have hz' := hz i j e
    have he : basedLabel B q e = g o * basedLabel A q e * (g o)⁻¹ := by
      rw [hb']
      group
    rw [mul_assoc,hz',he]
    group
  · rintro ⟨c,hχ,h⟩
    refine ⟨g o*c,?_ ,by rw [map_mul,hχ,mul_inv_cancel]⟩
    intro i j e
    rw [mul_assoc,h i j e,← mul_assoc,hb,mul_assoc]

/-- If the transported labels map to the same character, every gauge takes
a common character value at every vertex of the rooted directed graph. -/
theorem path_independent_constant_character
    (A B : {i j : V} → E i j → G) {o : V} (q : ∀ i, Path E o i)
    {L : Type*} [CommGroup L] (χ : G →* L) (g : V → G) (hg : IsGauge E (@A) (@B) g)
    (hE : ∀ i j (e : E i j), χ (A e) = χ (B e)) (i : V) :
    χ (g i) = χ (g o) := by
  have he (i j : V) (e : E i j) : χ (g i) = χ (g j) := by
    have h := congrArg χ (hg i j e)
    simp only [map_mul, hE] at h
    exact mul_right_cancel (h.trans (mul_comm _ _))
  have hor {i j : V} (p : Path E i j) : χ (g i) = χ (g j) := by
    induction p with
    | nil => rfl
    | step e p ih => exact (he _ _ e).trans ih
  exact (hor (q i)).symm

end Graph


section JointInvariants

variable {K n I J : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A nonvanishing diagonal twist leaves the entire support equivalence
relation intact. Thus iterated classification uses exactly the same components. -/
theorem twist_preserves_support_components (A : I → Matrix n n K) (v : n → K)
    (hv : ∀ i, v i ≠ 0) : SupportSetoid (twist v A) = SupportSetoid A := by
  have h : (fun i j => ∃ t : I, twist v A t i j ≠ 0) =
      (fun i j => ∃ t : I, A t i j ≠ 0) := by
    funext i j
    congr 1
    funext t
    apply propext
    simp [twist, hv, div_ne_zero]
  change Setoid.mk (Relation.EqvGen _) _ = Setoid.mk (Relation.EqvGen _) _
  simp only [h]

/-- Trace and determinant of a weighted transporter are simultaneously the
linear and multiplicative component statistics of one parameter. -/
theorem joint_trace_determinant_profile
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (d t : K) :
    (∃ X : Matrix n n K, X.det = d ∧ X.trace = t ∧ Transport a A (twist v A) X) ↔
      (∃ c : Component A → K, (∏ i, v i) * (∏ i, c (component A i)) = d ∧
        (∑ i, v i * c (component A i)) = t) := by
  simp only [component_transport_classification a ha A v hv]
  constructor
  · rintro ⟨X,hd,ht,c,rfl⟩
    exact ⟨c,(component_det A v c).symm.trans hd,by simpa using ht⟩
  · rintro ⟨c,hd,ht⟩
    refine ⟨diagonal (fun i => v i * c (component A i)), (component_det A v c).trans hd, ?_,c,rfl⟩
    simpa using ht

/-- For connected support and nonzero total twist, trace fixes the entire
transporter, including whether its determinant can be one. -/
theorem connected_trace_fixes_transporter
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0)
    (r : n) (hc : ∀ i, component A i = component A r) (hs : (∑ i, v i) ≠ 0)
    (X : Matrix n n K) (hX : Transport a A (twist v A) X) :
    X = diagonal (fun i => v i * (X.trace / ∑ j, v j)) := by
  obtain ⟨c,hc'⟩ := (component_transport_classification a ha A v hv X).1 hX
  have ht : X.trace = (∑ i, v i) * c (component A r) := by
    rw [hc', Matrix.trace_diagonal, Finset.sum_mul]
    simp only [hc]
  calc
    X = diagonal (fun i => v i * c (component A r)) := by simpa only [hc] using hc'
    _ = diagonal (fun i => v i * (X.trace / ∑ j, v j)) := by
      have he : c (component A r) = X.trace / ∑ j, v j := by
        rw [ht]
        field_simp [hs]
      simp only [he]

/-- For connected support, trace zero can occur on an invertible transporter
exactly when the total twist is zero. -/
theorem invertible_trace_zero_iff
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0)
    (r : n) (hc : ∀ i, component A i = component A r) :
    (∃ X : Matrix n n K, X.det ≠ 0 ∧ X.trace = 0 ∧ Transport a A (twist v A) X) ↔
      (∑ i, v i) = 0 := by
  constructor
  · rintro ⟨X,hd,ht,hX⟩
    obtain ⟨c,rfl⟩ := (component_transport_classification a ha A v hv X).1 hX
    have he : c (component A r) ≠ 0 := by
      intro hz
      apply hd
      rw [Matrix.det_diagonal]
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      rw [hz,mul_zero]
    rw [Matrix.trace_diagonal] at ht
    simp only [hc,← Finset.sum_mul] at ht
    exact (mul_eq_zero.1 ht).resolve_right he
  · intro h
    refine ⟨diagonal v, by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hv i, ?_,?_⟩
    · simpa using h
    · apply (component_transport_classification a ha A v hv _).2
      exact ⟨fun _ => 1, by simp⟩

/-- The locus of orthogonal transporters is an explicit intersection of
coordinate square conditions and the component parameter space. -/
theorem orthogonal_component_profile
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) :
    (∃ X : Matrix n n K, Xᵀ * X = 1 ∧ Transport a A (twist v A) X) ↔
      ∃ c : Component A → K, ∀ i, (v i * c (component A i)) ^ 2 = 1 := by
  simp only [component_transport_classification a ha A v hv]
  constructor
  · rintro ⟨X,hX,c,rfl⟩
    refine ⟨c,fun i => ?_⟩
    have he := congrArg (fun M : Matrix n n K => M i i) hX
    simpa [Matrix.diagonal_mul_diagonal,pow_two] using he
  · rintro ⟨c,h⟩
    refine ⟨diagonal (fun i => v i * c (component A i)),?_,c,rfl⟩
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr
    funext i
    simpa [pow_two] using h i

/-- A fixed transporter is invertible precisely when all of its component
scalars survive. The representative property of quotient components
is used to rule out vanishing hidden factors. -/
theorem invertible_component_profile
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A : I → Matrix n n K) (v : n → K) (hv : ∀ i, v i ≠ 0) (X : Matrix n n K) :
    (X.det ≠ 0 ∧ Transport a A (twist v A) X) ↔
      (∃ c : Component A → K, (∀ j, c j ≠ 0) ∧
        X = diagonal (fun i => v i * c (component A i))) := by
  constructor
  · rintro ⟨hd,hT⟩
    obtain ⟨c,rfl⟩ := (component_transport_classification a ha A v hv X).1 hT
    refine ⟨c, ?_, rfl⟩
    intro j
    induction j using Quotient.inductionOn with
    | _ i =>
      intro h
      apply hd
      rw [Matrix.det_diagonal]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change v i * c (component A i) = 0
      rw [show c (component A i) = 0 from h, mul_zero]
  · rintro ⟨c,hc,rfl⟩
    refine ⟨?_,(component_transport_classification a ha A v hv _).2 ⟨c,rfl⟩⟩
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hv i) (hc _)

/-- With complete diagonal labelling, simultaneous congruence restricted to
the anchor centralizer is equivalent to the quadratic scalar profile. -/
theorem anchored_congruence_scalar_profile
    (a : J → n → K) (ha : Function.Injective (fun i t => a t i))
    (A B : I → Matrix n n K) (d : K) :
    (∃ X : Matrix n n K, X.det = d ∧
      (∀ t, X * diagonal (a t) = diagonal (a t) * X) ∧
      ∀ t, (X * A t) * Xᵀ = B t) ↔
    (∃ x : n → K, (∏ i, x i) = d ∧
      ∀ t i j, x i * A t i j * x j = B t i j) := by
  constructor
  · rintro ⟨X,hd,hA,hT⟩
    have he := diag_form a ha X hA
    refine ⟨fun i => X i i, ?_,?_⟩
    · rw [he] at hd
      simpa only [Matrix.det_diagonal] using hd
    · intro t i j
      have h := congrArg (fun M : Matrix n n K => M i j) (hT t)
      rw [he] at h
      simpa only [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  · rintro ⟨x,hd,hx⟩
    refine ⟨diagonal x, by rwa [Matrix.det_diagonal],
      fun t => (Matrix.commute_diagonal _ _).eq, ?_⟩
    intro t
    ext i j
    simpa only [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] using hx t i j

end JointInvariants


section PowerArithmetic

variable {G : Type*} [CommGroup G]

private theorem pow_zpow_flip (x : G) (a : ℤ) (k : ℕ) :
    (x ^ a) ^ k = (x ^ k) ^ a := by
  rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm a, _root_.zpow_mul, _root_.zpow_natCast]

private theorem add_natural_zpow (x : G) (m n : ℕ) (a b : ℤ) :
    (x ^ m) ^ a * (x ^ n) ^ b = x ^ ((m : ℤ) * a + (n : ℤ) * b) := by
  calc
    (x ^ m) ^ a * (x ^ n) ^ b = (x ^ (m : ℤ)) ^ a * (x ^ (n : ℤ)) ^ b := by
      simp only [_root_.zpow_natCast]
    _ = _ := by rw [_root_.zpow_add,_root_.zpow_mul,_root_.zpow_mul]

/-- Products of two independent power contributions give exactly the powers
of the gcd of the two exponents in any commutative group. -/
theorem two_power_product_profile (m n : ℕ) (z : G) :
    (∃ a b : G, a ^ m * b ^ n = z) ↔ (∃ c : G, c ^ (Nat.gcd m n) = z) := by
  constructor
  · rintro ⟨a,b,rfl⟩
    obtain ⟨i, hi⟩ := Nat.gcd_dvd_left m n
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right m n
    refine ⟨a ^ i * b ^ j, ?_⟩
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, ← hi, ← hj]
  · rintro ⟨c,rfl⟩
    refine ⟨c ^ Nat.gcdA m n,c ^ Nat.gcdB m n,?_⟩
    rw [pow_zpow_flip,pow_zpow_flip,add_natural_zpow,
      ← Nat.gcd_eq_gcd_ab,_root_.zpow_natCast]

/-- The possible product of an arbitrary list of independent power factors
depends only on the gcd of the list. Zero exponents are allowed. -/
theorem list_power_product_profile (ks : List ℕ) (z : G) :
    (List.foldr (fun k (P : G → Prop) w => ∃ x y : G, P y ∧ x ^ k * y = w)
       (fun w => w = 1) ks) z ↔ ∃ c : G, c ^ (ks.foldr Nat.gcd 0) = z := by
  induction ks generalizing z with
  | nil => simp [eq_comm]
  | cons k ks ih =>
    simp only [List.foldr_cons]
    rw [← two_power_product_profile]
    constructor
    · rintro ⟨x,y,hy,rfl⟩
      obtain ⟨c,rfl⟩ := (ih y).1 hy
      exact ⟨x,c,rfl⟩
    · rintro ⟨x,c,rfl⟩
      exact ⟨x,c ^ ks.foldr Nat.gcd 0,(ih _).2 ⟨c,rfl⟩,rfl⟩

/-- A first and a second prescribed power have a unique joint root for
coprime exponents exactly when the two cross powers agree. -/
theorem simultaneous_coprime_roots (m n : ℕ) (h : Nat.Coprime m n) (a b : G) :
    (∃! x : G, x ^ m = a ∧ x ^ n = b) ↔ a ^ n = b ^ m := by
  have hb : (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab,h.gcd_eq_one,Nat.cast_one]
  let x : G := a ^ Nat.gcdA m n * b ^ Nat.gcdB m n
  constructor
  · rintro ⟨y,⟨hm,hn⟩,_⟩
    rw [← hm,← hn,← pow_mul,← pow_mul,mul_comm m]
  · intro hcross
    refine ⟨x,⟨?_,?_⟩,?_⟩
    · dsimp [x]
      rw [mul_pow,pow_zpow_flip,pow_zpow_flip,← hcross,
        add_natural_zpow,hb,_root_.zpow_one]
    · dsimp [x]
      rw [mul_pow,pow_zpow_flip,pow_zpow_flip,hcross,
        add_natural_zpow,hb,_root_.zpow_one]
    · rintro y ⟨hm,hn⟩
      dsimp [x]
      rw [← hm,← hn,add_natural_zpow,hb,_root_.zpow_one]

/-- A power map is bijective on the N-torsion fibre whenever its exponent is
coprime to N. The conclusion specifies both existence and uniqueness. -/
theorem coprime_power_on_torsion (m n : ℕ) (h : Nat.Coprime m n)
    (a : G) (ha : a ^ n = 1) : ∃! x : G, x ^ m = a ∧ x ^ n = 1 :=
  (simultaneous_coprime_roots m n h a 1).2 (by simpa using ha)

/-- Consecutive power observations reconstruct the underlying group element,
including the exponent-zero boundary. -/
theorem consecutive_powers_recover (m : ℕ) (a b : G) :
    (a ^ m = b ^ m ∧ a ^ (m+1) = b ^ (m+1)) ↔ a = b := by
  constructor
  · rintro ⟨h,h'⟩
    rw [pow_succ,pow_succ,h] at h'
    exact mul_left_cancel h'
  · rintro rfl
    simp

/-- Two torsion tests collapse exactly to one gcd torsion test. -/
theorem joint_torsion_gcd (m n : ℕ) (x : G) :
    (x ^ m = 1 ∧ x ^ n = 1) ↔ x ^ (Nat.gcd m n) = 1 := by
  constructor
  · rintro ⟨hm,hn⟩
    rw [← _root_.zpow_natCast,Nat.gcd_eq_gcd_ab,_root_.zpow_add,_root_.zpow_mul,_root_.zpow_mul,
      _root_.zpow_natCast,_root_.zpow_natCast,hm,hn,_root_.one_zpow,_root_.one_zpow,one_mul]
  · intro h
    obtain ⟨i,hi⟩ := Nat.gcd_dvd_left m n
    obtain ⟨j,hj⟩ := Nat.gcd_dvd_right m n
    exact ⟨by rw [hi,pow_mul,h,one_pow],by rw [hj,pow_mul,h,one_pow]⟩

end PowerArithmetic


section CongruenceAndBlocks

variable {K n I : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A simultaneous congruence with one equal nonzero determinant anchor
has transporter determinant in the square-one subgroup. -/
theorem congruence_anchor_determinant_sign
    (X A B : Matrix n n K) (h : X * A * Xᵀ = B)
    (ha : A.det ≠ 0) (hb : B.det = A.det) : X.det ^ 2 = 1 := by
  have he := congrArg Matrix.det h
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hb] at he
  apply mul_right_cancel₀ ha
  calc
    X.det ^ 2 * A.det = X.det * A.det * X.det := by ring
    _ = A.det := he
    _ = 1 * A.det := by ring

/-- For odd common side, one determinant constraint on an invertible anchor
is sufficient to lift an ordinary simultaneous congruence to determinant one. -/
theorem odd_simultaneous_congruence_lift
    (A B : I → Matrix n n K) (o : I) (hn : Odd (Fintype.card n))
    (ha : (A o).det ≠ 0) (hb : (B o).det = (A o).det)
    (X : Matrix n n K) (hX : ∀ i, X * A i * Xᵀ = B i) :
    ∃ Y : Matrix n n K, Y.det = 1 ∧ ∀ i, Y * A i * Yᵀ = B i := by
  have hs := congruence_anchor_determinant_sign X (A o) (B o) (hX o) ha hb
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show X.det ^ 2 = (1 : K)^2 by simpa using hs) with h | h
  · exact ⟨X,h,hX⟩
  · refine ⟨-X, ?_, fun i => ?_⟩
    · rw [Matrix.det_neg, h]
      simp [hn.neg_one_pow]
    · simpa [Matrix.neg_mul, Matrix.mul_neg] using hX i

/-- Source reflection of one coordinate corrects the sign for simultaneous
congruence of diagonal tuples, in either parity of the matrix side. -/
theorem diagonal_tuple_congruence_lift
    (A : I → n → K) (B : I → Matrix n n K) (o : I) (r : n)
    (ha : (diagonal (A o)).det ≠ 0) (hb : (B o).det = (diagonal (A o)).det)
    (X : Matrix n n K) (hX : ∀ i, X * diagonal (A i) * Xᵀ = B i) :
    ∃ Y : Matrix n n K, Y.det = 1 ∧ ∀ i, Y * diagonal (A i) * Yᵀ = B i := by
  have hs := congruence_anchor_determinant_sign X _ (B o) (hX o) ha hb
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show X.det ^ 2 = (1 : K)^2 by simpa using hs) with h | h
  · exact ⟨X,h,hX⟩
  · let d : n → K := fun i => if i = r then -1 else 1
    let J := Matrix.diagonal d
    have hd : J.det = -1 := by simp [J, d, Matrix.det_diagonal]
    have hJ (i : I) : J * diagonal (A i) * Jᵀ = diagonal (A i) := by
      simp only [J, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases hr : j = r <;> simp [d,hr]
    refine ⟨X*J,by rw [Matrix.det_mul,h,hd]; ring,?_⟩
    intro i
    rw [Matrix.transpose_mul]
    calc
      X * J * diagonal (A i) * (Jᵀ * Xᵀ) = X * (J * diagonal (A i) * Jᵀ) * Xᵀ := by
        simp only [Matrix.mul_assoc]
      _ = B i := by rw [hJ,hX]

/-- Direct and inverse-transpose congruences on two forms yield simultaneous
similarity of their products, with no nonsingularity requirement on the forms. -/
theorem paired_dual_congruence_product
    (X Y A B C D : Matrix n n K) (hYX : Y*X=1) (hXY : X*Y=1)
    (hA : X*A*Xᵀ=B) (hC : Yᵀ*C*Y=D) :
    X * (A*C) = (B*D)*X := by
  have hT : Xᵀ * Yᵀ = 1 := by
    rw [← Matrix.transpose_mul,hYX,Matrix.transpose_one]
  symm
  rw [← hA, ← hC]
  calc
    ((X*A*Xᵀ)*(Yᵀ*C*Y))*X = (X*A)*(Xᵀ*Yᵀ)*C*(Y*X) := by
      simp only [Matrix.mul_assoc]
    _ = X*(A*C) := by rw [hT,hYX,Matrix.mul_one,Matrix.mul_one,Matrix.mul_assoc]

/-- A transpose-dual operation on simultaneous similarity admits exactly the
inverse-transpose transporter, preserving determinant-one. -/
theorem dual_similarity_preserves_special
    (A B : I → Matrix n n K) (X Y : Matrix n n K)
    (hXY : X*Y=1) (hYX : Y*X=1) (hd : X.det=1)
    (h : ∀ i, X*A i=B i*X) :
    Yᵀ.det=1 ∧ ∀ i, Yᵀ*(A i)ᵀ=(B i)ᵀ*Yᵀ := by
  refine ⟨?_,?_⟩
  · have he := congrArg Matrix.det hYX
    simpa [Matrix.det_mul, Matrix.det_transpose,hd] using he
  · intro i
    have he : A i * Y = Y * B i := by
      calc
        A i*Y = (Y*X)*A i*Y := by rw [hYX,Matrix.one_mul]
        _ = Y*(X*A i)*Y := by simp only [Matrix.mul_assoc]
        _ = Y*B i*(X*Y) := by rw [h]; simp only [Matrix.mul_assoc]
        _ = Y*B i := by rw [hXY,Matrix.mul_one]
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose he

/-- A nonsingular anchoring product transports precisely when its opposite
order does, after switching the two coordinate changes. -/
theorem normalized_product_swap
    (A B X Y : Matrix n n K) (hXY : X*Y=1) (hYX : Y*X=1)
    (hA : X*A=B*X) :
    A * Y = Y * B := by
  calc
    A*Y = (Y*X)*A*Y := by rw [hYX,Matrix.one_mul]
    _ = Y*(X*A)*Y := by simp only [Matrix.mul_assoc]
    _ = Y*B*(X*Y) := by rw [hA]; simp only [Matrix.mul_assoc]
    _ = Y*B := by rw [hXY,Matrix.mul_one]

end CongruenceAndBlocks

section Residuals

variable {R I : Type*} [Ring R]

/-- A coupled pair of equivalence equations transports a product across the
first change of basis, with an exact linear residual formula. -/
theorem product_two_legs_residual
    (x y a b c d : R) :
    x*(a*b)-(c*d)*x=(x*a-c*y)*b+c*(y*b-d*x) := by
  noncomm_ring

/-- Both sides of a polynomial calculus inverse identity can be pushed
through unrelated entry maps, with all error terms explicit. -/
theorem cross_inverse_residual
    (u v x y a b : R) :
    u - v = u*(1 - x*y) + (u*x - x*a)*y + x*(a*y - y*b) +
      (x*y - 1)*b + (b-v) := by
  noncomm_ring

/-- If off-diagonal products vanish, independent partial inverses of two
blocks assemble to an ordinary two-sided inverse. -/
theorem complementary_inverse_assembly
    (x₁ x₂ y₁ y₂ p q : R)
    (h₁ : y₁*x₁=p) (h₂ : y₂*x₂=1-p)
    (h₃ : x₁*y₁=q) (h₄ : x₂*y₂=1-q)
    (h₅ : y₁*x₂=0) (h₆ : y₂*x₁=0) (h₇ : x₁*y₂=0) (h₈ : x₂*y₁=0) :
    (y₁+y₂)*(x₁+x₂)=1 ∧ (x₁+x₂)*(y₁+y₂)=1 := by
  constructor
  · simp only [add_mul,mul_add,h₁,h₂,h₅,h₆]
    noncomm_ring
  · simp only [add_mul,mul_add,h₃,h₄,h₇,h₈]
    noncomm_ring

/-- Decomposing one side through an idempotent gives mutually annihilating
compressed changes of basis on the two complementary corners. -/
theorem transported_complementary_blocks
    (x y p q : R) (hYX : y*x=1) (hXY : x*y=1) (h : x*p=q*x)
    (hp : p*p=p) :
    (y*q)*(x*p)=p ∧ (x*p)*(y*q)=q ∧
    (y*q)*(x*(1-p))=0 ∧ (x*p)*(y*(1-q))=0 := by
  have hy : p*y=y*q := by
    calc
      p*y = (y*x)*p*y := by rw [hYX,one_mul]
      _ = y*(x*p)*y := by noncomm_ring
      _ = y*q*(x*y) := by rw [h]; noncomm_ring
      _ = y*q := by rw [hXY,mul_one]
  have heq : x*p*y=q := by rw [h,mul_assoc,hXY,mul_one]
  have hq : q*q=q := by
    calc
      q*q = (x*p*y)*(x*p*y) := by rw [heq]
      _ = x*p*(y*x)*p*y := by noncomm_ring
      _ = q := by rw [hYX,mul_one,mul_assoc x,hp,heq]
  constructor
  · rw [← hy]
    calc
      p*y*(x*p) = p*(y*x)*p := by noncomm_ring
      _ = p := by rw [hYX,mul_one,hp]
  constructor
  · rw [← hy]
    calc
      x*p*(p*y) = x*(p*p)*y := by noncomm_ring
      _ = q := by rw [hp,h,mul_assoc,hXY,mul_one]
  constructor
  · rw [← hy]
    calc
      p*y*(x*(1-p))=p*(y*x)*(1-p) := by noncomm_ring
      _ = 0 := by rw [hYX,mul_one,mul_sub,mul_one,hp,sub_self]
  · rw [h]
    calc
      q*x*(y*(1-q)) = q*(x*y)*(1-q) := by noncomm_ring
      _ = 0 := by rw [hXY,mul_one,mul_sub,mul_one,hq,sub_self]

/-- An operator whose row and column equations both restrict to each of two
complementary corners is transported globally by the assembled inverse pair. -/
theorem corner_transport_assembly
    (A B : I → R) (x₁ x₂ y₁ y₂ p q : R)
    (h₁ : y₁*x₁=p) (h₂ : y₂*x₂=1-p)
    (h₃ : x₁*y₁=q) (h₄ : x₂*y₂=1-q)
    (h₅ : y₁*x₂=0) (h₆ : y₂*x₁=0) (h₇ : x₁*y₂=0) (h₈ : x₂*y₁=0)
    (hA : ∀ i, x₁*A i=B i*x₁) (hB : ∀ i, x₂*A i=B i*x₂) :
    ∃ x y : R, y*x=1 ∧ x*y=1 ∧ ∀ i, x*A i=B i*x := by
  obtain ⟨hy,hx⟩ := complementary_inverse_assembly _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  exact ⟨x₁+x₂,y₁+y₂,hy,hx,fun i => by rw [add_mul,mul_add,hA,hB]⟩

/-- The noncommutative word relation for the polynomial-calculus intertwiner
is closed under arbitrary finite word length with no additional hypothesis
on commutativity or on the coefficient ring. -/
theorem finite_word_conjugacy_from_generators
    (A B : I → R) (x : R) (h : ∀ i, x*A i=B i*x) (w : List I) :
    x*(w.map A).prod=(w.map B).prod*x := by
  induction w with
  | nil => simp
  | cons i w ih =>
    change x*(A i*(w.map A).prod)=B i*(w.map B).prod*x
    rw [← mul_assoc,h i,mul_assoc,ih,← mul_assoc]

end Residuals

end TwoHundredB
