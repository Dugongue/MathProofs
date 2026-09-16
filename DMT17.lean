import Mathlib

/-!
# Abundance and asymmetry of binary bent codes

Ding, Munemasa, and Tonchev, "Bent Vectorial Functions, Codes and Designs"
(2019), Conjecture 17, arXiv:1808.08487.

For a binary vectorial bent function F : F₂^(2m) → F₂^ell, the code consists
of all words x ↦ c + a(x) + μ(F(x)), with a and μ linear. Equivalence means
an arbitrary permutation of coordinates; no affine restriction is imposed.

Main results:
* `bent_code_parameters`: length 2^(2m), dimension 2m + ell + 1,
  and minimum distance 2^(2m-1) - 2^(m-1).
* `bent_class_eq_iff` and `bent_transitive_iff`: exact bridges between
  ordinary code equivalence/symmetry and the column orbits being counted.
* `codeClasses_lower`: 2^(ell * 2^m) ≤ 2^(d²) T, where d = 2m + ell + 1
  and T counts inequivalent codes obtained from all such bent functions.
* `transitiveClasses_bound`: at most 2^(d⁴ + d) of these classes are transitive.
* `eventual_uniform_bounds`: eventually, simultaneously for every 1 ≤ ell ≤ m,
  T ≥ 2^m and the transitive-class count times 2^m is at most T.
* `conjecture17`: for each fixed ell ≥ 1, exponentially many inequivalent
  codes exist and the proportion admitting a two-transitive group tends to zero.

The construction, finite group bounds, code parameters, equivalence bridges,
and limits are proved here from Mathlib. The construction uses arbitrary maps
C : GF(2^m) → F₂^ell in F_C(x,y) = P(xy) + C(y), with P a linear surjection.
-/

namespace DMT17

open scoped BigOperators
open Function
noncomputable section

abbrev Bit := ZMod 2

instance linearMapFintype {V W : Type*} [AddCommGroup V] [Module Bit V]
    [AddCommGroup W] [Module Bit W] [Fintype V] [Fintype W] : Fintype (V →ₗ[Bit] W) := by
  classical
  exact Fintype.ofInjective (fun f : V →ₗ[Bit] W => (f : V → W)) DFunLike.coe_injective

instance linearEquivFintype {V : Type*} [AddCommGroup V] [Module Bit V] [Fintype V] :
    Fintype (V ≃ₗ[Bit] V) :=
  Fintype.ofInjective (fun f : V ≃ₗ[Bit] V => f.toLinearMap) LinearEquiv.toLinearMap_injective

/-- A finite subgroup has a generating set of logarithmic size. -/
theorem small_generators {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = H ∧ 2 ^ s.card ≤ Nat.card H := by
  classical
  let := Fintype.ofFinite G
  have hex : ∃ n : ℕ, ∃ s : Finset G, s.card = n ∧ Subgroup.closure (s : Set G) = H :=
    ⟨(H : Set G).toFinset.card, (H : Set G).toFinset, rfl, by simp⟩
  obtain ⟨s, hs, hsH⟩ := Nat.find_spec hex
  have hirr : ∀ a ∈ s, a ∉ Subgroup.closure ((s.erase a : Finset G) : Set G) := by
    intro a ha hmem
    have heq : Subgroup.closure ((s.erase a : Finset G) : Set G) = H := by
      rw [← hsH]
      apply le_antisymm (Subgroup.closure_mono (by simp))
      rw [Subgroup.closure_le]
      intro x hx
      by_cases hxa : x = a
      · simpa [hxa] using hmem
      · exact Subgroup.subset_closure (Finset.mem_erase.mpr ⟨hxa, hx⟩)
    have hmin := Nat.find_min' hex ⟨s.erase a, rfl, heq⟩
    have hlt := Finset.card_erase_lt_of_mem ha
    omega
  suffices ∀ t : Finset G,
      (∀ a ∈ t, a ∉ Subgroup.closure ((t.erase a : Finset G) : Set G)) →
      2 ^ t.card ≤ Nat.card (Subgroup.closure (t : Set G)) from
    ⟨s, hsH, hsH ▸ this s hirr⟩
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    intro ht
    have hta : a ∉ Subgroup.closure (t : Set G) := by
      simpa [ha] using ht a (Finset.mem_insert_self a t)
    have hi := ih (by
      intro b hb hmem
      apply ht b (Finset.mem_insert_of_mem hb)
      apply Subgroup.closure_mono _ hmem
      intro x hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
        Finset.mem_insert_of_mem (Finset.mem_erase.mp hx).2⟩)
    let K := Subgroup.closure (t : Set G)
    let L := Subgroup.closure ((insert a t : Finset G) : Set G)
    have hKL : K ≤ L := Subgroup.closure_mono (by simp)
    have hne : K ≠ L := by
      intro h
      apply hta
      rw [show Subgroup.closure (t : Set G) = L from h]
      exact Subgroup.subset_closure (Finset.mem_insert_self a t)
    have hlt : Nat.card K < Nat.card L := lt_of_le_of_ne
      (Subgroup.card_le_of_le hKL) (fun h => hne (Subgroup.eq_of_le_of_card_ge hKL h.ge))
    obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hKL
    have hq2 : 2 ≤ q := by
      have hp : 0 < Nat.card K := Nat.card_pos
      nlinarith
    have hdouble : 2 * Nat.card K ≤ Nat.card L := by nlinarith
    rw [Finset.card_insert_of_notMem ha, pow_succ]
    change 2 ^ t.card * 2 ≤ Nat.card L
    nlinarith

/-- The subgroup count uses generating tuples, not subsets of the group. -/
theorem subgroup_count {G : Type*} [Group G] [Fintype G] (r : ℕ)
    (hG : Fintype.card G ≤ 2 ^ r) :
    Nat.card (Subgroup G) ≤ 2 ^ (r * r) := by
  classical
  let generate (f : Fin r → G) := Subgroup.closure (Set.range f)
  have hsurj : Surjective generate := by
    intro H
    obtain ⟨s, hs, hsize⟩ := small_generators H
    have hsr : s.card ≤ r := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      exact hsize.trans (H.card_le_card_group.trans (by simpa using hG))
    obtain ⟨e⟩ : Nonempty (s ↪ Fin r) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hsr)
    let f : Fin r → G := Function.extend e Subtype.val (fun _ => 1)
    refine ⟨f, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : ∃ x, e x = i
      · obtain ⟨x, rfl⟩ := hi
        change Function.extend e Subtype.val (fun _ => 1) (e x) ∈ H
        rw [e.injective.extend_apply]
        rw [← hs]
        exact Subgroup.subset_closure x.property
      · change Function.extend e Subtype.val (fun _ => 1) i ∈ H
        rw [Function.extend_apply' _ _ _ hi]
        exact H.one_mem
    · rw [← hs, Subgroup.closure_le]
      intro x hx
      apply Subgroup.subset_closure
      exact ⟨e ⟨x, hx⟩, e.injective.extend_apply _ _ _⟩
  calc
    Nat.card (Subgroup G) ≤ Nat.card (Fin r → G) := Nat.card_le_card_of_surjective _ hsurj
    _ = Fintype.card G ^ r := by simp [Nat.card_eq_fintype_card]
    _ ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left hG _
    _ = 2 ^ (r * r) := (pow_mul _ _ _).symm

/-- The number of subsets that are single subgroup orbits. -/
theorem orbit_set_count {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] (r : ℕ) (hG : Fintype.card G ≤ 2 ^ r) :
    Nat.card {s : Set X // ∃ H : Subgroup G, ∃ x : X, s = MulAction.orbit H x} ≤
      2 ^ (r * r) * Fintype.card X := by
  classical
  let f (p : Subgroup G × X) :
      {s : Set X // ∃ H : Subgroup G, ∃ x : X, s = MulAction.orbit H x} :=
    ⟨MulAction.orbit p.1 p.2, p.1, p.2, rfl⟩
  have hf : Surjective f := by
    rintro ⟨s, H, x, rfl⟩
    exact ⟨(H, x), rfl⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := X)]
    exact Nat.mul_le_mul_right _ (subgroup_count r hG))

def sign (b : Bit) : ℝ := if b = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign, Bit]

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 :=
  (by decide : ∀ b : Bit, b = 0 ∨ b = 1) b

theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl
  · rw [zero_add, sign_zero, one_mul]
  · rcases bit_cases b with rfl | rfl
    · rw [add_zero, sign_zero, mul_one]
    · rw [show (1 : Bit) + 1 = 0 from rfl, sign_zero, sign_one]
      norm_num

@[simp] theorem sign_sq (a : Bit) : sign a ^ 2 = 1 := by
  rcases bit_cases a with rfl | rfl <;> norm_num

section Characters
variable {V : Type*} [AddCommGroup V] [Module Bit V] [Fintype V]

theorem functional_nonzero {a : V →ₗ[Bit] Bit} (ha : a ≠ 0) : ∃ x, a x = 1 := by
  by_contra h
  apply ha
  ext x
  exact (bit_cases (a x)).resolve_right (fun hx => h ⟨x, hx⟩)

/-- Orthogonality of the actual binary characters. -/
theorem linear_character_sum (a : V →ₗ[Bit] Bit) :
    (∑ x, sign (a x)) = if a = 0 then (Fintype.card V : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    obtain ⟨v, hv⟩ := functional_nonzero ha
    have h := Equiv.sum_comp (Equiv.addRight v) (fun x => sign (a x))
    change (∑ x, sign (a (x + v))) = ∑ x, sign (a x) at h
    simp_rw [map_add, sign_add, hv, sign_one, mul_neg_one] at h
    rw [Finset.sum_neg_distrib] at h
    linarith

end Characters

section Bent
variable {V W : Type*} [AddCommGroup V] [Module Bit V] [Fintype V]
  [AddCommGroup W] [Module Bit W]

/-- Unnormalized binary Walsh coefficient, with every linear input frequency. -/
def walsh (F : V → W) (μ : W →ₗ[Bit] Bit) (a : V →ₗ[Bit] Bit) : ℝ :=
  ∑ x, sign (μ (F x) + a x)

/-- Vectorial bentness: every nonzero component has flat Walsh spectrum. -/
def Bent (F : V → W) : Prop :=
  ∀ μ : W →ₗ[Bit] Bit, μ ≠ 0 → ∀ a : V →ₗ[Bit] Bit,
    walsh F μ a ^ 2 = Fintype.card V

/-- No nonzero component of a bent map on a nontrivial domain is affine. -/
theorem bent_no_affine (F : V → W) (hF : Bent F) (hV : 1 < Fintype.card V)
    (μ : W →ₗ[Bit] Bit) (a : V →ₗ[Bit] Bit) (c : Bit)
    (h : ∀ x, c + a x + μ (F x) = 0) : μ = 0 ∧ a = 0 ∧ c = 0 := by
  have hμ : μ = 0 := by
    by_contra hn
    have hb := hF μ hn a
    have hc : walsh F μ a = (Fintype.card V : ℝ) * sign c := by
      unfold walsh
      have he : ∀ x, μ (F x) + a x = c := by
        intro x
        have hx := h x
        have ht : c + c = 0 := by rcases bit_cases c with rfl | rfl <;> rfl
        linear_combination hx - ht
      simp_rw [he]
      simp
    rw [hc, mul_pow, sign_sq, mul_one] at hb
    have hp : (1 : ℝ) < Fintype.card V := by exact_mod_cast hV
    nlinarith
  have hc : c = 0 := by simpa [hμ] using h 0
  refine ⟨hμ, ?_, hc⟩
  ext x
  simpa [hμ, hc] using h x

end Bent

section MaioranaMcFarland
variable {K W : Type*} [Field K] [Fintype K] [Algebra Bit K]
  [AddCommGroup W] [Module Bit W]

/-- Multiplication followed by a binary functional is a nondegenerate pairing. -/
def pairing (ψ : K →ₗ[Bit] Bit) : K →ₗ[Bit] (K →ₗ[Bit] Bit) :=
  LinearMap.mk₂ Bit (fun y x => ψ (x * y))
    (by intros; simp [mul_add]) (by intros; simp)
    (by intros; simp [add_mul]) (by intros; simp)

omit [Fintype K] in
@[simp] theorem pairing_apply (ψ : K →ₗ[Bit] Bit) (y x : K) :
    pairing ψ y x = ψ (x * y) := rfl

theorem pairing_injective (ψ : K →ₗ[Bit] Bit) (hψ : ψ ≠ 0) :
    Injective (pairing ψ) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro y hy
  by_contra hyn
  obtain ⟨t, ht⟩ := functional_nonzero hψ
  have he := congrArg (fun f : K →ₗ[Bit] Bit => f (t / y)) hy
  simp [pairing_apply, div_mul_cancel₀ _ hyn, ht] at he

theorem pairing_surjective (ψ : K →ₗ[Bit] Bit) (hψ : ψ ≠ 0) :
    Surjective (pairing ψ) := by
  let := Fintype.ofFinite (K →ₗ[Bit] Bit)
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨pairing_injective ψ hψ, ?_⟩).2
  rw [Module.card_eq_pow_finrank (K := Bit) (V := K), Module.card_eq_pow_finrank (K := Bit) (V := K →ₗ[Bit] Bit), Subspace.dual_finrank_eq]

/-- An arbitrary output offset is permitted in the vectorial MM construction. -/
def mm (P : K →ₗ[Bit] W) (C : K → W) (v : K × K) : W := P (v.1 * v.2) + C v.2

omit [Fintype K] in
theorem mm_injective (P : K →ₗ[Bit] W) : Injective (mm P) := by
  intro C D h
  funext y
  simpa [mm] using congrFun h (0, y)

/-- Exact Walsh evaluation; no bentness oracle is assumed. -/
theorem mm_walsh (P : K →ₗ[Bit] W) (hP : Surjective P) (C : K → W)
    (μ : W →ₗ[Bit] Bit) (hμ : μ ≠ 0) (a : K × K →ₗ[Bit] Bit) :
    ∃ y : K, walsh (mm P C) μ a =
      Fintype.card K * sign (μ (C y) + a (0, y)) := by
  classical
  let ψ := μ.comp P
  have hψ : ψ ≠ 0 := by
    intro h
    apply hμ
    ext w
    obtain ⟨t, rfl⟩ := hP w
    exact congrArg (fun f : K →ₗ[Bit] Bit => f t) h
  let α := a.comp (LinearMap.inl Bit K K)
  obtain ⟨y, hy⟩ := pairing_surjective ψ hψ α
  refine ⟨y, ?_⟩
  have hfreq : ∀ z : K, pairing ψ z + α = 0 ↔ z = y := by
    intro z
    rw [← hy]
    have hz : pairing ψ z + pairing ψ y = pairing ψ (z + y) := (map_add _ _ _).symm
    rw [hz, ← map_zero (pairing ψ), (pairing_injective ψ hψ).eq_iff]
    have hyy : y + y = 0 := by
      have := congrArg (fun b : Bit => b • y) (show (1 : Bit) + 1 = 0 from rfl)
      simpa [add_smul] using this
    constructor
    · intro h
      have := congrArg (fun z => z + y) h
      simpa [add_assoc, hyy] using this
    · rintro rfl; exact hyy
  have ha : ∀ x z : K, a (x, z) = α x + a (0, z) := by
    intro x z
    simpa [α] using map_add a (x, 0) (0, z)
  unfold walsh
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ z, ∑ x, sign (μ (mm P C (x, z)) + a (x, z))) =
        ∑ z, sign (μ (C z) + a (0, z)) * ∑ x, sign ((pairing ψ z + α) x) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [← sign_add]
      congr 1
      change μ (P (x * z) + C z) + a (x, z) =
        μ (C z) + a (0, z) + (ψ (x * z) + α x)
      rw [map_add, ha x z]
      change μ (P (x * z)) + μ (C z) + (α x + a (0, z)) =
        μ (C z) + a (0, z) + (μ (P (x * z)) + α x)
      ring
    _ = ∑ z, sign (μ (C z) + a (0, z)) *
        (if z = y then (Fintype.card K : ℝ) else 0) := by
      simp_rw [linear_character_sum, hfreq]
    _ = _ := by simp; ring

theorem mm_bent (P : K →ₗ[Bit] W) (hP : Surjective P) (C : K → W) : Bent (mm P C) := by
  intro μ hμ a
  obtain ⟨y, hy⟩ := mm_walsh P hP C μ hμ a
  rw [hy, mul_pow, sign_sq, mul_one, Fintype.card_prod]
  push_cast
  ring

end MaioranaMcFarland

section OrbitCounting
variable (G : Type*) {X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]

/-- Equivalence classes represented by a finite collection of objects. -/
def classImage (s : Finset X) : Finset (Quotient (MulAction.orbitRel G X)) := by
  classical
  exact s.image (Quotient.mk (MulAction.orbitRel G X))

omit [Fintype X] in
/-- An orbit has at most one image for each group element. -/
theorem classImage_lower (s : Finset X) :
    s.card ≤ Fintype.card G * (classImage G s).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have hs : {a ∈ s | Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x} ⊆
      Finset.univ.image (fun g : G => g • x) := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact he))
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, hg⟩
  exact (Finset.card_le_card hs).trans (by simpa using
    (Finset.card_image_le (s := Finset.univ) (f := fun g : G => g • x)))

omit [Fintype G] [Fintype X] in
theorem classImage_mono {s t : Finset X} (h : s ⊆ t) : classImage G s ⊆ classImage G t := by
  classical
  exact Finset.image_subset_image h

end OrbitCounting

section Configurations
variable {A : Type*} [AddCommGroup A] [Module Bit A] [Fintype A]

/-- A column set is transitive when a group of linear symmetries is transitive on it. -/
def TransitiveColumns (s : Set A) : Prop :=
  ∃ H : Subgroup (A ≃ₗ[Bit] A), ∃ x : A, s = MulAction.orbit H x

theorem linear_group_card :
    Nat.card (A ≃ₗ[Bit] A) ≤ 2 ^ (Module.finrank Bit A * Module.finrank Bit A) := by
  classical
  let := Fintype.ofFinite (A →ₗ[Bit] A)
  let := Fintype.ofFinite (A ≃ₗ[Bit] A)
  calc
    Nat.card (A ≃ₗ[Bit] A) ≤ Nat.card (A →ₗ[Bit] A) :=
      Nat.card_le_card_of_injective _ LinearEquiv.toLinearMap_injective
    _ = _ := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bit),
        Module.finrank_linearMap]
      simp [Bit]

/-- Universal bound for transitive binary column configurations of dimension d. -/
theorem transitive_columns_count :
    Nat.card {s : Set A // TransitiveColumns s} ≤
      2 ^ ((Module.finrank Bit A) ^ 4 + Module.finrank Bit A) := by
  classical
  let := Fintype.ofFinite (A ≃ₗ[Bit] A)
  have h := orbit_set_count (G := A ≃ₗ[Bit] A) (X := A)
    (Module.finrank Bit A * Module.finrank Bit A) (by simpa using (linear_group_card (A := A)))
  have hA : Fintype.card A = 2 ^ Module.finrank Bit A := by
    simpa [Bit] using (Module.card_eq_pow_finrank (K := Bit) (V := A))
  simpa only [TransitiveColumns, hA, ← pow_add, show
    (Module.finrank Bit A * Module.finrank Bit A) *
      (Module.finrank Bit A * Module.finrank Bit A) + Module.finrank Bit A =
      (Module.finrank Bit A) ^ 4 + Module.finrank Bit A by ring] using h

end Configurations

abbrev Space (n : ℕ) := Fin n → Bit
abbrev Ambient (n ell : ℕ) := Bit × (Space n × Space ell)
def dimension (m ell : ℕ) : ℕ := 2 * m + ell + 1

def column {V W : Type*} (F : V → W) (x : V) : Bit × (V × W) := (1, x, F x)
def columns {V W : Type*} (F : V → W) : Set (Bit × (V × W)) := Set.range (column F)

theorem column_injective {V W : Type*} (F : V → W) : Injective (column F) := by
  intro x y h
  exact congrArg (fun z => z.2.1) h

theorem columns_injective {V W : Type*} : Injective (@columns V W) := by
  intro F H h
  funext x
  have hx : column F x ∈ columns H := h ▸ Set.mem_range_self x
  obtain ⟨y, hy⟩ := hx
  have hxy : y = x := congrArg (fun z => z.2.1) hy
  subst y
  exact (congrArg (fun z => z.2.2) hy).symm

/-- Exactly the graph-column configurations of binary vectorial bent functions. -/
def configurations (m ell : ℕ) : Finset (Set (Ambient (2 * m) ell)) := by
  classical
  exact Finset.univ.filter (fun s => ∃ F : Space (2 * m) → Space ell, Bent F ∧ s = columns F)

open scoped Pointwise

/-- Unlabelled bent-code classes; the code-equivalence bridge is proved below. -/
def codeClasses (m ell : ℕ) := classImage (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell)
  (configurations m ell)

def transitiveClasses (m ell : ℕ) :
    Finset (Quotient (MulAction.orbitRel
      (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) (Set (Ambient (2 * m) ell)))) := by
  classical
  exact classImage (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell)
    ((configurations m ell).filter TransitiveColumns)

theorem ambient_finrank (m ell : ℕ) :
    Module.finrank Bit (Ambient (2 * m) ell) = dimension m ell := by
  simp [Ambient, Space, dimension, Module.finrank_prod]
  omega

theorem transitiveClasses_bound (m ell : ℕ) :
    (transitiveClasses m ell).card ≤ 2 ^ (dimension m ell ^ 4 + dimension m ell) := by
  classical
  have h₁ : (transitiveClasses m ell).card ≤
      ((configurations m ell).filter TransitiveColumns).card := Finset.card_image_le
  have h₂ : ((configurations m ell).filter TransitiveColumns).card ≤
      Nat.card {s : Set (Ambient (2 * m) ell) // TransitiveColumns s} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩
  have h₃ := transitive_columns_count (A := Ambient (2 * m) ell)
  rw [ambient_finrank] at h₃
  exact (h₁.trans h₂).trans h₃

/-- Bentness is preserved by a linear reindexing of the domain. -/
theorem bent_reindex {U V W : Type*} [AddCommGroup U] [Module Bit U] [Fintype U]
    [AddCommGroup V] [Module Bit V] [Fintype V] [AddCommGroup W] [Module Bit W]
    (e : U ≃ₗ[Bit] V) (F : V → W) (hF : Bent F) : Bent (F ∘ e) := by
  intro μ hμ a
  have he : walsh (F ∘ e) μ a = walsh F μ (a.comp e.symm.toLinearMap) := by
    unfold walsh
    convert e.toEquiv.sum_comp (fun x => sign (μ (F x) + a (e.symm x))) using 1 <;> simp
  rw [he, hF μ hμ, Fintype.card_congr e.toEquiv]

abbrev BinaryField (m : ℕ) := GaloisField 2 m

instance binaryFieldDecidableEq (m : ℕ) : DecidableEq (BinaryField m) := Classical.decEq _
instance binaryFieldFintype (m : ℕ) : Fintype (BinaryField m) := Fintype.ofFinite _

def fieldCoordinates (m : ℕ) (hm : m ≠ 0) : BinaryField m ≃ₗ[Bit] Space m :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Bit, Space, GaloisField.finrank 2 hm])

def inputCoordinates (m : ℕ) (hm : m ≠ 0) : Space (2 * m) ≃ₗ[Bit] (BinaryField m × BinaryField m) :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Bit, Space, Module.finrank_prod, GaloisField.finrank 2 hm]; omega)

/-- A surjective binary output projection exists throughout the Nyberg range. -/
def outputProjection (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m) :
    BinaryField m →ₗ[Bit] Space ell where
  toFun x i := fieldCoordinates m hm x ⟨i.val, lt_of_lt_of_le i.isLt hell⟩
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem outputProjection_surjective (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m) :
    Surjective (outputProjection m ell hm hell) := by
  classical
  intro w
  let v : Space m := fun j => if h : j.val < ell then w ⟨j.val, h⟩ else 0
  refine ⟨(fieldCoordinates m hm).symm v, ?_⟩
  ext i
  simp [outputProjection, v, i.isLt]

def bentFamily (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m)
    (C : BinaryField m → Space ell) : Space (2 * m) → Space ell :=
  mm (outputProjection m ell hm hell) C ∘ inputCoordinates m hm

theorem bentFamily_bent (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m)
    (C : BinaryField m → Space ell) : Bent (bentFamily m ell hm hell C) :=
  bent_reindex _ _ (mm_bent _ (outputProjection_surjective m ell hm hell) C)

theorem bentFamily_injective (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m) :
    Injective (bentFamily m ell hm hell) := by
  intro C D h
  apply mm_injective (outputProjection m ell hm hell)
  funext v
  obtain ⟨x, rfl⟩ := (inputCoordinates m hm).surjective v
  exact congrFun h x

theorem family_parameter_count (m ell : ℕ) (hm : m ≠ 0) :
    Fintype.card (BinaryField m → Space ell) = 2 ^ (ell * 2 ^ m) := by
  have hK : Fintype.card (BinaryField m) = 2 ^ m := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 m hm
  simp [Space, Bit, hK, ← pow_mul]

/-- Exact finite lower bound on inequivalent bent codes, without subtraction or rounding. -/
theorem codeClasses_lower (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m) :
    2 ^ (ell * 2 ^ m) ≤ 2 ^ (dimension m ell ^ 2) * (codeClasses m ell).card := by
  classical
  let f := fun C : BinaryField m → Space ell => columns (bentFamily m ell hm hell C)
  let s := Finset.univ.image f
  have hinj : Injective f := columns_injective.comp (bentFamily_injective m ell hm hell)
  have hcard : s.card = 2 ^ (ell * 2 ^ m) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, family_parameter_count m ell hm]
  have hsub : s ⊆ configurations m ell := by
    intro t ht
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bentFamily m ell hm hell C,
      bentFamily_bent m ell hm hell C, rfl⟩
  have hc := classImage_lower (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) s
  rw [hcard] at hc
  have hg : Fintype.card (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) ≤
      2 ^ (dimension m ell ^ 2) := by
    have h := linear_group_card (A := Ambient (2 * m) ell)
    rw [ambient_finrank, ← pow_two] at h
    simpa [Nat.card_eq_fintype_card] using h
  exact hc.trans (Nat.mul_le_mul hg (Finset.card_le_card (classImage_mono _ hsub)))

/-- There is at least one bent-code class for every admissible pair of dimensions. -/
theorem codeClasses_pos (m ell : ℕ) (hm : m ≠ 0) (hell : ell ≤ m) :
    0 < (codeClasses m ell).card := by
  have h := codeClasses_lower m ell hm hell
  have hp : 0 < 2 ^ (ell * 2 ^ m) := by positivity
  by_contra hn
  have hz : (codeClasses m ell).card = 0 := by omega
  simp [hz] at h

section Codes
variable {I A : Type*} [AddCommGroup A] [Module Bit A]

/-- The binary row code generated by a family of columns. -/
def evaluation (c : I → A) : (A →ₗ[Bit] Bit) →ₗ[Bit] (I → Bit) where
  toFun φ i := φ (c i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def linearCode (c : I → A) : Submodule Bit (I → Bit) := (evaluation c).range

/-- Permuting the coordinates of a word. -/
def permute (e : Equiv.Perm I) : (I → Bit) ≃ₗ[Bit] (I → Bit) where
  toFun w := w ∘ e
  invFun w := w ∘ e.symm
  left_inv _ := by ext i; simp
  right_inv _ := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Ordinary permutation equivalence, with a specified coordinate permutation. -/
def CodePermutation (c d : I → A) (e : Equiv.Perm I) : Prop :=
  (linearCode d).map (permute e).toLinearMap = linearCode c

variable [Fintype A]

/-- A coordinate equivalence between full-rank generator matrices lifts to GL. -/
theorem codePermutation_lift (c d : I → A)
    (hc : Injective (evaluation c)) (hd : Injective (evaluation d))
    (e : Equiv.Perm I) (he : CodePermutation c d e) :
    ∃ g : A ≃ₗ[Bit] A, ∀ i, g (c i) = d (e i) := by
  classical
  let ec := LinearEquiv.ofInjective (evaluation c) hc
  let ed := LinearEquiv.ofInjective (evaluation d) hd
  let ep := (permute e).submoduleMap (linearCode d)
  let T := ed.trans (ep.trans ((LinearEquiv.ofEq _ _ he).trans ec.symm))
  have hT (φ : A →ₗ[Bit] Bit) (i : I) : T φ (c i) = φ (d (e i)) := by
    have h := congrArg (fun z : linearCode c => (z : I → Bit) i)
      (ec.apply_symm_apply ((LinearEquiv.ofEq _ _ he) (ep (ed φ))))
    exact h
  let g := (Module.evalEquiv Bit A).trans (T.dualMap.trans (Module.evalEquiv Bit A).symm)
  refine ⟨g, fun i => ?_⟩
  apply (Module.evalEquiv Bit A).injective
  ext φ
  change (Module.evalEquiv Bit A) (g (c i)) φ = φ (d (e i))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.dualMap_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  exact hT φ i

omit [Fintype A] in
theorem codePermutation_of_linear (c d : I → A) (e : Equiv.Perm I)
    (g : A ≃ₗ[Bit] A) (h : ∀ i, g (c i) = d (e i)) : CodePermutation c d e := by
  ext w
  constructor
  · rintro ⟨v, ⟨φ, rfl⟩, rfl⟩
    refine ⟨φ.comp g.toLinearMap, ?_⟩
    ext i
    exact congrArg φ (h i)
  · rintro ⟨φ, rfl⟩
    refine ⟨evaluation d (φ.comp g.symm.toLinearMap), ⟨_, rfl⟩, ?_⟩
    ext i
    change φ (g.symm (d (e i))) = φ (c i)
    rw [← h i, g.symm_apply_apply]

/-- The bridge is an equivalence, not just a source of sufficient symmetries. -/
theorem codePermutation_iff (c d : I → A)
    (hc : Injective (evaluation c)) (hd : Injective (evaluation d)) (e : Equiv.Perm I) :
    CodePermutation c d e ↔ ∃ g : A ≃ₗ[Bit] A, ∀ i, g (c i) = d (e i) :=
  ⟨codePermutation_lift c d hc hd e, fun ⟨g, hg⟩ => codePermutation_of_linear c d e g hg⟩

end Codes

section FullRank
variable {V W : Type*} [AddCommGroup V] [Module Bit V] [Fintype V]
    [AddCommGroup W] [Module Bit W]

/-- Bent graph columns have full rank. -/
theorem bent_evaluation_injective (F : V → W) (hF : Bent F) (hV : 1 < Fintype.card V) :
    Injective (evaluation (column F)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  let a : V →ₗ[Bit] Bit := φ.comp
    ((LinearMap.inr Bit Bit (V × W)).comp (LinearMap.inl Bit V W))
  let μ : W →ₗ[Bit] Bit := φ.comp
    ((LinearMap.inr Bit Bit (V × W)).comp (LinearMap.inr Bit V W))
  let c := φ (1, 0, 0)
  have hsplit (x : V) (y : W) : φ (1, x, y) = c + a x + μ y := by
    have hz : ((1 : Bit), x, y) = ((1, 0, 0) + (0, x, 0)) + (0, 0, y) := by simp
    rw [hz, map_add, map_add]
    rfl
  have hz (x : V) : c + a x + μ (F x) = 0 := by
    rw [← hsplit]
    exact congrFun hφ x
  obtain ⟨hμ, ha, hc⟩ := bent_no_affine F hF hV μ a c hz
  apply LinearMap.ext
  intro z
  rcases z with ⟨b, x, y⟩
  rcases bit_cases b with rfl | rfl
  · have he : ((0 : Bit), x, y) = (0, x, 0) + (0, 0, y) := by simp
    rw [he, map_add]
    change a x + μ y = 0
    simp [ha, hμ]
  · simpa [hc, ha, hμ] using hsplit x y

/-- The code dimension claimed in the literature. -/
theorem bent_code_dimension (m ell : ℕ) (hm : m ≠ 0)
    (F : Space (2 * m) → Space ell) (hF : Bent F) :
    Module.finrank Bit (linearCode (column F)) = dimension m ell := by
  have hv : 1 < Fintype.card (Space (2 * m)) := by
    simp [Space, Bit, hm]
  have h := (LinearEquiv.ofInjective (evaluation (column F))
    (bent_evaluation_injective F hF hv)).finrank_eq
  rw [Subspace.dual_finrank_eq, ambient_finrank] at h
  exact h.symm

end FullRank

/-- Exponential domination, with a constant independent of the output dimension. -/
theorem eventual_exponent_bound : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ ell, ell ≤ m → dimension m ell ^ 4 + dimension m ell + dimension m ell ^ 2 + m ≤ 2 ^ m := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1 : ℝ) < 2)).const_mul 277
  simp only [mul_zero] at ht
  have he : ∀ᶠ m : ℕ in Filter.atTop, (277 : ℝ) * (m : ℝ) ^ 4 ≤ 2 ^ m := by
    have h := ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h] with m hm
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have hm' : (277 : ℝ) * (m : ℝ) ^ 4 / 2 ^ m ≤ 1 := by simpa only [mul_div_assoc] using hm
    simpa only [one_mul] using (div_le_iff₀ hp).mp hm'
  filter_upwards [he, Filter.eventually_ge_atTop 1] with m he hm ell hell
  have hd : dimension m ell ≤ 4 * m := by unfold dimension; omega
  have h4 : dimension m ell ^ 4 ≤ 256 * m ^ 4 := by
    calc
      _ ≤ (4 * m) ^ 4 := by gcongr
      _ = _ := by ring
  have h2 : dimension m ell ^ 2 ≤ 16 * m ^ 2 := by
    calc
      _ ≤ (4 * m) ^ 2 := by gcongr
      _ = _ := by ring
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hm4 : m ^ 2 ≤ m ^ 4 := by nlinarith [sq_nonneg (m * m - 1 : ℤ)]
  have hn : 277 * m ^ 4 ≤ 2 ^ m := by exact_mod_cast he
  nlinarith

/-- Uniform finite bounds for all admissible output dimensions once m is large. -/
theorem eventual_uniform_bounds : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ ell, 1 ≤ ell → ell ≤ m →
      2 ^ m ≤ (codeClasses m ell).card ∧
      (transitiveClasses m ell).card * 2 ^ m ≤ (codeClasses m ell).card := by
  filter_upwards [eventual_exponent_bound, Filter.eventually_ge_atTop 1] with m hm hm1 ell hl hell
  have he := hm ell hell
  have hexp : dimension m ell ^ 2 + (dimension m ell ^ 4 + dimension m ell + m) ≤
      ell * 2 ^ m := by
    have h := Nat.mul_le_mul_right (2 ^ m) hl
    nlinarith
  have hp : 2 ^ (dimension m ell ^ 2) *
      (2 ^ (dimension m ell ^ 4 + dimension m ell) * 2 ^ m) ≤
      2 ^ (ell * 2 ^ m) := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) hexp
  have ht : 2 ^ (dimension m ell ^ 4 + dimension m ell) * 2 ^ m ≤
      (codeClasses m ell).card := by
    have h := hp.trans (codeClasses_lower m ell (by omega) hell)
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  constructor
  · exact (Nat.le_mul_of_pos_left _ (by positivity)).trans ht
  · exact (Nat.mul_le_mul_right _ (transitiveClasses_bound m ell)).trans ht

/-- Almost every code in the family is not even transitive, uniformly over 1 ≤ ell ≤ m. -/
theorem almost_all_nontransitive (ell : ℕ) (hell : 1 ≤ ell) :
    Filter.Tendsto (fun m => ((transitiveClasses m ell).card : ℝ) / (codeClasses m ell).card)
      Filter.atTop (nhds 0) := by
  have hb : ∀ᶠ m : ℕ in Filter.atTop,
      ((transitiveClasses m ell).card : ℝ) / (codeClasses m ell).card ≤ (1 / 2 : ℝ) ^ m := by
    filter_upwards [eventual_uniform_bounds, Filter.eventually_ge_atTop ell] with m hm hmell
    obtain ⟨hg, ht⟩ := hm ell hell hmell
    have hp : (0 : ℝ) < (codeClasses m ell).card := by
      exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2 ^ m) hg)
    rw [one_div_pow, div_le_div_iff₀ hp (by positivity)]
    simpa only [one_mul] using (show ((transitiveClasses m ell).card : ℝ) * 2 ^ m ≤ (codeClasses m ell).card by exact_mod_cast ht)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall (fun m => by positivity)) hb

/-- Exponentially many inequivalent ordinary codes, for each fixed nonzero output dimension. -/
theorem exponentially_many_codes (ell : ℕ) (hell : 1 ≤ ell) :
    ∀ᶠ m : ℕ in Filter.atTop, 2 ^ m ≤ (codeClasses m ell).card := by
  filter_upwards [eventual_uniform_bounds, Filter.eventually_ge_atTop ell] with m hm hmell
  exact (hm ell hell hmell).1

section CodeOrbits
variable {I A : Type*} [AddCommGroup A] [Module Bit A] [Fintype A]

omit [Fintype A] in
theorem linear_range_eq (c d : I → A) (e : Equiv.Perm I) (g : A ≃ₗ[Bit] A)
    (h : ∀ i, g (c i) = d (e i)) : g • Set.range c = Set.range d := by
  ext y
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨e i, (h i).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨c (e.symm j), Set.mem_range_self _, by simpa using h (e.symm j)⟩

omit [Fintype A] in
/-- Distinct columns turn a linear equivalence of column sets into a coordinate permutation. -/
theorem linear_range_permutation (c d : I → A) (hc : Injective c) (hd : Injective d)
    (g : A ≃ₗ[Bit] A) (h : g • Set.range c = Set.range d) :
    ∃ e : Equiv.Perm I, ∀ i, g (c i) = d (e i) := by
  classical
  have hi (i : I) : ∃ j, d j = g (c i) := by
    have hx := Set.smul_mem_smul_set (a := g) (Set.mem_range_self (f := c) i)
    rw [h] at hx
    exact hx
  let f : I → I := fun i => (hi i).choose
  have hf (i : I) : d (f i) = g (c i) := (hi i).choose_spec
  have hfi : Injective f := by
    intro i j hij
    apply hc
    apply g.injective
    rw [← hf i, ← hf j, hij]
  have hfs : Surjective f := by
    intro j
    have hj : d j ∈ g • Set.range c := h.symm ▸ Set.mem_range_self j
    obtain ⟨_, ⟨i, rfl⟩, hij⟩ := Set.mem_smul_set.mp hj
    exact ⟨i, hd ((hf i).trans hij)⟩
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun i => (hf i).symm⟩

/-- Equality in the quotient used for counting is exactly ordinary code equivalence. -/
theorem column_class_eq_iff (c d : I → A) (hc : Injective c) (hd : Injective d)
    (hcr : Injective (evaluation c)) (hdr : Injective (evaluation d)) :
    Quotient.mk (MulAction.orbitRel (A ≃ₗ[Bit] A) (Set A)) (Set.range c) =
      Quotient.mk (MulAction.orbitRel (A ≃ₗ[Bit] A) (Set A)) (Set.range d) ↔
      ∃ e : Equiv.Perm I, CodePermutation c d e := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact h.symm))
    obtain ⟨e, he⟩ := linear_range_permutation c d hc hd g hg
    exact ⟨e, codePermutation_of_linear c d e g he⟩
  · rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := codePermutation_lift c d hcr hdr e he
    exact (Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨g, linear_range_eq c d e g hg⟩))).symm

/-- Transitivity of the ordinary coordinate automorphism group. -/
def TransitiveCode (c : I → A) : Prop :=
  ∀ i j, ∃ e : Equiv.Perm I, CodePermutation c c e ∧ e i = j

/-- Two-transitivity of the ordinary coordinate automorphism group. -/
def TwoTransitiveCode (c : I → A) : Prop :=
  ∀ i j k l, i ≠ j → k ≠ l →
    ∃ e : Equiv.Perm I, CodePermutation c c e ∧ e i = k ∧ e j = l

omit [Fintype A] in
theorem twoTransitive_transitive [Nontrivial I] (c : I → A) (h : TwoTransitiveCode c) :
    TransitiveCode c := by
  intro i k
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨l, hl⟩ := exists_ne k
  obtain ⟨e, he, hi, _⟩ := h i j k l hj.symm hl.symm
  exact ⟨e, he, hi⟩

/-- Orbit transitivity and ordinary code transitivity coincide for full-rank distinct columns. -/
theorem transitiveCode_iff [Nonempty I] (c : I → A)
    (hc : Injective c) (hr : Injective (evaluation c)) :
    TransitiveCode c ↔ TransitiveColumns (Set.range c) := by
  classical
  constructor
  · intro h
    let H := MulAction.stabilizer (A ≃ₗ[Bit] A) (Set.range c)
    let i₀ : I := Classical.choice inferInstance
    refine ⟨H, c i₀, Set.ext (fun y => ?_)⟩
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨e, he, hej⟩ := h i₀ j
      obtain ⟨g, hg⟩ := codePermutation_lift c c hr hr e he
      have hgH : g ∈ H := MulAction.mem_stabilizer_iff.mpr (linear_range_eq c c e g hg)
      exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, by simpa [hej] using hg i₀⟩
    · intro hy
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      have hg := MulAction.mem_stabilizer_iff.mp g.property
      exact hg ▸ Set.smul_mem_smul_set (a := g.val) (Set.mem_range_self i₀)
  · rintro ⟨H, x, hs⟩ i j
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (hs ▸ Set.mem_range_self (f := c) i)
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp (hs ▸ Set.mem_range_self (f := c) j)
    let g : H := b * a⁻¹
    have hg : g.val • Set.range c = Set.range c := by
      rw [hs]
      exact MulAction.smul_orbit g x
    obtain ⟨e, he⟩ := linear_range_permutation c c hc hc g.val hg
    refine ⟨e, codePermutation_of_linear c c e g.val he, hc ?_⟩
    rw [← he i]
    change g • c i = c j
    rw [← ha, ← hb]
    simp [g, mul_smul]

end CodeOrbits

/-- The counted quotient has precisely the ordinary permutation-equivalence relation. -/
theorem bent_class_eq_iff (m ell : ℕ) (hm : m ≠ 0)
    (F H : Space (2 * m) → Space ell) (hF : Bent F) (hH : Bent H) :
    Quotient.mk (MulAction.orbitRel
      (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) (Set (Ambient (2 * m) ell))) (columns F) =
    Quotient.mk (MulAction.orbitRel
      (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) (Set (Ambient (2 * m) ell))) (columns H) ↔
    ∃ e, CodePermutation (column F) (column H) e := by
  have hv : 1 < Fintype.card (Space (2 * m)) := by simp [Space, Bit, hm]
  exact column_class_eq_iff _ _ (column_injective _) (column_injective _)
    (bent_evaluation_injective F hF hv) (bent_evaluation_injective H hH hv)

/-- The transitive classes in the bound are exactly those with transitive code automorphisms. -/
theorem bent_transitive_iff (m ell : ℕ) (hm : m ≠ 0)
    (F : Space (2 * m) → Space ell) (hF : Bent F) :
    TransitiveCode (column F) ↔ TransitiveColumns (columns F) := by
  apply transitiveCode_iff _ (column_injective _)
  exact bent_evaluation_injective F hF (by simp [Space, Bit, hm])

/-- Classes admitting a two-transitive coordinate automorphism group. -/
def twoTransitiveClasses (m ell : ℕ) :
    Finset (Quotient (MulAction.orbitRel
      (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell) (Set (Ambient (2 * m) ell)))) := by
  classical
  exact classImage
    (Ambient (2 * m) ell ≃ₗ[Bit] Ambient (2 * m) ell)
    ((configurations m ell).filter (fun s => ∃ F : Space (2 * m) → Space ell,
      Bent F ∧ s = columns F ∧ TwoTransitiveCode (column F)))

theorem twoTransitiveClasses_subset (m ell : ℕ) (hm : m ≠ 0) :
    twoTransitiveClasses m ell ⊆ transitiveClasses m ell := by
  classical
  let : Nontrivial (Space (2 * m)) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simp [Space, Bit, hm])
  apply classImage_mono
  intro s hs
  obtain ⟨hs, F, hF, rfl, ht⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hs,
    (bent_transitive_iff m ell hm F hF).mp (twoTransitive_transitive _ ht)⟩

/-- Ding–Munemasa–Tonchev Conjecture 17: exponential growth and asymptotically no two-transitivity. -/
theorem conjecture17 (ell : ℕ) (hell : 1 ≤ ell) :
    (∀ᶠ m : ℕ in Filter.atTop, 2 ^ m ≤ (codeClasses m ell).card) ∧
    Filter.Tendsto (fun m => ((twoTransitiveClasses m ell).card : ℝ) / (codeClasses m ell).card)
      Filter.atTop (nhds 0) := by
  refine ⟨exponentially_many_codes ell hell, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (almost_all_nontransitive ell hell) (Filter.Eventually.of_forall (fun m => by positivity))
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (twoTransitiveClasses_subset m ell (by omega))

section Weights
variable {I V W : Type*} [Fintype I]
    [AddCommGroup V] [Module Bit V] [Fintype V] [AddCommGroup W] [Module Bit W]

/-- Binary Hamming weight. -/
def weight (w : I → Bit) : ℕ := by classical exact (Finset.univ.filter (fun i => w i = 1)).card

theorem sign_sum_weight (w : I → Bit) :
    (∑ i, sign (w i)) = (Fintype.card I : ℝ) - 2 * weight w := by
  classical
  have he (b : Bit) : sign b = 1 - 2 * (if b = 1 then (1 : ℝ) else 0) := by
    rcases bit_cases b with rfl | rfl <;> norm_num [sign]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_boole]
  rfl

def graphWord (F : V → W) (c : Bit) (a : V →ₗ[Bit] Bit) (μ : W →ₗ[Bit] Bit) : V → Bit :=
  fun x => c + a x + μ (F x)

def graphFunctional (c : Bit) (a : V →ₗ[Bit] Bit) (μ : W →ₗ[Bit] Bit) :
    (Bit × (V × W)) →ₗ[Bit] Bit :=
  (LinearMap.fst Bit Bit (V × W)).smulRight c +
    a.comp ((LinearMap.fst Bit V W).comp (LinearMap.snd Bit Bit (V × W))) +
    μ.comp ((LinearMap.snd Bit V W).comp (LinearMap.snd Bit Bit (V × W)))

omit [Fintype V] in
theorem graphWord_mem (F : V → W) (c : Bit) (a : V →ₗ[Bit] Bit) (μ : W →ₗ[Bit] Bit) :
    graphWord F c a μ ∈ linearCode (column F) := by
  refine ⟨graphFunctional c a μ, ?_⟩
  ext x
  simp [evaluation, graphFunctional, graphWord, column]

omit [Fintype V] in
/-- The row-code definition agrees with adjoining the component truth tables to RM(1,n). -/
theorem mem_code_iff (F : V → W) (w : V → Bit) :
    w ∈ linearCode (column F) ↔ ∃ c a μ, w = graphWord F c a μ := by
  constructor
  · rintro ⟨φ, rfl⟩
    let a : V →ₗ[Bit] Bit := φ.comp
      ((LinearMap.inr Bit Bit (V × W)).comp (LinearMap.inl Bit V W))
    let μ : W →ₗ[Bit] Bit := φ.comp
      ((LinearMap.inr Bit Bit (V × W)).comp (LinearMap.inr Bit V W))
    refine ⟨φ (1, 0, 0), a, μ, ?_⟩
    funext x
    change φ (1, x, F x) = φ (1, 0, 0) + a x + μ (F x)
    have he : ((1 : Bit), x, F x) = ((1, 0, 0) + (0, x, 0)) + (0, 0, F x) := by simp
    rw [he, map_add, map_add]
    rfl
  · rintro ⟨c, a, μ, rfl⟩
    exact graphWord_mem F c a μ

theorem graphWord_sign_sum (F : V → W) (c : Bit) (a : V →ₗ[Bit] Bit) (μ : W →ₗ[Bit] Bit) :
    (∑ x, sign (graphWord F c a μ x)) = sign c * walsh F μ a := by
  simp only [graphWord, walsh, sign_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Weights

def minimumWeight (m : ℕ) := 2 ^ (2 * m - 1) - 2 ^ (m - 1)

theorem minimumWeight_identity (m : ℕ) (hm : m ≠ 0) :
    (2 : ℝ) ^ (2 * m) - 2 * minimumWeight m = 2 ^ m := by
  have he₁ : (2 : ℝ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    conv_lhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ]
    ring
  have he₂ : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    ring
  have hle : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [minimumWeight, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat]
  linarith

theorem minimumWeight_pos (m : ℕ) (hm : m ≠ 0) : 0 < minimumWeight m := by
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- Every nonzero codeword meets the claimed minimum-distance bound. -/
theorem bent_weight_lower (m ell : ℕ) (hm : m ≠ 0)
    (F : Space (2 * m) → Space ell) (hF : Bent F)
    (w : Space (2 * m) → Bit) (hw : w ∈ linearCode (column F)) (hw0 : w ≠ 0) :
    minimumWeight m ≤ weight w := by
  obtain ⟨c, a, μ, rfl⟩ := (mem_code_iff F w).mp hw
  have hs := sign_sum_weight (graphWord F c a μ)
  rw [graphWord_sign_sum] at hs
  have hcard : Fintype.card (Space (2 * m)) = 2 ^ (2 * m) := by simp [Space, Bit]
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at hs
  have hd := minimumWeight_identity m hm
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hsbound : sign c * walsh F μ a ≤ (2 : ℝ) ^ m := by
    by_cases hμ : μ = 0
    · subst μ
      have he : walsh F 0 a = if a = 0 then (Fintype.card (Space (2 * m)) : ℝ) else 0 := by
        simpa [walsh] using linear_character_sum a
      rw [he]
      split_ifs with ha
      · subst a
        rcases bit_cases c with rfl | rfl
        · exact False.elim (hw0 (by ext x; simp [graphWord]))
        · rw [sign_one, neg_one_mul]
          have hn : (0 : ℝ) ≤ Fintype.card (Space (2 * m)) := by positivity
          linarith
      · simp
    · have hb := hF μ hμ a
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ) ^ (2 * m) = (2 ^ m) ^ 2 by ring] at hb
      have he : (sign c * walsh F μ a) ^ 2 = ((2 : ℝ) ^ m) ^ 2 := by
        rw [mul_pow, sign_sq, one_mul, hb]
      nlinarith [sq_nonneg (sign c * walsh F μ a - (2 : ℝ) ^ m)]
  have hr : (minimumWeight m : ℝ) ≤ weight (graphWord F c a μ) := by linarith
  exact_mod_cast hr

/-- A minimum-weight word exists; the distance bound is attained. -/
theorem bent_weight_attained (m ell : ℕ) (hm : m ≠ 0) (hell : 1 ≤ ell)
    (F : Space (2 * m) → Space ell) (hF : Bent F) :
    ∃ w ∈ linearCode (column F), w ≠ 0 ∧ weight w = minimumWeight m := by
  classical
  let μ : Space ell →ₗ[Bit] Bit := LinearMap.proj ⟨0, by omega⟩
  have hμ : μ ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (fun _ => 1)
    change (1 : Bit) = 0 at he
    exact one_ne_zero he
  have hcard : Fintype.card (Space (2 * m)) = 2 ^ (2 * m) := by simp [Space, Bit]
  have hb := hF μ hμ 0
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ) ^ (2 * m) = (2 ^ m) ^ 2 by ring] at hb
  have hex : ∃ c : Bit, sign c * walsh F μ 0 = (2 : ℝ) ^ m := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with h | h
    · exact ⟨0, by rw [sign_zero, one_mul, h]⟩
    · exact ⟨1, by rw [sign_one, h]; ring⟩
  obtain ⟨c, hc⟩ := hex
  let w := graphWord F c 0 μ
  have hw : weight w = minimumWeight m := by
    have hs := sign_sum_weight w
    rw [graphWord_sign_sum, hc, hcard, Nat.cast_pow, Nat.cast_ofNat] at hs
    have hd := minimumWeight_identity m hm
    have he : (weight w : ℝ) = minimumWeight m := by linarith
    exact_mod_cast he
  refine ⟨w, graphWord_mem F c 0 μ, ?_, hw⟩
  intro hz
  have hp := minimumWeight_pos m hm
  have he : weight w = 0 := by simp [hz, weight]
  omega

/-- Complete length, dimension, and minimum-distance parameters of every code being counted. -/
theorem bent_code_parameters (m ell : ℕ) (hm : m ≠ 0) (hell : 1 ≤ ell)
    (F : Space (2 * m) → Space ell) (hF : Bent F) :
    Fintype.card (Space (2 * m)) = 2 ^ (2 * m) ∧
    Module.finrank Bit (linearCode (column F)) = 2 * m + ell + 1 ∧
    (∀ w ∈ linearCode (column F), w ≠ 0 → 2 ^ (2 * m - 1) - 2 ^ (m - 1) ≤ weight w) ∧
    (∃ w ∈ linearCode (column F), w ≠ 0 ∧ weight w = 2 ^ (2 * m - 1) - 2 ^ (m - 1)) :=
  ⟨by simp [Space, Bit], bent_code_dimension m ell hm F hF,
    fun w hw hw0 => bent_weight_lower m ell hm F hF w hw hw0,
    bent_weight_attained m ell hm hell F hF⟩

end
end DMT17
