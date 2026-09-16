import Mathlib

set_option maxHeartbeats 800000

/-!
Bent concatenations from affine rearrangements of one seed.
All auxiliary results are proved here; only Mathlib is imported.
-/

namespace BentFunctions

abbrev Bit := ZMod 2

@[simp] theorem bit_two : (2 : Bit) = 0 := rfl
@[simp] theorem bit_four : (4 : Bit) = 0 := rfl
@[simp] theorem bit_one_add_one : (1 : Bit) + 1 = 0 := rfl

variable {V : Type*} [AddCommGroup V] [Module Bit V]

theorem twice (v : V) : v + v = 0 := by
  have h : (2 : Bit) • v = 0 := by rw [bit_two, zero_smul]
  simpa only [two_smul] using h

def second (f : V → Bit) (a b z : V) : Bit :=
  f z + f (z + a) + f (z + b) + f (z + a + b)

def IsM (f : V → Bit) (W : Submodule Bit V) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, ∀ z, second f a b z = 0

def HasIndex [FiniteDimensional Bit V] (f : V → Bit) (k : ℕ) : Prop :=
  (∀ W, IsM f W → Module.finrank Bit W ≤ k) ∧
    ∃ W, IsM f W ∧ Module.finrank Bit W = k

abbrev Extension (V : Type*) := V × (Bit × Bit)

def selector (g h : V → Bit) (z : Extension V) : Bit :=
  (1 + z.2.2) * g z.1 + z.2.2 * h z.1 + z.2.1 * z.2.2

def projection : Extension V →ₗ[Bit] V := LinearMap.fst Bit V (Bit × Bit)

def lastCoordinate : Extension V →ₗ[Bit] Bit :=
  (LinearMap.snd Bit Bit Bit).comp (LinearMap.snd Bit V (Bit × Bit))

def middleDirection : Extension V := (0, (1, 0))

def lift (K : Submodule Bit V) : Submodule Bit (Extension V) :=
  let e : V × Bit →ₗ[Bit] Extension V :=
    { toFun := fun z => (z.1, (z.2, 0))
      map_add' := by intros; rfl
      map_smul' := by intros; ext <;> simp }
  (K.prod (⊤ : Submodule Bit Bit)).map e
@[simp] theorem mem_lift (K : Submodule Bit V) (z : Extension V) :
    z ∈ lift K ↔ z.1 ∈ K ∧ z.2.2 = 0 := by
  simp only [lift, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1, rfl⟩
  · rintro ⟨ha, ht⟩
    exact ⟨(z.1, z.2.1), ⟨ha, trivial⟩, by ext <;> simp_all⟩

omit [Module Bit V] in
theorem selector_second (g h : V → Bit) (a b z : V) (r s u t : Bit) :
    second (selector g h) (a, (r, 0)) (b, (s, 0)) (z, (u, t)) =
      (1 + t) * second g a b z + t * second h a b z := by
  simp only [second, selector, Prod.fst_add, Prod.snd_add, add_zero]
  ring_nf
  simp

omit [Module Bit V] in
theorem selector_middle (g h : V → Bit) (a z : Extension V) :
    second (selector g h) middleDirection a z = a.2.2 := by
  simp only [second, selector, middleDirection, Prod.fst_add, Prod.snd_add,
    add_zero]
  ring_nf
  simp

theorem lift_isM (g h : V → Bit) (K : Submodule Bit V)
    (hg : IsM g K) (hh : IsM h K) : IsM (selector g h) (lift K) := by
  rintro ⟨a, r, t⟩ ha ⟨b, s, v⟩ hb ⟨z, u, w⟩
  obtain ⟨ha, rfl⟩ := (mem_lift K _).mp ha
  obtain ⟨hb, rfl⟩ := (mem_lift K _).mp hb
  rw [selector_second, hg a ha b hb z, hh a ha b hb z]
  simp

theorem projected_isM (g h : V → Bit) (W : Submodule Bit (Extension V))
    (hW : IsM (selector g h) W) (ht : W ≤ LinearMap.ker lastCoordinate) :
    IsM g (W.map projection) ∧ IsM h (W.map projection) := by
  have common (f : V → Bit) (t : Bit)
      (he : ∀ a b z r s, second (selector g h) (a, (r, 0)) (b, (s, 0))
        (z, (0, t)) = second f a b z) : IsM f (W.map projection) := by
    rintro a ⟨⟨a', r, t'⟩, ha, rfl⟩ b ⟨⟨b', s, v⟩, hb, rfl⟩ z
    have hat : t' = 0 := ht ha
    have hbt : v = 0 := ht hb
    subst t'
    subst v
    simpa only [he, projection, LinearMap.fst_apply] using hW _ ha _ hb (z, (0, t))
  constructor
  · apply common g 0
    intros
    simp [selector_second]
  · apply common h 1
    intros
    simp [selector_second]

section Dimension

variable [FiniteDimensional Bit V]

theorem lift_finrank (K : Submodule Bit V) :
    Module.finrank Bit (lift K) = Module.finrank Bit K + 1 := by
  let e : lift K ≃ₗ[Bit] (K × Bit) :=
    { toFun := fun z => (⟨z.1.1, ((mem_lift K z).mp z.2).1⟩, z.1.2.1)
      invFun := fun z => ⟨(z.1.1, (z.2, 0)), (mem_lift K _).mpr ⟨z.1.2, rfl⟩⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have ht := ((mem_lift K z).mp z.2).2
        ext <;> simp_all
      right_inv := by intro z; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  simpa using e.finrank_eq

theorem horizontal_bound (W : Submodule Bit (Extension V))
    (ht : W ≤ LinearMap.ker lastCoordinate) :
    Module.finrank Bit W ≤ Module.finrank Bit (W.map projection) + 1 := by
  let e : W →ₗ[Bit] (W.map projection × Bit) :=
    { toFun := fun z => (⟨z.1.1, ⟨z, z.2, rfl⟩⟩, z.1.2.1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have hfirst := congrArg (fun z : W.map projection × Bit => z.1.1) hab
    have hmiddle := congrArg (fun z : W.map projection × Bit => z.2) hab
    have ha : a.1.2.2 = 0 := ht a.2
    have hb : b.1.2.2 = 0 := ht b.2
    exact Prod.ext hfirst (Prod.ext hmiddle (ha.trans hb.symm))
  simpa using LinearMap.finrank_le_finrank_of_injective hi

omit [FiniteDimensional Bit V] in
theorem horizontal_injective (W : Submodule Bit (Extension V))
    (ht : W ≤ LinearMap.ker lastCoordinate) (hu : middleDirection ∉ W) :
    Function.Injective (projection.comp W.subtype) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro a ha
  have hx : a.1.1 = 0 := ha
  have hz : a.1.2.2 = 0 := ht a.2
  have hb : a.1.2.1 = 0 ∨ a.1.2.1 = 1 :=
    (by decide : ∀ t : Bit, t = 0 ∨ t = 1) _
  rcases hb with hb | hb
  · change a = 0
    apply Subtype.ext
    exact Prod.ext hx (Prod.ext hb hz)
  · exfalso
    apply hu
    have he : a.1 = middleDirection := Prod.ext hx (Prod.ext hb hz)
    exact he ▸ a.2

theorem projection_finrank (W : Submodule Bit (Extension V))
    (hi : Function.Injective (projection.comp W.subtype)) :
    Module.finrank Bit (W.map projection) = Module.finrank Bit W := by
  have hr : (projection.comp W.subtype).range = W.map projection := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h := (projection.comp W.subtype).finrank_range_add_finrank_ker
  rw [hr, LinearMap.ker_eq_bot.mpr hi] at h
  simpa using h

theorem selector_index (g h : V → Bit) (k : ℕ)
    (upper : ∀ K, IsM g K → IsM h K → Module.finrank Bit K ≤ k)
    (attained : ∃ K, IsM g K ∧ IsM h K ∧ Module.finrank Bit K = k) :
    HasIndex (selector g h) (k + 1) := by
  constructor
  · intro W hW
    by_cases ht : W ≤ LinearMap.ker lastCoordinate
    · have hc := projected_isM g h W hW ht
      exact (horizontal_bound W ht).trans (Nat.add_le_add_right (upper _ hc.1 hc.2) 1)
    · let t : W →ₗ[Bit] Bit := lastCoordinate.comp W.subtype
      let W₀ : Submodule Bit (Extension V) := t.ker.map W.subtype
      have hle : W₀ ≤ W := by
        rintro z ⟨a, ha, rfl⟩
        exact a.2
      have hzero : W₀ ≤ LinearMap.ker lastCoordinate := by
        rintro z ⟨a, ha, rfl⟩
        exact ha
      have hsub : IsM (selector g h) W₀ := fun a ha b hb z => hW a (hle ha) b (hle hb) z
      have hu : middleDirection ∉ W := by
        intro hu
        apply ht
        intro a ha
        change a.2.2 = 0
        rw [← selector_middle g h a 0]
        exact hW _ hu _ ha 0
      have hinj := horizontal_injective W₀ hzero (fun h => hu (hle h))
      have hc := projected_isM g h W₀ hsub hzero
      have hk := upper _ hc.1 hc.2
      rw [projection_finrank W₀ hinj] at hk
      have hd : Module.finrank Bit W₀ = Module.finrank Bit t.ker :=
        Submodule.finrank_map_subtype_eq W t.ker
      have hr := t.finrank_range_add_finrank_ker
      have hb : Module.finrank Bit t.range ≤ 1 := by simpa using t.range.finrank_le
      omega
  · obtain ⟨K, hg, hh, hk⟩ := attained
    exact ⟨lift K, lift_isM g h K hg hh, by rw [lift_finrank, hk]⟩

end Dimension

/-- Extended affine equivalence, including affine output terms. -/
def EAEquivalent (f g : V → Bit) : Prop :=
  ∃ (L : V ≃ₗ[Bit] V) (c : V) (ℓ : V →ₗ[Bit] Bit) (d : Bit),
    ∀ z, g z = f (L z + c) + ℓ z + d

theorem second_affine {X : Type*} [AddCommGroup X] [Module Bit X]
    (f : X → Bit) (L : V ≃ₗ[Bit] X) (c : X)
    (ℓ : V →ₗ[Bit] Bit) (d : Bit) (a b z : V) :
    second (fun z => f (L z + c) + ℓ z + d) a b z =
      second f (L a) (L b) (L z + c) := by
  simp only [second, map_add]
  have h₁ : L z + L a + c = L z + c + L a := by abel
  have h₂ : L z + L b + c = L z + c + L b := by abel
  have h₃ : L z + L a + L b + c = L z + c + L a + L b := by abel
  rw [h₁, h₂, h₃]
  ring_nf
  simp

theorem affine_isM_iff {X : Type*} [AddCommGroup X] [Module Bit X]
    (f : X → Bit) (L : V ≃ₗ[Bit] X) (c : X)
    (ℓ : V →ₗ[Bit] Bit) (d : Bit) (W : Submodule Bit V) :
    IsM (fun z => f (L z + c) + ℓ z + d) W ↔ IsM f (W.map L.toLinearMap) := by
  constructor
  · intro h a ha b hb z
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have hz := h a ha b hb (L.symm (z - c))
    rw [second_affine f L c ℓ d] at hz
    simpa using hz
  · intro h a ha b hb z
    rw [second_affine f L c ℓ d]
    exact h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _

theorem ea_index [FiniteDimensional Bit V] (f g : V → Bit) (k : ℕ)
    (hfg : EAEquivalent f g) (hf : HasIndex f k) : HasIndex g k := by
  obtain ⟨L, c, ℓ, d, he⟩ := hfg
  have hg : g = fun z => f (L z + c) + ℓ z + d := funext he
  rw [hg]
  constructor
  · intro W hW
    have h := hf.1 (W.map L.toLinearMap) ((affine_isM_iff f L c ℓ d W).mp hW)
    simpa only [L.finrank_map_eq] using h
  · obtain ⟨K, hK, hk⟩ := hf.2
    let W := K.map L.symm.toLinearMap
    have heq : W.map L.toLinearMap = K := by
      ext z
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        simpa using hv
      · intro hz
        exact ⟨L.symm z, ⟨z, hz, rfl⟩, L.apply_symm_apply z⟩
    refine ⟨W, (affine_isM_iff f L c ℓ d W).mpr ?_, ?_⟩
    · simpa only [heq] using hK
    · simpa only [W, L.symm.finrank_map_eq] using hk

theorem index_unique [FiniteDimensional Bit V] {f : V → Bit} {k l : ℕ}
    (hk : HasIndex f k) (hl : HasIndex f l) : k = l := by
  obtain ⟨K, hK, hkd⟩ := hk.2
  obtain ⟨L, hL, hld⟩ := hl.2
  have h₁ := hk.1 L hL
  have h₂ := hl.1 K hK
  omega

theorem different_indices [FiniteDimensional Bit V] {f g : V → Bit} {k l : ℕ}
    (hf : HasIndex f k) (hg : HasIndex g l) (hne : k ≠ l) : ¬ EAEquivalent f g := by
  intro he
  exact hne (index_unique (ea_index f g k he hf) hg)

/-- All M-subspaces of dimension at least two lie in the distinguished subspace. -/
def Rigid [FiniteDimensional Bit V] (g : V → Bit) (U : Submodule Bit V) : Prop :=
  IsM g U ∧ ∀ W, IsM g W → 2 ≤ Module.finrank Bit W → W ≤ U

theorem isM_mono {f : V → Bit} {U W : Submodule Bit V}
    (h : W ≤ U) (hu : IsM f U) : IsM f W :=
  fun a ha b hb z => hu a (h ha) b (h hb) z

/-- The exact index formula whenever the intersection is nonzero. -/
theorem affine_selector_index [FiniteDimensional Bit V] (g : V → Bit)
    (U : Submodule Bit V) (L : V ≃ₗ[Bit] V) (c : V) (hg : Rigid g U)
    (hpos : 0 < Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap)) :
    HasIndex (selector g (fun z => g (L z + c)))
      (Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap) + 1) := by
  have transport (W : Submodule Bit V) :
      IsM (fun z => g (L z + c)) W ↔ IsM g (W.map L.toLinearMap) := by
    simpa only [LinearMap.zero_apply, add_zero] using affine_isM_iff g L c 0 0 W
  apply selector_index
  · intro K hK hKL
    by_cases hd : 2 ≤ Module.finrank Bit K
    · apply Submodule.finrank_mono
      apply le_inf (hg.2 K hK hd)
      have him : K.map L.toLinearMap ≤ U := hg.2 _ ((transport K).mp hKL)
        (by simpa only [L.finrank_map_eq] using hd)
      intro z hz
      exact him ⟨z, hz, rfl⟩
    · omega
  · refine ⟨U ⊓ U.comap L.toLinearMap, isM_mono inf_le_left hg.1, ?_, rfl⟩
    apply (transport _).mpr
    apply isM_mono _ hg.1
    rintro z ⟨v, hv, rfl⟩
    exact hv.2

theorem bit_cases (t : Bit) : t = 0 ∨ t = 1 :=
  (by decide : ∀ t : Bit, t = 0 ∨ t = 1) t

theorem line_isM (f : V → Bit) (v : V) : IsM f (Submodule.span Bit {v}) := by
  intro a ha b hb z
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rcases bit_cases r with rfl | rfl <;> rcases bit_cases s with rfl | rfl <;>
    simp only [zero_smul, one_smul, second, add_zero, add_assoc, twice]
  all_goals
    first
    | simp [twice]
    | calc
        _ = (f z + f z) + (f (z + v) + f (z + v)) := by abel
        _ = 0 := by simp [twice]

/-- The affine formula includes the case of a zero-dimensional intersection. -/
theorem affine_selector_index_full [FiniteDimensional Bit V] [Nontrivial V]
    (g : V → Bit) (U : Submodule Bit V) (L : V ≃ₗ[Bit] V) (c : V)
    (hg : Rigid g U) :
    HasIndex (selector g (fun z => g (L z + c)))
      (max 1 (Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap)) + 1) := by
  by_cases hp : 0 < Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap)
  · simpa only [max_eq_right (Nat.succ_le_of_lt hp)] using affine_selector_index g U L c hg hp
  · have hz : Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap) = 0 := by omega
    rw [hz, max_eq_left (by omega : 0 ≤ 1)]
    apply selector_index
    · intro K hK hKL
      by_contra hd
      have hd : 2 ≤ Module.finrank Bit K := by omega
      have him : IsM g (K.map L.toLinearMap) := by
        apply (affine_isM_iff g L c 0 0 K).mp
        simpa using hKL
      have hle : K ≤ U ⊓ U.comap L.toLinearMap := by
        refine le_inf (hg.2 K hK hd) ?_
        have h := hg.2 _ him (by simpa only [L.finrank_map_eq] using hd)
        intro z hz
        exact h ⟨z, hz, rfl⟩
      have h := Submodule.finrank_mono hle
      omega
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨Submodule.span Bit {v}, line_isM g v,
        line_isM (fun z => g (L z + c)) v, finrank_span_singleton hv⟩

open scoped BigOperators

def sign (t : Bit) : ℤ := if t = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := rfl
@[simp] theorem sign_one : sign 1 = -1 := rfl

theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide

@[simp] theorem sign_sq (a : Bit) : sign a ^ 2 = 1 := by
  rcases bit_cases a with rfl | rfl <;> decide

noncomputable def walsh [Fintype V] (f : V → Bit) (a : V →ₗ[Bit] Bit) : ℤ :=
  ∑ z, sign (f z + a z)

/-- Bentness in the usual, unnormalized Walsh convention. -/
def Bent [Fintype V] (f : V → Bit) : Prop :=
  ∀ a : V →ₗ[Bit] Bit, walsh f a ^ 2 = Fintype.card V

theorem sum_bit (f : Bit → ℤ) : ∑ t, f t = f 0 + f 1 := by
  have h : (Finset.univ : Finset Bit) = {0, 1} := by decide
  rw [h]
  simp

def baseEmbedding : V →ₗ[Bit] Extension V :=
  { toFun := fun z => (z, (0, 0))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

theorem selector_walsh [Fintype V] (g h : V → Bit) (a : Extension V →ₗ[Bit] Bit) :
    walsh (selector g h) a =
      if a middleDirection = 0 then 2 * walsh g (a.comp baseEmbedding)
      else 2 * sign (a (0, (0, 1))) * walsh h (a.comp baseEmbedding) := by
  have ha0 : a (0, (0, 0)) = 0 := a.map_zero
  have hz (z : V) (u t : Bit) :
      a (z, (u, t)) = a (z, (0, 0)) + a (0, (u, 0)) + a (0, (0, t)) := by
    rw [← map_add, ← map_add]
    congr 1
    ext <;> simp
  have hu (z : V) : a (z, (1, 0)) = a (z, (0, 0)) + a (0, (1, 0)) := by
    simpa only [ha0, add_zero] using hz z 1 0
  have ht (z : V) : a (z, (0, 1)) = a (z, (0, 0)) + a (0, (0, 1)) := by
    simpa only [ha0, add_zero] using hz z 0 1
  have hut (z : V) : a (z, (1, 1)) =
      a (z, (0, 0)) + a (0, (1, 0)) + a (0, (0, 1)) := hz z 1 1
  simp only [walsh, Fintype.sum_prod_type, sum_bit]
  simp only [selector, mul_zero, mul_one, zero_mul, one_mul, add_zero,
    zero_add, bit_one_add_one]
  conv_lhs =>
    arg 2
    ext z
    rw [hu z, ht z, hut z]
  simp only [sign_add]
  have he (z : V) : baseEmbedding z = (z, (0, 0)) := rfl
  rcases bit_cases (a middleDirection) with ha | ha <;>
    simp only [middleDirection] at ha
  · simp only [middleDirection, ha, sign_zero, sign_one, mul_one, ite_true,
      LinearMap.comp_apply, he]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  · simp only [middleDirection, ha, sign_one, one_ne_zero, ite_false,
      LinearMap.comp_apply, he]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
theorem selector_bent [Fintype V] (g h : V → Bit) (hg : Bent g) (hh : Bent h) :
    Bent (selector g h) := by
  intro a
  rw [selector_walsh]
  split_ifs
  · rw [mul_pow, hg]
    simp [Extension, Fintype.card_prod]
    ring
  · rw [mul_pow, mul_pow, sign_sq, hh]
    simp [Extension, Fintype.card_prod]
    ring

theorem affine_bent [Fintype V] (f : V → Bit) (hf : Bent f)
    (L : V ≃ₗ[Bit] V) (c : V) : Bent (fun z => f (L z + c)) := by
  intro a
  let b := a.comp L.symm.toLinearMap
  let e : V ≃ V := L.toEquiv.trans (Equiv.addRight c)
  have hs := Equiv.sum_comp e (fun z => sign (f z + b z))
  change (∑ z, sign (f (L z + c) + a (L.symm (L z + c)))) = walsh f b at hs
  have hc : walsh f b = walsh (fun z => f (L z + c)) a * sign (a (L.symm c)) := by
    rw [← hs, walsh, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    simp only [map_add, L.symm_apply_apply, sign_add]
    ring
  have h := congrArg (fun x : ℤ => x ^ 2) hc
  rw [mul_pow, sign_sq, mul_one, hf b] at h
  exact h.symm

/-- Any two affine rearrangements with different intersection indices give
EA-inequivalent bent concatenations of the same seed. -/
theorem affine_orbit_pair [Fintype V] [FiniteDimensional Bit V] [Nontrivial V]
    (g : V → Bit) (U : Submodule Bit V) (hb : Bent g) (hr : Rigid g U)
    (A B : V ≃ₗ[Bit] V) (c d : V)
    (hne : max 1 (Module.finrank Bit ↥(U ⊓ U.comap A.toLinearMap)) ≠
      max 1 (Module.finrank Bit ↥(U ⊓ U.comap B.toLinearMap))) :
    Bent (selector g (fun z => g (A z + c))) ∧
    Bent (selector g (fun z => g (B z + d))) ∧
    ¬ EAEquivalent (selector g (fun z => g (A z + c)))
      (selector g (fun z => g (B z + d))) := by
  refine ⟨selector_bent g _ hb (affine_bent g hb A c),
    selector_bent g _ hb (affine_bent g hb B d), ?_⟩
  apply different_indices (affine_selector_index_full g U A c hr)
    (affine_selector_index_full g U B d hr)
  omega

abbrev Triple := Bit × (Bit × Bit)
abbrev Six := Triple × Triple

/-- The trace-cubic seed over the eight-element field, expanded in binary coordinates. -/
def seed (z : Six) : Bit :=
  z.1.1 * (z.2.1 + z.2.2.1 + z.2.2.2 + z.2.2.1 * z.2.2.2) +
  z.1.2.1 * (z.2.2.2 + z.2.1 * z.2.2.1) +
  z.1.2.2 * (z.2.2.1 + z.2.1 * z.2.2.1 + z.2.1 * z.2.2.2)

def horizontal : Submodule Bit Six :=
  LinearMap.ker (LinearMap.snd Bit Triple Triple)

def testDirection : Fin 7 → Six :=
  ![0, ((1, (0, 0)), 0), ((0, (1, 0)), 0), ((0, (0, 1)), 0),
    (0, (1, (0, 0))), (0, (0, (1, 0))), (0, (0, (0, 1)))]

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_pair_certificate : ∀ a b : Six,
    (∀ z : Six, second seed a b z = 0) →
      a = 0 ∨ b = 0 ∨ a = b ∨ (a.2 = 0 ∧ b.2 = 0) := by
  have hc : ∀ a b : Six, a = 0 ∨ b = 0 ∨ a = b ∨ (a.2 = 0 ∧ b.2 = 0) ∨
      ∃ i : Fin 7, second seed a b (testDirection i) ≠ 0 := by
    rintro ⟨⟨a₀, a₁, a₂⟩, ⟨a₃, a₄, a₅⟩⟩
    fin_cases a₀ <;> fin_cases a₁ <;> fin_cases a₂ <;>
      fin_cases a₃ <;> fin_cases a₄ <;> fin_cases a₅ <;> decide +kernel
  intro a b hab
  rcases hc a b with ha | hb | he | hh | ⟨i, hi⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr hh))
  · exact (hi (hab _)).elim
theorem seed_rigid : Rigid seed horizontal := by
  constructor
  · rintro ⟨a, y⟩ ha ⟨b, w⟩ hb ⟨x, z⟩
    change y = 0 at ha
    change w = 0 at hb
    subst y
    subst w
    simp only [second, seed, Prod.fst_add, Prod.snd_add, add_zero]
    ring_nf
    simp
  · intro W hW hd a ha
    change a.2 = 0
    by_contra hn
    have ha0 : a ≠ 0 := by intro h; exact hn (congrArg Prod.snd h)
    have hle : W ≤ Submodule.span Bit {a} := by
      intro b hb
      rcases seed_pair_certificate a b (hW a ha b hb) with h | h | h | h
      · exact False.elim (ha0 h)
      · simpa only [h] using (Submodule.zero_mem (Submodule.span Bit {a}))
      · subst b
        exact Submodule.subset_span (Set.mem_singleton a)
      · exact False.elim (hn h.1)
    have h := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha0] at h
    omega

def tripleDot (x y : Triple) : Bit := x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2

def sixDot (x y : Six) : Bit := tripleDot x.1 y.1 + tripleDot x.2 y.2

theorem six_form (a : Six →ₗ[Bit] Bit) : ∃ p : Six, ∀ z, a z = sixDot p z := by
  let e₀ : Six := ((1, (0, 0)), (0, (0, 0)))
  let e₁ : Six := ((0, (1, 0)), (0, (0, 0)))
  let e₂ : Six := ((0, (0, 1)), (0, (0, 0)))
  let e₃ : Six := ((0, (0, 0)), (1, (0, 0)))
  let e₄ : Six := ((0, (0, 0)), (0, (1, 0)))
  let e₅ : Six := ((0, (0, 0)), (0, (0, 1)))
  refine ⟨((a e₀, (a e₁, a e₂)), (a e₃, (a e₄, a e₅))), ?_⟩
  intro z
  have hz : z = z.1.1 • e₀ + z.1.2.1 • e₁ + z.1.2.2 • e₂ +
      z.2.1 • e₃ + z.2.2.1 • e₄ + z.2.2.2 • e₅ := by
    ext <;> simp [e₀, e₁, e₂, e₃, e₄, e₅]
  conv_lhs => rw [hz]
  simp only [map_add, map_smul, smul_eq_mul, sixDot, tripleDot]
  ring

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_spectrum : ∀ p : Six, (∑ z : Six, sign (seed z + sixDot p z)) ^ 2 = 64 := by
  rintro ⟨⟨a₀, a₁, a₂⟩, ⟨a₃, a₄, a₅⟩⟩
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases a₃ <;> fin_cases a₄ <;> fin_cases a₅ <;> decide +kernel

theorem seed_bent : Bent seed := by
  intro a
  obtain ⟨p, hp⟩ := six_form a
  have hc : Fintype.card Six = 64 := by decide
  simpa only [walsh, hp, hc, Nat.cast_ofNat] using seed_spectrum p

/-- Swap the last two coordinate pairs. -/
def swapOne : Six ≃ₗ[Bit] Six :=
  { toFun := fun z => ((z.1.1, (z.2.2.1, z.2.2.2)), (z.2.1, (z.1.2.1, z.1.2.2)))
    invFun := fun z => ((z.1.1, (z.2.2.1, z.2.2.2)), (z.2.1, (z.1.2.1, z.1.2.2)))
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Swap only the last coordinate pair. -/
def swapTwo : Six ≃ₗ[Bit] Six :=
  { toFun := fun z => ((z.1.1, (z.1.2.1, z.2.2.2)), (z.2.1, (z.2.2.1, z.1.2.2)))
    invFun := fun z => ((z.1.1, (z.1.2.1, z.2.2.2)), (z.2.1, (z.2.2.1, z.1.2.2)))
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

theorem intersection_one :
    Module.finrank Bit ↥(horizontal ⊓ horizontal.comap swapOne.toLinearMap) = 1 := by
  let e : ↥(horizontal ⊓ horizontal.comap swapOne.toLinearMap) ≃ₗ[Bit] Bit :=
    { toFun := fun z => z.1.1.1
      invFun := fun x => ⟨((x, (0, 0)), (0, (0, 0))), ⟨rfl, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨⟨x₀, x₁, x₂⟩, ⟨y₀, y₁, y₂⟩⟩, hz⟩
        apply Subtype.ext
        change (y₀, (y₁, y₂)) = (0, (0, 0)) ∧
          (y₀, (x₁, x₂)) = (0, (0, 0)) at hz
        simp only [Prod.mk.injEq] at hz
        simp_all
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  simpa using e.finrank_eq

theorem intersection_two :
    Module.finrank Bit ↥(horizontal ⊓ horizontal.comap swapTwo.toLinearMap) = 2 := by
  let e : ↥(horizontal ⊓ horizontal.comap swapTwo.toLinearMap) ≃ₗ[Bit] (Bit × Bit) :=
    { toFun := fun z => (z.1.1.1, z.1.1.2.1)
      invFun := fun x => ⟨((x.1, (x.2, 0)), (0, (0, 0))), ⟨rfl, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨⟨x₀, x₁, x₂⟩, ⟨y₀, y₁, y₂⟩⟩, hz⟩
        apply Subtype.ext
        change (y₀, (y₁, y₂)) = (0, (0, 0)) ∧
          (y₀, (y₁, x₂)) = (0, (0, 0)) at hz
        simp only [Prod.mk.injEq] at hz
        simp_all
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  simpa using e.finrank_eq

def exampleOne : Extension Six → Bit := selector seed (fun z => seed (swapOne z))
def exampleTwo : Extension Six → Bit := selector seed (fun z => seed (swapTwo z))

theorem example_one_index : HasIndex exampleOne 2 := by
  simpa only [intersection_one, add_zero, Nat.reduceAdd, exampleOne] using
    affine_selector_index seed horizontal swapOne 0 seed_rigid
      (by rw [intersection_one]; omega)

theorem example_two_index : HasIndex exampleTwo 3 := by
  simpa only [intersection_two, add_zero, Nat.reduceAdd, exampleTwo] using
    affine_selector_index seed horizontal swapTwo 0 seed_rigid
      (by rw [intersection_two]; omega)

/-- A concrete pair on eight variables, with no seed hypotheses. -/
theorem explicit_inequivalent_bent_pair :
    Bent exampleOne ∧ Bent exampleTwo ∧ ¬ EAEquivalent exampleOne exampleTwo := by
  refine ⟨?_, ?_, different_indices example_one_index example_two_index (by decide)⟩
  · exact selector_bent seed _ seed_bent
      (by simpa only [add_zero] using affine_bent seed seed_bent swapOne 0)
  · exact selector_bent seed _ seed_bent
      (by simpa only [add_zero] using affine_bent seed seed_bent swapTwo 0)

abbrev Cube (m : ℕ) := Fin m → Bit

def maioranaMcFarland {m : ℕ} (π : Cube m ≃ Cube m) (r : Cube m → Bit)
    (z : Cube m × Cube m) : Bit := dotProduct z.1 (π z.2) + r z.2

/-- The EA closure of the classical Maiorana–McFarland class. -/
def InCompletedMM [FiniteDimensional Bit V] (f : V → Bit) : Prop :=
  ∃ m, Module.finrank Bit V = 2 * m ∧
    ∃ (L : V ≃ₗ[Bit] (Cube m × Cube m)) (c : Cube m × Cube m)
      (π : Cube m ≃ Cube m) (r : Cube m → Bit) (ℓ : V →ₗ[Bit] Bit) (d : Bit),
      ∀ z, f z = maioranaMcFarland π r (L z + c) + ℓ z + d

theorem mm_isM {m : ℕ} (π : Cube m ≃ Cube m) (r : Cube m → Bit) :
    IsM (maioranaMcFarland π r)
      ((⊤ : Submodule Bit (Cube m)).prod (⊥ : Submodule Bit (Cube m))) := by
  rintro ⟨a, y⟩ ha ⟨b, w⟩ hb ⟨x, z⟩
  have hy : y = 0 := ha.2
  have hw : w = 0 := hb.2
  subst y
  subst w
  simp only [second, maioranaMcFarland, Prod.fst_add, Prod.snd_add, add_zero,
    add_dotProduct]
  ring_nf
  simp

theorem completedMM_has_half_subspace [FiniteDimensional Bit V] {f : V → Bit}
    (hf : InCompletedMM f) :
    ∃ W, IsM f W ∧ 2 * Module.finrank Bit W = Module.finrank Bit V := by
  obtain ⟨m, hm, L, c, π, r, ℓ, d, he⟩ := hf
  let U := (⊤ : Submodule Bit (Cube m)).prod (⊥ : Submodule Bit (Cube m))
  let W := U.map L.symm.toLinearMap
  have heq : W.map L.toLinearMap = U := by
    ext z
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      simpa using hv
    · intro hz
      exact ⟨L.symm z, ⟨z, hz, rfl⟩, L.apply_symm_apply z⟩
  refine ⟨W, ?_, ?_⟩
  · have h := (affine_isM_iff (maioranaMcFarland π r) L c ℓ d W).mpr
      (by simpa only [heq] using mm_isM π r)
    have he' : f = fun z => maioranaMcFarland π r (L z + c) + ℓ z + d := funext he
    simpa only [he'] using h
  · let e : U ≃ₗ[Bit] Cube m :=
      { toFun := fun z => z.1.1
        invFun := fun z => ⟨(z, 0), ⟨trivial, rfl⟩⟩
        left_inv := by
          intro z
          apply Subtype.ext
          exact Prod.ext rfl (show (0 : Cube m) = z.1.2 from z.2.2.symm)
        right_inv := by intro z; rfl
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hU : Module.finrank Bit U = m := by simpa [Cube] using e.finrank_eq
    have hd : Module.finrank Bit W = m := by
      simpa only [W, L.symm.finrank_map_eq] using hU
    rw [hd, hm]

theorem outside_completedMM [FiniteDimensional Bit V] {f : V → Bit} {k : ℕ}
    (hf : HasIndex f k) (hk : 2 * k < Module.finrank Bit V) : ¬ InCompletedMM f := by
  intro h
  obtain ⟨W, hW, hd⟩ := completedMM_has_half_subspace h
  have hb := hf.1 W hW
  omega

theorem explicit_open_problem_pair :
    Bent exampleOne ∧ Bent exampleTwo ∧
    ¬ InCompletedMM exampleOne ∧ ¬ InCompletedMM exampleTwo ∧
    ¬ EAEquivalent exampleOne exampleTwo := by
  have hd : Module.finrank Bit (Extension Six) = 8 := by
    simp [Extension, Six, Triple, Bit, Module.finrank_prod]
  exact ⟨explicit_inequivalent_bent_pair.1, explicit_inequivalent_bent_pair.2.1,
    outside_completedMM example_one_index (by rw [hd]; omega),
    outside_completedMM example_two_index (by rw [hd]; omega),
    explicit_inequivalent_bent_pair.2.2⟩

/-- Adding a hyperbolic quadratic pair raises the linearity index by exactly one. -/
theorem quadratic_extension_index [FiniteDimensional Bit V] {f : V → Bit} {k : ℕ}
    (hf : HasIndex f k) : HasIndex (selector f f) (k + 1) := by
  apply selector_index f f k
  · exact fun W hW _ => hf.1 W hW
  · obtain ⟨W, hW, hd⟩ := hf.2
    exact ⟨W, hW, hW, hd⟩

def exchangePairs : Extension (Extension V) ≃ₗ[Bit] Extension (Extension V) :=
  { toFun := fun z => ((z.1.1, z.2), z.1.2)
    invFun := fun z => ((z.1.1, z.2), z.1.2)
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

theorem selector_extension (g h : V → Bit) (z : Extension (Extension V)) :
    selector (selector g g) (selector h h) z =
      selector (selector g h) (selector g h) (exchangePairs z) := by
  simp only [selector, exchangePairs, LinearEquiv.coe_mk]
  ring_nf
  simp; ring

/-- Six seed coordinates followed by n independent quadratic pairs. -/
abbrev Space : ℕ → Type
  | 0 => Six
  | n + 1 => Extension (Space n)

@[reducible] instance spaceGroup : (n : ℕ) → AddCommGroup (Space n)
  | 0 => inferInstanceAs (AddCommGroup Six)
  | n + 1 => letI := spaceGroup n; inferInstanceAs (AddCommGroup (Extension (Space n)))

@[reducible] instance spaceModule : (n : ℕ) → Module Bit (Space n)
  | 0 => inferInstanceAs (Module Bit Six)
  | n + 1 => letI := spaceModule n; inferInstanceAs (Module Bit (Extension (Space n)))

@[reducible] instance spaceFinite : (n : ℕ) → Fintype (Space n)
  | 0 => inferInstanceAs (Fintype Six)
  | n + 1 => letI := spaceFinite n; inferInstanceAs (Fintype (Extension (Space n)))

instance spaceDimension : (n : ℕ) → FiniteDimensional Bit (Space n)
  | 0 => inferInstanceAs (FiniteDimensional Bit Six)
  | n + 1 => letI := spaceDimension n
             inferInstanceAs (FiniteDimensional Bit (Extension (Space n)))

def extendedSeed : (n : ℕ) → Space n → Bit
  | 0 => seed
  | n + 1 => selector (extendedSeed n) (extendedSeed n)

def extendedMap (A : Six ≃ₗ[Bit] Six) : (n : ℕ) → Space n ≃ₗ[Bit] Space n
  | 0 => A
  | n + 1 => (extendedMap A n).prodCongr (LinearEquiv.refl Bit (Bit × Bit))

def orbitFunction (A : Six ≃ₗ[Bit] Six) (n : ℕ) : Space (n + 1) → Bit :=
  selector (extendedSeed n) (fun z => extendedSeed n (extendedMap A n z))

theorem space_finrank (n : ℕ) : Module.finrank Bit (Space n) = 6 + 2 * n := by
  induction n with
  | zero => simp [Space, Six, Triple, Module.finrank_prod]
  | succ n ih =>
    change Module.finrank Bit (Extension (Space n)) = _
    simp only [Extension, Module.finrank_prod, Module.finrank_self, ih]
    omega

theorem extended_seed_bent (n : ℕ) : Bent (extendedSeed n) := by
  induction n with
  | zero => exact seed_bent
  | succ n ih => exact selector_bent _ _ ih ih

theorem orbit_bent (A : Six ≃ₗ[Bit] Six) (n : ℕ) : Bent (orbitFunction A n) :=
  selector_bent _ _ (extended_seed_bent n)
    (by simpa only [add_zero] using
      affine_bent (extendedSeed n) (extended_seed_bent n) (extendedMap A n) 0)

theorem orbit_succ (A : Six ≃ₗ[Bit] Six) (n : ℕ) (z : Space (n + 2)) :
    orbitFunction A (n + 1) z =
      selector (orbitFunction A n) (orbitFunction A n) (exchangePairs z) := by
  have h : (fun z => extendedSeed (n + 1) (extendedMap A (n + 1) z)) =
      selector (fun z => extendedSeed n (extendedMap A n z))
        (fun z => extendedSeed n (extendedMap A n z)) := by
    funext z
    rfl
  change selector (selector (extendedSeed n) (extendedSeed n))
    (fun z => extendedSeed (n + 1) (extendedMap A (n + 1) z)) z = _
  rw [h]
  exact selector_extension _ _ z

theorem orbit_index (A : Six ≃ₗ[Bit] Six) (k : ℕ)
    (hbase : HasIndex (orbitFunction A 0) k) (n : ℕ) :
    HasIndex (orbitFunction A n) (k + n) := by
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have he : EAEquivalent (selector (orbitFunction A n) (orbitFunction A n))
        (orbitFunction A (n + 1)) := by
      refine ⟨exchangePairs, 0, 0, 0, ?_⟩
      intro z
      simpa only [add_zero, LinearMap.zero_apply] using orbit_succ A n z
    simpa only [Nat.add_assoc] using
      ea_index _ _ _ he (quadratic_extension_index ih)

/-- In every even dimension at least eight, one explicit seed supplies two
EA-inequivalent bent concatenations outside the completed MM class. -/
theorem open_problem_pair_every_dimension (n : ℕ) :
    Module.finrank Bit (Space (n + 1)) = 8 + 2 * n ∧
    Bent (orbitFunction swapOne n) ∧ Bent (orbitFunction swapTwo n) ∧
    HasIndex (orbitFunction swapOne n) (2 + n) ∧
    HasIndex (orbitFunction swapTwo n) (3 + n) ∧
    ¬ InCompletedMM (orbitFunction swapOne n) ∧
    ¬ InCompletedMM (orbitFunction swapTwo n) ∧
    ¬ EAEquivalent (orbitFunction swapOne n) (orbitFunction swapTwo n) := by
  have h₁ := orbit_index swapOne 2 example_one_index n
  have h₂ := orbit_index swapTwo 3 example_two_index n
  have hd : Module.finrank Bit (Space (n + 1)) = 8 + 2 * n := by
    rw [space_finrank]
    omega
  exact ⟨hd, orbit_bent swapOne n, orbit_bent swapTwo n, h₁, h₂,
    outside_completedMM h₁ (by rw [hd]; omega),
    outside_completedMM h₂ (by rw [hd]; omega),
    different_indices h₁ h₂ (by omega)⟩

/-- The off-diagonal block, expressed without choosing coordinates. -/
def offDiagonal (U : Submodule Bit V) (L : V ≃ₗ[Bit] V) : U →ₗ[Bit] V ⧸ U :=
  U.mkQ.comp (L.toLinearMap.comp U.subtype)

theorem intersection_rank [FiniteDimensional Bit V] (U : Submodule Bit V)
    (L : V ≃ₗ[Bit] V) :
    Module.finrank Bit ↥(U ⊓ U.comap L.toLinearMap) =
      Module.finrank Bit U - Module.finrank Bit (offDiagonal U L).range := by
  have he : (offDiagonal U L).ker.map U.subtype = U ⊓ U.comap L.toLinearMap := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, ?_⟩
      change U.mkQ (L v) = 0 at hv
      exact (Submodule.Quotient.mk_eq_zero U).mp hv
    · intro hz
      refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
      change U.mkQ (L z) = 0
      exact (Submodule.Quotient.mk_eq_zero U).mpr hz.2
  have hd := Submodule.finrank_map_subtype_eq U (offDiagonal U L).ker
  rw [he] at hd
  have hr := (offDiagonal U L).finrank_range_add_finrank_ker
  omega

/-- The exact rank formula is independent of the affine translation. -/
theorem affine_selector_block_rank [FiniteDimensional Bit V] [Nontrivial V]
    (g : V → Bit) (U : Submodule Bit V) (L : V ≃ₗ[Bit] V) (c : V)
    (hg : Rigid g U) :
    HasIndex (selector g (fun z => g (L z + c)))
      (max 1 (Module.finrank Bit U - Module.finrank Bit (offDiagonal U L).range) + 1) := by
  simpa only [intersection_rank] using affine_selector_index_full g U L c hg

end BentFunctions
