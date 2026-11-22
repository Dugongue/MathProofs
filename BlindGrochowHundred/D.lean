import Mathlib

namespace BlindHundred.Probes

section Modules

variable {R V W Z U : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z] [AddCommGroup U] [Module R U]

/-- All probes constant on the fibers of a surjective probe factor uniquely. -/
private theorem unique_decoder_iff_kernel (f : V →ₗ[R] W) (g : V →ₗ[R] Z)
    (hf : Function.Surjective f) :
    (∃! d : W →ₗ[R] Z, d.comp f = g) ↔ f.ker ≤ g.ker := by
  constructor
  · rintro ⟨d, hd, _⟩ x hx
    have h := LinearMap.congr_fun hd x
    simpa [LinearMap.mem_ker.mp hx, LinearMap.mem_ker] using h.symm
  · intro hk
    let e := f.quotKerEquivOfSurjective hf
    let d := (f.ker.liftQ g hk).comp e.symm.toLinearMap
    refine ⟨d, ?_, ?_⟩
    · ext x
      change f.ker.liftQ g hk (e.symm (f x)) = g x
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    · intro d' hd
      ext y
      obtain ⟨x, rfl⟩ := hf y
      change d' (f x) = f.ker.liftQ g hk (e.symm (f x))
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
      exact LinearMap.congr_fun hd x

/-- Factor through the actual image without requiring the advertised codomain to be reached. -/
theorem image_decoder (f : V →ₗ[R] W) (g : V →ₗ[R] Z) (h : f.ker ≤ g.ker) :
    ∃! d : f.range →ₗ[R] Z, d.comp f.rangeRestrict = g := by
  apply (unique_decoder_iff_kernel _ _ (LinearMap.range_eq_top.mp f.range_rangeRestrict)).mpr
  simpa using h

/-- A decoder is injective precisely when the observed kernels are identical. -/
theorem faithful_decoder_iff (f : V →ₗ[R] W) (g : V →ₗ[R] Z) (d : W →ₗ[R] Z)
    (hf : Function.Surjective f) (h : d.comp f = g) :
    Function.Injective d ↔ f.ker = g.ker := by
  constructor
  · intro inj
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← h, LinearMap.comp_apply, ← d.map_zero, inj.eq_iff]
  · intro he
    apply LinearMap.ker_eq_bot.mp
    ext y
    obtain ⟨x, rfl⟩ := hf y
    have hh := LinearMap.congr_fun h x
    change d (f x) = g x at hh
    rw [LinearMap.mem_ker, hh, Submodule.mem_bot, ← LinearMap.mem_ker, ← he, LinearMap.mem_ker]

/-- A decoder onto the advertised codomain exists precisely when the second probe reaches it. -/
theorem surjective_decoder_iff (f : V →ₗ[R] W) (g : V →ₗ[R] Z) (d : W →ₗ[R] Z)
    (hf : Function.Surjective f) (h : d.comp f = g) :
    Function.Surjective d ↔ Function.Surjective g := by
  subst g
  constructor
  · intro hd
    exact hd.comp hf
  · intro hd z
    obtain ⟨x, hx⟩ := hd z
    exact ⟨f x, hx⟩

/-- Equal kernel relations classify surjective probe presentations, with unique transport. -/
private theorem output_transport_iff (f : V →ₗ[R] W) (g : V →ₗ[R] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (∃! e : W ≃ₗ[R] Z, e.toLinearMap.comp f = g) ↔ f.ker = g.ker := by
  constructor
  · rintro ⟨e, he, _⟩
    exact (faithful_decoder_iff f g e.toLinearMap hf he).mp e.injective
  · intro hk
    obtain ⟨d, hd, hunique⟩ := (unique_decoder_iff_kernel f g hf).mpr hk.le
    let e := LinearEquiv.ofBijective d
      ⟨(faithful_decoder_iff f g _ hf hd).mpr hk, (surjective_decoder_iff f g _ hf hd).mpr hg⟩
    refine ⟨e, hd, ?_⟩
    intro e' he'
    ext y
    exact LinearMap.congr_fun (hunique e'.toLinearMap he') y

/-- Simultaneous output transport on actual images is governed by kernels after input transport. -/
theorem image_transport_after_input (f : V →ₗ[R] W) (g : U →ₗ[R] Z)
    (u : V ≃ₗ[R] U) :
    (∃! e : f.range ≃ₗ[R] g.range,
      e.toLinearMap.comp f.rangeRestrict = g.rangeRestrict.comp u.toLinearMap) ↔
        f.ker = (g.comp u.toLinearMap).ker := by
  rw [output_transport_iff _ _ (LinearMap.range_eq_top.mp f.range_rangeRestrict)
    ((LinearMap.range_eq_top.mp g.range_rangeRestrict).comp u.surjective)]
  change f.rangeRestrict.ker = (g.rangeRestrict.comp u.toLinearMap).ker ↔ _
  simp [LinearMap.ker_comp]

/-- Erasing a probe loses no information exactly when it can be decoded on the retained image. -/
theorem erasure_iff_decoder (f : V →ₗ[R] W) (g : V →ₗ[R] Z) :
    (f.prod g).ker = f.ker ↔ ∃ d : f.range →ₗ[R] Z, d.comp f.rangeRestrict = g := by
  rw [LinearMap.ker_prod, inf_eq_left]
  constructor
  · intro h
    obtain ⟨d, hd, _⟩ := image_decoder f g h
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩ x hx
    have fx : f.rangeRestrict x = 0 := Subtype.ext (LinearMap.mem_ker.mp hx)
    exact LinearMap.mem_ker.mpr (by rw [← hd, LinearMap.comp_apply, fx, map_zero])

/-- A redundant observation makes the joint image the graph of its decoder. -/
theorem joint_image_is_graph (f : V →ₗ[R] W) (g : V →ₗ[R] Z)
    (d : f.range →ₗ[R] Z) (h : d.comp f.rangeRestrict = g) (w : W) (z : Z) :
    (w, z) ∈ (f.prod g).range ↔ ∃ hw : w ∈ f.range, d ⟨w, hw⟩ = z := by
  constructor
  · rintro ⟨x, hx⟩
    have hw : f x = w := congrArg Prod.fst hx
    have hz : g x = z := congrArg Prod.snd hx
    refine ⟨⟨x, hw⟩, ?_⟩
    have he : (⟨w, ⟨x, hw⟩⟩ : f.range) = f.rangeRestrict x := Subtype.ext hw.symm
    rw [he, ← LinearMap.comp_apply, h, hz]
  · rintro ⟨hw, hz⟩
    obtain ⟨x, hx⟩ := hw
    have he : (⟨w, ⟨x, hx⟩⟩ : f.range) = f.rangeRestrict x := Subtype.ext hx.symm
    exact ⟨x, Prod.ext hx (by rwa [he, ← LinearMap.comp_apply, h] at hz)⟩

/-- Joint data separate a pair precisely when one component does. -/
theorem adaptive_separation {I : Type*} (f : I → V →ₗ[R] W) (x y : V) :
    LinearMap.pi f x ≠ LinearMap.pi f y ↔ ∃ i, f i x ≠ f i y := by
  classical
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (funext hn)
  · rintro ⟨i, hi⟩ h
    exact hi (congrFun h i)

/-- Any probe that is determined by joint observations factors through their actual image. -/
theorem joint_decoder_iff {I : Type*} (f : I → V →ₗ[R] W) (g : V →ₗ[R] Z) :
    (∃! d : (LinearMap.pi f).range →ₗ[R] Z, d.comp (LinearMap.pi f).rangeRestrict = g) ↔
      ∀ x, (∀ i, f i x = 0) → g x = 0 := by
  rw [unique_decoder_iff_kernel _ _ (LinearMap.range_eq_top.mp (LinearMap.pi f).range_rangeRestrict)]
  rw [LinearMap.ker_rangeRestrict]
  constructor
  · intro h x hx
    exact LinearMap.mem_ker.mp (h (LinearMap.mem_ker.mpr (funext hx)))
  · intro h x hx
    exact LinearMap.mem_ker.mpr (h x (congrFun (LinearMap.mem_ker.mp hx)))

/-- A retained probe with a left inverse uniquely decodes every further observation on its image. -/
theorem full_recovery_from_split_probe (f : V →ₗ[R] W) (g : V →ₗ[R] Z) (s : W →ₗ[R] V)
    (h : s.comp f = LinearMap.id) : ∃! d : f.range →ₗ[R] Z, d.comp f.rangeRestrict = g := by
  apply image_decoder
  intro x hx
  have he := LinearMap.congr_fun h x
  change s (f x) = x at he
  rw [LinearMap.mem_ker.mp hx, map_zero] at he
  rw [← he]
  exact Submodule.zero_mem _

/-- A panel whose last coordinate can be reconstructed from the first has the same fibers. -/
theorem redundant_probe_preserves_fibers (f : V →ₗ[R] W) (g : V →ₗ[R] Z)
    (d : f.range →ₗ[R] Z) (h : d.comp f.rangeRestrict = g) (x y : V) :
    f.prod g x = f.prod g y ↔ f x = f y := by
  constructor
  · exact congrArg Prod.fst
  · intro hxy
    have h' : f.rangeRestrict x = f.rangeRestrict y := Subtype.ext hxy
    apply Prod.ext hxy
    rw [← h]
    exact congrArg d h'

end Modules

section Dimension
variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K V]

/-- A strict refinement of the observations strictly increases their image dimension. -/
theorem strict_kernel_refinement_rank (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (h : g.ker < f.ker) :
    Module.finrank K f.range < Module.finrank K g.range := by
  have hn := Submodule.finrank_lt_finrank_of_lt h
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  omega

/-- Among nested probe kernels, equal image dimensions certify identical information. -/
theorem rank_certifies_decodability (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (h : g.ker ≤ f.ker) :
    Module.finrank K f.range = Module.finrank K g.range ↔
      ∃! d : f.range →ₗ[K] Z, d.comp f.rangeRestrict = g := by
  rw [unique_decoder_iff_kernel _ _ (LinearMap.range_eq_top.mp f.range_rangeRestrict)]
  simp only [LinearMap.ker_rangeRestrict]
  constructor
  · intro hr
    by_contra hn
    exact (strict_kernel_refinement_rank f g (lt_of_le_not_ge h hn)).ne hr
  · intro h'
    have hf := f.finrank_range_add_finrank_ker
    have hg := g.finrank_range_add_finrank_ker
    rw [le_antisymm h' h] at hf
    omega

/-- The additional rank is exactly what the second probe detects on the first kernel. -/
theorem joint_rank_increments (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    Module.finrank K (f.prod g).range = Module.finrank K f.range +
      Module.finrank K (g.domRestrict f.ker).range := by
  let h := g.domRestrict f.ker
  have r₁ := (f.prod g).finrank_range_add_finrank_ker
  have r₂ := f.finrank_range_add_finrank_ker
  have r₃ := h.finrank_range_add_finrank_ker
  have hc : h.ker = (f.prod g).ker.comap f.ker.subtype := by
    ext x
    simp [h, LinearMap.ker_prod, LinearMap.mem_ker]
  have he : (f.prod g).ker ≤ f.ker := by
    rw [LinearMap.ker_prod]
    exact inf_le_left
  let e : (f.prod g).ker ≃ₗ[K] h.ker :=
    LinearEquiv.ofLinearMap
      { toFun := fun x => ⟨⟨x, he x.property⟩, hc ▸ x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      { toFun := fun x => ⟨x.val, Eq.mp (congrArg (fun P : Submodule K f.ker => x.val ∈ P) hc) x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      (by ext; rfl) (by ext; rfl)
  have hr := e.finrank_eq
  change _ = _ + Module.finrank K h.range
  omega

/-- Strictly positive information gain has a concrete vector witness in the old kernel. -/
theorem improvement_has_witness (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    Module.finrank K f.range < Module.finrank K (f.prod g).range ↔
      ∃ x, f x = 0 ∧ g x ≠ 0 := by
  classical
  constructor
  · intro hr
    by_contra hn
    push_neg at hn
    have hk : (f.prod g).ker = f.ker := by
      rw [LinearMap.ker_prod, inf_eq_left]
      exact fun x hx => LinearMap.mem_ker.mpr (hn x (LinearMap.mem_ker.mp hx))
    have h₁ := f.finrank_range_add_finrank_ker
    have h₂ := (f.prod g).finrank_range_add_finrank_ker
    rw [hk] at h₂
    omega
  · rintro ⟨x, hx, hg⟩
    apply strict_kernel_refinement_rank
    rw [LinearMap.ker_prod]
    refine lt_of_le_not_ge inf_le_left ?_
    intro he
    exact hg (LinearMap.mem_ker.mp ((Submodule.mem_inf.mp (he (LinearMap.mem_ker.mpr hx))).2))

/-- Two probe ranks add exactly up to the codimension accounted for by their common quotient. -/
theorem joint_rank_overlap (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    Module.finrank K (f.prod g).range + Module.finrank K (V ⧸ (f.ker ⊔ g.ker)) =
      Module.finrank K f.range + Module.finrank K g.range := by
  have h₁ := (f.prod g).finrank_range_add_finrank_ker
  have h₂ := f.finrank_range_add_finrank_ker
  have h₃ := g.finrank_range_add_finrank_ker
  have h₄ := Submodule.finrank_sup_add_finrank_inf_eq f.ker g.ker
  have h₅ := (f.ker ⊔ g.ker).mkQ.finrank_range_add_finrank_ker
  rw [LinearMap.ker_prod] at h₁
  rw [Submodule.ker_mkQ, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
    finrank_top] at h₅
  omega

/-- Two surjective probes remain jointly surjective precisely when they have no common quotient. -/
theorem joint_surjectivity_iff (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (f.prod g) ↔ f.ker ⊔ g.ker = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := h (f x, 0)
    have hfy : f y = f x := congrArg Prod.fst hy
    have hgy : g y = 0 := congrArg Prod.snd hy
    exact Submodule.mem_sup.mpr
      ⟨x - y, LinearMap.mem_ker.mpr (by rw [map_sub, hfy, sub_self]),
       y, LinearMap.mem_ker.mpr hgy, sub_add_cancel x y⟩
  · intro h
    apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_prod_eq h, LinearMap.range_eq_top.mpr hf, LinearMap.range_eq_top.mpr hg]
    apply top_unique
    intro x _
    exact ⟨Submodule.mem_top, Submodule.mem_top⟩

/-- Finite-rank probe panels preserve rank under any fixed linear recoding with a left inverse. -/
theorem split_recoding_rank (f : V →ₗ[K] W) (r : W →ₗ[K] Z) (s : Z →ₗ[K] W)
    (h : s.comp r = LinearMap.id) :
    Module.finrank K (r.comp f).range = Module.finrank K f.range := by
  have hi : Function.Injective r := by
    apply Function.LeftInverse.injective (g := s)
    exact fun x => LinearMap.congr_fun h x
  have hker : (r.comp f).ker = f.ker := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    rw [← r.map_zero, hi.eq_iff]
  have h₁ := (r.comp f).finrank_range_add_finrank_ker
  have h₂ := f.finrank_range_add_finrank_ker
  rw [hker] at h₁
  omega

/-- Finite-rank presentations into the same ambient output have equivalent left orbits
whenever they have the same kernel. -/
theorem ambient_orbit_iff_kernel (f g : V →ₗ[K] W) :
    (∃ e : W ≃ₗ[K] W, e.toLinearMap.comp f = g) ↔ f.ker = g.ker := by
  constructor
  · rintro ⟨e, he⟩
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← he, LinearMap.comp_apply]
    change f x = 0 ↔ e (f x) = 0
    exact ⟨fun h => h ▸ e.map_zero, fun h => e.injective (h.trans e.map_zero.symm)⟩
  · intro hk
    have hr : f.rangeRestrict.ker = g.rangeRestrict.ker := by simpa using hk
    obtain ⟨e, he, _⟩ := (output_transport_iff _ _
      (LinearMap.range_eq_top.mp f.range_rangeRestrict)
      (LinearMap.range_eq_top.mp g.range_rangeRestrict)).mpr hr
    obtain ⟨E, hE⟩ := Submodule.exists_linearEquiv_restrict_eq e
    refine ⟨E, ?_⟩
    ext x
    have hh := congrArg Subtype.val (LinearMap.congr_fun he x)
    exact (hE (f.rangeRestrict x)).symm.trans hh

/-- A joint pair furnishes a basis-free splitting precisely when each component is
onto and the two kernels are complementary. -/
theorem joint_product_equivalence (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (∃ e : V ≃ₗ[K] W × Z, e.toLinearMap = f.prod g) ↔ IsCompl f.ker g.ker := by
  rw [isCompl_iff]
  constructor
  · rintro ⟨e, he⟩
    have hinj : Function.Injective (f.prod g) := he ▸ e.injective
    have hsurj : Function.Surjective (f.prod g) := he ▸ e.surjective
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, ← LinearMap.ker_prod]
      exact LinearMap.ker_eq_bot.mpr hinj
    · rw [codisjoint_iff]
      exact (joint_surjectivity_iff f g hf hg).mp hsurj
  · rintro ⟨hd, hs⟩
    have hker : (f.prod g).ker = ⊥ := LinearMap.ker_prod f g ▸ hd.eq_bot
    refine ⟨LinearEquiv.ofBijective _ ⟨LinearMap.ker_eq_bot.mp hker, ?_⟩, rfl⟩
    exact (joint_surjectivity_iff f g hf hg).mpr hs.eq_top

/-- Replacing two observations by their sum cannot increase the joint rank. -/
theorem summed_observation_rank_bound (f g : V →ₗ[K] W) :
    Module.finrank K (f + g).range ≤ Module.finrank K (f.prod g).range := by
  have hker : (f.prod g).ker ≤ (f + g).ker := by
    rw [LinearMap.ker_prod]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.mp hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.mem_ker.mp hx₁,
      LinearMap.mem_ker.mp hx₂, add_zero]
  have hn := Submodule.finrank_mono hker
  have h₁ := (f + g).finrank_range_add_finrank_ker
  have h₂ := (f.prod g).finrank_range_add_finrank_ker
  omega

end Dimension

section Compression

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V]
variable {I : Type*} [DecidableEq I]

def panelKernel (f : I → V →ₗ[K] W) (s : Finset I) : Submodule K V :=
  ⨅ i : {i // i ∈ s}, (f i).ker

private theorem mem_panel_iff (f : I → V →ₗ[K] W) (s : Finset I) (x : V) :
    x ∈ panelKernel f s ↔ ∀ i ∈ s, f i x = 0 := by
  simp [panelKernel, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem panel_insert (f : I → V →ₗ[K] W) (s : Finset I) (i : I) :
    panelKernel f (insert i s) = (f i).ker ⊓ panelKernel f s := by
  ext x
  simp [mem_panel_iff, LinearMap.mem_ker]

/-- All constraints on a finite-dimensional subspace can be compressed to at most
the number of dimensions they remove, even with infinitely many available probes. -/
theorem compress_on_subspace (f : I → V →ₗ[K] W) (P : Submodule K V) :
    ∃ s : Finset I, P ⊓ panelKernel f s = P ⊓ (LinearMap.pi f).ker ∧
      s.card + Module.finrank K ↥(P ⊓ (LinearMap.pi f).ker) ≤ Module.finrank K P := by
  classical
  let H := (LinearMap.pi f).ker
  change ∃ s : Finset I, P ⊓ panelKernel f s = P ⊓ H ∧
    s.card + Module.finrank K ↥(P ⊓ H) ≤ Module.finrank K P
  have hr : ∀ n : ℕ, ∀ Q : Submodule K V, Module.finrank K Q = n →
      ∃ s : Finset I, Q ⊓ panelKernel f s = Q ⊓ H ∧
        s.card + Module.finrank K ↥(Q ⊓ H) ≤ Module.finrank K Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hQ
      by_cases hle : Q ≤ H
      · refine ⟨∅, ?_, ?_⟩
        · rw [inf_eq_left.mpr hle]
          have eh : panelKernel f ∅ = ⊤ := by ext x; simp [mem_panel_iff]
          rw [eh, inf_top_eq]
        · rw [Finset.card_empty, zero_add]
          exact Submodule.finrank_mono inf_le_left
      · obtain ⟨x, hx, hnx⟩ : ∃ x : V, x ∈ Q ∧ x ∉ H := by
          by_contra hn
          push_neg at hn
          exact hle hn
        have hnx' : ¬ ∀ i : I, f i x = 0 := by
          intro hh
          exact hnx (LinearMap.mem_ker.mpr (funext hh))
        push_neg at hnx'
        obtain ⟨i, hi⟩ := hnx'
        let Q' := Q ⊓ (f i).ker
        have hlt : Q' < Q := by
          apply lt_of_le_not_ge inf_le_left
          intro hn
          exact hi (LinearMap.mem_ker.mp ((Submodule.mem_inf.mp (hn hx)).2))
        have hd := Submodule.finrank_lt_finrank_of_lt hlt
        have hH : H ≤ (f i).ker := by
          intro y hy
          exact LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp hy) i)
        have hx' : Q' ⊓ H = Q ⊓ H := by simp [Q', inf_assoc, inf_eq_right.mpr hH]
        obtain ⟨s, hs, hcard⟩ := ih (Module.finrank K Q') (by omega) Q' rfl
        refine ⟨insert i s, ?_, ?_⟩
        · rw [panel_insert, ← inf_assoc, ← show Q' = Q ⊓ (f i).ker from rfl, hs, hx']
        · rw [hx'] at hcard
          have hi' := Finset.card_insert_le i s
          omega
  exact hr _ P rfl

/-- A complete panel can be represented by at most its joint rank many components. -/
theorem rank_budgeted_compression (f : I → V →ₗ[K] W) :
    ∃ s : Finset I, panelKernel f s = (LinearMap.pi f).ker ∧
      s.card ≤ Module.finrank K (LinearMap.pi f).range := by
  obtain ⟨s, hs, hn⟩ := compress_on_subspace f ⊤
  simp only [top_inf_eq, finrank_top] at hs hn
  have hr := (LinearMap.pi f).finrank_range_add_finrank_ker
  have hk := (LinearEquiv.ofEq ((⊤ : Submodule K V) ⊓ (LinearMap.pi f).ker)
    (LinearMap.pi f).ker (top_inf_eq _)).finrank_eq
  exact ⟨s, hs, by omega⟩

/-- Two panels admit one jointly chosen set of indices preserving both kernels. -/
theorem common_compression (f g : I → V →ₗ[K] W) :
    ∃ s : Finset I, panelKernel f s = (LinearMap.pi f).ker ∧
      panelKernel g s = (LinearMap.pi g).ker ∧
      s.card ≤ Module.finrank K (LinearMap.pi f).range +
        Module.finrank K (LinearMap.pi g).range := by
  obtain ⟨a, ha, hca⟩ := rank_budgeted_compression f
  obtain ⟨b, hb, hcb⟩ := rank_budgeted_compression g
  refine ⟨a ∪ b, ?_, ?_, (Finset.card_union_le a b).trans (Nat.add_le_add hca hcb)⟩
  · ext x
    rw [← ha, mem_panel_iff, mem_panel_iff]
    constructor
    · intro h i hi
      exact h i (Finset.mem_union_left _ hi)
    · intro h i _
      have hx := LinearMap.mem_ker.mp (ha ▸ (mem_panel_iff _ _ _).mpr h)
      exact congrFun hx i
  · ext x
    rw [← hb, mem_panel_iff, mem_panel_iff]
    constructor
    · intro h i hi
      exact h i (Finset.mem_union_right _ hi)
    · intro h i _
      have hx := LinearMap.mem_ker.mp (hb ▸ (mem_panel_iff _ _ _).mpr h)
      exact congrFun hx i

/-- On a fixed subspace, any panel that detects every nonzero vector has a
complete subpanel of size at most the dimension of that subspace. -/
theorem compressed_separation_on_subspace (f : I → V →ₗ[K] W) (P : Submodule K V)
    (h : ∀ x ∈ P, (∀ i, f i x = 0) → x = 0) :
    ∃ s : Finset I, s.card ≤ Module.finrank K P ∧
      ∀ x ∈ P, (∀ i ∈ s, f i x = 0) → x = 0 := by
  obtain ⟨s, he, hs⟩ := compress_on_subspace f P
  refine ⟨s, by omega, ?_⟩
  intro x hx hzero
  have hh : x ∈ P ⊓ (LinearMap.pi f).ker := he ▸
    Submodule.mem_inf.mpr ⟨hx, (mem_panel_iff f _ _).mpr hzero⟩
  exact h x hx (congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hh).2))

/-- A complete scalar subpanel can be chosen with exactly the joint rank many probes.
The dimension lower bound holds for every finite complete scalar subpanel. -/
theorem scalar_compression_is_sharp (f : I → V →ₗ[K] K) :
    (∃ s : Finset I, panelKernel f s = (LinearMap.pi f).ker ∧
      s.card = Module.finrank K (LinearMap.pi f).range) ∧
    ∀ t : Finset I, panelKernel f t = (LinearMap.pi f).ker →
      Module.finrank K (LinearMap.pi f).range ≤ t.card := by
  classical
  have lower (t : Finset I) (h : panelKernel f t = (LinearMap.pi f).ker) :
      Module.finrank K (LinearMap.pi f).range ≤ t.card := by
    let ft := LinearMap.pi (fun i : {i // i ∈ t} => f i)
    have hk : ft.ker = (LinearMap.pi f).ker := by
      simpa [ft, LinearMap.ker_pi, panelKernel] using h
    have h₁ := ft.finrank_range_add_finrank_ker
    have h₂ := (LinearMap.pi f).finrank_range_add_finrank_ker
    have h₃ : Module.finrank K ft.range ≤ t.card := by
      have hle := Submodule.finrank_le ft.range
      simpa [Module.finrank_pi, ft] using hle
    rw [hk] at h₁
    omega
  obtain ⟨s, hs, hr⟩ := rank_budgeted_compression f
  exact ⟨⟨s, hs, le_antisymm hr (lower s hs)⟩, lower⟩

end Compression

end BlindHundred.Probes
