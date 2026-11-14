import Mathlib

/-!
# Theorem S: GL-Levi sections give TI-hardness for all five actions

Over any field `K`, suppose a group `G` of linear automorphisms of `H` has a GL-Levi section
`e : H ≃ U × U'`: every `g ∈ GL(U)` extends to some `P ∈ G` of the form `e⁻¹ ∘ (g × g') ∘ e`.
Then, for each of the five actions of Chen–Grochow–Qiao–Tang–Zhang (Definition 1.6), the
GL-isomorphism problem on `U` reduces to the G-isomorphism problem on `H` through the linear
padding maps `ι = e⁻¹ ∘ inl` (covariant modes) and `ι* = (fst ∘ e)ᵀ` (contragredient modes).

The file only imports Mathlib.
-/

open Module Function TensorProduct

namespace LeviHardness

section Extension

variable {K : Type*} [Field K]

/-- An injective map from a subspace extends injectively to the whole space when dimensions agree. -/
theorem exists_injective_extend {E E' : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']
    (hdim : finrank K E = finrank K E') (p : Submodule K E) (f : p →ₗ[K] E')
    (hf : Injective f) : ∃ F : E →ₗ[K] E', Injective F ∧ ∀ x : p, F x = f x := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  obtain ⟨r, hr⟩ := (LinearMap.range f).exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hq
  have h2 := Submodule.finrank_add_eq_of_isCompl hr
  have h3 : finrank K (LinearMap.range f) = finrank K p := LinearMap.finrank_range_of_inj hf
  have hqr : finrank K q = finrank K r := by omega
  let j : q ≃ₗ[K] r := LinearEquiv.ofFinrankEq q r hqr
  refine ⟨LinearMap.ofIsCompl hq f (r.subtype ∘ₗ j.toLinearMap), ?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hzpq : z ∈ p ⊔ q := by rw [hq.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hzpq
    have hza : LinearMap.ofIsCompl hq f (r.subtype ∘ₗ j.toLinearMap) a = f ⟨a, ha⟩ :=
      LinearMap.ofIsCompl_apply_left hq ⟨a, ha⟩
    have hzb : LinearMap.ofIsCompl hq f (r.subtype ∘ₗ j.toLinearMap) b = (j ⟨b, hb⟩ : E') :=
      LinearMap.ofIsCompl_apply_right hq ⟨b, hb⟩
    rw [map_add, hza, hzb] at hz
    have hfa : f ⟨a, ha⟩ ∈ LinearMap.range f ⊓ r := by
      refine ⟨LinearMap.mem_range_self f _, ?_⟩
      have : f ⟨a, ha⟩ = -(j ⟨b, hb⟩ : E') := eq_neg_of_add_eq_zero_left hz
      rw [this]; exact r.neg_mem (j ⟨b, hb⟩).2
    rw [hr.inf_eq_bot, Submodule.mem_bot] at hfa
    have ha0 : (⟨a, ha⟩ : p) = 0 := hf (by rw [hfa, map_zero])
    have hb0 : (j ⟨b, hb⟩ : E') = 0 := by rw [hfa, zero_add] at hz; exact hz
    have hb1 : j ⟨b, hb⟩ = 0 := Subtype.ext hb0
    have hb0' : (⟨b, hb⟩ : q) = 0 := by
      rwa [LinearEquiv.map_eq_zero_iff] at hb1
    have ha' : a = 0 := congrArg Subtype.val ha0
    have hb' : b = 0 := congrArg Subtype.val hb0'
    rw [ha', hb', add_zero]
  · exact LinearMap.ofIsCompl_apply_left hq x

/-- A linear map on `V` whose transpose restricts to a prescribed map on a subspace of `Dual V`. -/
theorem exists_dual_lift {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q' : Submodule K (Dual K V)) (φ : Q' →ₗ[K] Dual K V) :
    ∃ L : V →ₗ[K] V, ∀ β : Q', ∀ v : V, (β : Dual K V) (L v) = φ β v := by
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend φ
  refine ⟨(evalEquiv K V).symm.toLinearMap ∘ₗ Λ.dualMap ∘ₗ (Dual.eval K V), fun β v => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, apply_evalEquiv_symm_apply,
    LinearMap.dualMap_apply, Dual.eval_apply]
  rw [← hΛ, LinearMap.comp_apply, Submodule.subtype_apply]

/-- **Dual-support extension lemma.** If `f` on `S ⊆ V` and `h` on `Q ⊆ V*` are injective and
compatible with the evaluation pairing, then one automorphism `g` of `V` extends `f`, and its
contragredient extends `h`, in the sense `h α ∘ g = α`. -/
theorem dual_support_extension {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) (Q : Submodule K (Dual K V))
    (f : S →ₗ[K] V) (hf : Injective f) (h : Q →ₗ[K] Dual K V) (hh : Injective h)
    (hpair : ∀ s : S, ∀ α : Q, h α (f s) = (α : Dual K V) s) :
    ∃ g : V ≃ₗ[K] V, (∀ s : S, g s = f s) ∧
      (∀ α : Q, ∀ v : V, h α (g v) = (α : Dual K V) v) := by
  classical
  set E : Submodule K V := Q.dualCoannihilator with hE
  set Q' : Submodule K (Dual K V) := LinearMap.range h with hQ'
  set E' : Submodule K V := Q'.dualCoannihilator with hE'
  have hdimQ : finrank K Q' = finrank K Q := LinearMap.finrank_range_of_inj hh
  have hdim : finrank K E = finrank K E' := by
    have a1 : finrank K Q + finrank K E = finrank K V :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq Q
    have a2 : finrank K Q' + finrank K E' = finrank K V :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq Q'
    omega
  have memE : ∀ v : V, v ∈ E ↔ ∀ α : Q, (α : Dual K V) v = 0 := by
    intro v
    rw [hE, Submodule.mem_dualCoannihilator]
    exact ⟨fun H α => H α α.2, fun H φ hφ => H ⟨φ, hφ⟩⟩
  have memE' : ∀ v : V, v ∈ E' ↔ ∀ α : Q, h α v = 0 := by
    intro v
    rw [hE', Submodule.mem_dualCoannihilator]
    constructor
    · intro H α; exact H _ (LinearMap.mem_range_self h α)
    · rintro H φ ⟨α, rfl⟩; exact H α
  -- the part of `S` inside `E`, viewed inside `E`
  let p : Submodule K E := S.comap E.subtype
  let incl : p →ₗ[K] S := LinearMap.codRestrict S (E.subtype ∘ₗ p.subtype) (fun x => x.2)
  have hfE' : ∀ x : p, f (incl x) ∈ E' := by
    intro x
    rw [memE']
    intro α
    rw [hpair]
    exact (memE _).1 (x : E).2 α
  let f0 : p →ₗ[K] E' := LinearMap.codRestrict E' (f ∘ₗ incl) hfE'
  have hf0 : Injective f0 := by
    intro x y hxy
    have h1 : f (incl x) = f (incl y) := congrArg Subtype.val hxy
    have h2 := hf h1
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : V)) h2
  obtain ⟨κ, hκinj, hκ⟩ := exists_injective_extend hdim p f0 hf0
  -- a complement of `S ⊔ E`
  obtain ⟨R, hR⟩ := (S ⊔ E).exists_isCompl
  -- a dual lift
  obtain ⟨L, hL⟩ := exists_dual_lift Q'
    (Q.subtype ∘ₗ (LinearEquiv.ofInjective h hh).symm.toLinearMap)
  have hLα : ∀ α : Q, ∀ v : V, h α (L v) = (α : Dual K V) v := by
    intro α v
    have e1 : (LinearEquiv.ofInjective h hh).symm ⟨h α, LinearMap.mem_range_self h α⟩ = α := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    have := hL ⟨h α, LinearMap.mem_range_self h α⟩ v
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, e1, Submodule.subtype_apply] at this
    exact this
  have hκS : ∀ (s : S) (hs : (s : V) ∈ E), (κ ⟨s, hs⟩ : V) = f s := by
    intro s hs
    have := hκ ⟨⟨s, hs⟩, s.2⟩
    exact congrArg Subtype.val this
  let ψ : S × (E × R) →ₗ[K] V := f.coprod ((E'.subtype ∘ₗ κ).coprod (L ∘ₗ R.subtype))
  let π : S × (E × R) →ₗ[K] V := S.subtype.coprod (E.subtype.coprod R.subtype)
  have hψ : ∀ s e r, ψ (s, (e, r)) = f s + ((κ e : V) + L r) := fun _ _ _ => rfl
  have hπ : ∀ s e r, π (s, (e, r)) = (s : V) + ((e : V) + r) := fun _ _ _ => rfl
  have hπsurj : Surjective π := by
    rw [← LinearMap.range_eq_top]
    simp only [π, LinearMap.range_coprod, Submodule.range_subtype]
    rw [← sup_assoc, hR.sup_eq_top]
  have hRmem : ∀ r : R, (r : V) ∈ S ⊔ E → (r : V) = 0 := by
    intro r hr
    have hmem : (r : V) ∈ (S ⊔ E) ⊓ R := ⟨hr, r.2⟩
    rw [hR.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hker : LinearMap.ker π ≤ LinearMap.ker ψ := by
    rintro ⟨s, e, r⟩ hz
    rw [LinearMap.mem_ker, hπ] at hz
    rw [LinearMap.mem_ker, hψ]
    have hz' : ((s : V) + e) + r = 0 := by rw [add_assoc]; exact hz
    have hr : (r : V) = 0 := by
      apply hRmem
      rw [eq_neg_of_add_eq_zero_right hz']
      exact (S ⊔ E).neg_mem (Submodule.add_mem_sup s.2 e.2)
    have hs : (s : V) = -(e : V) := by
      rw [hr, add_zero] at hz'
      exact eq_neg_of_add_eq_zero_left hz'
    have hsE : (s : V) ∈ E := by rw [hs]; exact E.neg_mem e.2
    have he : e = -(⟨s, hsE⟩ : E) := by
      apply Subtype.ext
      rw [Submodule.coe_neg]
      show (e : V) = -(s : V)
      rw [hs, neg_neg]
    rw [hr, map_zero, add_zero, he, map_neg, Submodule.coe_neg, hκS s hsE, add_neg_cancel]
  let g0 : V →ₗ[K] V := (LinearMap.ker π).liftQ ψ hker ∘ₗ
    (π.quotKerEquivOfSurjective hπsurj).symm.toLinearMap
  have hg0 : ∀ z, g0 (π z) = ψ z := by
    intro z
    have hq : (π.quotKerEquivOfSurjective hπsurj).symm (π z) = Submodule.Quotient.mk z := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [g0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hq, Submodule.liftQ_apply]
  have hg0inj : Injective g0 := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨⟨s, e, r⟩, rfl⟩ := hπsurj v
    rw [LinearMap.mem_ker, hg0, hψ] at hv
    have hdual : ∀ α : Q, (α : Dual K V) ((s : V) + r) = 0 := by
      intro α
      have := congrArg (h α) hv
      rw [map_add, map_add, hpair, hLα, map_zero] at this
      have hk : h α (κ e : V) = 0 := (memE' _).1 (κ e).2 α
      rw [hk, zero_add] at this
      rw [map_add]
      exact this
    have hsr : (s : V) + r ∈ E := (memE _).2 hdual
    have hr : (r : V) = 0 := by
      apply hRmem
      have : (r : V) = ((s : V) + r) - s := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hsr) (Submodule.mem_sup_left s.2)
    rw [hr, map_zero, add_zero] at hv
    have hsE : (s : V) ∈ E := by rw [hr, add_zero] at hsr; exact hsr
    have hsum : κ ((⟨s, hsE⟩ : E) + e) = 0 := by
      apply Subtype.ext
      rw [map_add, Submodule.coe_add, hκS s hsE, Submodule.coe_zero]
      exact hv
    have hxe : (⟨s, hsE⟩ : E) + e = 0 := hκinj (by rw [hsum, map_zero])
    have hxe' : (s : V) + e = 0 := congrArg Subtype.val hxe
    rw [hπ, hr, add_zero]
    exact hxe'
  refine ⟨LinearEquiv.ofInjectiveEndo g0 hg0inj, fun s => ?_, fun α v => ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]
    have hs : (s : V) = π (s, (0, 0)) := by rw [hπ]; simp
    rw [hs, hg0, hψ]
    simp
  · obtain ⟨⟨s, e, r⟩, rfl⟩ := hπsurj v
    rw [LinearEquiv.coe_ofInjectiveEndo, hg0, hψ, hπ]
    rw [map_add, map_add, map_add, map_add, hpair, hLα, (memE' _).1 (κ e).2 α,
      (memE _).1 e.2 α]

end Extension

section ModeSupport

variable {K : Type*} [Field K]
variable {V W X Y : Type*}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def evalSmul (x : X) (v : V) : Module.Dual K X →ₗ[K] V where
  toFun φ := φ x • v
  map_add' φ ψ := by simp [add_smul]
  map_smul' c φ := by simp [smul_smul]

@[simp] theorem evalSmul_apply (x : X) (v : V) (φ : Module.Dual K X) :
    evalSmul x v φ = φ x • v := rfl

noncomputable def contractBil : V →ₗ[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  LinearMap.mk₂ K (fun v x => evalSmul x v)
    (fun v w x => by ext φ; simp [smul_add])
    (fun c v x => by ext φ; exact smul_comm _ _ _)
    (fun v x y => by ext φ; simp [add_smul])
    (fun v c x => by ext φ; simp [smul_smul])

noncomputable def contract : V ⊗[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  TensorProduct.lift contractBil

@[simp] theorem contract_tmul (v : V) (x : X) (φ : Module.Dual K X) :
    contract (v ⊗ₜ[K] x) φ = φ x • v := rfl

theorem contract_map (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) (φ : Module.Dual K Y) :
    contract (TensorProduct.map f g T) φ = f (contract T (g.dualMap φ)) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [LinearMap.dualMap_apply]
  | add a b ha hb => simp [ha, hb]

/-- The mode support of `T ∈ V ⊗ X`: the image of its flattening `X* → V`. -/
noncomputable def msupp (T : V ⊗[K] X) : Submodule K V := LinearMap.range (contract T)

theorem mem_msupp (T : V ⊗[K] X) (φ : Module.Dual K X) : contract T φ ∈ msupp T :=
  LinearMap.mem_range_self _ _

theorem msupp_map_le (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) ≤ (msupp T).map f := by
  rintro w ⟨φ, rfl⟩
  exact ⟨contract T (g.dualMap φ), mem_msupp _ _, (contract_map f g T φ).symm⟩

theorem msupp_map (f : V →ₗ[K] W) {g : X →ₗ[K] Y} (hg : Function.Injective g) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) = (msupp T).map f := by
  refine le_antisymm (msupp_map_le f g T) ?_
  rintro w ⟨v, ⟨ψ, rfl⟩, rfl⟩
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hg ψ
  exact ⟨φ, by rw [contract_map f g T φ, hφ]⟩

theorem dualTensorHom_injective [FiniteDimensional K X] :
    Function.Injective (dualTensorHom K (Module.Dual K X) V) := by
  classical
  exact (dualTensorHomEquivOfBasis (N := V)
    (Module.finBasis K (Module.Dual K X))).injective

theorem contract_eq_comp :
    (contract : V ⊗[K] X →ₗ[K] Module.Dual K X →ₗ[K] V) =
      (dualTensorHom K (Module.Dual K X) V) ∘ₗ
        (TensorProduct.map (Module.Dual.eval K X) (LinearMap.id : V →ₗ[K] V)) ∘ₗ
        (TensorProduct.comm K V X).toLinearMap := by
  refine TensorProduct.ext' fun v x => ?_
  ext φ
  simp [dualTensorHom_apply]

theorem contract_injective [FiniteDimensional K X] :
    Function.Injective (contract : V ⊗[K] X →ₗ[K] Module.Dual K X →ₗ[K] V) := by
  classical
  have hev : Function.Injective (Module.Dual.eval K X) := by
    have : (Module.evalEquiv K X).toLinearMap = Module.Dual.eval K X := rfl
    rw [← this]
    exact (Module.evalEquiv K X).injective
  have h2 : Function.Injective
      (TensorProduct.map (Module.Dual.eval K X) (LinearMap.id : V →ₗ[K] V)) :=
    TensorProduct.map_injective_of_flat_flat _ _ hev Function.injective_id
  rw [contract_eq_comp]
  intro a b hab
  exact (TensorProduct.comm K V X).injective
    (h2 (dualTensorHom_injective (V := V) (X := X) hab))

theorem eq_zero_of_msupp_eq_bot [FiniteDimensional K X] (T : V ⊗[K] X) (h : msupp T = ⊥) :
    T = 0 := by
  apply contract_injective (V := V) (X := X)
  ext φ
  have : contract T φ ∈ msupp T := mem_msupp T φ
  rw [h, Submodule.mem_bot] at this
  simpa using this

theorem map_eq_of_eqOn_msupp [FiniteDimensional K X] {Z : Type*} [AddCommGroup Z] [Module K Z]
    (T : V ⊗[K] X) (f f' : V →ₗ[K] W) (hff : ∀ v ∈ msupp T, f v = f' v) (h : X →ₗ[K] Z) :
    TensorProduct.map f h T = TensorProduct.map f' h T := by
  set e : V →ₗ[K] W := f - f' with he
  have hfe : f = f' + e := by rw [he]; abel
  have hzero : TensorProduct.map e (LinearMap.id : X →ₗ[K] X) T = 0 := by
    apply eq_zero_of_msupp_eq_bot (V := W) (X := X)
    refine le_antisymm ?_ bot_le
    rintro w ⟨φ, rfl⟩
    rw [contract_map e LinearMap.id T φ]
    have hmem : contract T (LinearMap.dualMap (LinearMap.id : X →ₗ[K] X) φ) ∈ msupp T :=
      mem_msupp _ _
    have := hff _ hmem
    simp only [he, LinearMap.sub_apply, Submodule.mem_bot]
    rw [this]
    abel
  have hsplit : TensorProduct.map e h T = 0 := by
    have : TensorProduct.map e h = (TensorProduct.map (LinearMap.id : W →ₗ[K] W) h) ∘ₗ
        TensorProduct.map e (LinearMap.id : X →ₗ[K] X) := by
      rw [← TensorProduct.map_comp]; simp
    rw [this]
    simp [LinearMap.comp_apply, hzero]
  rw [hfe, TensorProduct.map_add_left]
  simp [hsplit]

attribute [irreducible] contract msupp

end ModeSupport

section Braid

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ W₁ W₂ W₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]
  [AddCommGroup W₃] [Module K W₃]

noncomputable def braid2 (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) ≃ₗ[K] U₂ ⊗[K] (U₁ ⊗[K] U₃) :=
  (TensorProduct.assoc K U₁ U₂ U₃).symm ≪≫ₗ
    TensorProduct.congr (TensorProduct.comm K U₁ U₂) (LinearEquiv.refl K U₃) ≪≫ₗ
    TensorProduct.assoc K U₂ U₁ U₃

noncomputable def braid3 (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) ≃ₗ[K] U₃ ⊗[K] (U₁ ⊗[K] U₂) :=
  (TensorProduct.assoc K U₁ U₂ U₃).symm ≪≫ₗ TensorProduct.comm K (U₁ ⊗[K] U₂) U₃

theorem braid2_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid2 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) (braid2 K U₁ U₂ U₃ T) := by
  have : (braid2 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) ∘ₗ (braid2 K U₁ U₂ U₃).toLinearMap :=
    TensorProduct.ext_threefold' fun x y z => by simp [braid2]
  exact DFunLike.congr_fun this T

theorem braid3_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid3 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) (braid3 K U₁ U₂ U₃ T) := by
  have : (braid3 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) ∘ₗ (braid3 K U₁ U₂ U₃).toLinearMap :=
    TensorProduct.ext_threefold' fun x y z => by simp [braid3]
  exact DFunLike.congr_fun this T

/-- Mode supports of a three-tensor. -/
noncomputable def supp1 (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) : Submodule K U₁ := msupp T
noncomputable def supp2 (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) : Submodule K U₂ :=
  msupp (braid2 K U₁ U₂ U₃ T)
noncomputable def supp3 (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) : Submodule K U₃ :=
  msupp (braid3 K U₁ U₂ U₃ T)

theorem map3_comp {Z₁ Z₂ Z₃ : Type*} [AddCommGroup Z₁] [Module K Z₁] [AddCommGroup Z₂]
    [Module K Z₂] [AddCommGroup Z₃] [Module K Z₃]
    (a₁ : W₁ →ₗ[K] Z₁) (a₂ : W₂ →ₗ[K] Z₂) (a₃ : W₃ →ₗ[K] Z₃)
    (b₁ : U₁ →ₗ[K] W₁) (b₂ : U₂ →ₗ[K] W₂) (b₃ : U₃ →ₗ[K] W₃) (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    TensorProduct.map a₁ (TensorProduct.map a₂ a₃) (TensorProduct.map b₁ (TensorProduct.map b₂ b₃) T)
      = TensorProduct.map (a₁ ∘ₗ b₁) (TensorProduct.map (a₂ ∘ₗ b₂) (a₃ ∘ₗ b₃)) T := by
  rw [TensorProduct.map_comp, TensorProduct.map_comp]
  rfl

/-- Changing each mode map on the corresponding mode support does not change the image. -/
theorem map3_congr [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃]
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (a₁ b₁ : U₁ →ₗ[K] W₁) (a₂ b₂ : U₂ →ₗ[K] W₂) (a₃ b₃ : U₃ →ₗ[K] W₃)
    (h₁ : ∀ v ∈ supp1 T, a₁ v = b₁ v) (h₂ : ∀ v ∈ supp2 T, a₂ v = b₂ v)
    (h₃ : ∀ v ∈ supp3 T, a₃ v = b₃ v) :
    TensorProduct.map a₁ (TensorProduct.map a₂ a₃) T
      = TensorProduct.map b₁ (TensorProduct.map b₂ b₃) T := by
  have s1 : TensorProduct.map a₁ (TensorProduct.map a₂ a₃) T
      = TensorProduct.map b₁ (TensorProduct.map a₂ a₃) T :=
    map_eq_of_eqOn_msupp T a₁ b₁ h₁ _
  have s2 : TensorProduct.map b₁ (TensorProduct.map a₂ a₃) T
      = TensorProduct.map b₁ (TensorProduct.map b₂ a₃) T := by
    apply (braid2 K W₁ W₂ W₃).injective
    rw [braid2_map, braid2_map]
    exact map_eq_of_eqOn_msupp _ a₂ b₂ h₂ _
  have s3 : TensorProduct.map b₁ (TensorProduct.map b₂ a₃) T
      = TensorProduct.map b₁ (TensorProduct.map b₂ b₃) T := by
    apply (braid3 K W₁ W₂ W₃).injective
    rw [braid3_map, braid3_map]
    exact map_eq_of_eqOn_msupp _ a₃ b₃ h₃ _
  rw [s1, s2, s3]

theorem map3_injective {f₁ : U₁ →ₗ[K] W₁} {f₂ : U₂ →ₗ[K] W₂} {f₃ : U₃ →ₗ[K] W₃}
    (h₁ : Injective f₁) (h₂ : Injective f₂) (h₃ : Injective f₃) :
    Injective (TensorProduct.map f₁ (TensorProduct.map f₂ f₃)) :=
  TensorProduct.map_injective_of_flat_flat _ _ h₁
    (TensorProduct.map_injective_of_flat_flat _ _ h₂ h₃)

/-- Rigidity in mode 1: a transporter between padded tensors carries supports onto supports. -/
theorem rig1 {ι₁ : U₁ →ₗ[K] W₁} {ι₂ : U₂ →ₗ[K] W₂} {ι₃ : U₃ →ₗ[K] W₃}
    (hι₂ : Injective ι₂) (hι₃ : Injective ι₃)
    (P₁ : W₁ →ₗ[K] W₁) {P₂ : W₂ →ₗ[K] W₂} {P₃ : W₃ →ₗ[K] W₃}
    (hP₂ : Injective P₂) (hP₃ : Injective P₃) (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map P₁ (TensorProduct.map P₂ P₃)
        (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A)
      = TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    (supp1 A).map (P₁ ∘ₗ ι₁) = (supp1 B).map ι₁ := by
  have i23 : Injective (TensorProduct.map ι₂ ι₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃
  have p23 : Injective (TensorProduct.map P₂ P₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hP₂ hP₃
  have h1 := msupp_map P₁ p23 (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A)
  rw [hAB, msupp_map ι₁ i23 A, msupp_map ι₁ i23 B] at h1
  rw [Submodule.map_comp]
  exact h1.symm

theorem rig2 {ι₁ : U₁ →ₗ[K] W₁} {ι₂ : U₂ →ₗ[K] W₂} {ι₃ : U₃ →ₗ[K] W₃}
    (hι₁ : Injective ι₁) (hι₃ : Injective ι₃)
    {P₁ : W₁ →ₗ[K] W₁} (P₂ : W₂ →ₗ[K] W₂) {P₃ : W₃ →ₗ[K] W₃}
    (hP₁ : Injective P₁) (hP₃ : Injective P₃) (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map P₁ (TensorProduct.map P₂ P₃)
        (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A)
      = TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    (supp2 A).map (P₂ ∘ₗ ι₂) = (supp2 B).map ι₂ := by
  have h := congrArg (braid2 K W₁ W₂ W₃) hAB
  simp only [braid2_map] at h
  exact rig1 hι₁ hι₃ P₂ hP₁ hP₃ _ _ h

theorem rig3 {ι₁ : U₁ →ₗ[K] W₁} {ι₂ : U₂ →ₗ[K] W₂} {ι₃ : U₃ →ₗ[K] W₃}
    (hι₁ : Injective ι₁) (hι₂ : Injective ι₂)
    {P₁ : W₁ →ₗ[K] W₁} {P₂ : W₂ →ₗ[K] W₂} (P₃ : W₃ →ₗ[K] W₃)
    (hP₁ : Injective P₁) (hP₂ : Injective P₂) (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map P₁ (TensorProduct.map P₂ P₃)
        (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A)
      = TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    (supp3 A).map (P₃ ∘ₗ ι₃) = (supp3 B).map ι₃ := by
  have h := congrArg (braid3 K W₁ W₂ W₃) hAB
  simp only [braid3_map] at h
  exact rig1 hι₁ hι₂ P₃ hP₁ hP₂ _ _ h

end Braid

section Restrict

variable {K : Type*} [Field K]
variable {U H : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup H] [Module K H]

/-- The contragredient of a linear automorphism. -/
noncomputable def contra (P : H ≃ₗ[K] H) : Dual K H ≃ₗ[K] Dual K H := P.symm.dualMap

theorem contra_apply (P : H ≃ₗ[K] H) (φ : Dual K H) (x : H) : contra P φ x = φ (P.symm x) :=
  rfl

theorem coe_inj {M : Type*} [AddCommGroup M] [Module K M] (P : M ≃ₗ[K] M) :
    Injective (P : M →ₗ[K] M) :=
  P.injective

/-- A map carrying a subspace back into the image of `ι` restricts to an automorphism of `U`. -/
theorem exists_restrict_aut {ι : U →ₗ[K] H} (hι : Injective ι) {P : H →ₗ[K] H}
    (hP : Injective P) (p : Submodule K U) (hmaps : ∀ u ∈ p, P (ι u) ∈ LinearMap.range ι) :
    ∃ g : U ≃ₗ[K] U, ∀ u ∈ p, ι (g u) = P (ι u) := by
  let f : p →ₗ[K] U := (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range ι) ((P ∘ₗ ι) ∘ₗ p.subtype) (fun u => hmaps u u.2)
  have hfι : ∀ u : p, ι (f u) = P (ι u) := by
    intro u
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hf : Injective f := by
    intro x y hxy
    have : P (ι x) = P (ι y) := by rw [← hfι, ← hfι, hxy]
    exact Subtype.ext (hι (hP this))
  obtain ⟨F, hFinj, hF⟩ := exists_injective_extend rfl p f hf
  refine ⟨LinearEquiv.ofInjectiveEndo F hFinj, fun u hu => ?_⟩
  rw [LinearEquiv.coe_ofInjectiveEndo]
  exact (congrArg ι (hF ⟨u, hu⟩)).trans (hfι ⟨u, hu⟩)

/-- The dual version: one automorphism of `U` matches `P` on a subspace of `U` and the
contragredient of `P` on a subspace of `U*`. -/
theorem exists_restrict_aut_dual {ι : U →ₗ[K] H} (hι : Injective ι)
    {ιd : Dual K U →ₗ[K] Dual K H} (hιd : Injective ιd)
    (hpair : ∀ (β : Dual K U) (u : U), ιd β (ι u) = β u) (P : H ≃ₗ[K] H)
    (p : Submodule K U) (hmaps : ∀ u ∈ p, P (ι u) ∈ LinearMap.range ι)
    (q : Submodule K (Dual K U)) (hmapsd : ∀ α ∈ q, contra P (ιd α) ∈ LinearMap.range ιd) :
    ∃ g : U ≃ₗ[K] U, (∀ u ∈ p, ι (g u) = P (ι u)) ∧
      (∀ α ∈ q, ιd (contra g α) = contra P (ιd α)) := by
  let f : p →ₗ[K] U := (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range ι)
      ((P.toLinearMap ∘ₗ ι) ∘ₗ p.subtype) (fun u => hmaps u u.2)
  let h : q →ₗ[K] Dual K U := (LinearEquiv.ofInjective ιd hιd).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range ιd)
      (((contra P).toLinearMap ∘ₗ ιd) ∘ₗ q.subtype) (fun α => hmapsd α α.2)
  have hfι : ∀ u : p, ι (f u) = P (ι u) := by
    intro u
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hhι : ∀ α : q, ιd (h α) = contra P (ιd α) := by
    intro α
    simp only [h, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hf : Injective f := by
    intro x y hxy
    have : P (ι x) = P (ι y) := by rw [← hfι, ← hfι, hxy]
    exact Subtype.ext (hι (P.injective this))
  have hh : Injective h := by
    intro x y hxy
    have : contra P (ιd x) = contra P (ιd y) := by rw [← hhι, ← hhι, hxy]
    exact Subtype.ext (hιd ((contra P).injective this))
  have hpq : ∀ s : p, ∀ α : q, h α (f s) = (α : Dual K U) s := by
    intro s α
    rw [← hpair (h α) (f s), hhι, hfι, contra_apply, LinearEquiv.symm_apply_apply, hpair]
  obtain ⟨g, hgf, hgd⟩ := dual_support_extension p q f hf h hh hpq
  refine ⟨g, fun u hu => ?_, fun α hα => ?_⟩
  · exact (congrArg ι (hgf ⟨u, hu⟩)).trans (hfι ⟨u, hu⟩)
  · have hcg : contra g α = h ⟨α, hα⟩ := by
      ext v
      rw [contra_apply]
      have := hgd ⟨α, hα⟩ (g.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    rw [hcg, hhι]

end Restrict

section Levi

variable {K : Type*} [Field K]

section Pad

variable {U U' H : Type*} [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']
  [AddCommGroup H] [Module K H]

/-- `e : H ≃ U × U'` is a **GL-Levi section** of `G`: every automorphism `g` of `U` extends to an
element of `G` that is block diagonal for `H ≅ U × U'` with `g` as its first block. -/
def IsLeviSection (G : Subgroup (H ≃ₗ[K] H)) (e : H ≃ₗ[K] U × U') : Prop :=
  ∀ g : U ≃ₗ[K] U, ∃ g' : U' ≃ₗ[K] U', e ≪≫ₗ (g.prodCongr g') ≪≫ₗ e.symm ∈ G

/-- Covariant padding `U → H`. -/
noncomputable def pad (e : H ≃ₗ[K] U × U') : U →ₗ[K] H :=
  e.symm.toLinearMap ∘ₗ LinearMap.inl K U U'

/-- Contragredient padding `U* → H*`. -/
noncomputable def padD (e : H ≃ₗ[K] U × U') : Dual K U →ₗ[K] Dual K H :=
  (LinearMap.fst K U U' ∘ₗ e.toLinearMap).dualMap

theorem pad_injective (e : H ≃ₗ[K] U × U') : Injective (pad e) :=
  e.symm.injective.comp LinearMap.inl_injective

theorem padD_injective (e : H ≃ₗ[K] U × U') : Injective (padD e) := by
  apply LinearMap.dualMap_injective_of_surjective
  intro u
  exact ⟨e.symm (u, 0), by simp⟩

theorem padD_pad (e : H ≃ₗ[K] U × U') (β : Dual K U) (u : U) : padD e β (pad e u) = β u := by
  simp [padD, pad, LinearMap.dualMap_apply]

theorem levi_pad (e : H ≃ₗ[K] U × U') (g : U ≃ₗ[K] U) (g' : U' ≃ₗ[K] U') (u : U) :
    (e ≪≫ₗ (g.prodCongr g') ≪≫ₗ e.symm) (pad e u) = pad e (g u) := by
  simp [pad, LinearEquiv.prodCongr_apply]

theorem levi_padD (e : H ≃ₗ[K] U × U') (g : U ≃ₗ[K] U) (g' : U' ≃ₗ[K] U') (β : Dual K U) :
    contra (e ≪≫ₗ (g.prodCongr g') ≪≫ₗ e.symm) (padD e β) = padD e (contra g β) := by
  ext x
  simp [contra_apply, padD, LinearMap.dualMap_apply, LinearEquiv.prodCongr_symm,
    LinearEquiv.prodCongr_apply]

theorem levi_comp (e : H ≃ₗ[K] U × U') (g : U ≃ₗ[K] U) (g' : U' ≃ₗ[K] U') :
    ((e ≪≫ₗ (g.prodCongr g') ≪≫ₗ e.symm : H ≃ₗ[K] H) : H →ₗ[K] H) ∘ₗ pad e
      = pad e ∘ₗ (g : U →ₗ[K] U) :=
  LinearMap.ext (levi_pad e g g')

theorem levi_compD (e : H ≃ₗ[K] U × U') (g : U ≃ₗ[K] U) (g' : U' ≃ₗ[K] U') :
    ((contra (e ≪≫ₗ (g.prodCongr g') ≪≫ₗ e.symm) : Dual K H ≃ₗ[K] Dual K H) :
        Dual K H →ₗ[K] Dual K H) ∘ₗ padD e
      = padD e ∘ₗ ((contra g : Dual K U ≃ₗ[K] Dual K U) : Dual K U →ₗ[K] Dual K U) :=
  LinearMap.ext (levi_padD e g g')

/-- Mode-support images under a transporter stay inside the padding. -/
theorem maps_into_range {ι : U →ₗ[K] H} {P : H →ₗ[K] H} {p q : Submodule K U}
    (hpq : p.map (P ∘ₗ ι) = q.map ι) : ∀ u ∈ p, P (ι u) ∈ LinearMap.range ι := by
  intro u hu
  have : (P ∘ₗ ι) u ∈ p.map (P ∘ₗ ι) := Submodule.mem_map_of_mem hu
  rw [hpq] at this
  exact LinearMap.map_le_range this

theorem maps_into_range_sup {ι : U →ₗ[K] H} {P : H →ₗ[K] H} {p₁ p₂ q₁ q₂ : Submodule K U}
    (h₁ : p₁.map (P ∘ₗ ι) = q₁.map ι) (h₂ : p₂.map (P ∘ₗ ι) = q₂.map ι) :
    ∀ u ∈ p₁ ⊔ p₂, P (ι u) ∈ LinearMap.range ι := by
  intro u hu
  have : (P ∘ₗ ι) u ∈ (p₁ ⊔ p₂).map (P ∘ₗ ι) := Submodule.mem_map_of_mem hu
  rw [Submodule.map_sup, h₁, h₂] at this
  have hle : q₁.map ι ⊔ q₂.map ι ≤ LinearMap.range ι :=
    sup_le LinearMap.map_le_range LinearMap.map_le_range
  exact hle this

theorem maps_into_range_sup3 {ι : U →ₗ[K] H} {P : H →ₗ[K] H} {p₁ p₂ p₃ q₁ q₂ q₃ : Submodule K U}
    (h₁ : p₁.map (P ∘ₗ ι) = q₁.map ι) (h₂ : p₂.map (P ∘ₗ ι) = q₂.map ι)
    (h₃ : p₃.map (P ∘ₗ ι) = q₃.map ι) :
    ∀ u ∈ p₁ ⊔ p₂ ⊔ p₃, P (ι u) ∈ LinearMap.range ι := by
  intro u hu
  have : (P ∘ₗ ι) u ∈ (p₁ ⊔ p₂ ⊔ p₃).map (P ∘ₗ ι) := Submodule.mem_map_of_mem hu
  rw [Submodule.map_sup, Submodule.map_sup, h₁, h₂, h₃] at this
  have hle : q₁.map ι ⊔ q₂.map ι ⊔ q₃.map ι ≤ LinearMap.range ι :=
    sup_le (sup_le LinearMap.map_le_range LinearMap.map_le_range) LinearMap.map_le_range
  exact hle this

end Pad

/-! ### The five actions -/

variable {U U' H : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup U'] [Module K U'] [AddCommGroup H] [Module K H]
variable {W W' HW : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W'] [Module K W'] [AddCommGroup HW] [Module K HW]

/-- **Action (v)** `(P, P, P)` (trilinear forms). -/
theorem levi_reduction_v {G : Subgroup (H ≃ₗ[K] H)} {e : H ≃ₗ[K] U × U'}
    (hL : IsLeviSection G e) (A B : U ⊗[K] (U ⊗[K] U)) :
    (∃ g : U ≃ₗ[K] U, TensorProduct.map (g : U →ₗ[K] U)
        (TensorProduct.map (g : U →ₗ[K] U) (g : U →ₗ[K] U)) A = B) ↔
    (∃ P ∈ G, TensorProduct.map (P : H →ₗ[K] H)
        (TensorProduct.map (P : H →ₗ[K] H) (P : H →ₗ[K] H))
        (TensorProduct.map (pad e) (TensorProduct.map (pad e) (pad e)) A)
      = TensorProduct.map (pad e) (TensorProduct.map (pad e) (pad e)) B) := by
  have hι := pad_injective e
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := hL g
    refine ⟨_, hg', ?_⟩
    rw [map3_comp, map3_comp, levi_comp]
  · rintro ⟨P, -, hP⟩
    have r1 := rig1 hι hι (P : H →ₗ[K] H) (coe_inj P) (coe_inj P) A B hP
    have r2 := rig2 hι hι (P : H →ₗ[K] H) (coe_inj P) (coe_inj P) A B hP
    have r3 := rig3 hι hι (P : H →ₗ[K] H) (coe_inj P) (coe_inj P) A B hP
    obtain ⟨g, hg⟩ := exists_restrict_aut hι (coe_inj P) _ (maps_into_range_sup3 r1 r2 r3)
    refine ⟨g, map3_injective hι hι hι ?_⟩
    rw [← hP, map3_comp, map3_comp]
    refine map3_congr A _ _ _ _ _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · exact hg v (Submodule.mem_sup_left (Submodule.mem_sup_left hv))
    · exact hg v (Submodule.mem_sup_left (Submodule.mem_sup_right hv))
    · exact hg v (Submodule.mem_sup_right hv)

/-- **Action (ii)** `(P, P, Q)` (bilinear maps / matrix space isometry). -/
theorem levi_reduction_ii {G : Subgroup (H ≃ₗ[K] H)} {e : H ≃ₗ[K] U × U'}
    {GW : Subgroup (HW ≃ₗ[K] HW)} {eW : HW ≃ₗ[K] W × W'}
    (hL : IsLeviSection G e) (hLW : IsLeviSection GW eW) (A B : U ⊗[K] (U ⊗[K] W)) :
    (∃ g : U ≃ₗ[K] U, ∃ k : W ≃ₗ[K] W, TensorProduct.map (g : U →ₗ[K] U)
        (TensorProduct.map (g : U →ₗ[K] U) (k : W →ₗ[K] W)) A = B) ↔
    (∃ P ∈ G, ∃ Q ∈ GW, TensorProduct.map (P : H →ₗ[K] H)
        (TensorProduct.map (P : H →ₗ[K] H) (Q : HW →ₗ[K] HW))
        (TensorProduct.map (pad e) (TensorProduct.map (pad e) (pad eW)) A)
      = TensorProduct.map (pad e) (TensorProduct.map (pad e) (pad eW)) B) := by
  have hι := pad_injective e
  have hιW := pad_injective eW
  constructor
  · rintro ⟨g, k, rfl⟩
    obtain ⟨g', hg'⟩ := hL g
    obtain ⟨k', hk'⟩ := hLW k
    refine ⟨_, hg', _, hk', ?_⟩
    rw [map3_comp, map3_comp, levi_comp, levi_comp]
  · rintro ⟨P, -, Q, -, hP⟩
    have r1 := rig1 hι hιW (P : H →ₗ[K] H) (coe_inj P) (coe_inj Q) A B hP
    have r2 := rig2 hι hιW (P : H →ₗ[K] H) (coe_inj P) (coe_inj Q) A B hP
    have r3 := rig3 hι hι (Q : HW →ₗ[K] HW) (coe_inj P) (coe_inj P) A B hP
    obtain ⟨g, hg⟩ := exists_restrict_aut hι (coe_inj P) _ (maps_into_range_sup r1 r2)
    obtain ⟨k, hk⟩ := exists_restrict_aut hιW (coe_inj Q) _ (maps_into_range r3)
    refine ⟨g, k, map3_injective hι hι hιW ?_⟩
    rw [← hP, map3_comp, map3_comp]
    refine map3_congr A _ _ _ _ _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · exact hg v (Submodule.mem_sup_left hv)
    · exact hg v (Submodule.mem_sup_right hv)
    · exact hk v hv

/-- **Action (iii)** `(P, P⁻ᵀ, Q)` (matrix space conjugacy). -/
theorem levi_reduction_iii {G : Subgroup (H ≃ₗ[K] H)} {e : H ≃ₗ[K] U × U'}
    {GW : Subgroup (HW ≃ₗ[K] HW)} {eW : HW ≃ₗ[K] W × W'}
    (hL : IsLeviSection G e) (hLW : IsLeviSection GW eW) (A B : U ⊗[K] (Dual K U ⊗[K] W)) :
    (∃ g : U ≃ₗ[K] U, ∃ k : W ≃ₗ[K] W, TensorProduct.map (g : U →ₗ[K] U)
        (TensorProduct.map ((contra g : Dual K U ≃ₗ[K] Dual K U) : Dual K U →ₗ[K] Dual K U)
          (k : W →ₗ[K] W)) A = B) ↔
    (∃ P ∈ G, ∃ Q ∈ GW, TensorProduct.map (P : H →ₗ[K] H)
        (TensorProduct.map ((contra P : Dual K H ≃ₗ[K] Dual K H) : Dual K H →ₗ[K] Dual K H)
          (Q : HW →ₗ[K] HW))
        (TensorProduct.map (pad e) (TensorProduct.map (padD e) (pad eW)) A)
      = TensorProduct.map (pad e) (TensorProduct.map (padD e) (pad eW)) B) := by
  have hι := pad_injective e
  have hιd := padD_injective e
  have hιW := pad_injective eW
  constructor
  · rintro ⟨g, k, rfl⟩
    obtain ⟨g', hg'⟩ := hL g
    obtain ⟨k', hk'⟩ := hLW k
    refine ⟨_, hg', _, hk', ?_⟩
    rw [map3_comp, map3_comp, levi_comp, levi_compD, levi_comp]
  · rintro ⟨P, -, Q, -, hP⟩
    have r1 := rig1 hιd hιW (P : H →ₗ[K] H) (coe_inj (contra P)) (coe_inj Q) A B hP
    have r2 := rig2 hι hιW ((contra P : Dual K H ≃ₗ[K] Dual K H) : Dual K H →ₗ[K] Dual K H)
      (coe_inj P) (coe_inj Q) A B hP
    have r3 := rig3 hι hιd (Q : HW →ₗ[K] HW) (coe_inj P) (coe_inj (contra P)) A B hP
    obtain ⟨g, hg, hgd⟩ := exists_restrict_aut_dual hι hιd (padD_pad e) P _
      (maps_into_range r1) _ (maps_into_range r2)
    obtain ⟨k, hk⟩ := exists_restrict_aut hιW (coe_inj Q) _ (maps_into_range r3)
    refine ⟨g, k, map3_injective hι hιd hιW ?_⟩
    rw [← hP, map3_comp, map3_comp]
    refine map3_congr A _ _ _ _ _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · exact hg v hv
    · exact hgd v hv
    · exact hk v hv

/-- **Action (iv)** `(P, P, P⁻ᵀ)` (algebras). -/
theorem levi_reduction_iv {G : Subgroup (H ≃ₗ[K] H)} {e : H ≃ₗ[K] U × U'}
    (hL : IsLeviSection G e) (A B : U ⊗[K] (U ⊗[K] Dual K U)) :
    (∃ g : U ≃ₗ[K] U, TensorProduct.map (g : U →ₗ[K] U)
        (TensorProduct.map (g : U →ₗ[K] U)
          ((contra g : Dual K U ≃ₗ[K] Dual K U) : Dual K U →ₗ[K] Dual K U)) A = B) ↔
    (∃ P ∈ G, TensorProduct.map (P : H →ₗ[K] H)
        (TensorProduct.map (P : H →ₗ[K] H)
          ((contra P : Dual K H ≃ₗ[K] Dual K H) : Dual K H →ₗ[K] Dual K H))
        (TensorProduct.map (pad e) (TensorProduct.map (pad e) (padD e)) A)
      = TensorProduct.map (pad e) (TensorProduct.map (pad e) (padD e)) B) := by
  have hι := pad_injective e
  have hιd := padD_injective e
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := hL g
    refine ⟨_, hg', ?_⟩
    rw [map3_comp, map3_comp, levi_comp, levi_compD]
  · rintro ⟨P, -, hP⟩
    have r1 := rig1 hι hιd (P : H →ₗ[K] H) (coe_inj P) (coe_inj (contra P)) A B hP
    have r2 := rig2 hι hιd (P : H →ₗ[K] H) (coe_inj P) (coe_inj (contra P)) A B hP
    have r3 := rig3 hι hι ((contra P : Dual K H ≃ₗ[K] Dual K H) : Dual K H →ₗ[K] Dual K H)
      (coe_inj P) (coe_inj P) A B hP
    obtain ⟨g, hg, hgd⟩ := exists_restrict_aut_dual hι hιd (padD_pad e) P _
      (maps_into_range_sup r1 r2) _ (maps_into_range r3)
    refine ⟨g, map3_injective hι hι hιd ?_⟩
    rw [← hP, map3_comp, map3_comp]
    refine map3_congr A _ _ _ _ _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · exact hg v (Submodule.mem_sup_left hv)
    · exact hg v (Submodule.mem_sup_right hv)
    · exact hgd v hv

end Levi

section ActionI

variable {K : Type*} [Field K]
variable {U₁ U₁' H₁ U₂ U₂' H₂ U₃ U₃' H₃ : Type*}
  [AddCommGroup U₁] [Module K U₁] [FiniteDimensional K U₁] [AddCommGroup U₁'] [Module K U₁']
  [AddCommGroup H₁] [Module K H₁]
  [AddCommGroup U₂] [Module K U₂] [FiniteDimensional K U₂] [AddCommGroup U₂'] [Module K U₂']
  [AddCommGroup H₂] [Module K H₂]
  [AddCommGroup U₃] [Module K U₃] [FiniteDimensional K U₃] [AddCommGroup U₃'] [Module K U₃']
  [AddCommGroup H₃] [Module K H₃]

/-- **Action (i)** `(P, Q, R)` (plain three-tensor isomorphism). -/
theorem levi_reduction_i {G₁ : Subgroup (H₁ ≃ₗ[K] H₁)} {G₂ : Subgroup (H₂ ≃ₗ[K] H₂)}
    {G₃ : Subgroup (H₃ ≃ₗ[K] H₃)}
    {e₁ : H₁ ≃ₗ[K] U₁ × U₁'} {e₂ : H₂ ≃ₗ[K] U₂ × U₂'} {e₃ : H₃ ≃ₗ[K] U₃ × U₃'}
    (h₁ : IsLeviSection G₁ e₁) (h₂ : IsLeviSection G₂ e₂) (h₃ : IsLeviSection G₃ e₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ g₁ : U₁ ≃ₗ[K] U₁, ∃ g₂ : U₂ ≃ₗ[K] U₂, ∃ g₃ : U₃ ≃ₗ[K] U₃,
        TensorProduct.map (g₁ : U₁ →ₗ[K] U₁)
          (TensorProduct.map (g₂ : U₂ →ₗ[K] U₂) (g₃ : U₃ →ₗ[K] U₃)) A = B) ↔
    (∃ P₁ ∈ G₁, ∃ P₂ ∈ G₂, ∃ P₃ ∈ G₃, TensorProduct.map (P₁ : H₁ →ₗ[K] H₁)
        (TensorProduct.map (P₂ : H₂ →ₗ[K] H₂) (P₃ : H₃ →ₗ[K] H₃))
        (TensorProduct.map (pad e₁) (TensorProduct.map (pad e₂) (pad e₃)) A)
      = TensorProduct.map (pad e₁) (TensorProduct.map (pad e₂) (pad e₃)) B) := by
  have hι₁ := pad_injective e₁
  have hι₂ := pad_injective e₂
  have hι₃ := pad_injective e₃
  constructor
  · rintro ⟨g₁, g₂, g₃, rfl⟩
    obtain ⟨g₁', k₁⟩ := h₁ g₁
    obtain ⟨g₂', k₂⟩ := h₂ g₂
    obtain ⟨g₃', k₃⟩ := h₃ g₃
    refine ⟨_, k₁, _, k₂, _, k₃, ?_⟩
    rw [map3_comp, map3_comp, levi_comp, levi_comp, levi_comp]
  · rintro ⟨P₁, -, P₂, -, P₃, -, hP⟩
    have r1 := rig1 hι₂ hι₃ (P₁ : H₁ →ₗ[K] H₁) (coe_inj P₂) (coe_inj P₃) A B hP
    have r2 := rig2 hι₁ hι₃ (P₂ : H₂ →ₗ[K] H₂) (coe_inj P₁) (coe_inj P₃) A B hP
    have r3 := rig3 hι₁ hι₂ (P₃ : H₃ →ₗ[K] H₃) (coe_inj P₁) (coe_inj P₂) A B hP
    obtain ⟨g₁, hg₁⟩ := exists_restrict_aut hι₁ (coe_inj P₁) _ (maps_into_range r1)
    obtain ⟨g₂, hg₂⟩ := exists_restrict_aut hι₂ (coe_inj P₂) _ (maps_into_range r2)
    obtain ⟨g₃, hg₃⟩ := exists_restrict_aut hι₃ (coe_inj P₃) _ (maps_into_range r3)
    refine ⟨g₁, g₂, g₃, map3_injective hι₁ hι₂ hι₃ ?_⟩
    rw [← hP, map3_comp, map3_comp]
    exact map3_congr A _ _ _ _ _ _ (fun v hv => hg₁ v hv) (fun v hv => hg₂ v hv)
      (fun v hv => hg₃ v hv)

end ActionI

section SLInstance

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- **The hypothesis is inhabited.** For the special linear group of `U × K`, the identity
splitting is a GL-Levi section: extend `g` by `(det g)⁻¹` on the extra line. So Theorem S yields
`X_GL(U) ≤ X_SL(U × K)` for all five actions. -/
theorem sl_isLeviSection :
    IsLeviSection (LinearEquiv.det : ((U × K) ≃ₗ[K] (U × K)) →* Kˣ).ker
      (LinearEquiv.refl K (U × K)) := by
  intro g
  refine ⟨LinearEquiv.smulOfUnit (LinearEquiv.det g)⁻¹, ?_⟩
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_one]
  have hP : ((LinearEquiv.refl K (U × K) ≪≫ₗ
      (g.prodCongr (LinearEquiv.smulOfUnit (LinearEquiv.det g)⁻¹)) ≪≫ₗ
      (LinearEquiv.refl K (U × K)).symm : (U × K) ≃ₗ[K] (U × K)) : (U × K) →ₗ[K] (U × K))
      = LinearMap.prodMap (g : U →ₗ[K] U)
          ((((LinearEquiv.det g)⁻¹ : Kˣ) : K) • (LinearMap.id : K →ₗ[K] K)) := by
    apply LinearMap.ext
    intro x
    simp [LinearEquiv.smulOfUnit, Units.smul_def]
  rw [hP, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self,
    pow_one, mul_one, ← LinearEquiv.coe_det]
  exact Units.mul_inv _

end SLInstance

end LeviHardness
