import Mathlib

/-!
# Ordinary tensor isomorphism reduces to special-linear tensor isomorphism

Zero-padding doubles each mode and preserves and reflects equivalence over every
field. The coordinate projection has exactly eight times the input size.
-/

namespace JouxNarayanan54

open Matrix TensorProduct

section Definitions
universe u
variable {K : Type u} [Field K]

abbrev Tensor (K : Type u) (I : Type) := I × I × I → K
abbrev DoubleIndex (n : ℕ) := Fin n ⊕ Fin n

/-- Three independent changes of basis, one in each mode. -/
def action {I : Type} [Fintype I] (P Q R : Matrix I I K) (A : Tensor K I) :
    Tensor K I :=
  fun x => ∑ i, ∑ j, ∑ k, P x.1 i * Q x.2.1 j * R x.2.2 k * A (i, j, k)

/-- Ordinary tensor isomorphism. -/
def GLIsomorphic {I : Type} [Fintype I] [DecidableEq I] (A B : Tensor K I) : Prop :=
  ∃ P Q R : Matrix I I K,
    P.det ≠ 0 ∧ Q.det ≠ 0 ∧ R.det ≠ 0 ∧ action P Q R A = B

/-- Tensor isomorphism with determinant one in every mode. -/
def SLIsomorphic {I : Type} [Fintype I] [DecidableEq I] (A B : Tensor K I) : Prop :=
  ∃ P Q R : Matrix I I K,
    P.det = 1 ∧ Q.det = 1 ∧ R.det = 1 ∧ action P Q R A = B

/-- The actual reduction: retain the original corner and set all other entries to zero. -/
def pad {n : ℕ} (A : Tensor K (Fin n)) : Tensor K (DoubleIndex n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => A (i, j, k)
  | _ => 0

end Definitions

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

section Rigidity

variable {K : Type*} [Field K]
variable {U H X Y : Type*}
variable [AddCommGroup U] [Module K U] [AddCommGroup H] [Module K H]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem msupp_padded_rigidity
    (ι : U →ₗ[K] H) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    (g : H →ₗ[K] H) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B) :
    ((msupp A).map ι).map g = (msupp B).map ι := by
  have h1 := msupp_map g hk (TensorProduct.map ι j A)
  rw [msupp_map ι hj A] at h1
  rw [← h1, hAB, msupp_map ι hj B]

theorem pad_reflect [FiniteDimensional K U]
    {ι : U →ₗ[K] H} (hι : Function.Injective ι) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    {g : H →ₗ[K] H} (hg : Function.Injective g) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B) :
    ∃ P : U ≃ₗ[K] U, ∀ u ∈ msupp A, g (ι u) = ι (P u) := by
  have hrig := msupp_padded_rigidity ι hj g hk A B hAB
  set e : (msupp A) ≃ₗ[K] (msupp B) :=
    (Submodule.equivMapOfInjective ι hι (msupp A)) ≪≫ₗ
      (Submodule.equivMapOfInjective g hg ((msupp A).map ι)) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrig) ≪≫ₗ
      (Submodule.equivMapOfInjective ι hι (msupp B)).symm with he
  obtain ⟨P, hP⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P, fun u hu => ?_⟩
  have hcoe : ι ((e ⟨u, hu⟩ : msupp B) : U) = g (ι u) := by
    rw [he]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.map_equivMapOfInjective_symm_apply ι hι (msupp B)]
    simp [Submodule.coe_equivMapOfInjective_apply]
  rw [← hcoe, hP ⟨u, hu⟩]

theorem pad_substitute [FiniteDimensional K U] [FiniteDimensional K X]
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    {ι : U →ₗ[K] H} (hι : Function.Injective ι) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    {g : H →ₗ[K] H} (hg : Function.Injective g) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B)
    (m : X →ₗ[K] Z) :
    ∃ P : U ≃ₗ[K] U,
      TensorProduct.map (ι ∘ₗ (P : U →ₗ[K] U)) m A = TensorProduct.map (g ∘ₗ ι) m A := by
  obtain ⟨P, hP⟩ := pad_reflect hι hj hg hk A B hAB
  exact ⟨P, map_eq_of_eqOn_msupp A _ _ (fun u hu => (hP u hu).symm) m⟩

end Rigidity

section ThreeTensor

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ W₁ W₂ W₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]
  [AddCommGroup W₃] [Module K W₃]

noncomputable def glAct (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] U₁ ⊗[K] (U₂ ⊗[K] U₃) :=
  TensorProduct.map (P₁ : U₁ →ₗ[K] U₁)
    (TensorProduct.map (P₂ : U₂ →ₗ[K] U₂) (P₃ : U₃ →ₗ[K] U₃))

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

theorem braid2_natural (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃) :
    (braid2 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) ∘ₗ (braid2 K U₁ U₂ U₃).toLinearMap :=
  TensorProduct.ext_threefold' fun x y z => by simp [braid2]

theorem braid2_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid2 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) (braid2 K U₁ U₂ U₃ T) :=
  DFunLike.congr_fun (braid2_natural f₁ f₂ f₃) T

theorem braid3_natural (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃) :
    (braid3 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) ∘ₗ (braid3 K U₁ U₂ U₃).toLinearMap :=
  TensorProduct.ext_threefold' fun x y z => by simp [braid3]

theorem braid3_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid3 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) (braid3 K U₁ U₂ U₃ T) :=
  DFunLike.congr_fun (braid3_natural f₁ f₂ f₃) T

end ThreeTensor

section SupportCancellation

open TensorProduct

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ H₁ H₂ H₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup H₁] [Module K H₁] [AddCommGroup H₂] [Module K H₂]
  [AddCommGroup H₃] [Module K H₃]

noncomputable def padG (ι₁ : U₁ →ₗ[K] H₁) (ι₂ : U₂ →ₗ[K] H₂) (ι₃ : U₃ →ₗ[K] H₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] H₁ ⊗[K] (H₂ ⊗[K] H₃) :=
  TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)

theorem padG_injective {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃) :
    Function.Injective (padG ι₁ ι₂ ι₃) :=
  TensorProduct.map_injective_of_flat_flat _ _ hι₁
    (TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃)

theorem padG_mode1_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    ∃ P₁ : U₁ ≃ₗ[K] U₁,
      TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₂ ι₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃
  have hk : Function.Injective
      (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₂.injective g₃.injective
  exact pad_substitute (K := K) (U := U₁) (H := H₁) (X := U₂ ⊗[K] U₃) (Y := H₂ ⊗[K] H₃)
    (Z := H₂ ⊗[K] H₃) hι₁ hj g₁.injective hk A B hAB
    (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃))

theorem padG_mode2_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B)
    (m₁ : U₁ →ₗ[K] H₁) :
    ∃ P₂ : U₂ ≃ₗ[K] U₂,
      TensorProduct.map m₁
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂)) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map m₁
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₁ ι₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₁ hι₃
  have hk : Function.Injective
      (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₃ : H₃ →ₗ[K] H₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₃.injective
  have hAB₂ :
      TensorProduct.map (g₂ : H₂ →ₗ[K] H₂)
          (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₂ (TensorProduct.map ι₁ ι₃) (braid2 K U₁ U₂ U₃ A)) =
        TensorProduct.map ι₂ (TensorProduct.map ι₁ ι₃) (braid2 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid2 K H₁ H₂ H₃) hAB
    simpa only [braid2_map] using hb
  obtain ⟨P₂, hP₂⟩ :=
    pad_substitute (K := K) (U := U₂) (H := H₂) (X := U₁ ⊗[K] U₃) (Y := H₁ ⊗[K] H₃)
      (Z := H₁ ⊗[K] H₃) hι₂ hj g₂.injective hk
      (braid2 K U₁ U₂ U₃ A) (braid2 K U₁ U₂ U₃ B) hAB₂
      (TensorProduct.map m₁ ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃))
  refine ⟨P₂, ?_⟩
  apply (braid2 K H₁ H₂ H₃).injective
  rw [braid2_map, braid2_map]
  exact hP₂

theorem padG_mode3_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B)
    (m₁ : U₁ →ₗ[K] H₁) (m₂ : U₂ →ₗ[K] H₂) :
    ∃ P₃ : U₃ ≃ₗ[K] U₃,
      TensorProduct.map m₁ (TensorProduct.map m₂ (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A =
        TensorProduct.map m₁ (TensorProduct.map m₂ ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₁ ι₂) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₁ hι₂
  have hk : Function.Injective
      (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₂ : H₂ →ₗ[K] H₂)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₂.injective
  have hAB₃ :
      TensorProduct.map (g₃ : H₃ →ₗ[K] H₃)
          (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₂ : H₂ →ₗ[K] H₂))
          (TensorProduct.map ι₃ (TensorProduct.map ι₁ ι₂) (braid3 K U₁ U₂ U₃ A)) =
        TensorProduct.map ι₃ (TensorProduct.map ι₁ ι₂) (braid3 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid3 K H₁ H₂ H₃) hAB
    simpa only [braid3_map] using hb
  obtain ⟨P₃, hP₃⟩ :=
    pad_substitute (K := K) (U := U₃) (H := H₃) (X := U₁ ⊗[K] U₂) (Y := H₁ ⊗[K] H₂)
      (Z := H₁ ⊗[K] H₂) hι₃ hj g₃.injective hk
      (braid3 K U₁ U₂ U₃ A) (braid3 K U₁ U₂ U₃ B) hAB₃
      (TensorProduct.map m₁ m₂)
  refine ⟨P₃, ?_⟩
  apply (braid3 K H₁ H₂ H₃).injective
  rw [braid3_map, braid3_map]
  exact hP₃

theorem padG_cancel_substituted
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (h : TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    glAct P₁ P₂ P₃ A = B := by
  apply padG_injective hι₁ hι₂ hι₃
  have hnorm :
      (padG ι₁ ι₂ ι₃ : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] H₁ ⊗[K] (H₂ ⊗[K] H₃)) ∘ₗ
          glAct P₁ P₂ P₃ =
        TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) := by
    simp only [padG, glAct, ← TensorProduct.map_comp]
  calc
    padG ι₁ ι₂ ι₃ (glAct P₁ P₂ P₃ A) =
        TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A := by
      simpa only [LinearMap.comp_apply] using DFunLike.congr_fun hnorm A
    _ = padG ι₁ ι₂ ι₃ B := h

theorem gl_of_padded_general [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    ∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃),
      glAct P₁ P₂ P₃ A = B := by
  obtain ⟨P₁, h₁⟩ := padG_mode1_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
  obtain ⟨P₂, h₂⟩ := padG_mode2_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
    (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
  obtain ⟨P₃, h₃⟩ := padG_mode3_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
    (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁)) (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
  have h₀ :
      TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B := by
    have hnorm :
        (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
            (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))) ∘ₗ
            (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)) =
          TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
            (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂)
              ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) := by
      simp only [← TensorProduct.map_comp]
    have heval := DFunLike.congr_fun hnorm A
    simp only [LinearMap.comp_apply] at heval
    exact heval.symm.trans hAB
  exact ⟨P₁, P₂, P₃, padG_cancel_substituted hι₁ hι₂ hι₃ P₁ P₂ P₃ A B
    (h₃.trans (h₂.trans (h₁.trans h₀)))⟩

end SupportCancellation

section TensorCoordinates

open Matrix
open TensorProduct Module

universe u

variable {K : Type u} [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable abbrev e (ι : Type) [Fintype ι] [DecidableEq ι] : Module.Basis ι K (ι → K) :=
  Pi.basisFun K ι

noncomputable def tb (ι : Type) [Fintype ι] [DecidableEq ι] :
    Module.Basis (ι × ι × ι) K ((ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K))) :=
  (e ι).tensorProduct ((e ι).tensorProduct (e ι))

theorem tb_apply (i j k : ι) :
    tb ι (i, j, k) = (e ι i) ⊗ₜ[K] ((e ι j) ⊗ₜ[K] (e ι k)) := by
  simp [tb, Module.Basis.tensorProduct_apply]

noncomputable def toTensor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (ι × ι × ι → K) ≃ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  (Finsupp.linearEquivFunOnFinite K K (ι × ι × ι)).symm.trans (tb ι).repr.symm

theorem toTensor_apply (A : ι × ι × ι → K) :
    toTensor ι A = ∑ x, A x • tb ι x := by
  simp only [toTensor, LinearEquiv.trans_apply]
  rw [Module.Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply]
  simp [Finsupp.sum_fintype]

noncomputable def glActMat (P Q R : Matrix ι ι K) :
    (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) →ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  TensorProduct.map (Matrix.toLin' P) (TensorProduct.map (Matrix.toLin' Q) (Matrix.toLin' R))

theorem repr_toTensor (A : ι × ι × ι → K) (x : ι × ι × ι) :
    (tb ι).repr (toTensor ι A) x = A x := by
  simp [toTensor]

theorem repr_toLin'_basis (P : Matrix ι ι K) (i a : ι) :
    (e ι).repr (Matrix.toLin' P (e ι i)) a = P a i := by
  simp [Matrix.toLin'_apply, Pi.basisFun_apply]

theorem repr_glActMat_tb (P Q R : Matrix ι ι K) (i j k a b c : ι) :
    (tb ι).repr (glActMat P Q R (tb ι (i, j, k))) (a, b, c) = P a i * Q b j * R c k := by
  rw [tb_apply]
  simp only [glActMat, TensorProduct.map_tmul, tb]
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [repr_toLin'_basis, smul_eq_mul]
  ring

theorem toTensor_action (P Q R : Matrix ι ι K) (A : ι × ι × ι → K) :
    toTensor ι (action P Q R A) = glActMat P Q R (toTensor ι A) := by
  apply (tb ι).repr.injective
  ext ⟨a, b, c⟩
  rw [repr_toTensor]
  conv_rhs => rw [toTensor_apply, map_sum, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [action, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [repr_glActMat_tb]
  ring

noncomputable def linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) : (ι → K) ≃ₗ[K] (ι → K) :=
  Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P ((Matrix.isUnit_iff_isUnit_det P).mp hP))

theorem coe_linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) :
    (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' P :=
  Matrix.toLinearEquiv'_apply P _

theorem isUnit_toMatrix' (f : (ι → K) ≃ₗ[K] (ι → K)) :
    IsUnit (LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K))) := by
  have h₁ : LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) *
      LinearMap.toMatrix' (f.symm : (ι → K) →ₗ[K] (ι → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have h₂ : LinearMap.toMatrix' (f.symm : (ι → K) →ₗ[K] (ι → K)) *
      LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

theorem glAct_toTensor_iff (A B : ι × ι × ι → K) :
    (∃ P Q R : Matrix ι ι K, IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ action P Q R A = B) ↔
      ∃ (e₁ e₂ e₃ : (ι → K) ≃ₗ[K] (ι → K)), glAct e₁ e₂ e₃ (toTensor ι A) = toTensor ι B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    refine ⟨linEquivOfIsUnit P hP, linEquivOfIsUnit Q hQ, linEquivOfIsUnit R hR, ?_⟩
    rw [← h, toTensor_action]
    simp only [glAct, glActMat, coe_linEquivOfIsUnit]
  · rintro ⟨e₁, e₂, e₃, h⟩
    refine ⟨LinearMap.toMatrix' (e₁ : (ι → K) →ₗ[K] (ι → K)),
      LinearMap.toMatrix' (e₂ : (ι → K) →ₗ[K] (ι → K)),
      LinearMap.toMatrix' (e₃ : (ι → K) →ₗ[K] (ι → K)),
      isUnit_toMatrix' e₁, isUnit_toMatrix' e₂, isUnit_toMatrix' e₃, ?_⟩
    apply (toTensor ι).injective
    rw [toTensor_action, ← h]
    simp only [glAct, glActMat, Matrix.toLin'_toMatrix']

end TensorCoordinates

section Padding
universe u
variable {K : Type u} [Field K]

def inclusion {n : ℕ} : (Fin n → K) →ₗ[K] (DoubleIndex n → K) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

theorem inclusion_injective {n : ℕ} : Function.Injective (inclusion (K := K) (n := n)) := by
  intro v w h
  funext i
  exact congrFun h (Sum.inl i)

theorem inclusion_single {n : ℕ} (i : Fin n) :
    inclusion (Pi.single i (1 : K)) = Pi.single (Sum.inl i) 1 := by
  ext (j | j) <;> simp [inclusion, Pi.single_apply]

theorem toTensor_pad {n : ℕ} (A : Tensor K (Fin n)) :
    toTensor (DoubleIndex n) (pad A) =
      TensorProduct.map inclusion (TensorProduct.map inclusion inclusion)
        (toTensor (Fin n) A) := by
  simp [toTensor_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
    pad, tb_apply, inclusion_single]

noncomputable def liftMatrix {n : ℕ} (P : Matrix (Fin n) (Fin n) K) :
    Matrix (DoubleIndex n) (DoubleIndex n) K :=
  Matrix.fromBlocks P 0 0 P⁻¹ᵀ

theorem liftMatrix_det {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (hP : P.det ≠ 0) :
    (liftMatrix P).det = 1 := by
  unfold liftMatrix
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.mul_inverse_cancel _ (isUnit_iff_ne_zero.mpr hP)]

theorem action_lift_pad {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K)
    (A : Tensor K (Fin n)) :
    action (liftMatrix P) (liftMatrix Q) (liftMatrix R) (pad A) =
      pad (action P Q R A) := by
  funext x
  rcases x with ⟨i | i, j | j, k | k⟩ <;>
    simp [action, pad, liftMatrix, Fintype.sum_sum_type]

/-- Zero-padding preserves and reflects isomorphism, for arbitrary input tensors. -/
theorem padding_correct {n : ℕ} (A B : Tensor K (Fin n)) :
    GLIsomorphic A B ↔ SLIsomorphic (pad A) (pad B) := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    exact ⟨liftMatrix P, liftMatrix Q, liftMatrix R,
      liftMatrix_det P hP, liftMatrix_det Q hQ, liftMatrix_det R hR,
      (action_lift_pad P Q R A).trans (congrArg pad h)⟩
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    have unit_of_det_one : ∀ M : Matrix (DoubleIndex n) (DoubleIndex n) K,
        M.det = 1 → IsUnit M := fun M hM =>
      (Matrix.isUnit_iff_isUnit_det M).mpr (hM ▸ isUnit_one)
    obtain ⟨g₁, g₂, g₃, hg⟩ := (glAct_toTensor_iff (pad A) (pad B)).mp
      ⟨P, Q, R, unit_of_det_one P hP, unit_of_det_one Q hQ, unit_of_det_one R hR, h⟩
    rw [toTensor_pad, toTensor_pad] at hg
    obtain ⟨e₁, e₂, e₃, he⟩ := gl_of_padded_general
      inclusion_injective inclusion_injective inclusion_injective g₁ g₂ g₃
      (toTensor (Fin n) A) (toTensor (Fin n) B) hg
    obtain ⟨P', Q', R', hP', hQ', hR', h'⟩ :=
      (glAct_toTensor_iff A B).mpr ⟨e₁, e₂, e₃, he⟩
    exact ⟨P', Q', R', ((Matrix.isUnit_iff_isUnit_det P').mp hP').ne_zero,
      ((Matrix.isUnit_iff_isUnit_det Q').mp hQ').ne_zero,
      ((Matrix.isUnit_iff_isUnit_det R').mp hR').ne_zero, h'⟩

/-- No coordinates of the original tensor are lost. -/
theorem pad_injective (n : ℕ) : Function.Injective (pad (K := K) (n := n)) := by
  intro A B h
  funext ⟨i, j, k⟩
  exact congrFun h (Sum.inl i, Sum.inl j, Sum.inl k)

/-- Each mode doubles in dimension. -/
theorem output_dimension (n : ℕ) : Fintype.card (DoubleIndex n) = 2 * n := by
  simp [DoubleIndex, two_mul]

/-- Exact output size: eight times the input coordinate count. -/
theorem output_size (n : ℕ) :
    Fintype.card (DoubleIndex n × DoubleIndex n × DoubleIndex n) =
      8 * Fintype.card (Fin n × Fin n × Fin n) := by
  simp only [Fintype.card_prod, output_dimension, Fintype.card_fin]
  ring

/-- Finite coordinate-array problems. -/
structure CoordProblem (K : Type u) where
  Idx : ℕ → Type
  fin : ∀ n, Fintype (Idx n)
  Rel : ∀ n, (Idx n → K) → (Idx n → K) → Prop

attribute [instance] CoordProblem.fin

/-- A source coordinate or a zero constant. -/
def evaluateSource {I : Type} (A : I → K) : Option I → K
  | some i => A i
  | none => 0

/-- A polynomial-size coordinate projection, with its correctness certificate. -/
structure Projection (P Q : CoordProblem K) where
  size : ℕ → ℕ
  source : ∀ n, Q.Idx (size n) → Option (P.Idx n)
  polyBound : ∃ c k : ℕ, ∀ n,
    Fintype.card (Q.Idx (size n)) ≤ c * (Fintype.card (P.Idx n) + 1) ^ k
  correct : ∀ n (A B : P.Idx n → K), P.Rel n A B ↔
    Q.Rel (size n) (fun j => evaluateSource A (source n j))
      (fun j => evaluateSource B (source n j))

def GL3TI (K : Type u) [Field K] : CoordProblem K where
  Idx n := Fin n × Fin n × Fin n
  fin _ := inferInstance
  Rel _ := GLIsomorphic

def TISL (K : Type u) [Field K] : CoordProblem K where
  Idx n := DoubleIndex n × DoubleIndex n × DoubleIndex n
  fin _ := inferInstance
  Rel _ := SLIsomorphic

/-- The computable source map: copy the original corner and put zero elsewhere. -/
def paddingSource (n : ℕ) :
    DoubleIndex n × DoubleIndex n × DoubleIndex n → Option (Fin n × Fin n × Fin n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => some (i, j, k)
  | _ => none

theorem paddingSource_correct {n : ℕ} (A : Tensor K (Fin n)) :
    (fun x => evaluateSource A (paddingSource n x)) = pad A := by
  funext x
  rcases x with ⟨i | i, j | j, k | k⟩ <;> rfl

/-- The explicit polynomial-size GL-to-SL reduction. -/
def reduction : Projection (GL3TI K) (TISL K) where
  size := id
  source := paddingSource
  polyBound := by
    refine ⟨8, 1, fun n => ?_⟩
    change Fintype.card (DoubleIndex n × DoubleIndex n × DoubleIndex n) ≤
      8 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 1
    rw [output_size, pow_one]
    omega
  correct := by
    intro n A B
    dsimp [GL3TI, TISL] at A B ⊢
    rw [paddingSource_correct, paddingSource_correct]
    exact padding_correct A B

/-- Applying the reduction is exactly zero-padding. -/
theorem reduction_map {n : ℕ} (A : Tensor K (Fin n)) :
    (fun j => evaluateSource A ((reduction (K := K)).source n j)) = pad A :=
  paddingSource_correct A

/-- Joux--Narayanan Question 5.4, as a polynomial-size coordinate projection. -/
theorem question54 : Nonempty (Projection (GL3TI K) (TISL K)) := ⟨reduction⟩

/-- The explicit prime-field instance of the question. -/
theorem question54_prime (p : ℕ) [Fact p.Prime] {n : ℕ}
    (A B : Tensor (ZMod p) (Fin n)) :
    GLIsomorphic A B ↔ SLIsomorphic (pad A) (pad B) :=
  padding_correct A B

end Padding

end JouxNarayanan54

#print axioms JouxNarayanan54.padding_correct
#print axioms JouxNarayanan54.output_size
#print axioms JouxNarayanan54.question54
#print axioms JouxNarayanan54.question54_prime
