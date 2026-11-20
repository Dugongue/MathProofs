import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Independent primal vectors and independent dual vectors with zero
pairings form one orbit, with both families indexed in their given order. -/
namespace Mathproof.EvenTI.Reciprocal.Sampling

open Module
open scoped BigOperators

noncomputable section

variable {K V V' W A D : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

private theorem align_independent [Finite A] {u : A → V} {v : A → V'}
    (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (hdim : finrank K V = finrank K V') :
    ∃ e : V ≃ₗ[K] V', ∀ i, e (u i) = v i := by
  classical
  letI := Fintype.ofFinite A
  let P := Submodule.span K (Set.range u)
  let Q := Submodule.span K (Set.range v)
  obtain ⟨P', hP'⟩ := P.exists_isCompl
  obtain ⟨Q', hQ'⟩ := Q.exists_isCompl
  have hP : finrank K P = Fintype.card A := finrank_span_eq_card hu
  have hQ : finrank K Q = Fintype.card A := finrank_span_eq_card hv
  have hPdim := Submodule.finrank_add_eq_of_isCompl hP'
  have hQdim := Submodule.finrank_add_eq_of_isCompl hQ'
  let e₁ : P ≃ₗ[K] Q := (Basis.span hu).equiv (Basis.span hv) (Equiv.refl A)
  let e₂ : P' ≃ₗ[K] Q' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let e := (P.prodEquivOfIsCompl P' hP').symm.trans
    ((e₁.prodCongr e₂).trans (Q.prodEquivOfIsCompl Q' hQ'))
  refine ⟨e, fun i => ?_⟩
  have hu' : ((Basis.span hu i : P) : V) = u i :=
    congrArg Subtype.val (Basis.span_apply hu i)
  have hsplit : (P.prodEquivOfIsCompl P' hP').symm (u i) = (Basis.span hu i, 0) :=
    hu' ▸ Submodule.prodEquivOfIsCompl_symm_apply_left P P' hP' (Basis.span hu i)
  change (Q.prodEquivOfIsCompl Q' hQ') ((e₁.prodCongr e₂)
    ((P.prodEquivOfIsCompl P' hP').symm (u i))) = v i
  rw [hsplit]
  change ↑(e₁ (Basis.span hu i)) + ↑(e₂ 0) = v i
  simp only [e₁, Basis.equiv_apply, Equiv.refl_apply, map_zero, Submodule.coe_zero, add_zero]
  exact congrArg Subtype.val (Basis.span_apply hv i)

def evalRows (d : D → Module.Dual K V) : V →ₗ[K] (D → K) := LinearMap.pi d

theorem evalRows_surjective (d : D → Module.Dual K V) (hd : LinearIndependent K d) :
    Function.Surjective (evalRows d) := by
  intro x
  let B := Basis.span hd
  let f := B.constr K x
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨(evalEquiv K V).symm g, ?_⟩
  funext j
  have h₁ : g (d j) = x j := by
    have h := LinearMap.congr_fun hg (B j)
    exact (show g (B j : Module.Dual K V) = f (B j) from h).trans (B.constr_basis K x j) |> fun hj => (congrArg g (congrArg Subtype.val (Basis.span_apply hd j))).symm.trans hj
  have h₂ := LinearMap.congr_fun ((evalEquiv K V).apply_symm_apply g) (d j)
  exact h₂.trans h₁

variable [AddCommGroup W] [Module K W]

private def splitSurjection (f : V →ₗ[K] W) (s : W →ₗ[K] V) (hs : f.comp s = LinearMap.id) :
    (f.ker × W) ≃ₗ[K] V where
  toFun x := x.1.val + s x.2
  invFun x := (⟨x - s (f x), by
    have h := LinearMap.congr_fun hs (f x)
    change f (s (f x)) = f x at h
    simp [h]⟩, f x)
  left_inv x := by
    rcases x with ⟨u, w⟩
    have h := LinearMap.congr_fun hs w
    change f (s w) = w at h
    apply Prod.ext
    · apply Subtype.ext
      have hu : f u.val = 0 := u.property
      simp [h, hu]
    · have hu : f u.val = 0 := u.property
      simp [h, hu]
  right_inv x := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    abel
  map_smul' c x := by simp [smul_add]

private theorem align_surjections [Finite A] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (g : V' →ₗ[K] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    {u : A → V} {v : A → V'} (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (hfu : ∀ i, f (u i) = 0) (hgv : ∀ i, g (v i) = 0)
    (hdim : finrank K V = finrank K V') :
    ∃ e : V ≃ₗ[K] V', (∀ i, e (u i) = v i) ∧ ∀ x, g (e x) = f x := by
  let u' : A → f.ker := fun i => ⟨u i, hfu i⟩
  let v' : A → g.ker := fun i => ⟨v i, hgv i⟩
  have hu' : LinearIndependent K u' := hu.of_comp f.ker.subtype
  have hv' : LinearIndependent K v' := hv.of_comp g.ker.subtype
  have hKf := f.finrank_range_add_finrank_ker
  have hKg := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hKf
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hKg
  obtain ⟨k, hk⟩ := align_independent hu' hv' (by omega)
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  obtain ⟨t, ht⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hmem (x : V) : x - s (f x) ∈ f.ker := by
    have hsx : f (s (f x)) = f x := LinearMap.congr_fun hs (f x)
    change f (x - s (f x)) = 0
    simp [hsx]
  let e := (splitSurjection f s hs).symm.trans
    ((k.prodCongr (LinearEquiv.refl K W)).trans (splitSurjection g t ht))
  refine ⟨e, ?_, ?_⟩
  · intro i
    change (k ⟨u i - s (f (u i)), hmem (u i)⟩).val + t (f (u i)) = v i
    have hsub : (⟨u i - s (f (u i)), hmem (u i)⟩ : f.ker) = u' i := by
      apply Subtype.ext
      simp [hfu, u']
    rw [hsub, hk]
    simp [hfu, v']
  · intro x
    change g ((k ⟨x - s (f x), hmem x⟩).val + t (f x)) = f x
    rw [map_add, show g (k ⟨x - s (f x), hmem x⟩).val = 0 from (k _).property, zero_add]
    exact LinearMap.congr_fun ht (f x)

/-- The joint selected row space is a single orbit for the natural action
on the primal space and the contragredient action on its dual. -/
theorem align_orthogonal_families [Finite A] [Fintype D]
    {u v : A → V} {d e : D → Module.Dual K V}
    (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (hd : LinearIndependent K d) (he : LinearIndependent K e)
    (hud : ∀ i j, d j (u i) = 0) (hve : ∀ i j, e j (v i) = 0) :
    ∃ f : V ≃ₗ[K] V, (∀ i, f (u i) = v i) ∧
      ∀ j, (e j).comp f.toLinearMap = d j := by
  obtain ⟨f, hf, h⟩ := align_surjections (evalRows d) (evalRows e)
    (evalRows_surjective d hd) (evalRows_surjective e he) hu hv
    (fun i => funext (hud i)) (fun i => funext (hve i)) rfl
  exact ⟨f, hf, fun j => LinearMap.ext (fun x => congrFun (h x) j)⟩

#print axioms evalRows_surjective
#print axioms align_orthogonal_families

end
end Mathproof.EvenTI.Reciprocal.Sampling
