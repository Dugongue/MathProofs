import EvenP1LawOrbit
import EvenP1LawMatrix
import Mathlib.SetTheory.Cardinal.Finite

namespace Mathproof.EvenTI.Reciprocal.Sampling

open Module
open scoped BigOperators

noncomputable section

variable {K V R A D : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev PrimalRows (K A V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {u : A → V // LinearIndependent K u}

abbrev rowAnnihilator (u : A → V) : Submodule K (Module.Dual K V) :=
  (Submodule.span K (Set.range u)).dualAnnihilator

abbrev DualRows (u : A → V) (D : Type*) :=
  {d : D → rowAnnihilator (K := K) u // LinearIndependent K d}

abbrev RowSample (K A D V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  Σ u : PrimalRows K A V, DualRows (K := K) u.val D

private theorem rowSample_ext {x y : RowSample K A D V}
    (hU : x.1.val = y.1.val) (hD : ∀ j, (x.2.val j).val = (y.2.val j).val) :
    x = y := by
  obtain ⟨u, d⟩ := x
  obtain ⟨v, e⟩ := y
  have h : u = v := Subtype.ext hU
  subst v
  congr 1
  apply Subtype.ext
  funext j
  exact Subtype.ext (hD j)

variable [Fintype R] [DecidableEq R]

def selectBasisRows (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    (b : Basis R K V) : RowSample K A D V := by
  let u : PrimalRows K A V := ⟨fun i => b (p i), b.linearIndependent.comp _ p.injective⟩
  let e (j : D) : rowAnnihilator (K := K) u.val :=
    ⟨b.dualBasis (d j), (Submodule.mem_dualAnnihilator _).mpr fun w hw => by
      have hφ : Submodule.span K (Set.range u.val) ≤ (b.dualBasis (d j)).ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        change b.dualBasis (d j) (b (p i)) = 0
        rw [Basis.dualBasis_apply_self]
        simp [dis i j, Ne.symm (dis i j)]
      exact hφ hw⟩
  refine ⟨u, ⟨e, ?_⟩⟩
  apply LinearIndependent.of_comp (rowAnnihilator (K := K) u.val).subtype
  exact b.dualBasis.linearIndependent.comp _ d.injective

private def mapBasis (f : V ≃ₗ[K] V) : Basis R K V ≃ Basis R K V where
  toFun b := b.map f
  invFun b := b.map f.symm
  left_inv b := DFunLike.ext _ _ fun i => by simp only [Basis.map_apply, LinearEquiv.symm_apply_apply]
  right_inv b := DFunLike.ext _ _ fun i => by simp only [Basis.map_apply, LinearEquiv.apply_symm_apply]

private theorem mapBasis_select_eq (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    {x y : RowSample K A D V}
    (f : V ≃ₗ[K] V) (hU : ∀ i, f (x.1.val i) = y.1.val i)
    (hD : ∀ j, ((y.2.val j).val).comp f.toLinearMap = (x.2.val j).val)
    (b : Basis R K V) (hx : selectBasisRows p d dis b = x) :
    selectBasisRows p d dis (b.map f) = y := by
  apply rowSample_ext
  · funext i
    change f (b (p i)) = y.1.val i
    have h := congrArg (fun z : RowSample K A D V => z.1.val i) hx
    change b (p i) = x.1.val i at h
    rw [h, hU]
  · intro j
    apply LinearMap.ext
    intro v
    have h := congrArg (fun z : RowSample K A D V => (z.2.val j).val) hx
    change b.dualBasis (d j) = (x.2.val j).val at h
    change (b.map f).dualBasis (d j) v = _
    calc
      _ = b.dualBasis (d j) (f.symm v) := by
        simp only [Basis.dualBasis_apply, Basis.map_repr, LinearEquiv.trans_apply]
      _ = _ := by
        rw [h]
        have h' := LinearMap.congr_fun (hD j) (f.symm v)
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h'.symm

variable [FiniteDimensional K V] [Finite A] [Fintype D]

private theorem independent_coe {W : Type*} [AddCommGroup W] [Module K W] (S : Submodule K W)
    (d : D → S) (h : LinearIndependent K d) :
    LinearIndependent K (fun i => (d i).val) := h.map' S.subtype S.ker_subtype

set_option maxHeartbeats 1000000 in
/-- All legal two-sided lists admit the same number of reciprocal completions. -/
def selectedBasisFibersEquiv (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    (x y : RowSample K A D V) :
    {b : Basis R K V // selectBasisRows p d dis b = x} ≃
    {b : Basis R K V // selectBasisRows p d dis b = y} := by
  classical
  let dx : D → Module.Dual K V := fun j => (x.2.val j).val
  let dy : D → Module.Dual K V := fun j => (y.2.val j).val
  have hx : LinearIndependent K dx := by
    change LinearIndependent K ((rowAnnihilator (K := K) x.1.val).subtype ∘ x.2.val)
    exact independent_coe (rowAnnihilator (K := K) x.1.val) x.2.val x.2.property
  have hy : LinearIndependent K dy := by
    change LinearIndependent K ((rowAnnihilator (K := K) y.1.val).subtype ∘ y.2.val)
    exact independent_coe (rowAnnihilator (K := K) y.1.val) y.2.val y.2.property
  have orth (z : RowSample K A D V) (i : A) (j : D) :
      ((z.2.val j).val) (z.1.val i) = 0 :=
    (Submodule.mem_dualAnnihilator _).mp (z.2.val j).property _
      (Submodule.subset_span ⟨i, rfl⟩)
  let h := align_orthogonal_families x.1.property y.1.property hx hy (orth x) (orth y)
  let f := Classical.choose h
  have hf := Classical.choose_spec h
  have hinvU (i : A) : f.symm (y.1.val i) = x.1.val i := by rw [← hf.1 i, f.symm_apply_apply]
  have hinvD (j : D) : ((x.2.val j).val).comp f.symm.toLinearMap = (y.2.val j).val := by
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun (hf.2 j) (f.symm v)
    change (dy j) (f (f.symm v)) = (dx j) (f.symm v) at hv
    rw [f.apply_symm_apply] at hv
    exact hv.symm
  exact Equiv.subtypeEquiv (mapBasis f) fun b => ⟨mapBasis_select_eq p d dis f hf.1 hf.2 b, by
    intro hb
    have hm := mapBasis_select_eq p d dis f.symm hinvU hinvD (b.map f) hb
    change selectBasisRows p d dis ((mapBasis f).symm ((mapBasis f) b)) = x at hm
    simpa only [Equiv.symm_apply_apply] using hm⟩

#print axioms selectedBasisFibersEquiv

end
end Mathproof.EvenTI.Reciprocal.Sampling
