import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Conditioning on the exact right and left flattening kernels leaves a
uniform square invertible coefficient matrix in bases of the induced spaces. -/
namespace Mathproof.EvenOrdinaryTISingular
open Module

noncomputable section

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

abbrev KernelRange (P : Submodule K V) (Q : Submodule K W) :=
  {f : V →ₗ[K] W // f.ker = P ∧ f.range = Q}

/-- Recover a flattening from its exact quotient-to-image isomorphism. -/
def fromKernelRangeEquiv (P : Submodule K V) (Q : Submodule K W)
    (e : (V ⧸ P) ≃ₗ[K] Q) : V →ₗ[K] W :=
  Q.subtype.comp (e.toLinearMap.comp P.mkQ)

theorem fromKernelRangeEquiv_ker (P : Submodule K V) (Q : Submodule K W)
    (e : (V ⧸ P) ≃ₗ[K] Q) : (fromKernelRangeEquiv P Q e).ker = P := by
  ext x
  conv_rhs => rw [← P.ker_mkQ]
  simp only [LinearMap.mem_ker]
  change ((e (P.mkQ x) : Q) : W) = 0 ↔ P.mkQ x = 0
  constructor
  · intro h
    apply e.injective
    rw [map_zero]
    exact Subtype.ext h
  · intro h
    rw [h, map_zero]
    rfl

theorem fromKernelRangeEquiv_range (P : Submodule K V) (Q : Submodule K W)
    (e : (V ⧸ P) ≃ₗ[K] Q) : (fromKernelRangeEquiv P Q e).range = Q := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (e (P.mkQ x)).property
  · intro hy
    obtain ⟨x, hx⟩ := P.mkQ_surjective (e.symm ⟨y, hy⟩)
    refine ⟨x, ?_⟩
    change ((e (P.mkQ x) : Q) : W) = y
    rw [hx, e.apply_symm_apply]

def toKernelRangeEquiv (P : Submodule K V) (Q : Submodule K W)
    (f : KernelRange P Q) : (V ⧸ P) ≃ₗ[K] Q := by
  obtain ⟨f, hP, hQ⟩ := f
  subst P
  subst Q
  exact f.quotKerEquivRange

theorem toKernelRangeEquiv_mk (P : Submodule K V) (Q : Submodule K W)
    (f : KernelRange P Q) (x : V) :
    ((toKernelRangeEquiv P Q f (P.mkQ x) : Q) : W) = f.val x := by
  obtain ⟨f, hP, hQ⟩ := f
  subst P
  subst Q
  exact f.quotKerEquivRange_apply_mk x

/-- Exact quotient coordinates, bijective on the entire conditioned fiber. -/
def kernelRangeEquiv (P : Submodule K V) (Q : Submodule K W) :
    KernelRange P Q ≃ ((V ⧸ P) ≃ₗ[K] Q) where
  toFun := toKernelRangeEquiv P Q
  invFun := fun e => ⟨fromKernelRangeEquiv P Q e,
    fromKernelRangeEquiv_ker P Q e, fromKernelRangeEquiv_range P Q e⟩
  left_inv := fun f => Subtype.ext (LinearMap.ext (toKernelRangeEquiv_mk P Q f))
  right_inv := by
    intro e
    apply LinearEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := P.mkQ_surjective z
    apply Subtype.ext
    exact toKernelRangeEquiv_mk P Q ⟨fromKernelRangeEquiv P Q e,
      fromKernelRangeEquiv_ker P Q e, fromKernelRangeEquiv_range P Q e⟩ x

abbrev TwoKernels (P : Submodule K V) (S : Submodule K (Module.Dual K W)) :=
  {f : V →ₗ[K] W // f.ker = P ∧ f.dualMap.ker = S}

/-- Pinning the exact dual kernel is equivalent to pinning the exact image. -/
theorem dualKernel_eq_iff_range_eq (f : V →ₗ[K] W) (Q : Submodule K W) :
    f.dualMap.ker = Q.dualAnnihilator ↔ f.range = Q := by
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, Subspace.dualAnnihilator_inj]

def twoKernelsEquiv (P : Submodule K V) (Q : Submodule K W) :
    TwoKernels P Q.dualAnnihilator ≃ KernelRange P Q :=
  Equiv.subtypeEquivRight (fun f => and_congr_right (fun _ => dualKernel_eq_iff_range_eq f Q))

/-- Exact rectangular spaces are converted to a square invertible coefficient matrix
when quotient and image have a common chosen coordinate size. -/
def twoKernelsGL (P : Submodule K V) (Q : Submodule K W) {s : ℕ}
    (eD : (V ⧸ P) ≃ₗ[K] (Fin s → K)) (eR : Q ≃ₗ[K] (Fin s → K)) :
    TwoKernels P Q.dualAnnihilator ≃ GL (Fin s) K :=
  let e : ((V ⧸ P) ≃ₗ[K] Q) ≃ ((Fin s → K) ≃ₗ[K] (Fin s → K)) :=
    { toFun := fun g => eD.symm.trans (g.trans eR)
      invFun := fun g => eD.trans (g.trans eR.symm)
      left_inv := by intro g; ext z; simp
      right_inv := by intro g; ext z; simp }
  (twoKernelsEquiv P Q).trans <| (kernelRangeEquiv P Q).trans <| e.trans
    (((Matrix.GeneralLinearGroup.toLin (n := Fin s) (R := K)).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin s → K)).toEquiv).symm)

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.kernelRangeEquiv
#print axioms Mathproof.EvenOrdinaryTISingular.dualKernel_eq_iff_range_eq
#print axioms Mathproof.EvenOrdinaryTISingular.twoKernelsGL
