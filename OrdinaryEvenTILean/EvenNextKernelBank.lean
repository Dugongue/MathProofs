import EvenNextEnumeration
import Mathlib.LinearAlgebra.Basis.Basic

namespace EvenTI.Contract
open Module
open scoped BigOperators

variable {K : Type} [Field K] [Fintype K]

/-- Coefficient parametrization extracted from an independently certified
kernel basis. The basis data can come from the existing physical row reducer. -/
noncomputable def frameFromVectors {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {c : Nat}
    (f : V →ₗ[K] W) (xs : Fin c → V) (independent : LinearIndependent K xs)
    (spanKernel : Submodule.span K (Set.range xs) = f.ker) :
    (Fin c → K) ≃ₗ[K] f.ker :=
  (Basis.span independent).equivFun.symm.trans (LinearEquiv.ofEq _ _ spanKernel)

theorem frameFromVectors_apply {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {c : Nat}
    (f : V →ₗ[K] W) (xs : Fin c → V) (independent : LinearIndependent K xs)
    (spanKernel : Submodule.span K (Set.range xs) = f.ker) (a : Fin c → K) :
    (frameFromVectors f xs independent spanKernel a).val = ∑ i, a i • xs i := by
  change (Submodule.span K (Set.range xs)).subtype ((Basis.span independent).equivFun.symm a) = _
  simp [Basis.equivFun_symm_apply, Basis.span_apply]

/-- Straight-line coefficient combinations of supplied vectors. -/
def linearChoices {V : Type*} [AddCommGroup V] [Module K V] {c : Nat}
    (F : FieldEncoding K) (xs : Fin c → V) (budget : Nat) : List V :=
  (coefficientChoices F c budget).map fun a => ∑ i, a i • xs i

theorem linearChoices_eq_kernel {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {c : Nat} (F : FieldEncoding K)
    (f : V →ₗ[K] W) (xs : Fin c → V) (independent : LinearIndependent K xs)
    (spanKernel : Submodule.span K (Set.range xs) = f.ker) (budget : Nat) :
    linearChoices F xs budget = kernelChoices F f (frameFromVectors f xs independent spanKernel) budget := by
  unfold linearChoices kernelChoices
  congr 1
  funext a
  exact (frameFromVectors_apply f xs independent spanKernel a).symm

/-- Read the exact row-major basis representation emitted by the finite
kernel-basis routine, starting at its output address. -/
def readBasis {m c : Nat} (read : Nat → K) (offset : Nat) : Fin c → Fin m → K :=
  fun i j => read (offset + (i.val * m + j.val))

def bankKernelChoices {m c : Nat} (F : FieldEncoding K)
    (read : Nat → K) (offset budget : Nat) : List (Fin m → K) :=
  linearChoices F (readBasis (m := m) (c := c) read offset) budget

theorem mem_bankKernelChoices {m p c : Nat} (F : FieldEncoding K)
    (f : (Fin m → K) →ₗ[K] (Fin p → K))
    (read : Nat → K) (offset budget : Nat) (xs : Fin c → Fin m → K)
    (bank : ∀ i j, read (offset + (i.val * m + j.val)) = xs i j)
    (independent : LinearIndependent K xs)
    (spanKernel : Submodule.span K (Set.range xs) = f.ker) (v : Fin m → K) :
    v ∈ bankKernelChoices (c := c) F read offset budget ↔
      f v = 0 ∧ Fintype.card K ^ c ≤ budget := by
  have h : readBasis read offset = xs := funext fun i => funext (bank i)
  unfold bankKernelChoices
  rw [h, linearChoices_eq_kernel F f xs independent spanKernel]
  exact mem_kernelChoices F f _ budget v

#print axioms frameFromVectors_apply
#print axioms mem_bankKernelChoices

end EvenTI.Contract
