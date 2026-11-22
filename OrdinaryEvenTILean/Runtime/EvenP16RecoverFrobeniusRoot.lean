import EvenP6CellsFixed
import Mathproof.Meta.P15RecogIMPRank20261007

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPIntertwinerScan20261001 (blockSize)
open Mathproof.P15RecogIMPRank20261007 (KQ kernelFramed_run)
open Mathproof.Problem18ClaudeIMPUniformBanks20261002 (uw)
open Mathproof.Problem18IMPKernelWitness20261001 (decoded)
open Mathproof.Problem18IMPUniformKernelFromMatrix20261002 (program budget)

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K] [Field A] [Algebra K A] {n : ℕ}

private def leftMultiply (u : A) : A →ₗ[K] A where
  toFun x := u*x
  map_add' x y := mul_add _ _ _
  map_smul' k x := by simp [Algebra.smul_def, mul_left_comm]

def frobeniusRootDifference (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  C.toLinearMap.comp (((FiniteField.frobeniusAlgHom K A).toLinearMap -
    leftMultiply (K := K) (u : A)).comp C.symm.toLinearMap)

def frobeniusRootMatrix (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' (frobeniusRootDifference C u)

/-- Frobenius root matrix construction uses one fixed q-power and one
multiplication on each stored algebra basis vector. -/
theorem frobeniusRootMatrix_entry (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ) (i j : Fin n) :
    frobeniusRootMatrix C u i j =
      C ((C.symm (Pi.single j 1))^Fintype.card K - (u : A)*C.symm (Pi.single j 1)) i := by
  rw [frobeniusRootMatrix,LinearMap.toMatrix'_apply]
  rfl

theorem frobeniusRoot_kernel_iff (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ) (x : Fin n → K) :
    (frobeniusRootMatrix C u).mulVec x = 0 ↔
      (C.symm x)^Fintype.card K = (u : A)*C.symm x := by
  rw [← Matrix.toLin'_apply, frobeniusRootMatrix, Matrix.toLin'_toMatrix']
  change C ((C.symm x)^Fintype.card K - (u : A)*C.symm x) = 0 ↔ _
  rw [← C.map_zero, C.injective.eq_iff, sub_eq_zero]

theorem frobeniusRoot_eq_unitPower (u : Aˣ) (x : A) (hx : x ≠ 0) :
    x^Fintype.card K = (u : A)*x ↔ Units.mk0 x hx ^ (Fintype.card K-1) = u := by
  have hp : Fintype.card K-1+1 = Fintype.card K := by
    have hq : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  constructor
  · intro h
    apply Units.ext
    change x^(Fintype.card K-1) = (u : A)
    apply mul_right_cancel₀ hx
    rw [←pow_succ,hp,h]
  · intro h
    have hh : x^(Fintype.card K-1) = (u : A) := congrArg Units.val h
    rw [←hp,pow_succ,hh]

/-- Recover a root from the kernel solver's actual column-major matrix.
The paid result either installs a nonzero root vector or reports exactly
that there is no root. In particular zero kernel and zero dimension are covered. -/
theorem frobeniusRoot_run (F : FieldPresentation K) (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ)
    {B S : ℕ} {s : Env}
    (hS : Slots F canonical KQ.WS S B s)
    (hRows : s.vars uw.nR=n) (hCols : s.vars uw.mR=n)
    (hCap : (n+1)*blockSize n n ≤ S)
    (hData : ∀ i j : Fin n, val F canonical KQ.WS s (5+j.val*n+i.val) = frobeniusRootMatrix C u i j) :
    ∃ t, Run B program s t (budget F n n) ∧ Slots F canonical KQ.WS S B t ∧
      (decoded F n n t = none ↔ ¬ ∃ a : Aˣ, a^(Fintype.card K-1)=u) ∧
      (∀ x, decoded F n n t = some x →
        ∃ hx : C.symm x ≠ 0, Units.mk0 (C.symm x) hx ^ (Fintype.card K-1) = u) ∧
      (∀ j < S, (n+1)*blockSize n n ≤ j → val F canonical KQ.WS t j = val F canonical KQ.WS s j) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,hr,ht,hnone,hsome,hKeep,hI,hO⟩ :=
    kernelFramed_run F (frobeniusRootMatrix C u) hS hRows hCols hCap hData
  have nonzero (x : Fin n → K) (hx : x ≠ 0) : C.symm x ≠ 0 := by
    intro h
    exact hx (C.symm.injective (h.trans C.symm.map_zero.symm))
  refine ⟨t,hr,ht,?_,?_,hKeep,hI,hO⟩
  · rw [hnone]
    constructor
    · rintro h ⟨a,ha⟩
      have he : Units.mk0 (a:A) a.ne_zero = a := Units.ext rfl
      have hh := (frobeniusRoot_eq_unitPower (K:=K) u (a:A) a.ne_zero).mpr (by rwa [he])
      have hv := (frobeniusRoot_kernel_iff C u (C (a:A))).mpr (by simpa only [C.symm_apply_apply] using hh)
      exact a.ne_zero (C.injective ((h _ hv).trans C.map_zero.symm))
    · intro h x hx
      by_contra hn
      have hn' := nonzero x hn
      exact h ⟨Units.mk0 (C.symm x) hn', (frobeniusRoot_eq_unitPower (K:=K) u _ hn').mp
        ((frobeniusRoot_kernel_iff C u x).mp hx)⟩
  · intro x hx
    obtain ⟨hn,hk⟩ := hsome x hx
    exact ⟨nonzero x hn, (frobeniusRoot_eq_unitPower (K:=K) u _ (nonzero x hn)).mp
      ((frobeniusRoot_kernel_iff C u x).mp hk)⟩

#print axioms frobeniusRootMatrix_entry
#print axioms frobeniusRoot_kernel_iff
#print axioms frobeniusRoot_eq_unitPower
#print axioms frobeniusRoot_run
end EvenTI.P16Recover
