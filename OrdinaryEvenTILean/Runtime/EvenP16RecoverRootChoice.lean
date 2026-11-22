import EvenP16RecoverFrobeniusRoot
import EvenP15RecoverPrefixCRT

set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPIntertwinerScan20261001 (blockSize)
open Mathproof.P15RecogIMPRank20261007 (KQ)
open Mathproof.Problem18ClaudeIMPUniformBanks20261002 (uw)
open Mathproof.Problem18IMPKernelWitness20261001 (decoded)
open Mathproof.Problem18EliminationKernelWitness20261001 (witness witness_none_iff witness_some)
open Mathproof.Problem18IMPUniformKernelFromMatrix20261002 (program budget kernel_from_matrix_run)

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K] [Field A] [DecidableEq A]
  [Algebra K A] {n : ℕ}

def decodeRootUnit (C : A ≃ₗ[K] (Fin n → K)) (x : Fin n → K) : Option Aˣ :=
  if h : C.symm x ≠ 0 then some (Units.mk0 (C.symm x) h) else none

/-- The deterministic root selector uses the same witness order as the
physical kernel command. -/
def frobeniusRootChoice (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ) : Option Aˣ :=
  (witness (frobeniusRootMatrix C u)).bind (decodeRootUnit C)

theorem frobeniusRootChoice_sound (C : A ≃ₗ[K] (Fin n → K)) (u a : Aˣ)
    (h : frobeniusRootChoice C u = some a) : a^(Fintype.card K-1)=u := by
  obtain ⟨x,hx,hd⟩ := Option.bind_eq_some_iff.mp h
  have hk := (witness_some (frobeniusRootMatrix C u) x hx).2
  unfold decodeRootUnit at hd
  split at hd
  · rename_i hn
    obtain rfl := Option.some.inj hd
    exact (frobeniusRoot_eq_unitPower (K:=K) u _ hn).mp ((frobeniusRoot_kernel_iff C u x).mp hk)
  · contradiction

theorem frobeniusRootChoice_complete (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ)
    (h : ∃ a : Aˣ, a^(Fintype.card K-1)=u) : (frobeniusRootChoice C u).isSome = true := by
  obtain ⟨a,ha⟩ := h
  have he : Units.mk0 (a:A) a.ne_zero = a := Units.ext rfl
  have hh := (frobeniusRoot_eq_unitPower (K:=K) u (a:A) a.ne_zero).mpr (by rwa [he])
  have hv := (frobeniusRoot_kernel_iff C u (C (a:A))).mpr (by simpa only [C.symm_apply_apply] using hh)
  unfold frobeniusRootChoice
  cases hW : witness (frobeniusRootMatrix C u) with
  | none =>
    have hZero := (witness_none_iff (frobeniusRootMatrix C u)).mp hW _ hv
    exact False.elim (a.ne_zero (C.injective (hZero.trans C.map_zero.symm)))
  | some x =>
    have hNZ := (witness_some (frobeniusRootMatrix C u) x hW).1
    have hZero : C.symm x ≠ 0 := fun h => hNZ (C.symm.injective (h.trans C.symm.map_zero.symm))
    simp only [Option.bind_some,decodeRootUnit,dif_pos hZero,Option.isSome_some]

/-- The physical program yields the exact reference-choice payload. The
field unit is a view of the nonzero kernel vector already stored. -/
theorem frobeniusRootChoice_run (F : FieldPresentation K) (C : A ≃ₗ[K] (Fin n → K)) (u : Aˣ)
    {B S : ℕ} {s : Env} (hS : Slots F canonical KQ.WS S B s)
    (hRows : s.vars uw.nR=n) (hCols : s.vars uw.mR=n)
    (hCap : (n+1)*blockSize n n ≤ S)
    (hData : ∀ i j : Fin n, val F canonical KQ.WS s (5+j.val*n+i.val)=frobeniusRootMatrix C u i j) :
    ∃ t, Run B program s t (budget F n n) ∧ Slots F canonical KQ.WS S B t ∧
      (decoded F n n t).bind (decodeRootUnit C) = frobeniusRootChoice C u ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,hr,ht,hW,hI,hO⟩ := kernel_from_matrix_run F (frobeniusRootMatrix C u) hS hRows hCols hCap hData
  exact ⟨t,hr,ht,by rw [hW, frobeniusRootChoice],hI,hO⟩

#print axioms frobeniusRootChoice_sound
#print axioms frobeniusRootChoice_complete
#print axioms frobeniusRootChoice_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open EvenTI.Part8 EvenTI.P15Recover EvenTI.CellPreparation EvenOrdinaryTI.LiveRows
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →ₐ[K] Y j)

local notation "V" => VarCount s t d
local notation "J" => RowCount t d
local notation "U" => ∀ v : Fin V, (physicalVarField X Y v)ˣ
local notation "H" => (Fintype.card K - 1)
local notation "eval" => (prefixEvaluation X Y orig emb)

variable (enum : Fin (Fintype.card K) ≃ K)
variable (views : ∀ r : Fin (RowCount t d), DenseFieldView (K := K) (physicalRowField Y r))
variable (rhs : ∀ j, (Y j)ˣ)

private theorem collectAt {n : ℕ} {A : Fin n → Type} (f : ∀ i, Option (A i)) (u : ∀ i, A i)
    (hu : collectSites f=some u) (i : Fin n) : f i=some (u i) := by
  unfold collectSites at hu
  split at hu
  · obtain rfl := Option.some.inj hu
    exact (Option.some_get _).symm
  · contradiction

theorem correctResidualCRT_preserves_power (u x : U)
    (hx : correctResidualCRT X Y orig emb enum views rhs u = some x) :
    ∀ v, x v^H = u v^H := by
  unfold correctResidualCRT at hx
  obtain ⟨L,_,h₁⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨rho,_,h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨z,_,rfl⟩ := Option.map_eq_some_iff.mp h₂
  intro v
  have hb : (L.decode (z v))^H = 1 := by
    apply Units.ext
    exact FiniteField.pow_card_sub_one_eq_one _ (L.decode (z v)).ne_zero
  have hc : (baseUnit (K:=K) (A:=physicalVarField X Y v) (L.decode (z v)))^H = 1 := by
    simp only [baseUnit,←map_pow,hb,map_one]
  change (u v * baseUnit (L.decode (z v)))^H = u v^H
  rw [mul_pow,hc,mul_one]

def finishChoosingRoots (roots : ∀ v : Fin V, Option ((physicalVarField X Y v)ˣ)) : Option U :=
  (collectSites roots).bind (correctResidualCRT X Y orig emb enum views rhs)

/-- Substituting any complete valid root selector preserves all successful
recovery attempts. Different field roots are absorbed by base CRT. -/
theorem finishChoosingRoots_covers (p : U)
    (roots₁ roots₂ : ∀ v : Fin V, Option ((physicalVarField X Y v)ˣ))
    (s₁ : ∀ v x, roots₁ v=some x → x^H=p v)
    (s₂ : ∀ v x, roots₂ v=some x → x^H=p v)
    (c₂ : ∀ v, (∃ x : (physicalVarField X Y v)ˣ, x^H=p v) → (roots₂ v).isSome=true)
    (h : (finishChoosingRoots X Y orig emb enum views rhs roots₁).isSome=true) :
    (finishChoosingRoots X Y orig emb enum views rhs roots₂).isSome=true := by
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨u,hU,hx'⟩ := Option.bind_eq_some_iff.mp hx
  have hU' (v : Fin V) : u v^H=p v := s₁ v _ (collectAt roots₁ u hU v)
  have he (v : Fin V) : ∃ w, roots₂ v=some w := Option.isSome_iff_exists.mp (c₂ v ⟨u v,hU' v⟩)
  choose w hw using he
  have hEval := correctResidualCRT_sound X Y orig emb enum views rhs u x hx'
  have hPow := correctResidualCRT_preserves_power X Y orig emb enum views rhs u x hx'
  have hPw (v : Fin V) : w v^H=x v^H := (s₂ v _ (hw v)).trans ((hPow v).trans (hU' v)).symm
  obtain ⟨y,hy,_⟩ := correctBaseResidual_of_powers X Y orig emb enum views rhs w x hEval hPw
  have hNew := correctResidualCRT_available X Y orig emb enum views rhs w
  rw [hy] at hNew
  unfold finishChoosingRoots
  rw [collectSites_some roots₂ w hw,Option.bind_some]
  exact hNew

/-- Every successful output from the new root selector obeys the original
signed prefix equations. -/
theorem finishChoosingRoots_sound (roots : ∀ v : Fin V, Option ((physicalVarField X Y v)ˣ))
    (x : U) (hx : finishChoosingRoots X Y orig emb enum views rhs roots=some x) :
    eval x=physicalRHS Y rhs := by
  obtain ⟨u,_,hu⟩ := Option.bind_eq_some_iff.mp hx
  exact correctResidualCRT_sound X Y orig emb enum views rhs u x hu

#print axioms correctResidualCRT_preserves_power
#print axioms finishChoosingRoots_covers
#print axioms finishChoosingRoots_sound
end EvenTI.P16Recover
