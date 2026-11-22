import EvenP15TrialField
import Mathproof.Meta.P15GEInit20261007

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P15Trial

open EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def fieldVectorStart : String := "even_trial_field_vector_start"
def fieldVectorLength : String := "even_trial_field_vector_length"
def fieldVectorIndex : String := "even_trial_field_vector_index"

def fieldVectorAddress : Expr :=
  .add (.var qN.WS) (.mul (.add (.var fieldVectorStart) (.var fieldVectorIndex)) (.var canonical.e))

noncomputable def visitFieldVector (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.assign labelAddress fieldVectorAddress) <|
    .seq (emitFieldLabel D F) (.assign fieldVectorIndex (.add (.var fieldVectorIndex) (.lit 1)))

def fieldVectorGuard : Cond := .lt (.var fieldVectorIndex) (.var fieldVectorLength)

noncomputable def fieldVectorProgram (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.assign fieldVectorIndex (.lit 0)) (.while fieldVectorGuard (visitFieldVector D F))

structure EmitFieldVectorInv (F : FieldPresentation K) (σ τ : Env) (B S a m : ℕ)
    (digits : ℕ → ℕ) : Prop where
  slots : Slots F canonical qN.WS S B τ
  bound : τ.vars fieldVectorIndex ≤ m
  start : τ.vars fieldVectorStart=a
  limit : τ.vars fieldVectorLength=m
  array : τ.arrs=σ.arrs
  tape : τ.inp=σ.inp
  keep : ∀ r, r ≠ fieldVectorIndex → r ≠ labelAddress → τ.vars r=σ.vars r
  output : τ.out=σ.out++(List.range (τ.vars fieldVectorIndex)).map digits

/-- Append a live field vector in row-major order, using the canonical
field-encoding label for each entry regardless of the internal basis. -/
theorem fieldVectorProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S a m : ℕ} {σ : Env} (hSlots : Slots F canonical qN.WS S B σ)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hLarge : 1 < B)
    (hFit : a+m ≤ S) (hA : σ.vars fieldVectorStart=a) (hM : σ.vars fieldVectorLength=m) :
    ∃ τ, Run B (fieldVectorProgram D F) σ τ ((emitFieldLabelCost F+16)*m+6) ∧
      τ.out=σ.out++((List.range m).map fun i => (D (val F canonical qN.WS σ (a+i))).val) ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ ∀ r, r ≠ fieldVectorIndex → r ≠ labelAddress → τ.vars r=σ.vars r := by
  let digits := fun i : ℕ => (D (val F canonical qN.WS σ (a+i))).val
  let I (τ : Env) := EmitFieldVectorInv F σ τ B S a m digits
  let V := fun τ : Env => m-τ.vars fieldVectorIndex
  have hSB := hSlots.slots_word
  let σ₀ := σ.setVar fieldVectorIndex 0
  have r₀ : Run B (.assign fieldVectorIndex (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hInit : I σ₀ :=
    ⟨Slots.setVar F canonical hSlots (by decide) (by decide) _,
      by simp [σ₀],by simpa [σ₀,show fieldVectorStart ≠ fieldVectorIndex by decide] using hA,
      by simpa [σ₀,show fieldVectorLength ≠ fieldVectorIndex by decide] using hM,
      rfl,rfl,fun r h₁ _ => by simp [σ₀,h₁],by simp [σ₀]⟩
  have hGuard (τ : Env) (h : I τ) :
      fieldVectorGuard.evalB B τ = some (decide (τ.vars fieldVectorIndex < m)) := by
    apply evalB_condLt (evalB_var (by have := h.bound; omega))
    exact evalB_var_iff.mpr ⟨h.limit.symm,h.limit ▸ (by omega : m < B)⟩
  have hStep (τ : Env) (h : I τ) (hg : fieldVectorGuard.evalB B τ=some true) :
      ∃ v, Run B (visitFieldVector D F) τ v (emitFieldLabelCost F+12) ∧ I v ∧ V v < V τ := by
    rw [hGuard τ h] at hg
    let i := τ.vars fieldVectorIndex
    have hi : i < m := of_decide_eq_true (Option.some.inj hg)
    have ha : a+i < S := by omega
    let dst := τ.vars qN.WS+(a+i)*F.e
    have hN := h.slots.base.memory_word
    have hFit' := h.slots.fit
    have hAddr : dst < B := by
      have hd := Nat.mul_le_mul_right F.e (show a+i ≤ S from ha.le)
      dsimp [dst]
      omega
    have hAdd : (Expr.add (.var fieldVectorStart) (.var fieldVectorIndex)).evalB B τ=some (a+i) :=
      evalB_bin (op := .add) (evalB_var_iff.mpr ⟨h.start.symm,h.start ▸ (by omega : a < B)⟩)
        (evalB_var (by change i < B; omega)) (ha.trans hSB)
    have hDegree : F.e < B := by
      have hDeg : F.e ≤ S*F.e := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hm : (Expr.mul (.add (.var fieldVectorStart) (.var fieldVectorIndex))
        (.var canonical.e)).evalB B τ=some ((a+i)*F.e) :=
      evalB_bin (op := .mul) hAdd (evalB_var_iff.mpr ⟨h.slots.base.degree.symm,
        h.slots.base.degree ▸ hDegree⟩) (by change (a+i)*F.e < B; dsimp [dst] at hAddr; omega)
    have ev : fieldVectorAddress.evalB B τ=some dst :=
      evalB_bin (op := .add) (evalB_var (by dsimp [dst] at hAddr; omega)) hm hAddr
    let t := τ.setVar labelAddress dst
    have r₁ : Run B (.assign labelAddress fieldVectorAddress) τ t 8 := Run.assign ev
    have hS : Slots F canonical qN.WS S B t :=
      Slots.setVar F canonical h.slots (by decide) (by decide) _
    have hVal : val F canonical qN.WS t (a+i)=val F canonical qN.WS σ (a+i) := by
      unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
      rw [show t.arrs=τ.arrs from rfl,h.array,
        show t.vars qN.WS=τ.vars qN.WS from rfl,h.keep _ (by decide) (by decide)]
    let u := {t with out := t.out++[digits i]}
    have he : t.vars labelAddress=t.vars qN.WS+(a+i)*F.e := by rfl
    have r₂ : Run B (emitFieldLabel D F) t u (emitFieldLabelCost F) := by
      have hh := emitFieldLabel_run D F hS ha hQ hP he
      simpa only [hVal,u,digits] using hh
    let v := u.setVar fieldVectorIndex (i+1)
    have hUp : (Expr.add (.var fieldVectorIndex) (.lit 1)).evalB B u=some (i+1) :=
      evalB_bin (op := .add) (evalB_var (by change i < B; omega)) (evalB_lit hLarge)
        (by change i+1 < B; omega)
    have r₃ : Run B (.assign fieldVectorIndex (.add (.var fieldVectorIndex) (.lit 1))) u v 4 :=
      Run.assign hUp
    have huS : Slots F canonical qN.WS S B u := slots_frame F hS rfl rfl (fun _ _ => rfl) rfl
    refine ⟨v,(r₁.seq (r₂.seq r₃)).mono (by omega),
      ⟨Slots.setVar F canonical huS (by decide) (by decide) _,by simp [v]; omega,
        by simpa [v,u,t,show fieldVectorStart ≠ fieldVectorIndex by decide,show fieldVectorStart ≠ labelAddress by decide] using h.start,
        by simpa [v,u,t,show fieldVectorLength ≠ fieldVectorIndex by decide,show fieldVectorLength ≠ labelAddress by decide] using h.limit,
        h.array,h.tape,?_,?_⟩,?_⟩
    · intro r h₁ h₂
      simp [v,u,t,h₁,h₂,h.keep r h₁ h₂]
    · change τ.out++[digits i] = σ.out++(List.range (i+1)).map digits
      rw [h.output,show τ.vars fieldVectorIndex=i from rfl,List.range_succ,List.map_append]
      simp [List.append_assoc]
    · simp [V,v]
      omega
  obtain ⟨τ,hR,hI,hStop⟩ := Run.while_count I V (emitFieldLabelCost F+12)
    (fun t h => ⟨_,hGuard t h⟩) hStep hInit
  rw [hGuard τ hI] at hStop
  have hEnd : τ.vars fieldVectorIndex=m := Nat.le_antisymm hI.bound
    (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hStop)))
  refine ⟨τ,(r₀.seq hR).mono ?_,hI.output.trans ?_,hI.array,hI.tape,hI.keep⟩
  · change 2+((1+3+(emitFieldLabelCost F+12))*m+1+3) ≤ (emitFieldLabelCost F+16)*m+6
    rw [show 1+3+(emitFieldLabelCost F+12)=emitFieldLabelCost F+16 by omega]
    omega
  · rw [hEnd]

#print axioms fieldVectorProgram_run
end EvenTI.P15Trial
