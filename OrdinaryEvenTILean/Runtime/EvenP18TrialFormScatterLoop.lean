import EvenP18TrialFormScatter

set_option autoImplicit false
set_option maxRecDepth 17500
set_option maxHeartbeats 750000

namespace EvenTI.P18Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P15Trial EvenTI.P16Trial EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

def publicFormLength : String := "even.trial.readback.length"

def publicFormGuard : Cond := .lt (.var publicFormCursor) (.var publicFormLength)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def scatterPublicFormStep (D : FieldEncoding K) (F : FieldPresentation K) (bank : String) : Com :=
  .seq (scatterPublicFormWord D F bank)
    (.assign publicFormCursor (.add (.var publicFormCursor) (.lit 1)))

noncomputable def scatterPublicForm (D : FieldEncoding K) (F : FieldPresentation K) (bank : String) : Com :=
  .seq (.assign publicFormCursor (.lit 0)) (.while publicFormGuard (scatterPublicFormStep D F bank))

noncomputable def scatterPublicFormCost (F : FieldPresentation K) (d m : ℕ) : ℕ :=
  (24*d+27+installEncodedDigitCost F)*m+6

/-- Read a literal public form from a capture bank, scatter every field
label into the native coordinate order and preserve every outside slot. -/
theorem scatterPublicForm_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n start dest : ℕ} {σ : Env} (bank : String) (hBank : bank≠canonical.mem)
    (form : Coord d n → K) (hn : 0<n) (hnB : n<B) (hdB : d<B) (hmB : n^d<B)
    (hQ : Fintype.card K≤B) (hFit : dest+n^d≤S) (hReadFit : start+n^d≤B)
    (hS : Slots F canonical qN.WS S B σ)
    (hStart : σ.vars publicFormStart=start) (hDest : σ.vars publicFormTarget=dest)
    (hLen : σ.vars publicFormLength=n^d)
    (hModes : σ.vars emitFormModes=d) (hRadix : σ.vars reverseDigitBase=n)
    (hRead : ∀ j : Fin (n^d), (σ.arrs bank)[start+j.val]?=
      some (D (form ((cutOrder d n).symm j))).val) :
    ∃ τ, Run B (scatterPublicForm D F bank) σ τ (scatterPublicFormCost F d (n^d)) ∧
      Slots F canonical qN.WS S B τ ∧
      (∀ x, val F canonical qN.WS τ (dest+(inputCoordOrder n d x).val)=form x) ∧
      (∀ k, k<dest ∨ dest+n^d≤k → val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      (∀ r, r≠publicFormCursor → r∉scatterScratch → τ.vars r=σ.vars r) ∧
      τ.arrs bank=σ.arrs bank ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  let m := n^d
  let addr : Fin m → ℕ := fun j => dest+(inputCoordOrder n d ((cutOrder d n).symm j)).val
  let C := 24*d+19+installEncodedDigitCost F
  let V (ρ : Env) := m-ρ.vars publicFormCursor
  let I (ρ : Env) :=
    Slots F canonical qN.WS S B ρ ∧ ρ.vars publicFormCursor ≤ m ∧
    (∀ j : Fin m, j.val<ρ.vars publicFormCursor →
      val F canonical qN.WS ρ (addr j)=form ((cutOrder d n).symm j)) ∧
    (∀ k, k<dest ∨ dest+m≤k → val F canonical qN.WS ρ k=val F canonical qN.WS σ k) ∧
    (∀ r, r≠publicFormCursor → r∉scatterScratch → ρ.vars r=σ.vars r) ∧
    ρ.arrs bank=σ.arrs bank ∧ ρ.inp=σ.inp ∧ ρ.out=σ.out
  let α := σ.setVar publicFormCursor 0
  have hZero : 0<B := by omega
  have h₀ : Run B (.assign publicFormCursor (.lit 0)) σ α 2 := Run.assign (evalB_lit hZero)
  have hInit : I α := by
    refine ⟨Slots.setVar F canonical hS (by decide) (by decide) 0,?_,?_,?_,?_,rfl,rfl,rfl⟩
    · change 0 ≤ m
      omega
    · intro j hj
      change j.val<0 at hj
      omega
    · intro k hk
      exact val_setVar F canonical (by decide) σ 0 k
    · intro r hr hMem
      simp [α,hr]
  have guard (ρ : Env) (h : I ρ) :
      publicFormGuard.evalB B ρ=some (decide (ρ.vars publicFormCursor < m)) := by
    exact evalB_condLt (evalB_var (h.2.1.trans_lt hmB))
      (ev_var ((h.2.2.2.2.1 _ (by decide) (by decide)).trans hLen) hmB)
  have step (ρ : Env) (h : I ρ) (hg : publicFormGuard.evalB B ρ=some true) :
      ∃ τ, Run B (scatterPublicFormStep D F bank) ρ τ (C+4) ∧ I τ ∧ V τ<V ρ := by
    rw [guard ρ h] at hg
    rcases h with ⟨hSρ,hCur,hDone,hOutside,hVars,hArr,hI,hO⟩
    let i := ρ.vars publicFormCursor
    have hi : i < m := of_decide_eq_true (Option.some.inj hg)
    let j : Fin m := ⟨i,hi⟩
    obtain ⟨β,r,hSβ,hVal,hMem,hKeep,hBankβ,hIβ,hOβ⟩ :=
      scatterPublicFormWord_run D F bank hBank form j hn hnB hdB hmB hQ hFit hSρ
        ((hVars _ (by decide) (by decide)).trans hStart)
        ((hVars _ (by decide) (by decide)).trans hDest) rfl
        ((hVars _ (by decide) (by decide)).trans hModes)
        ((hVars _ (by decide) (by decide)).trans hRadix)
        (by have := j.isLt; omega) (by rw [hArr]; exact hRead j)
    let τ := β.setVar publicFormCursor (i+1)
    have hCopy : β.vars publicFormCursor=i := hKeep _ (by decide)
    have r₁ : Run B (.assign publicFormCursor (.add (.var publicFormCursor) (.lit 1))) β τ 4 :=
      Run.assign (ev_add (ev_var hCopy (hi.trans hmB)) (evalB_lit (by omega)) (by omega))
    have hIdx : τ.vars publicFormCursor=i+1 := rfl
    have hv (k : ℕ) : val F canonical qN.WS τ k=val F canonical qN.WS β k :=
      val_setVar F canonical (by decide) β _ k
    refine ⟨τ,r.seq r₁,?_,?_⟩
    · refine ⟨Slots.setVar F canonical hSβ (by decide) (by decide) _,by rw [hIdx]; omega,
        ?_,?_,?_,hBankβ.trans hArr,hIβ.trans hI,hOβ.trans hO⟩
      · intro k hk
        rw [hIdx] at hk
        rw [hv]
        by_cases he : k=j
        · subst k
          exact hVal
        · have hNe : addr k≠addr j := by
            intro hEq
            apply he
            apply (cutOrder d n).symm.injective
            apply (inputCoordOrder n d).injective
            apply Fin.ext
            exact Nat.add_left_cancel hEq
          rw [hMem _ hNe]
          exact hDone k (by have : k.val ≠ i := fun ee => he (Fin.ext ee); omega)
      · intro k hk
        have hDestJ := (inputCoordOrder n d ((cutOrder d n).symm j)).isLt
        have hNe : k≠addr j := by
          dsimp only [addr]
          omega
        exact (hv _).trans ((hMem _ hNe).trans (hOutside _ hk))
      · intro r hr hf
        simpa only [τ,vars_setVar,if_neg hr] using (hKeep r hf).trans (hVars r hr hf)
    · change m-τ.vars publicFormCursor < m-ρ.vars publicFormCursor
      rw [hIdx,show ρ.vars publicFormCursor=i from rfl]
      omega
  obtain ⟨τ,r,hτ,hDone⟩ := Run.while_count I V (C+4)
    (fun ρ h => ⟨_,guard ρ h⟩) step hInit
  rw [guard τ hτ] at hDone
  rcases hτ with ⟨hSτ,hIdx,hInstalled,hOutside,hVars,hArr,hInp,hOut⟩
  have hCursor : τ.vars publicFormCursor=m :=
    le_antisymm hIdx (by have he := of_decide_eq_false (Option.some.inj hDone); omega)
  have hV : V α=m := rfl
  rw [hV] at r
  refine ⟨τ,(h₀.seq r).mono ?_,hSτ,?_,hOutside,hVars,hArr,hInp,hOut⟩
  · simp only [publicFormGuard,Cond.size,Expr.size,scatterPublicFormCost,C,m]
    have ht : 1+3+(24*d+19+installEncodedDigitCost F+4)=24*d+27+installEncodedDigitCost F := by omega
    rw [ht]
    omega
  · intro x
    have hX := hInstalled (cutOrder d n x) (by rw [hCursor]; exact (cutOrder d n x).isLt)
    simpa only [addr,Equiv.symm_apply_apply] using hX

#print axioms scatterPublicForm_run
end EvenTI.P18Trial


