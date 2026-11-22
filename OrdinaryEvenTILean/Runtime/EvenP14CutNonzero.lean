import EvenP12ComparePrepCoeffDigits
import EvenNextKernelBank

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites arrayWrites run_frame noRead)

def cutZeroCursor : String := "even_compare_zero_cursor"
def cutNonzero : String := "even_compare_nonzero"

def cutNonzeroGuard : Cond := .lt (.var cutZeroCursor) (.var coeffLength)
def cutZeroTest (zero : ℕ) : Cond := .eq (.get coefficientBank (.var cutZeroCursor)) (.lit zero)
def cutSetNonzero (zero : ℕ) : Com := .ite (cutZeroTest zero) .skip (.assign cutNonzero (.lit 1))
def cutNonzeroBody (zero : ℕ) : Com := .seq (cutSetNonzero zero)
  (.assign cutZeroCursor (.add (.var cutZeroCursor) (.lit 1)))
def cutNonzeroProgram (zero : ℕ) : Com :=
  .seq (.assign cutZeroCursor (.lit 0)) (.seq (.assign cutNonzero (.lit 0))
    (.while cutNonzeroGuard (cutNonzeroBody zero)))

/-- This numeric scan tests the decoded coefficient digits against the actual
public label of zero. The field encoding may assign zero a nonzero label. -/
theorem cutNonzeroProgram_run (zero c B : ℕ) (σ : Env)
    (hB : 1 < B) (hc : c < B) (hz : zero < B) (hLive : σ.vars coeffLength = c)
    (hFit : c ≤ (σ.arrs coefficientBank).length)
    (hWords : ∀ i < c, (σ.arrs coefficientBank).getD i 0 < B) :
    ∃ τ, Run B (cutNonzeroProgram zero) σ τ (24*c+8) ∧
      τ.vars cutNonzero ≤ 1 ∧
      (τ.vars cutNonzero = 1 ↔ ∃ j < c, (σ.arrs coefficientBank).getD j 0 ≠ zero) ∧
      (∀ r, r ≠ cutZeroCursor → r ≠ cutNonzero → τ.vars r = σ.vars r) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let x := (σ.setVar cutZeroCursor 0).setVar cutNonzero 0
  let a j := (σ.arrs coefficientBank).getD j 0
  let I (s : Env) := s.vars cutZeroCursor ≤ c ∧ s.vars coeffLength = c ∧ s.arrs = σ.arrs ∧
    s.vars cutNonzero ≤ 1 ∧ (s.vars cutNonzero = 1 ↔ ∃ j < s.vars cutZeroCursor, a j ≠ zero)
  let V (s : Env) := c - s.vars cutZeroCursor
  have init₁ : Run B (.assign cutZeroCursor (.lit 0)) σ (σ.setVar cutZeroCursor 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have init₂ : Run B (.assign cutNonzero (.lit 0)) (σ.setVar cutZeroCursor 0) x 2 :=
    Run.assign (evalB_lit (by omega))
  have hEx : x.vars cutZeroCursor = 0 := by simp [x,cutZeroCursor,cutNonzero]
  have hInit : I x := by
    have hLen0 : x.vars coeffLength = c := by
      simpa only [x,vars_setVar,show coeffLength ≠ cutNonzero by decide,
        show coeffLength ≠ cutZeroCursor by decide,if_false] using hLive
    have hBit0 : x.vars cutNonzero = 0 := by simp [x]
    exact ⟨by rw [hEx]; omega,hLen0,rfl,by rw [hBit0]; omega,by simp [hEx,hBit0]⟩
  have g (s : Env) (hs : I s) : cutNonzeroGuard.evalB B s = some (decide (s.vars cutZeroCursor < c)) := by
    unfold cutNonzeroGuard
    simpa only [hs.2.1] using (evalB_condLt
      (evalB_var (σ := s) (x := cutZeroCursor) (hs.1.trans_lt hc))
      (evalB_var (σ := s) (x := coeffLength) (hs.2.1 ▸ hc)))
  have go (s : Env) (hs : I s) (hg : cutNonzeroGuard.evalB B s = some true) :
      ∃ t, Run B (cutNonzeroBody zero) s t 20 ∧ I t ∧ V t < V s := by
    let j := s.vars cutZeroCursor
    have hj : j < c := by rw [g s hs] at hg; simpa [j] using hg
    have hb : j < (σ.arrs coefficientBank).length := hj.trans_le hFit
    have eJ : (Expr.var cutZeroCursor).evalB B s = some j := evalB_var (hj.trans hc)
    have eg : (Expr.get coefficientBank (.var cutZeroCursor)).evalB B s = some (a j) := by
      apply evalB_get eJ _ (hWords _ hj)
      rw [hs.2.2.1,List.getElem?_eq_getElem hb,List.getD_eq_getElem _ _ hb]
    have e := evalB_condEq eg (evalB_lit (σ := s) hz)
    let y := if a j = zero then s else s.setVar cutNonzero 1
    have rBit : Run B (cutSetNonzero zero) s y 10 := by
      by_cases h : a j = zero
      · have ee : (cutZeroTest zero).evalB B s = some true := by simpa [cutZeroTest,h] using e
        simpa only [cutSetNonzero,y,if_pos h] using
          (Run.ite_true (d := .assign cutNonzero (.lit 1)) ee Run.skip).mono (by simp [cutZeroTest,Cond.size,Expr.size] : _ ≤ 10)
      · have ee : (cutZeroTest zero).evalB B s = some false := by simpa [cutZeroTest,h] using e
        simpa only [cutSetNonzero,y,if_neg h] using
          (Run.ite_false (c := .skip) ee (Run.assign (x := cutNonzero) (evalB_lit hB))).mono (by simp [cutZeroTest,Cond.size,Expr.size] : _ ≤ 10)
    have hyFix (r : String) (hr : r ≠ cutNonzero) : y.vars r = s.vars r := by
      by_cases h : a j = zero
      · rw [show y = s from if_pos h]
      · rw [show y = s.setVar cutNonzero 1 from if_neg h]
        simp [vars_setVar,hr]
    have hY : y.vars cutZeroCursor = j := hyFix _ (by decide)
    let t := y.setVar cutZeroCursor (j+1)
    have ec : (Expr.var cutZeroCursor).evalB B y = some j :=
      evalB_var_iff.mpr ⟨hY.symm,hY ▸ hj.trans hc⟩
    have rInc : Run B (.assign cutZeroCursor (.add (.var cutZeroCursor) (.lit 1))) y t 4 :=
      Run.assign (evalB_bin (op := .add) ec (evalB_lit hB) (by change j+1 < B; omega))
    have et : t.vars cutZeroCursor = j+1 := by simp [t]
    have hNew : (∃ i < j+1, a i ≠ zero) ↔ (∃ i < j, a i ≠ zero) ∨ a j ≠ zero := by
      constructor
      · rintro ⟨i,hi,hn⟩
        by_cases he : i=j
        · exact Or.inr (he ▸ hn)
        · exact Or.inl ⟨i,by omega,hn⟩
      · rintro (⟨i,hi,hn⟩ | hn)
        · exact ⟨i,by omega,hn⟩
        · exact ⟨j,by omega,hn⟩
    refine ⟨t,(rBit.seq rInc).mono (by decide),⟨by rw [et]; omega,?_,?_,?_,?_⟩,?_⟩
    · simpa only [t,vars_setVar,show coeffLength ≠ cutZeroCursor by decide,if_false] using
        (hyFix coeffLength (by decide)).trans hs.2.1
    · by_cases h : a j=zero <;> simpa [y,t,h] using hs.2.2.1
    · change (t.vars cutNonzero ≤ 1)
      simp only [t,vars_setVar,show cutNonzero ≠ cutZeroCursor by decide,if_false]
      by_cases h : a j = zero
      · rw [show y = s from if_pos h]
        exact hs.2.2.2.1
      · rw [show y = s.setVar cutNonzero 1 from if_neg h]
        simp
    · rw [et,hNew]
      simp only [t,vars_setVar,show cutNonzero ≠ cutZeroCursor by decide,if_false]
      by_cases h : a j = zero
      · rw [show y = s from if_pos h]
        have hf : ¬ (a j ≠ zero) := fun hn => hn h
        simp only [hf,or_false]
        exact hs.2.2.2.2
      · rw [show y = s.setVar cutNonzero 1 from if_neg h]
        simp [h]
    · change c-t.vars cutZeroCursor < c-j
      omega
  obtain ⟨τ,hr,ht,hEnd⟩ := Run.while_count I V 20 (fun s hs => ⟨_,g s hs⟩) go hInit
  have hNo : ¬ τ.vars cutZeroCursor < c := by rw [g τ ht] at hEnd; simpa using hEnd
  have htR : τ.vars cutZeroCursor = c := le_antisymm ht.1 (by omega)
  have hRun : Run B (cutNonzeroProgram zero) σ τ (24*c+8) :=
    (init₁.seq (init₂.seq hr)).mono (by simp [V,hEx,cutNonzeroGuard,Cond.size] <;> omega)
  have hFrame := run_frame hRun
  refine ⟨τ,hRun,ht.2.2.2.1,by simpa only [htR,a] using ht.2.2.2.2,?_,ht.2.2.1,?_,?_⟩
  · intro r h₁ h₂
    apply hFrame.1
    simp [cutNonzeroProgram,cutNonzeroBody,cutSetNonzero,scalarWrites,h₁,h₂]
  · apply hFrame.2.2.2.1
    simp [cutNonzeroProgram,cutNonzeroBody,cutSetNonzero,noRead]
  · apply hFrame.2.2.2.2
    simp [cutNonzeroProgram,cutNonzeroBody,cutSetNonzero,Com.NoWrite]

variable {K V W : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The exact physical coefficient test eliminates precisely the zero form.
The semantic bridge uses the checked equivalence of coordinates and the
kernel basis, without assuming zero's label is zero. -/
theorem indexedCombination_ne_zero_iff (D : FieldEncoding K) {c : ℕ}
    (v : Fin (Fintype.card K^c)) (f : V →ₗ[K] W) (basis : Fin c → V)
    (hInd : LinearIndependent K basis) (hSpan : Submodule.span K (Set.range basis) = f.ker) :
    (∑ j, coefficients D c v j • basis j) ≠ 0 ↔
      ∃ i : Fin c, coefficientLabel (Fintype.card K) v.val i.val ≠ (D 0).val := by
  let E := frameFromVectors f basis hInd hSpan
  rw [← frameFromVectors_apply f basis hInd hSpan]
  constructor
  · intro h
    by_contra hh
    have ha : coefficients D c v = 0 := by
      funext j
      apply D.injective
      apply Fin.ext
      rw [← coefficientLabel_eq D v j]
      exact not_ne_iff.mp (fun hj => hh ⟨j,hj⟩)
    apply h
    change (E (coefficients D c v)).val = 0
    simp [ha]
  · rintro ⟨j,hj⟩ h
    apply hj
    have he : E (coefficients D c v) = E 0 := by
      rw [map_zero]
      exact Subtype.ext h
    rw [coefficientLabel_eq, E.injective he]
    rfl

#print axioms cutNonzeroProgram_run
#print axioms indexedCombination_ne_zero_iff
end EvenTI.P12ComparePrep
