import EvenP15ScalarMatrix

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 1500000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.P12CountPre (sentinelWords)
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites noRead run_frame)

def modeCursor : String := "even.scalar.mode.cursor"
def modeLimit : String := "even.scalar.mode.limit"
def modeAnswer : String := "even.scalar.mode.answer"

def modeReset : Com :=
  .seq (.assign "index" (.lit 0))
    (.seq (.assign "good" (.lit 1)) (.assign "diag" (.get "data" (.var "base"))))

def modeKeep : Com :=
  .ite (.eq (.var "good") (.lit 1)) .skip (.assign modeAnswer (.lit 0))

def modeAdvance : Com :=
  .seq (.assign "base" (.add (.var "base") (.var "count")))
    (.assign modeCursor (.add (.var modeCursor) (.lit 1)))

def modeBody (zeroDigit : ℕ) : Com :=
  .seq modeReset (.seq (scalarMatrixScan zeroDigit) (.seq modeKeep modeAdvance))

def modeGuard : Cond := .lt (.var modeCursor) (.var modeLimit)
def scalarModeLoop (zeroDigit : ℕ) : Com := .while modeGuard (modeBody zeroDigit)

theorem scalarWrittenBound {B k : ℕ} {c : Com} {s t : Env} (r : String)
    (h : BigStepB B c s t k) : noRead c → s.vars r < B → t.vars r < B := by
  induction h with
  | skip => exact fun _ h => h
  | assign h =>
    intro _ hb
    simp only [vars_setVar]
    split <;> first | exact Expr.lt_of_evalB h | exact hb
  | store => exact fun _ h => h
  | seq _ _ ih₁ ih₂ => exact fun h hb => ih₂ h.2 (ih₁ h.1 hb)
  | ite_true _ _ ih => exact fun h hb => ih h.1 hb
  | ite_false _ _ ih => exact fun h hb => ih h.2 hb
  | while_true _ _ _ ih₁ ih₂ => exact fun h hb => ih₂ h (ih₁ h hb)
  | while_false => exact fun _ h => h
  | read => exact fun h _ => False.elim h
  | write => exact fun _ h => h

private theorem probeScalarFrame {B C zeroDigit : ℕ} {s t : Env}
    (h : Run B (scalarMatrixScan zeroDigit) s t C) (r : String)
    (hGood : r ≠ "good") (hIndex : r ≠ "index") (hExpect : r ≠ "expect") :
    t.vars r = s.vars r := by
  apply (run_frame h).1
  change r ∉ (({"expect"} ∪ {"expect"}) ∪ ((∅ ∪ {"good"}) ∪ {"index"}) : Finset String)
  simp [hGood,hIndex,hExpect]

private theorem probeGoodBound {B C zeroDigit : ℕ} {s t : Env}
    (h : Run B (scalarMatrixScan zeroDigit) s t C) (hs : s.vars "good" < B) :
    t.vars "good" < B := by
  obtain ⟨_,_,hh⟩ := h
  exact scalarWrittenBound "good" hh ⟨⟨True.intro,True.intro⟩,⟨⟨True.intro,True.intro⟩,True.intro⟩⟩ hs

/-- Scan all the square matrices in one live contiguous bank. The invariant
tracks the conjunction of exactly the preceding matrix probes. -/
theorem scalarModeLoop_run (xs : List ℕ) (zeroDigit n modes start : ℕ)
    {B : ℕ} {σ : Env}
    (hB : 1 < B) (hLen : xs.length < B) (hCount : modes < B)
    (hn : 0 < n) (hStride : n+1 < B) (hSize : n*n < B) (hZero : zeroDigit < B)
    (hFit : start+modes*(n*n) ≤ xs.length) (hRead : ∀ a ∈ xs, a < B)
    (hData : σ.arrs "data" = sentinelWords xs)
    (hInit : σ.vars modeCursor=0) (hLimit : σ.vars modeLimit=modes)
    (hStart : σ.vars "base"=start) (hCell : σ.vars "count"=n*n)
    (hStep : σ.vars "stride"=n+1) (hYes : σ.vars modeAnswer=1) :
    ∃ τ, Run B (scalarModeLoop zeroDigit) σ τ ((60*(n*n)+36)*modes+4) ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out ∧
      (τ.vars modeAnswer=1 ↔
        ∀ i < modes, ∀ j < n*n,
          xs.getD (start+i*(n*n)+j) 0 =
            scalarExpected (n+1) (xs.getD (start+i*(n*n)) 0) zeroDigit j) := by
  let area := n*n
  let pos (i : ℕ) := start+i*area
  let good (i : ℕ) := ∀ j < area, xs.getD (pos i+j) 0 =
    scalarExpected (n+1) (xs.getD (pos i) 0) zeroDigit j
  let I (t : Env) := t.vars modeCursor ≤ modes ∧ t.vars modeLimit=modes ∧
    t.vars "base"=pos (t.vars modeCursor) ∧ t.vars "count"=area ∧ t.vars "stride"=n+1 ∧
    t.arrs=σ.arrs ∧ t.inp=σ.inp ∧ t.out=σ.out ∧
    (t.vars modeAnswer=1 ↔ ∀ i < t.vars modeCursor, good i)
  let V (t : Env) := modes-t.vars modeCursor
  have hArPos : 0 < area := Nat.mul_pos hn hn
  have guard (t : Env) (ht : I t) : modeGuard.evalB B t=some (decide (t.vars modeCursor<modes)) := by
    have hc := evalB_var (σ:=t) (x:=modeCursor) (ht.1.trans_lt hCount)
    have hl := evalB_var (σ:=t) (x:=modeLimit) (ht.2.1 ▸ hCount)
    simpa only [modeGuard,ht.2.1] using evalB_condLt hc hl
  have step (t : Env) (ht : I t) (hEntry : modeGuard.evalB B t=some true) :
      ∃ u, Run B (modeBody zeroDigit) t u (60*area+32) ∧ I u ∧ V u<V t := by
    let i := t.vars modeCursor
    rw [guard t ht] at hEntry
    have hi : i < modes := by simpa [i] using hEntry
    have hwidth : pos i+area ≤ xs.length := by
      rw [show pos i+area = pos (i+1) by simp [pos,Nat.succ_mul,Nat.add_assoc]]
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right area (Nat.succ_le_of_lt hi)) start).trans hFit
    have hPos : pos i < xs.length := by omega
    let t₁ := t.setVar "index" 0
    let t₂ := t₁.setVar "good" 1
    let diag := xs.getD (pos i) 0
    let t₃ := t₂.setVar "diag" diag
    have r₁ : Run B (.assign "index" (.lit 0)) t t₁ 2 := Run.assign (evalB_lit (by omega))
    have r₂ : Run B (.assign "good" (.lit 1)) t₁ t₂ 2 := Run.assign (evalB_lit hB)
    have hBase₂ : t₂.vars "base"=pos i := by simpa [t₂,t₁] using ht.2.2.1
    have hDiag : diag = xs[pos i] := List.getD_eq_getElem _ _ hPos
    have hDiagWord : diag < B := by
      rw [hDiag]
      exact hRead _ (List.getElem_mem hPos)
    have eDiag : (Expr.get "data" (.var "base")).evalB B t₂=some diag := by
      have e₀ : (Expr.var "base").evalB B t₂=some (pos i) :=
        evalB_var_iff.mpr ⟨hBase₂.symm,hBase₂ ▸ (hPos.trans hLen)⟩
      refine evalB_get e₀ ?_ hDiagWord
      change (t.arrs "data")[pos i]?=some diag
      rw [ht.2.2.2.2.2.1,hData,sentinelWords,List.getElem?_append_left hPos,
        List.getElem?_eq_getElem hPos]
      rw [hDiag]
    have r₃ : Run B (.assign "diag" (.get "data" (.var "base"))) t₂ t₃ 3 := Run.assign eDiag
    have hr : Run B modeReset t t₃ 7 := r₁.seq (r₂.seq r₃)
    obtain ⟨v,hv,hArr,hInp,hOut,hGood⟩ := scalarMatrixScan_run xs zeroDigit n (pos i) diag (σ := t₃)
      hB hLen hStride hZero hDiagWord hRead hwidth
      (by simp [t₃,t₂,t₁]) (by simpa [t₃,t₂,t₁] using ht.2.2.2.1)
      (by simpa [t₃,t₂,t₁] using ht.2.2.2.2.1)
      (by simpa [t₃] using hBase₂) (by simp [t₃]) (by simp [t₃,t₂])
      (by change t.arrs "data"=sentinelWords xs; rw [ht.2.2.2.2.2.1,hData])
    have hGood' : v.vars "good"=1 ↔ good i := hGood
    have hGoodB := probeGoodBound hv (show t₃.vars "good" < B by simpa [t₃,t₂] using hB)
    have hOld (r : String) (h₁ : r ≠ "good") (h₂ : r ≠ "index") (h₃ : r ≠ "expect")
        (h₄ : r ≠ "diag") : v.vars r=t.vars r := by
      calc
        v.vars r = t₃.vars r := probeScalarFrame hv r h₁ h₂ h₃
        _ = t.vars r := by simp [t₃,t₂,t₁,h₁,h₂,h₄]
    have hKCond := evalB_condEq (evalB_var (σ:=v) (x:="good") hGoodB) (evalB_lit hB)
    let w := if good i then v else v.setVar modeAnswer 0
    have hKeep : Run B modeKeep v w 6 := by
      by_cases h : good i
      · have e : (Cond.eq (.var "good") (.lit 1)).evalB B v=some true := by
          simpa [hGood'.mpr h] using hKCond
        simpa only [w,h,if_true,modeKeep] using
          (Run.ite_true (d:=.assign modeAnswer (.lit 0)) e Run.skip).mono (by decide : _ ≤ 6)
      · have hh : v.vars "good"≠1 := fun e => h (hGood'.mp e)
        have e : (Cond.eq (.var "good") (.lit 1)).evalB B v=some false := by
          simpa [hh,beq_iff_eq] using hKCond
        simpa only [w,h,if_false,modeKeep] using
          (Run.ite_false (c:=.skip)
            e (Run.assign (x:=modeAnswer) (evalB_lit (show 0 < B by omega)))).mono
            (by decide : _ ≤ 6)
    have hwVars (r : String) (hh : r ≠ modeAnswer) : w.vars r=v.vars r := by
      by_cases h : good i <;> simp [w,h,hh]
    have hDataW : w.arrs=v.arrs := by by_cases h : good i <;> simp [w,h]
    have hInW : w.inp=v.inp := by by_cases h : good i <;> simp [w,h]
    have hOutW : w.out=v.out := by by_cases h : good i <;> simp [w,h]
    have hBaseW : w.vars "base"=pos i :=
      (hwVars _ (by decide)).trans ((hOld _ (by decide) (by decide) (by decide) (by decide)).trans ht.2.2.1)
    have hAreaW : w.vars "count"=area :=
      (hwVars _ (by decide)).trans ((hOld _ (by decide) (by decide) (by decide) (by decide)).trans ht.2.2.2.1)
    have hIdxW : w.vars modeCursor=i :=
      (hwVars _ (by decide)).trans (hOld _ (by decide) (by decide) (by decide) (by decide))
    let x := w.setVar "base" (pos i+area)
    let u := x.setVar modeCursor (i+1)
    have ev {z : Env} {r : String} {s : ℕ} (h : z.vars r=s) (hs : s < B) :
        (Expr.var r).evalB B z=some s := evalB_var_iff.mpr ⟨h.symm,h ▸ hs⟩
    have r₄ : Run B (.assign "base" (.add (.var "base") (.var "count"))) w x 4 :=
      Run.assign (evalB_bin (op:=.add) (ev hBaseW (hPos.trans hLen)) (ev hAreaW hSize)
        (hwidth.trans_lt hLen))
    have r₅ : Run B (.assign modeCursor (.add (.var modeCursor) (.lit 1))) x u 4 :=
      Run.assign (evalB_bin (op:=.add)
        (ev (show x.vars modeCursor=i from by simpa [x,modeCursor] using hIdxW) (hi.trans hCount))
        (evalB_lit hB) ((Nat.succ_le_of_lt hi).trans_lt hCount))
    have hRun : Run B (modeBody zeroDigit) t u (7+((60*area+8)+(6+(4+4)))) :=
      hr.seq (hv.seq (hKeep.seq (r₄.seq r₅)))
    have hCursor : u.vars modeCursor=i+1 := by simp [u]
    have hKeepOther (r : String) (hb : r ≠ "base") (hc : r ≠ modeCursor) (hm : r ≠ modeAnswer)
        (h₁ : r ≠ "good") (h₂ : r ≠ "index") (h₃ : r ≠ "expect") (h₄ : r ≠ "diag") :
        u.vars r=t.vars r := by
      simp only [u,x,vars_setVar,hb,hc,if_false]
      exact (hwVars r hm).trans (hOld r h₁ h₂ h₃ h₄)
    refine ⟨u,hRun.mono (by omega),⟨by rw [hCursor]; exact Nat.succ_le_of_lt hi,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · exact (hKeepOther _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans ht.2.1
    · rw [hCursor]
      simp [u,x,modeCursor,pos,Nat.succ_mul,Nat.add_assoc]
    · exact (hKeepOther _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans ht.2.2.2.1
    · exact (hKeepOther _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans ht.2.2.2.2.1
    · exact hDataW.trans (hArr.trans ht.2.2.2.2.2.1)
    · exact hInW.trans (hInp.trans ht.2.2.2.2.2.2.1)
    · exact hOutW.trans (hOut.trans ht.2.2.2.2.2.2.2.1)
    · have hRest : (∀ j < i+1, good j) ↔ (∀ j < i, good j) ∧ good i := by
        constructor
        · intro h
          exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
        · rintro ⟨h,hself⟩ j hj
          by_cases hl : j < i
          · exact h j hl
          · rwa [show j=i by omega]
      rw [hCursor,hRest]
      change w.vars modeAnswer = 1 ↔ (∀ j < i, good j) ∧ good i
      by_cases h : good i
      · rw [show w.vars modeAnswer=t.vars modeAnswer by
          simpa [w,h] using hOld modeAnswer (by decide) (by decide) (by decide) (by decide),
          and_iff_left h]
        exact ht.2.2.2.2.2.2.2.2
      · simp [w,h]
    · simp only [V,hCursor]
      change modes-(i+1) < modes-i
      omega
  have hI : I σ := by simp [I,hInit,hLimit,hStart,hCell,hStep,hYes,pos,area]
  obtain ⟨τ,hRun,hτ,hStop⟩ :=
    Run.while_count I V (60*area+32) (fun t h => ⟨_,guard t h⟩) step hI
  rw [guard τ hτ] at hStop
  have hout : τ.vars modeCursor=modes := by
    have h₁ := hτ.1
    have h₂ : ¬ τ.vars modeCursor < modes := by simpa using hStop
    omega
  refine ⟨τ,hRun.mono ?_,hτ.2.2.2.2.2.1,hτ.2.2.2.2.2.2.1,hτ.2.2.2.2.2.2.2.1,?_⟩
  · simp [modeGuard,V,hInit,area]
    rw [show 4+(60*(n*n)+32)=60*(n*n)+36 by omega]
  · simpa only [hout,good,pos,area] using hτ.2.2.2.2.2.2.2.2

#print axioms scalarModeLoop_run
end EvenTI.P15Scalar