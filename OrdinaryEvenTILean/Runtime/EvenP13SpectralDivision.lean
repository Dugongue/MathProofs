import EvenP12RecognizeBudget
import Mathproof.Meta.P15DecideIMPEGens20261007

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_div ev_add)

def divisionCap : String := "even.spectral.div.cap"
def divisionCount : String := "even.spectral.div.count"
def divisionExponent : String := "even.spectral.div.exp"
def divisionAnswer : String := "even.spectral.div.answer"

def divisionGuard : Cond := .lt (.lit 0) (.var divisionCap)

def divisionBody (q : Nat) : Com :=
  .seq (.assign divisionCap (.bin .div (.var divisionCap) (.lit q)))
    (.assign divisionCount (.add (.var divisionCount) (.lit 1)))

def divisionFinish : Com :=
  .ite (.lt (.var divisionExponent) (.var divisionCount))
    (.assign divisionAnswer (.lit 1)) (.assign divisionAnswer (.lit 0))

def divisionBudget (q : Nat) : Com :=
  .seq (.assign divisionCount (.lit 0))
    (.seq (.while divisionGuard (divisionBody q)) divisionFinish)

private theorem size_div_small {x q : Nat} (hx : 0 < x) (hq : 2 ≤ q) :
    Nat.size (x/q) < Nat.size x := by
  have hp := Nat.size_pos.mpr hx
  have hEq : Nat.size x = (Nat.size x-1)+1 := by omega
  have hpow : x < 2^(Nat.size x-1)*2 := by
    have h := Nat.lt_size_self x
    rwa [hEq,pow_succ] at h
  have hx' : x/q < 2^(Nat.size x-1) :=
    (Nat.div_lt_iff_lt_mul (by omega)).2
      (hpow.trans_le (Nat.mul_le_mul_left _ hq))
  have h := Nat.size_le.mpr hx'
  omega

/-- Compare a fixed-base power against a cap by repeated division of the cap.
The instruction bound depends only on the bit length of the cap, even when a
malformed request supplies an arbitrarily large binary exponent. -/
theorem divisionBudget_run {q cap exp B : Nat} {σ : Env}
    (hq : 2 ≤ q) (hqB : q < B) (hcap : cap < B) (heB : exp < B)
    (hsize : Nat.size cap < B) (hc : σ.vars divisionCap = cap)
    (he : σ.vars divisionExponent = exp) :
    ∃ τ, Run B (divisionBudget q) σ τ (12*Nat.size cap+12) ∧
      τ.vars divisionAnswer = (if q^exp ≤ cap then 1 else 0) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let init := σ.setVar divisionCount 0
  let I (s : Env) : Prop :=
    s.vars divisionCap = cap / q ^ (s.vars divisionCount) ∧
    s.vars divisionCount + Nat.size (s.vars divisionCap) ≤ Nat.size cap ∧
    (∀ i < s.vars divisionCount, q^i ≤ cap) ∧
    s.vars divisionExponent = exp ∧ s.inp = σ.inp ∧ s.out = σ.out
  let V (s : Env) := Nat.size (s.vars divisionCap)
  have hb : 1 < B := by omega
  have capFit (s : Env) (hs : I s) : s.vars divisionCap < B := by
    rw [hs.1]
    exact (Nat.div_le_self _ _).trans_lt hcap
  have guardEval (s : Env) (hs : I s) :
      divisionGuard.evalB B s = some (decide (0 < s.vars divisionCap)) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var (capFit s hs))
  have step (s : Env) (hs : I s) (hg : divisionGuard.evalB B s = some true) :
      ∃ s', Run B (divisionBody q) s s' 8 ∧ I s' ∧ V s' < V s := by
    let i := s.vars divisionCount
    let c := s.vars divisionCap
    have hcp : 0 < c := by
      rw [guardEval s hs] at hg
      simpa [c] using hg
    have hi : i+1 < B := by
      have h₁ := hs.2.1
      have h₂ := Nat.size_pos.mpr hcp
      change i+Nat.size c ≤ Nat.size cap at h₁
      omega
    have hdec := size_div_small hcp hq
    let s₁ := s.setVar divisionCap (c/q)
    let s₂ := s₁.setVar divisionCount (i+1)
    have evC : (Expr.bin .div (.var divisionCap) (.lit q)).evalB B s = some (c/q) :=
      ev_div (evalB_var (capFit s hs)) (evalB_lit hqB)
        ((Nat.div_le_self _ _).trans_lt (capFit s hs))
    have hs₁ : s₁.vars divisionCount = i := by simp [s₁,divisionCap,divisionCount,i,vars_setVar]
    have evI : (Expr.add (.var divisionCount) (.lit 1)).evalB B s₁ = some (i+1) :=
      ev_add (ev_var hs₁ (by omega)) (evalB_lit hb) hi
    have r : Run B (divisionBody q) s s₂ 8 :=
      (Run.assign (x := divisionCap) evC).seq (Run.assign (x := divisionCount) evI)
    have hsC : s₂.vars divisionCap = c/q := by simp [s₂,s₁,divisionCap,divisionCount,vars_setVar]
    have hsI : s₂.vars divisionCount = i+1 := by simp [s₂,vars_setVar]
    refine ⟨s₂,r,⟨?_,?_,?_,?_,?_,?_⟩,by simpa [V,hsC,c] using hdec⟩
    · rw [hsC,hsI,show c = cap/q^i from hs.1,Nat.div_div_eq_div_mul,pow_succ]
    · rw [hsC,hsI]
      have := hs.2.1
      change i+Nat.size c ≤ Nat.size cap at this
      omega
    · intro j hj
      rw [hsI] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact hs.2.2.1 _ h
      · have hcp' := hcp
        have h' : 1 ≤ cap / q^i := by
          have hh : c = cap / q^i := hs.1
          omega
        have hm := (Nat.le_div_iff_mul_le (pow_pos (by omega) i)).mp h'
        simpa using hm
    · simpa [s₂,s₁,divisionExponent,divisionCap,divisionCount,vars_setVar] using hs.2.2.2.1
    · exact hs.2.2.2.2.1
    · exact hs.2.2.2.2.2
  have hin : I init := by
    simp [I,init,divisionCap,divisionCount,divisionExponent,vars_setVar] at *
    exact ⟨hc,by rw [hc],he⟩
  obtain ⟨t,hr,ht,hstop⟩ := Run.while_count I V 8
    (fun s hs => ⟨_,guardEval s hs⟩) step hin
  rw [guardEval t ht] at hstop
  have ht0 : t.vars divisionCap = 0 := by simpa using hstop
  let i := t.vars divisionCount
  have hbig : cap < q^i := by
    apply (Nat.div_eq_zero_iff_lt (pow_pos (by omega) i)).mp
    exact ht.1.symm.trans ht0
  have hdecision : exp < i ↔ q^exp ≤ cap := by
    constructor
    · exact ht.2.2.1 exp
    · intro h
      by_contra! hn
      have hq' := Nat.pow_le_pow_right (by omega : 0 < q) hn
      omega
  have hEval : (Cond.lt (.var divisionExponent) (.var divisionCount)).evalB B t =
      some (decide (exp < i)) :=
    evalB_condLt (ev_var ht.2.2.2.1 heB) (evalB_var (by have := ht.2.1; omega))
  have hInit : Run B (.assign divisionCount (.lit 0)) σ init 2 := Run.assign (evalB_lit (by omega))
  have hLoop : Run B (.while divisionGuard (divisionBody q)) init t (12*Nat.size cap+4) := by
    have heq : V init = Nat.size cap := by
      change Nat.size (init.vars divisionCap) = Nat.size cap
      rw [show init.vars divisionCap = σ.vars divisionCap by
        simp [init,divisionCap,divisionCount,vars_setVar],hc]
    rw [heq,show divisionGuard.size = 3 by decide] at hr
    exact hr.mono (by omega)
  by_cases h : exp < i
  · have eh : (Cond.lt (.var divisionExponent) (.var divisionCount)).evalB B t = some true := by
      rw [hEval]; simp [h]
    have r : Run B divisionFinish t (t.setVar divisionAnswer 1) 6 :=
      Run.ite_true eh (Run.assign (evalB_lit hb))
    exact ⟨_,(hInit.seq (hLoop.seq r)).mono (by omega),
      by simp [vars_setVar,hdecision.mp h],ht.2.2.2.2.1,ht.2.2.2.2.2⟩
  · have eh : (Cond.lt (.var divisionExponent) (.var divisionCount)).evalB B t = some false := by
      rw [hEval]; simp [h]
    have r : Run B divisionFinish t (t.setVar divisionAnswer 0) 6 :=
      Run.ite_false eh (Run.assign (evalB_lit (by omega)))
    have hf : ¬q^exp ≤ cap := fun hh => h (hdecision.mpr hh)
    exact ⟨_,(hInit.seq (hLoop.seq r)).mono (by omega),
      by simp [vars_setVar,hf],ht.2.2.2.2.1,ht.2.2.2.2.2⟩
#print axioms divisionBudget_run
end EvenTI.P13Spectral
