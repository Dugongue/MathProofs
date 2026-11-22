import EvenP13SpectralDivision
import EvenP11OracleCodec

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

def sumLeft : String := "even.spectral.sum.left"
def sumWord : String := "even.spectral.sum.word"

def anchorSum (xs : List Nat) : Nat := (xs.map (fun x => x-1)).sum

def sumGuard : Cond := .lt (.lit 0) (.var sumLeft)

def sumStep : Com :=
  .seq (.read sumWord)
    (.seq (.assign divisionExponent (.add (.var divisionExponent) (.sub (.var sumWord) (.lit 1))))
      (.assign sumLeft (.sub (.var sumLeft) (.lit 1))))

def sumLoop : Com := .while sumGuard sumStep

/-- Sum the positive words of the anchor-answer tape after decrementing them.
Zero delimiters contribute zero, as do encodings of an exponent of zero. -/
theorem sumLoop_run {B : Nat} {σ : Env}
    (hLeft : σ.vars sumLeft = σ.inp.length)
    (hLength : σ.inp.length < B) (hWords : ∀ w ∈ σ.inp, w < B)
    (hSum : σ.vars divisionExponent + anchorSum σ.inp < B) (hB : 1 < B) :
    ∃ τ, Run B sumLoop σ τ (15*σ.inp.length+4) ∧
      τ.vars divisionExponent = σ.vars divisionExponent + anchorSum σ.inp ∧
      τ.inp = [] ∧ Frame sumLoop σ τ := by
  let total := σ.vars divisionExponent + anchorSum σ.inp
  let I (t : Env) :=
    t.vars sumLeft = t.inp.length ∧ t.inp.length < B ∧
    (∀ w ∈ t.inp, w < B) ∧ t.vars divisionExponent + anchorSum t.inp = total
  let V (t : Env) := t.inp.length
  have ev (t : Env) (ht : I t) : sumGuard.evalB B t = some (decide (0 < t.inp.length)) := by
    have h : t.vars sumLeft < B := ht.1 ▸ ht.2.1
    simpa only [sumGuard,ht.1] using evalB_condLt
      (B := B) (σ := t) (e := .lit 0) (f := .var sumLeft)
      (evalB_lit (by omega)) (evalB_var h)
  have step (t : Env) (ht : I t) (hg : sumGuard.evalB B t = some true) :
      ∃ u, Run B sumStep t u 11 ∧ I u ∧ V u < V t := by
    have hPos : 0 < t.inp.length := by rw [ev t ht] at hg; simpa using hg
    cases hi : t.inp with
    | nil => simp [hi] at hPos
    | cons w ws =>
      let t₁ : Env := {t.setVar sumWord w with inp := ws}
      let t₂ := t₁.setVar divisionExponent (t.vars divisionExponent+(w-1))
      let u := t₂.setVar sumLeft ws.length
      have hw : w < B := ht.2.2.1 w (by simp [hi])
      have hsum : t.vars divisionExponent + (w-1) + anchorSum ws = total := by
        simpa [hi,anchorSum,Nat.add_assoc] using ht.2.2.2
      have htotal : total < B := hSum
      have he : t₁.vars divisionExponent = t.vars divisionExponent := by
        simp [t₁,sumWord,divisionExponent,vars_setVar]
      have hWord : t₁.vars sumWord = w := by simp [t₁,vars_setVar]
      have evW : (Expr.var sumWord).evalB B t₁ = some w := by
        rw [← hWord]
        exact evalB_var (hWord ▸ hw)
      have evE : (Expr.var divisionExponent).evalB B t₁ = some (t.vars divisionExponent) := by
        rw [← he]
        exact evalB_var (by rw [he]; omega)
      have eMinus : (Expr.sub (.var sumWord) (.lit 1)).evalB B t₁ = some (w-1) :=
        evalB_bin evW (evalB_lit hB) (by change w-1 < B; omega)
      have eAdd : (Expr.add (.var divisionExponent) (.sub (.var sumWord) (.lit 1))).evalB B t₁ =
          some (t.vars divisionExponent+(w-1)) :=
        evalB_bin evE eMinus (by change t.vars divisionExponent+(w-1) < B; omega)
      have hlEq : t.vars sumLeft = ws.length+1 := by rw [ht.1,hi]; rfl
      have hleft₂ : t₂.vars sumLeft = ws.length+1 := by
        simpa only [t₂,t₁,vars_setVar,show sumLeft ≠ divisionExponent by decide,
          show sumLeft ≠ sumWord by decide,if_false] using hlEq
      have hLen := ht.2.1
      rw [hi,List.length_cons] at hLen
      have eLeft : (Expr.sub (.var sumLeft) (.lit 1)).evalB B t₂ = some ws.length := by
        have evL : (Expr.var sumLeft).evalB B t₂ = some (ws.length+1) := by
          rw [← hleft₂]
          exact evalB_var (hleft₂ ▸ hLen)
        simpa using evalB_bin (op := .sub) evL (evalB_lit hB)
          (by change (ws.length+1)-1 < B; omega)
      have r : Run B sumStep t u 11 :=
        (Run.read (x := sumWord) hi).seq ((Run.assign (x := divisionExponent) eAdd).seq
          (Run.assign (x := sumLeft) eLeft))
      have hExp : u.vars divisionExponent = t.vars divisionExponent+(w-1) := by
        simp [u,t₂,sumLeft,divisionExponent,vars_setVar]
      refine ⟨u,r,⟨?_,?_,?_,?_⟩,?_⟩
      · simp [u,t₂,t₁,vars_setVar]
      · simpa [u,t₂,t₁] using (show ws.length < B by omega)
      · intro v hv
        exact ht.2.2.1 v (by simpa [u,t₂,t₁,hi] using Or.inr hv : v ∈ t.inp)
      · simpa only [hExp,show u.inp=ws from rfl] using hsum
      · simp [V,u,t₂,t₁,hi]
  obtain ⟨τ,hr,hτ,hstop⟩ := Run.while_count I V 11
    (fun t ht => ⟨_,ev t ht⟩) step ⟨hLeft,hLength,hWords,rfl⟩
  rw [ev τ hτ] at hstop
  have hn : τ.inp = [] := by simpa using hstop
  have r : Run B sumLoop σ τ (15*σ.inp.length+4) := by
    apply hr.mono
    simp [V,sumGuard,Cond.size,Expr.size]
  exact ⟨τ,r,by simpa [hn,anchorSum,total] using hτ.2.2.2,hn,Frame.of_run r⟩

theorem anchorSum_packed (xs : List Nat) :
    anchorSum (EvenTI.P10Oracle.packSegments (xs.map fun x => [x])) = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [EvenTI.P10Oracle.packSegments,EvenTI.P10Oracle.positiveWords,anchorSum] at ih ⊢
    omega

#print axioms sumLoop_run
#print axioms anchorSum_packed
end EvenTI.P13Spectral
