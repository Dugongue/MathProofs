import EvenP13SpectralAnchorLayout

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

def anchorLength : String := "even.anchor.length"
def digitIndex : String := "even.anchor.digit.index"
def digitGood : String := "even.anchor.digit.good"

def digitCheck (q : Nat) (bank : String) : Cond :=
  .lt (.get bank (.var digitIndex)) (.lit q)
def scanMore : Cond := .lt (.var digitIndex) (.var anchorLength)
def digitStep (q : Nat) (bank : String) : Com :=
  .seq (.ite (digitCheck q bank) .skip (.assign digitGood (.lit 0)))
    (.assign digitIndex (.add (.var digitIndex) (.lit 1)))
def digitLoop (q : Nat) (bank : String) : Com := .while scanMore (digitStep q bank)

theorem digitLoop_run (q n : Nat) (bank : String) (xs : List Nat) {B : Nat} {σ : Env}
    (hArr : σ.arrs bank = n::xs) (hLen : σ.vars anchorLength = xs.length+1)
    (hPos : σ.vars digitIndex = 1) (hGood : σ.vars digitGood = 1)
    (hB : 1 < B) (hq : q < B) (hLB : xs.length+1 < B)
    (hWords : ∀ v ∈ xs, v < B) :
    ∃ τ, Run B (digitLoop q bank) σ τ (16*xs.length+4) ∧
      (τ.vars digitGood = 1 ↔ ∀ x ∈ xs, x < q) ∧
      τ.vars digitGood ≤ 1 ∧ Frame (digitLoop q bank) σ τ := by
  let len := xs.length+1
  let good (xs : List Nat) : Prop := ∀ x ∈ xs, x < q
  let inv (t : Env) : Prop :=
    t.arrs bank = n::xs ∧ t.vars anchorLength = len ∧
    1 ≤ t.vars digitIndex ∧ t.vars digitIndex ≤ len ∧
    t.vars digitGood ≤ 1 ∧
    (t.vars digitGood = 1 ∧ good (xs.drop (t.vars digitIndex-1)) ↔ good xs)
  let V (t : Env) := len - t.vars digitIndex
  have guardEv (t : Env) (ht : inv t) :
      scanMore.evalB B t = some (decide (t.vars digitIndex < len)) := by
    have he := ht.2.1
    have hp := ht.2.2.2.1
    have hv : t.vars anchorLength < B := by rw [he]; exact hLB
    have z := evalB_condLt (B := B) (σ := t) (e := .var digitIndex) (f := .var anchorLength)
      (evalB_var (by omega)) (evalB_var hv)
    rwa [he] at z
  have step (t : Env) (ht : inv t) (hg : scanMore.evalB B t = some true) :
      ∃ s, Run B (digitStep q bank) t s 12 ∧ inv s ∧ V s < V t := by
    rw [guardEv t ht] at hg
    have hh : t.vars digitIndex < len := by simpa using hg
    let i := t.vars digitIndex-1
    have hI : i+1 = t.vars digitIndex := by dsimp [i]; have := ht.2.2.1; omega
    have hi : i < xs.length := by dsimp [len] at hh; omega
    let a := xs[i]
    have ha : a < B := hWords _ (List.getElem_mem hi)
    have hget : (t.arrs bank)[t.vars digitIndex]? = some a := by
      rw [← hI,ht.1,List.getElem?_cons_succ,List.getElem?_eq_getElem hi]
    have eqA : (Expr.get bank (.var digitIndex)).evalB B t = some a :=
      evalB_get (evalB_var (hh.trans hLB)) hget ha
    have eqQ : (digitCheck q bank).evalB B t = some (decide (a < q)) :=
      evalB_condLt eqA (evalB_lit hq)
    let b := if a < q then t.vars digitGood else 0
    let u := if a < q then t else t.setVar digitGood 0
    have hCode :
        Run B (.ite (digitCheck q bank) .skip (.assign digitGood (.lit 0))) t u 7 := by
      by_cases h : a < q
      · have h1 : (digitCheck q bank).evalB B t = some true := by rw [eqQ]; simp [h]
        have r := Run.ite_true (d := .assign digitGood (.lit 0)) h1 Run.skip
        simpa [u,h] using r.mono (by norm_num [digitCheck,Cond.size,Expr.size])
      · have h1 : (digitCheck q bank).evalB B t = some false := by rw [eqQ]; simp [h]
        have r := Run.ite_false (c := .skip) h1 (Run.assign (x := digitGood) (evalB_lit (show 0 < B by omega)))
        simpa [u,h] using r.mono (by norm_num [digitCheck,Cond.size,Expr.size])
    have hU : u.vars digitIndex = t.vars digitIndex := by
      by_cases h : a < q <;> simp [u,h,digitIndex,digitGood,vars_setVar]
    have hUb : u.vars digitGood = b := by by_cases h : a < q <;> simp [u,b,h,vars_setVar]
    let s := u.setVar digitIndex (t.vars digitIndex+1)
    have next := evalB_bin (B := B) (σ := u) (op := .add) (e := .var digitIndex) (f := .lit 1)
      (evalB_var (by rw [hU]; omega)) (evalB_lit hB)
      (by change u.vars digitIndex+1 < B; rw [hU]; omega)
    have hNext : (Expr.add (.var digitIndex) (.lit 1)).evalB B u =
        some (t.vars digitIndex+1) := by simpa only [Bop.apply_add,hU] using next
    have hr : Run B (digitStep q bank) t s 12 :=
      (hCode.seq (Run.assign (x := digitIndex) hNext)).mono (by norm_num [Expr.add,Expr.size])
    have hsI : s.vars digitIndex = t.vars digitIndex+1 := by simp [s,vars_setVar]
    have hsB : s.vars digitGood = b := by
      simp only [s,vars_setVar,show digitGood ≠ digitIndex by decide,if_false]
      exact hUb
    have hsL : s.vars anchorLength = len := by
      by_cases h : a < q <;>
        simp [s,u,h,anchorLength,digitGood,digitIndex,vars_setVar] <;> exact ht.2.1
    have hsA : s.arrs bank = n::xs := by by_cases h : a < q <;> simpa [s,u,h] using ht.1
    have htail : xs.drop (t.vars digitIndex-1) = a :: xs.drop (i+1) :=
      List.drop_eq_getElem_cons hi
    have hnext : s.vars digitIndex-1 = i+1 := by rw [hsI]; omega
    have hb : b ≤ 1 := by unfold b; split <;> omega
    refine ⟨s,hr,⟨hsA,hsL,by omega,by omega,hsB ▸ hb,?_⟩,?_⟩
    · rw [hsB,hnext,← ht.2.2.2.2.2,htail]
      simp [b,good]
      by_cases he : a < q <;> simp [b,he,and_assoc,and_left_comm]
    · simp only [V,hsI]; omega
  have i₀ : inv σ := by
    simp [inv,hArr,hLen,hPos,hGood,len]
  obtain ⟨τ,r,hτ,hStop⟩ := Run.while_count inv V 12
    (fun t ht => ⟨_,guardEv t ht⟩) step i₀
  rw [guardEv τ hτ] at hStop
  have hge : len ≤ τ.vars digitIndex := by simpa using hStop
  have hEnd : τ.vars digitIndex = len := by
    exact Nat.le_antisymm hτ.2.2.2.1 hge
  have hGood' := hτ.2.2.2.2.2
  rw [hEnd] at hGood'
  have hEq : len-1 = xs.length := by simp [len]
  rw [hEq,List.drop_length] at hGood'
  have hRun : Run B (digitLoop q bank) σ τ (16*xs.length+4) := by
    refine r.mono ?_
    simp [V,scanMore,Cond.size,Expr.size,len,hPos]
  exact ⟨τ,hRun,by simpa [good] using hGood',hτ.2.2.2.2.1,Frame.of_run hRun⟩

#print axioms digitLoop_run
end EvenTI.P13Spectral
