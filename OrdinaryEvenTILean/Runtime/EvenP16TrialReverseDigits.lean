import EvenP15TrialFormOrder
import Mathproof.Meta.P15DecideIMPEGens20261007
import Mathproof.Meta.P15DecideIMPRowKer20261007

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace EvenTI.P16Trial

open EvenTI.P15Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def reverseDigitBase : String := "even.trial.reverse.base"
def reverseDigitRemain : String := "even.trial.reverse.remain"
def reverseDigitQuotient : String := "even.trial.reverse.quotient"
def reverseDigitResult : String := "even.trial.reverse.result"

private def divideDigit : Expr := .div (.var reverseDigitQuotient) (.var reverseDigitBase)
private def extractDigit : Expr := .sub (.var reverseDigitQuotient)
  (.mul divideDigit (.var reverseDigitBase))
private def nextDigit : Expr := .add (.mul (.var reverseDigitResult) (.var reverseDigitBase)) extractDigit
private def reverseGuard : Cond := .lt (.lit 0) (.var reverseDigitRemain)
private def reverseLoopBody : Com :=
  .seq (.assign reverseDigitResult nextDigit)
    (.seq (.assign reverseDigitQuotient divideDigit)
      (.assign reverseDigitRemain (.sub (.var reverseDigitRemain) (.lit 1))))

def reverseDigits : Com :=
  .seq (.assign reverseDigitResult (.lit 0)) (.while reverseGuard reverseLoopBody)

private structure ReverseInvariant (n d k : ℕ) (σ τ : Env) : Prop where
  remain : τ.vars reverseDigitRemain ≤ d
  source : τ.vars reverseDigitQuotient ≤ k
  result : τ.vars reverseDigitResult < n^(d-τ.vars reverseDigitRemain)
  exactValue : reverseModeNumber n d k =
    τ.vars reverseDigitResult*n^(τ.vars reverseDigitRemain) +
      reverseModeNumber n (τ.vars reverseDigitRemain) (τ.vars reverseDigitQuotient)
  arrays : τ.arrs=σ.arrs
  input : τ.inp=σ.inp
  output : τ.out=σ.out
  keep : ∀ x, x ≠ reverseDigitRemain → x ≠ reverseDigitQuotient →
    x ≠ reverseDigitResult → τ.vars x=σ.vars x

/-- Evaluate the exact mixed-radix permutation used by the public encoding.
The physical loop takes linear time in the order, with all words bounded by
the size of an original dense cut side. -/
theorem reverseDigits_run {n d k B : ℕ} {σ : Env}
    (hn : 0 < n) (hNB : n < B) (hD : d < B) (hTop : n^d < B) (hk : k < n^d)
    (hBase : σ.vars reverseDigitBase=n) (hRem : σ.vars reverseDigitRemain=d)
    (hQuot : σ.vars reverseDigitQuotient=k) :
    ∃ τ, Run B reverseDigits σ τ (24*d+6) ∧
      τ.vars reverseDigitResult=reverseModeNumber n d k ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out ∧
      ∀ x, x ≠ reverseDigitRemain → x ≠ reverseDigitQuotient →
        x ≠ reverseDigitResult → τ.vars x=σ.vars x := by
  let I := ReverseInvariant n d k σ
  let P := fun τ : Env => τ.vars reverseDigitRemain
  have hPos : 0 < n^d := pow_pos hn _
  have hWord : 1 < B := by omega
  let σ₀ := σ.setVar reverseDigitResult 0
  have r₀ : Run B (.assign reverseDigitResult (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have h₀ : I σ₀ := by
    refine ⟨?_,?_,?_,?_,rfl,rfl,rfl,?_⟩
    · simpa [σ₀,show reverseDigitRemain ≠ reverseDigitResult by decide] using hRem.le
    · simpa [σ₀,show reverseDigitQuotient ≠ reverseDigitResult by decide] using hQuot.le
    · simp [σ₀,show reverseDigitRemain ≠ reverseDigitResult by decide,hRem]
    · simp [σ₀,show reverseDigitRemain ≠ reverseDigitResult by decide,
        show reverseDigitQuotient ≠ reverseDigitResult by decide,hRem,hQuot]
    · intro x _ _ hx
      simp [σ₀,hx]
  have hGuard (τ : Env) (h : I τ) :
      reverseGuard.evalB B τ=some (decide (0 < τ.vars reverseDigitRemain)) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var (h.remain.trans_lt hD))
  have hStep (τ : Env) (h : I τ) (hgt : reverseGuard.evalB B τ=some true) :
      ∃ u, Run B reverseLoopBody τ u 20 ∧ I u ∧ P u < P τ := by
    rw [hGuard τ h] at hgt
    let j := τ.vars reverseDigitRemain
    let v := τ.vars reverseDigitQuotient
    let a := τ.vars reverseDigitResult
    have hj : 0 < j := of_decide_eq_true (Option.some.inj hgt)
    have hjd : j ≤ d := h.remain
    have hva : v ≤ k := h.source
    have hSmall : a < n^(d-j) := h.result
    have hNew : a*n+v%n < n^(d-j+1) := by
      have ht := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hSmall)
      rw [Nat.succ_mul] at ht
      rw [pow_succ]
      have hv := Nat.mod_lt v hn
      omega
    have hPow := Nat.pow_le_pow_right hn (show d-j+1 ≤ d by omega)
    have hNext : a*n+v%n < B := (hNew.trans_le hPow).trans hTop
    have hOld : a < B :=
      (hSmall.trans_le (Nat.pow_le_pow_right hn (Nat.sub_le d j))).trans hTop
    have hVB : v < B := hva.trans_lt (hk.trans hTop)
    have hqB := (Nat.div_le_self v n).trans_lt hVB
    have hBase' : τ.vars reverseDigitBase=n := (h.keep _ (by decide) (by decide) (by decide)).trans hBase
    have eN := ev_var hBase' hNB
    have eV := ev_var (show τ.vars reverseDigitQuotient=v from rfl) hVB
    have eA := ev_var (show τ.vars reverseDigitResult=a from rfl) hOld
    have eQ := ev_div eV eN hqB
    have eD := ev_sub eV (ev_mul eQ eN ((Nat.div_mul_le_self v n).trans_lt hVB)) (by omega)
    rw [hmdg] at eD
    have eResult : nextDigit.evalB B τ=some (a*n+v%n) :=
      ev_add (ev_mul eA eN (by omega)) eD hNext
    let τ₁ := τ.setVar reverseDigitResult (a*n+v%n)
    have r₁ : Run B (.assign reverseDigitResult nextDigit) τ τ₁ 12 := Run.assign eResult
    have eV₁ := ev_var (show τ₁.vars reverseDigitQuotient=v from rfl) hVB
    have eN₁ := ev_var (show τ₁.vars reverseDigitBase=n from hBase') hNB
    have eQ₁ : divideDigit.evalB B τ₁=some (v/n) := ev_div eV₁ eN₁ hqB
    let τ₂ := τ₁.setVar reverseDigitQuotient (v/n)
    have r₂ : Run B (.assign reverseDigitQuotient divideDigit) τ₁ τ₂ 4 := Run.assign eQ₁
    have eJ := ev_var (show τ₂.vars reverseDigitRemain=j from rfl) (hjd.trans_lt hD)
    have eDec : (Expr.sub (.var reverseDigitRemain) (.lit 1)).evalB B τ₂=some (j-1) :=
      ev_sub eJ (evalB_lit hWord) (by omega)
    let u := τ₂.setVar reverseDigitRemain (j-1)
    have r₃ : Run B (.assign reverseDigitRemain (.sub (.var reverseDigitRemain) (.lit 1))) τ₂ u 4 :=
      Run.assign eDec
    have he : j=(j-1)+1 := by omega
    have he₂ : d-(j-1)=d-j+1 := by omega
    refine ⟨u,r₁.seq (r₂.seq r₃),?_,?_⟩
    · refine ⟨?_,?_,?_,?_,h.arrays,h.input,h.output,?_⟩
      · change j-1 ≤ d
        omega
      · change v/n ≤ k
        exact (Nat.div_le_self _ _).trans hva
      · change a*n+v%n < n^(d-(j-1))
        rwa [he₂]
      · have hh : reverseModeNumber n d k=a*n^j+reverseModeNumber n j v := h.exactValue
        change reverseModeNumber n d k=(a*n+v%n)*n^(j-1)+reverseModeNumber n (j-1) (v/n)
        conv_lhs => rw [hh]
        conv_lhs => rw [he,reverseModeNumber,pow_succ]
        ring
      · intro x h₁ h₂ h₃
        simpa [u,τ₂,τ₁,h₁,h₂,h₃] using h.keep x h₁ h₂ h₃
    · change j-1 < j
      omega
  obtain ⟨τ,r,hτ,hStop⟩ := Run.while_count I P 20 (fun τ h => ⟨_,hGuard τ h⟩) hStep h₀
  rw [hGuard τ hτ] at hStop
  have hEnd : τ.vars reverseDigitRemain=0 := by
    have hh := of_decide_eq_false (Option.some.inj hStop)
    omega
  have hExact := hτ.exactValue
  rw [hEnd,pow_zero,Nat.mul_one,reverseModeNumber,Nat.add_zero] at hExact
  have hR : Run B reverseDigits σ τ (24*d+6) := by
    have hp : P σ₀=d := by
      simpa [P,σ₀,show reverseDigitRemain ≠ reverseDigitResult by decide] using hRem
    rw [hp] at r
    exact (r₀.seq r).mono (by change 2+(24*d+4) ≤ 24*d+6; omega)
  exact ⟨τ,hR,hExact.symm,hτ.arrays,hτ.input,hτ.output,hτ.keep⟩

#print axioms reverseDigits_run
end EvenTI.P16Trial