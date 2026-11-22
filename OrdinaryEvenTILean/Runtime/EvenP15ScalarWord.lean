import EvenP15ScalarModeLoop
import EvenP15Totalizer
import EvenP12CountPreInput

set_option autoImplicit false
set_option maxRecDepth 7500
set_option maxHeartbeats 1800000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Lax51.TuringPolytime (TuringPolytime)
open Mathproof.Problem18IMPFieldLayout20261001 (noRead)
open EvenTI.P12CountPre (inputLoadLoop inputLoad_run inputBuffer_zero inputBuffer_full sentinelWords)
open EvenTI.P15Execution (totalBinary_of_boundedWordRuns)

def modeWidth : String := "even.scalar.mode.width"

def modeTapeSetup : Com :=
  .seq (.assign modeLimit (.get "data" (.lit 0))) <|
  .seq (.assign modeWidth (.get "data" (.lit 1))) <|
  .seq (.assign "base" (.lit 2)) <|
  .seq (.assign "count" (.mul (.var modeWidth) (.var modeWidth))) <|
  .seq (.assign "stride" (.add (.var modeWidth) (.lit 1))) <|
  .seq (.assign modeCursor (.lit 0)) (.assign modeAnswer (.lit 1))

def emitScalarAnswer : Com :=
  .ite (.eq (.var modeAnswer) (.lit 1)) (.write (.lit 1)) (.write (.lit 0))

def scalarWordProgram (zeroDigit : ℕ) : Com :=
  .seq (.read "length") <| .seq inputLoadLoop <| .seq modeTapeSetup <|
    .seq (scalarModeLoop zeroDigit) emitScalarAnswer

def FoldedScalarModes (zeroDigit : ℕ) (xs : List ℕ) (d n : ℕ) : Prop :=
  ∀ i < d, ∀ j < n*n,
    xs.getD (2+i*(n*n)+j) 0 = scalarExpected (n+1) (xs.getD (2+i*(n*n)) 0) zeroDigit j

noncomputable def scalarWordSpec (zeroDigit : ℕ) : List ℕ → List ℕ
  | d::n::ws => by
    classical
    exact if FoldedScalarModes zeroDigit (d::n::ws) d n then [1] else [0]
  | _ => [0]

def MatrixWords (q : ℕ) (xs : List ℕ) : Prop :=
  ∃ d n ws, xs = d::n::ws ∧ 0 < d ∧ 0 < n ∧ ws.length=d*(n*n) ∧ ∀ a ∈ ws,a≤q

/-- Consume the literal recovered matrix bank from the tape and emit one
scalar bit. Every visited entry belongs to the matrix payload. -/
theorem scalarWordProgram_run (zeroDigit q : ℕ) (xs : List ℕ) (hv : MatrixWords q xs)
    {B : ℕ} (hB : xs.length+q+zeroDigit+4 < B) :
    ∃ τ, Run B (scalarWordProgram zeroDigit)
      (initEnv (fun _ => xs.length+1) (xs.length::xs)) τ (120*xs.length+80) ∧
      τ.out = scalarWordSpec zeroDigit xs := by
  obtain ⟨d,n,ws,rfl,hd,hn,hw,hWords⟩ := hv
  let xs := d::n::ws
  have haddN : n ≤ n*n := Nat.le_mul_of_pos_right _ hn
  have hNN : n*n ≤ d*(n*n) := Nat.le_mul_of_pos_left _ hd
  have hD : d ≤ d*(n*n) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hn hn)
  have hL : xs.length = 2+d*(n*n) := by simp [xs,hw] <;> omega
  have hBig : xs.length+q+zeroDigit+4 < B := hB
  have hOne : 1 < B := by omega
  have hLen : xs.length < B := by omega
  have hD' : d < B := by omega
  have hN' : n < B := by omega
  have hNN' : n*n < B := by omega
  have hN1 : n+1 < B := by omega
  have hWords' (a : ℕ) (ha : a ∈ xs) : a < B := by
    simp only [xs,List.mem_cons] at ha
    rcases ha with rfl|rfl|ha
    · exact hD'
    · exact hN'
    · have := hWords a ha
      omega
  let s := initEnv (fun _ => xs.length+1) (xs.length::xs)
  let u := {s.setVar "length" xs.length with inp := xs}
  have r₀ : Run B (.read "length") s u 1 := Run.read rfl
  obtain ⟨v,r₁,_,hBank,hOut,_⟩ := inputLoad_run xs (σ:=u)
    (by simp [u]) (by simp [u,s,initEnv]) rfl
    (by simp [u,s,initEnv,inputBuffer_zero]) hLen hOne hWords'
  have hBank' := hBank.trans (inputBuffer_full xs)
  let v₁ := v.setVar modeLimit d
  let v₂ := v₁.setVar modeWidth n
  let v₃ := v₂.setVar "base" 2
  let v₄ := v₃.setVar "count" (n*n)
  let v₅ := v₄.setVar "stride" (n+1)
  let v₆ := v₅.setVar modeCursor 0
  let z := v₆.setVar modeAnswer 1
  have r₂ : Run B (.assign modeLimit (.get "data" (.lit 0))) v v₁ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by rw [hBank']; rfl) hD')
  have r₃ : Run B (.assign modeWidth (.get "data" (.lit 1))) v₁ v₂ 3 :=
    Run.assign (evalB_get (evalB_lit hOne) (by change (v.arrs "data")[1]? = _; rw [hBank']; rfl) hN')
  have r₄ : Run B (.assign "base" (.lit 2)) v₂ v₃ 2 :=
    Run.assign (evalB_lit (by omega))
  have e (i : Env) (h : i.vars modeWidth=n) :
      (Expr.var modeWidth).evalB B i=some n := evalB_var_iff.mpr ⟨h.symm,h ▸ hN'⟩
  have ev₃ : v₃.vars modeWidth=n := by simp [v₃,v₂,modeWidth]
  have ev₄ : v₄.vars modeWidth=n := by simpa [v₄,modeWidth] using ev₃
  have r₅ : Run B (.assign "count" (.mul (.var modeWidth) (.var modeWidth))) v₃ v₄ 4 :=
    Run.assign (evalB_bin (op:=.mul) (e v₃ ev₃) (e v₃ ev₃) hNN')
  have r₆ : Run B (.assign "stride" (.add (.var modeWidth) (.lit 1))) v₄ v₅ 4 :=
    Run.assign (evalB_bin (op:=.add) (e v₄ ev₄) (evalB_lit hOne) hN1)
  have r₇ : Run B (.assign modeCursor (.lit 0)) v₅ v₆ 2 := Run.assign (evalB_lit (by omega))
  have r₈ : Run B (.assign modeAnswer (.lit 1)) v₆ z 2 := Run.assign (evalB_lit hOne)
  have rSetup : Run B modeTapeSetup v z 20 := r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈)))))
  obtain ⟨t,r₉,_,_,hV,hBit⟩ := scalarModeLoop_run xs zeroDigit n d 2 (σ:=z)
    hOne hLen hD' hn hN1 hNN' (by omega) (by omega) hWords'
    (by exact hBank') (by simp [z,v₆,modeCursor,modeAnswer])
    (by simp [z,v₆,v₅,v₄,v₃,v₂,v₁,modeLimit,modeWidth,modeCursor,modeAnswer])
    (by simp [z,v₆,v₅,v₄,v₃,modeCursor,modeAnswer])
    (by simp [z,v₆,v₅,v₄,modeCursor,modeAnswer])
    (by simp [z,v₆,v₅,modeCursor,modeAnswer]) (by simp [z])
  have hout : t.out=[] := hV.trans hOut
  obtain ⟨time,hle,hRun⟩ := r₉
  have ht : t.vars modeAnswer < B :=
    scalarWrittenBound modeAnswer hRun (by repeat constructor) (by simpa [z] using hOne)
  have r₉' : Run B (scalarModeLoop zeroDigit) z t ((60*(n*n)+36)*d+4) := ⟨time,hle,hRun⟩
  let g : Cond := .eq (.var modeAnswer) (.lit 1)
  have eg : g.evalB B t=some (t.vars modeAnswer == 1) :=
    evalB_condEq (evalB_var ht) (evalB_lit hOne)
  have hLength : (60*(n*n)+36)*d ≤ 96*xs.length := by
    rw [show (60*(n*n)+36)*d = 60*(d*(n*n))+36*d by ring]
    omega
  have hTotal : 1+((13*xs.length+5)+(20+(((60*(n*n)+36)*d+4)+6))) ≤ 120*xs.length+80 := by omega
  by_cases hh : t.vars modeAnswer=1
  · let τ := {t with out := t.out++[1]}
    have eg' : g.evalB B t=some true := by simpa [hh] using eg
    have rr : Run B emitScalarAnswer t τ 6 :=
      Run.ite_true (d:=.write (.lit 0)) eg' (Run.write (evalB_lit hOne))
    refine ⟨τ,(r₀.seq (r₁.seq (rSetup.seq (r₉'.seq rr)))).mono hTotal,?_⟩
    have hFold : FoldedScalarModes zeroDigit (d::n::ws) d n := hBit.mp hh
    simp [τ,hout,scalarWordSpec,hFold,xs]
  · let τ := {t with out := t.out++[0]}
    have eF : (t.vars modeAnswer == 1) = false :=
      Bool.eq_false_iff.mpr (fun h => hh (beq_iff_eq.mp h))
    have eg' : g.evalB B t=some false := by rw [eF] at eg; exact eg
    have rr : Run B emitScalarAnswer t τ 6 :=
      Run.ite_false (c:=.write (.lit 1)) eg' (Run.write (evalB_lit (by omega : 0<B)))
    refine ⟨τ,(r₀.seq (r₁.seq (rSetup.seq (r₉'.seq rr)))).mono hTotal,?_⟩
    have hFold : ¬FoldedScalarModes zeroDigit (d::n::ws) d n := fun he => hh (hBit.mpr he)
    simp [τ,hout,scalarWordSpec,hFold,xs]

/-- A total binary predicate agreeing with literal scalarity throughout the
official matrix frame, with original input-bit time bound. -/
theorem scalarWord_binary (zeroDigit q : ℕ) :
    ∃ g, TuringPolytime g ∧ ∀ xs, MatrixWords q xs → g xs = scalarWordSpec zeroDigit xs := by
  apply totalBinary_of_boundedWordRuns (MatrixWords q) (scalarWordSpec zeroDigit)
    (scalarWordProgram zeroDigit) (Polynomial.X+Polynomial.C (q+zeroDigit+5))
    (120*Polynomial.X+80)
  intro xs hv
  have hs := Lax51Proofs.Encoding.length_le_bitSize xs
  have hb : xs.length+q+zeroDigit+4 < bitSize xs+(q+zeroDigit+5) := by omega
  obtain ⟨τ,hr,ho⟩ := scalarWordProgram_run zeroDigit q xs hv hb
  refine ⟨fun _ => xs.length+1,τ,?_,ho⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat]
  exact hr.mono (by omega)

#print axioms scalarWordProgram_run
#print axioms scalarWord_binary
end EvenTI.P15Scalar