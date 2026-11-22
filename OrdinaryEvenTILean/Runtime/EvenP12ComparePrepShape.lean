import EvenP12ComparePrepRaw
import EvenP10ScanCompare
import Mathproof.Meta.Problem18IMPNaturalPower20261001

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPNaturalPower20261001 (naturalPowerRoutine naturalPower_run)
set_option autoImplicit false

def rawOrder : String := "even.compare.shape.order"
def shapePower : Mathproof.Problem18IMPNaturalPower20261001.Names :=
  ⟨"even.compare.shape.dimension","even.compare.shape.half","even.compare.shape.side",
    "even.compare.shape.power.cursor"⟩

def rawShapeHeader : Com :=
  .seq (.assign rawOrder (.get rawPairIO.array (.lit 0)))
    (.seq (.assign shapePower.base (.get rawPairIO.array (.lit 1)))
      (.assign shapePower.exponent (.div (.var rawOrder) (.lit 2))))

def rawShapeProgram : Com := .seq rawShapeHeader (naturalPowerRoutine shapePower)

structure PairShape (σ : Env) (words : List Nat) (d n : Nat) : Prop where
  bank : σ.arrs rawPairIO.array = words
  order : σ.vars rawOrder = d
  dimension : σ.vars shapePower.base = n
  half : σ.vars shapePower.exponent = d/2
  side : σ.vars shapePower.out = n^(d/2)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem rawShapeProgram_run (F : FieldEncoding K) (words : List Nat) {p : ParsedPair K}
    (h : decodePair F words = some p) {B : Nat} {σ : Env}
    (hBank : σ.arrs rawPairIO.array = words) (hB : words.length < B) :
    ∃ τ, Run B rawShapeProgram σ τ (20*(words.length+1)+11) ∧
      PairShape τ words p.d p.n ∧ τ.arrs = σ.arrs ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  obtain ⟨rest,hWords,hLength,hD,hEven,hN⟩ := decodePair_some h
  have hLit : 2 < B := by
    have ha := congrArg List.length hWords
    simp only [List.length_cons] at ha
    omega
  have hPow : p.n^p.d < B := by
    have ha := congrArg List.length hWords
    simp only [List.length_cons] at ha
    omega
  have hnB : p.n < B := by
    have hx : p.n ≤ p.n^p.d := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < p.n) (by omega : 1 ≤ p.d)
    omega
  have hdB : p.d < B := by
    have hx := (Nat.lt_two_pow_self (n := p.d)).le.trans (Nat.pow_le_pow_left hN p.d)
    omega
  let t₁ := σ.setVar rawOrder p.d
  let t₂ := t₁.setVar shapePower.base p.n
  let t₃ := t₂.setVar shapePower.exponent (p.d/2)
  have r₁ : Run B (.assign rawOrder (.get rawPairIO.array (.lit 0))) σ t₁ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by rw [hBank,hWords]; rfl) hdB)
  have r₂ : Run B (.assign shapePower.base (.get rawPairIO.array (.lit 1))) t₁ t₂ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by change (σ.arrs rawPairIO.array)[1]? = _; rw [hBank,hWords]; rfl) hnB)
  have ho₂ : t₂.vars rawOrder = p.d := by simp [t₂,t₁,rawOrder,shapePower]
  have hHalf : p.d/2 < B := (Nat.div_le_self ..).trans_lt hdB
  have ev : (Expr.var rawOrder).evalB B t₂ = some p.d := by
    rw [evalB_var_iff,ho₂]; exact ⟨rfl,hdB⟩
  have r₃ : Run B (.assign shapePower.exponent (.div (.var rawOrder) (.lit 2))) t₂ t₃ 4 :=
    Run.assign (evalB_bin (op := .div) ev (evalB_lit hLit) hHalf)
  have hn₃ : t₃.vars shapePower.base = p.n := by simp [t₃,t₂,shapePower]
  have hh₃ : t₃.vars shapePower.exponent = p.d/2 := by simp [t₃]
  have hPowers : ∀ i ≤ p.d/2, p.n^i < B := by
    intro i hi
    exact (Nat.pow_le_pow_right (by omega) (hi.trans (Nat.div_le_self ..))).trans_lt hPow
  have hR := naturalPower_run shapePower t₃ (by decide) (by decide) (by decide)
    (by rw [hh₃]; exact hHalf) (by rw [hn₃]; exact hnB)
    (by rw [hh₃,hn₃]; exact hPowers)
  rw [hh₃] at hR
  let τ := Mathproof.Problem18IMPNaturalPower20261001.state shapePower t₃ (p.d/2)
  have rr := r₁.seq (r₂.seq r₃)
  have hWhole : Run B rawShapeProgram σ τ (20*(words.length+1)+11) :=
    (rr.seq hR).mono (by
      have hh : p.d/2 ≤ words.length := by
        have hd := Nat.div_le_self p.d 2
        have hp := Lax51Proofs.Encoding.length_le_bitSize words
        have h1 : p.d ≤ words.length := by
          let n := words.length
          have ha := congrArg List.length hWords
          simp only [List.length_cons] at ha
          have hx := (Nat.lt_two_pow_self (n := p.d)).le.trans (Nat.pow_le_pow_left hN p.d)
          omega
        omega
      omega)
  refine ⟨τ,hWhole,⟨hBank,?_,?_,?_,?_⟩,rfl,rfl,rfl⟩
  · simpa [τ,Mathproof.Problem18IMPNaturalPower20261001.state,t₃,rawOrder,shapePower] using ho₂
  · change t₃.vars shapePower.base = p.n
    exact hn₃
  · change t₃.vars shapePower.exponent = p.d/2
    exact hh₃
  · change t₃.vars shapePower.base ^ (p.d/2) = p.n ^ (p.d/2)
    rw [hn₃]

#print axioms rawShapeProgram_run
end EvenTI.P12ComparePrep
