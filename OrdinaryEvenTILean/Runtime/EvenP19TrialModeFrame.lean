import EvenP19TrialHigherContraction
import EvenP19TrialProjectionPair
import EvenP17TrialReciprocalSweep

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 17000

namespace EvenTI.P19Trial

open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P17Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

structure HigherBanks extends ContractionOffsets where
  formLeft : ℕ
  formRight : ℕ
  trace : ℕ
  square : ℕ
  highT : ℕ
  highU : ℕ

structure HigherLayout (b : HigherBanks) (m n S : ℕ) : Prop where
  tensorBeforeTrace : b.tensor+m*m ≤ b.trace
  formLeftBeforeTrace : b.formLeft+m ≤ b.trace
  formRightBeforeTrace : b.formRight+m ≤ b.trace
  traceBeforeLeft : b.trace+n*n ≤ b.left
  leftBeforeRight : b.left+(n*n)*m ≤ b.right
  rightBeforeTemp : b.right+(n*n)*m ≤ b.tmp
  tempBeforeProduct : b.tmp+m*(n*n) ≤ b.product
  productBeforeCross : b.product+(n*n)*(n*n) ≤ b.cross
  crossBeforeSquare : b.cross+(n*n)*(n*n) ≤ b.square
  squareBeforeHighT : b.square+(n*n)*(n*n) ≤ b.highT
  squareBeforeHighU : b.square+(n*n)*(n*n) ≤ b.highU
  highTFit : b.highT < S
  highUFit : b.highU < S
  highDistinct : b.highT ≠ b.highU
  ttBefore : b.tt<b.tensor ∧ b.tt<b.formLeft ∧ b.tt<b.formRight
  uuBefore : b.uu<b.tensor ∧ b.uu<b.formLeft ∧ b.uu<b.formRight
  lowDistinct : b.tt ≠ b.uu
  oneNext : b.one=b.zero+1
  oneBefore : b.one < b.trace
  zeroApart : b.zero≠b.tt ∧ b.zero≠b.uu
  oneApart : b.one≠b.tt ∧ b.one≠b.uu

def higherLowT : String := "even.higher.scratch.low.t"
def higherLowU : String := "even.higher.scratch.low.u"
def higherHighT : String := "even.higher.scratch.high.t"
def higherHighU : String := "even.higher.scratch.high.u"

/-- Stable caller words for one higher trial. The two form offsets are also
the destination words used by the native form-pair installer. -/
def higherRegisters (b : HigherBanks) (m n : ℕ) : List (String × ℕ) :=
  [(crossN,n),(contractionTensorWidth,m),(contractionLeftWidth,n*n),(contractionRightWidth,n*n),
   (contractionTensorBase,b.tensor),(contractionLeftBase,b.left),(contractionRightBase,b.right),
   (contractionTempBase,b.tmp),(contractionOutBase,b.product),
   (crossShuffleLeft,n),(crossShuffleRight,n),(crossShuffleSource,b.product),(crossShuffleOne,b.one),
   (anchorSideWord,n),(anchorCrossWord,b.cross),(anchorSquareWord,b.square),(anchorTraceWord,b.trace),(anchorUnitWord,b.one),
   (fieldVectorStart,b.trace),(fieldVectorLength,n*n),(emitAnchorWidth,n),
   (projectionLeftFormWord,b.formLeft),(projectionRightFormWord,b.formRight),
   (higherLowT,b.tt),(higherLowU,b.uu),(higherHighT,b.highT),(higherHighU,b.highU),(dZ,b.zero)]

private def dummyBanks : HigherBanks where
  tensor := 0
  left := 0
  right := 0
  tmp := 0
  product := 0
  cross := 0
  zero := 0
  one := 0
  tt := 0
  uu := 0
  formLeft := 0
  formRight := 0
  trace := 0
  square := 0
  highT := 0
  highU := 0

def higherRegisterNames : List String := (higherRegisters dummyBanks 0 0).map Prod.fst

def higherVisitControls : List String :=
  crossA :: crossStride :: reciprocalSweepIndex :: reciprocalSweepLimit :: higherRegisterNames

theorem higherRegister_name {b : HigherBanks} {m n : ℕ} {p : String × ℕ}
    (hp : p ∈ higherRegisters b m n) : p.1 ∈ higherRegisterNames := by
  change p.1 ∈ (higherRegisters b m n).map Prod.fst
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

variable {K : Type} [Field K] [Fintype K]

structure HigherFrame (F : FieldPresentation K) (b : HigherBanks)
    (B S m n : ℕ) (base s : Env) : Prop where
  slots : Slots F canonical qN.WS S B s
  registers : ∀ p ∈ higherRegisters b m n, s.vars p.1=p.2
  preserved : ∀ k < b.trace, k≠b.tt → k≠b.uu →
    val F canonical qN.WS s k=val F canonical qN.WS base k

theorem HigherFrame.setVar {F : FieldPresentation K} {b : HigherBanks} {B S m n : ℕ}
    {base s : Env} (h : HigherFrame F b B S m n base s) (r : String) (v : ℕ)
    (hreg : r∉higherRegisterNames) (hfield : r∉regNames canonical) (hword : r≠qN.WS) :
    HigherFrame F b B S m n base (s.setVar r v) := by
  refine ⟨Slots.setVar F canonical h.slots hfield hword v,?_,?_⟩
  · intro p hp
    have hNe : p.1≠r := fun e => hreg (e ▸ higherRegister_name hp)
    simpa only [vars_setVar,if_neg hNe] using h.registers p hp
  · intro k hk ht hu
    exact (val_setVar F canonical hword s v k).trans (h.preserved k hk ht hu)

def highScratch : Com :=
  .seq (.assign dT (.var higherHighT)) (.assign dU (.var higherHighU))

def lowScratch : Com :=
  .seq (.assign dT (.var higherLowT)) (.assign dU (.var higherLowU))

private theorem rearrangeScratch_run (F : FieldPresentation K)
    {B S t u : ℕ} {σ : Env} (rT rU : String) (hSafe : rU≠dT)
    (hS : Slots F canonical qN.WS S B σ) (hT : σ.vars rT=t) (hU : σ.vars rU=u)
    (ht : t<B) (hu : u<B) :
    ∃ τ, Run B (.seq (.assign dT (.var rT)) (.assign dU (.var rU))) σ τ 4 ∧
      Slots F canonical qN.WS S B τ ∧ τ.vars dT=t ∧ τ.vars dU=u ∧
      (∀ r, r≠dT → r≠dU → τ.vars r=σ.vars r) ∧
      (∀ k, val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  let α := σ.setVar dT t
  let τ := α.setVar dU u
  have r₁ : Run B (.assign dT (.var rT)) σ α 2 := Run.assign (ev_var hT ht)
  have huα : α.vars rU=u := by simpa only [α,vars_setVar,if_neg hSafe] using hU
  have r₂ : Run B (.assign dU (.var rU)) α τ 2 := Run.assign (ev_var huα hu)
  have hSα := Slots.setVar F canonical hS (by decide : dT∉regNames canonical) (by decide : dT≠qN.WS) t
  refine ⟨τ,r₁.seq r₂,
    Slots.setVar F canonical hSα (by decide : dU∉regNames canonical) (by decide : dU≠qN.WS) u,
    rfl,rfl,?_,?_,rfl,rfl⟩
  · intro r ht hu
    simp only [τ,α,vars_setVar,if_neg ht,if_neg hu]
  · intro k
    exact (val_setVar F canonical (by decide : dU≠qN.WS) α u k).trans
      (val_setVar F canonical (by decide : dT≠qN.WS) σ t k)

theorem highScratch_run (F : FieldPresentation K)
    {B S t u : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS S B σ) (hT : σ.vars higherHighT=t) (hU : σ.vars higherHighU=u)
    (ht : t<B) (hu : u<B) :
    ∃ τ, Run B highScratch σ τ 4 ∧
      Slots F canonical qN.WS S B τ ∧ τ.vars dT=t ∧ τ.vars dU=u ∧
      (∀ r, r≠dT → r≠dU → τ.vars r=σ.vars r) ∧
      (∀ k, val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧ τ.inp=σ.inp ∧ τ.out=σ.out :=
  rearrangeScratch_run F _ _ (by decide) hS hT hU ht hu

theorem lowScratch_run (F : FieldPresentation K)
    {B S t u : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS S B σ) (hT : σ.vars higherLowT=t) (hU : σ.vars higherLowU=u)
    (ht : t<B) (hu : u<B) :
    ∃ τ, Run B lowScratch σ τ 4 ∧
      Slots F canonical qN.WS S B τ ∧ τ.vars dT=t ∧ τ.vars dU=u ∧
      (∀ r, r≠dT → r≠dU → τ.vars r=σ.vars r) ∧
      (∀ k, val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧ τ.inp=σ.inp ∧ τ.out=σ.out :=
  rearrangeScratch_run F _ _ (by decide) hS hT hU ht hu

#print axioms HigherFrame.setVar
#print axioms highScratch_run
#print axioms lowScratch_run
end EvenTI.P19Trial
