import EvenP14ProjectionReplay
import EvenP14ProjectionEngine
import EvenP11OracleCodec

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace EvenTI.P15Trial

open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning

def rawStart : String := "even_trial_raw_start"
def rawEnd : String := "even_trial_raw_end"
def sourceStart : String := "even_trial_source_start"
def sourceEnd : String := "even_trial_source_end"
def targetStart : String := "even_trial_target_start"
def targetEnd : String := "even_trial_target_end"

def trialWritePositive : Com := .write (.add (.var "word") (.lit 1))

def replayPositive (left right : String) : Com :=
  .seq (.assign "cursor" (.var left)) (.seq (.assign "stop" (.var right)) (bankLoop trialWritePositive))

def writePositiveLength (left right : String) : Com :=
  .write (.add (.sub (.var right) (.var left)) (.lit 1))

def trialRecordProgram : Com :=
  .seq (writePositiveLength rawStart rawEnd) <|
  .seq (replayPositive rawStart rawEnd) <|
  .seq (writePositiveLength sourceStart sourceEnd) <|
  .seq (replayPositive sourceStart sourceEnd) <|
  .seq (replayPositive targetStart targetEnd) (.write (.lit 0))

structure TrialFrozen (r : String) : Prop where
  cursor : r ≠ "cursor"
  stop : r ≠ "stop"
  word : r ≠ "word"

instance (r : String) : Decidable (TrialFrozen r) :=
  decidable_of_iff (r ≠ "cursor" ∧ r ≠ "stop" ∧ r ≠ "word")
    ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.cursor,h.stop,h.word⟩⟩

theorem replayPositive_run (z : List ℕ) {s e B : ℕ} {σ : Env} {left right : String}
    (hLR : TrialFrozen left) (hRR : TrialFrozen right) (hs : s≤e) (he : e≤z.length)
    (hLen : z.length < B) (hLarge : 2 < B) (hWords : ∀ w ∈ z, w+1<B)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hS : σ.vars left=s) (hE : σ.vars right=e) :
    ∃ τ, Run B (replayPositive left right) σ τ (15*(e-s)+8) ∧
      τ.out=σ.out++positiveWords (slice z s e) ∧ τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧
      ∀ r, TrialFrozen r → τ.vars r=σ.vars r := by
  let σ₁ := σ.setVar "cursor" s
  let σ₂ := σ₁.setVar "stop" e
  have h₁ : Run B (.assign "cursor" (.var left)) σ σ₁ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hS.symm,hS ▸ (hs.trans (he)).trans_lt hLen⟩)
  have hE' : σ₁.vars right=e := by simpa only [σ₁,vars_setVar,hRR.cursor,if_false] using hE
  have h₂ : Run B (.assign "stop" (.var right)) σ₁ σ₂ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hE'.symm,hE' ▸ he.trans_lt hLen⟩)
  have hPos (τ : Env) (h : τ.vars "word" ∈ z) :
      Run B trialWritePositive τ {τ with out := τ.out ++ [Nat.succ (τ.vars "word")]} 4 := by
    have hw := hWords _ h
    exact Run.write (evalB_bin (op := .add) (evalB_var (by omega))
      (evalB_lit (by omega : 1 < B)) (by simpa only [Bop.apply] using hw))
  obtain ⟨τ,h₃,hFrame,hArr,hIn,hC,hOut⟩ :=
    bankLoop_run_of_mem z (start := s) (stop := e) (σ := σ₂) (c := 4) trialWritePositive Nat.succ hPos hs he
      (by simp [σ₂,σ₁]) (by simp [σ₂]) hBank hLen (by omega)
      (fun a ha => (Nat.lt_succ_self a).trans (hWords a ha))
  have hRun : Run B (replayPositive left right) σ τ (15*(e-s)+8) :=
    (h₁.seq (h₂.seq h₃)).mono (by omega)
  refine ⟨τ,hRun,hOut,hArr,hIn,?_⟩
  intro r hr
  rw [hFrame r hr.cursor hr.word]
  simp [σ₂,σ₁,hr.cursor,hr.stop]

theorem writePositiveLength_run {B a b : ℕ} {σ : Env} {left right : String}
    (ha : σ.vars left=a) (hb : σ.vars right=b) (hAB : a≤b) (hB : b+1<B) :
    Run B (writePositiveLength left right) σ {σ with out := σ.out++[(b-a)+1]} 6 := by
  by_cases h : a < B
  · have hv : (Expr.sub (.var right) (.var left)).evalB B σ=some (b-a) :=
      evalB_bin (op := .sub) (evalB_var_iff.mpr ⟨hb.symm,hb ▸ (by omega : b<B)⟩)
        (evalB_var_iff.mpr ⟨ha.symm,ha ▸ h⟩) (by simp only [Bop.apply]; omega)
    exact Run.write (evalB_bin (op := .add) hv (evalB_lit (by omega : 1<B))
      (by simp only [Bop.apply]; omega))
  · exfalso
    omega

structure TrialWindow (z : List ℕ) (σ : Env) (left right : String) (s e : ℕ) : Prop where
  start : σ.vars left=s
  stop : σ.vars right=e
  bounds : s≤e ∧ e≤z.length

/-- Append one literal packet for the existing prepared-attempt decoder. Raw,
source and target payloads may share one bank. Only the copy registers change. -/
theorem trialRecordProgram_run (z : List ℕ) {B a A b C c E : ℕ} {σ : Env}
    (hA : TrialWindow z σ rawStart rawEnd a A)
    (hC : TrialWindow z σ sourceStart sourceEnd b C)
    (hE : TrialWindow z σ targetStart targetEnd c E)
    (hLen : z.length+1<B) (hLarge : 2<B)
    (hWords : ∀ w ∈ z, w+1<B) (hBank : σ.arrs "data"=sentinelWords z) :
    ∃ τ, Run B trialRecordProgram σ τ (15*((A-a)+(C-b)+(E-c))+44) ∧
      τ.out=σ.out++positiveWords (pairW (slice z a A) (pairW (slice z b C) (slice z c E)))++[0] ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ ∀ r, TrialFrozen r → τ.vars r=σ.vars r := by
  let σ₁ := {σ with out := σ.out++[(A-a)+1]}
  have r₁ : Run B (writePositiveLength rawStart rawEnd) σ σ₁ 6 :=
    writePositiveLength_run hA.start hA.stop hA.bounds.1 (by have := hA.bounds.2; omega)
  obtain ⟨σ₂,r₂,ho₂,ha₂,hi₂,hv₂⟩ := replayPositive_run z (σ := σ₁) (by decide) (by decide)
    hA.bounds.1 hA.bounds.2 (by omega) hLarge hWords hBank hA.start hA.stop
  have src (r : String) (hr : TrialFrozen r) : σ₂.vars r=σ.vars r := hv₂ r hr
  let σ₃ := {σ₂ with out := σ₂.out++[(C-b)+1]}
  have r₃ : Run B (writePositiveLength sourceStart sourceEnd) σ₂ σ₃ 6 :=
    writePositiveLength_run ((src _ (by decide)).trans hC.start) ((src _ (by decide)).trans hC.stop)
      hC.bounds.1 (by have := hC.bounds.2; omega)
  obtain ⟨σ₄,r₄,ho₄,ha₄,hi₄,hv₄⟩ := replayPositive_run z (σ := σ₃) (by decide) (by decide)
    hC.bounds.1 hC.bounds.2 (by omega) hLarge hWords
    ((congrFun ha₂ "data").trans hBank) ((src _ (by decide)).trans hC.start)
    ((src _ (by decide)).trans hC.stop)
  have tgt (r : String) (hr : TrialFrozen r) : σ₄.vars r=σ.vars r := (hv₄ r hr).trans (src r hr)
  obtain ⟨σ₅,r₅,ho₅,ha₅,hi₅,hv₅⟩ := replayPositive_run z (σ := σ₄) (by decide) (by decide)
    hE.bounds.1 hE.bounds.2 (by omega) hLarge hWords
    ((congrFun (ha₄.trans ha₂) "data").trans hBank) ((tgt _ (by decide)).trans hE.start)
    ((tgt _ (by decide)).trans hE.stop)
  let τ := {σ₅ with out := σ₅.out++[0]}
  have r₆ : Run B (.write (.lit 0)) σ₅ τ 2 := Run.write (evalB_lit (by omega))
  refine ⟨τ,(r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))).mono ?_,?_,
    ha₅.trans (ha₄.trans ha₂),hi₅.trans (hi₄.trans hi₂),fun r hr => (hv₅ r hr).trans (tgt r hr)⟩
  · simp only [Nat.mul_add]
    omega
  · change σ₅.out++[0]=_
    rw [ho₅,ho₄]
    change ((σ₂.out++[(C-b)+1])++_)++_++[0]=_
    rw [ho₂]
    have hL₁ := slice_length z (c := a) hA.bounds.2
    have hL₂ := slice_length z (c := b) hC.bounds.2
    simp [σ₁,hL₁,hL₂,positiveWords,pairW,List.append_assoc]

#print axioms replayPositive_run
#print axioms trialRecordProgram_run
end EvenTI.P15Trial
