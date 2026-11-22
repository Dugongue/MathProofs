import EvenP14CutRankControl

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites run_frame noRead)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dL)
open Mathproof.P15DecideIMPKerBasis20261007 (KBLay XBs kK)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def liveCutStride (n d i : ℕ) : ℕ := if i ≤ d then n^(d-i) else 0

private theorem liveCutStride_next {n d i : ℕ} (hn : 2 ≤ n) (hi : i < d+1) :
    liveCutStride n d i / n = liveCutStride n d (i+1) := by
  have hle : i ≤ d := by omega
  by_cases h : i<d
  · have h' : i+1 ≤ d := by omega
    simp only [liveCutStride,if_pos hle,if_pos h']
    have hh : d-i = (d-(i+1))+1 := by omega
    rw [hh,pow_succ]
    exact Nat.mul_div_cancel _ (by omega)
  · have he : i=d := by omega
    subst i
    have hnle : ¬d+1≤d := by omega
    simp [liveCutStride,hnle,Nat.div_eq_of_lt (show 1<n by omega)]

def cutRankStart : Com :=
  .seq (.assign cutRankCursor (.lit 0)) <|
  .seq (.assign cutRankAccept (.lit 1)) <|
  .assign retainedStride (.var tNR)

def cutRankGuard : Cond := .lt (.var cutRankCursor) (.var cutRankLimit)

def cutRankUpdate : Com :=
  .seq (.ite (.eq (.var kK) (.lit 0)) .skip (.assign cutRankAccept (.lit 0))) <|
  .seq (.assign retainedStride (.bin .div (.var retainedStride) (.var tD))) <|
  .assign cutRankCursor (.add (.var cutRankCursor) (.lit 1))

noncomputable def cutRankSweepBody : Com := .seq cutRankModeCall cutRankUpdate

noncomputable def cutRankSweep : Com :=
  .seq cutRankStart (.while cutRankGuard cutRankSweepBody)

def CutRankSlotFixed (d n RB OUT Z Sn s : ℕ) : Prop :=
  s < Sn ∧ (n + 1) * XBs (n ^ d) n ≤ s ∧ (s < RB ∨ OUT + n * n ≤ s) ∧ s ≠ Z + 2 ∧ s ≠ Z + 3

def CutRankScalarFixed (r : String) : Prop :=
  CutRankRegisterFresh r ∧ r≠cutRankCursor ∧ r≠cutRankAccept ∧ r≠retainedStride


/-- Sweep all retained modes of an already installed candidate. The original
candidate, all protected cut-basis slots, and outer scan registers survive.
The answer is the exact Boolean filter used by the reference trial list. -/
theorem cutRankSweep_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : ℕ} {σ : Env} (x : Coord (d+1) n → K)
    (hd : 1 ≤ d) (hn : 2 ≤ n) (hL : n^(d+1) ≤ L) (hCount : d+1 < B)
    (layout : KBLay (n^d) n AM OUT Z Sn B)
    (hSourceLow : (n+1)*XBs (n^d) n ≤ src)
    (hSrcFit : src+n^d*n ≤ RB) (hDstFit : RB+n^d*n ≤ AM)
    (h : CutRankBank F x src RB AM OUT Z Sn B σ) :
    ∃ τ, Run B cutRankSweep σ τ ((cutRankModeCost F L+24)*(d+1)+10) ∧
      CutRankBank F x src RB AM OUT Z Sn B τ ∧
      τ.vars cutRankAccept ≤ 1 ∧
      (τ.vars cutRankAccept=1 ↔ rawRetainedFullRank x=true) ∧
      (∀ s, CutRankSlotFixed d n RB OUT Z Sn s →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, CutRankScalarFixed r → τ.vars r = σ.vars r) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
  let bank := CutRankBank F x src RB AM OUT Z Sn B
  let memKeep := CutRankSlotFixed d n RB OUT Z Sn
  let I (s : Env) :=
    bank s ∧ s.vars cutRankCursor≤d+1 ∧
      s.vars retainedStride=liveCutStride n d (s.vars cutRankCursor) ∧
      s.vars cutRankAccept≤1 ∧
      (s.vars cutRankAccept=1 ↔ ∀ j : Fin (d+1), j.val<s.vars cutRankCursor → retainedCutPass x j=true) ∧
      (∀ t, memKeep t → val F canonical qN.WS s t = val F canonical qN.WS σ t) ∧
      (∀ r, CutRankScalarFixed r → s.vars r = σ.vars r) ∧ s.inp=σ.inp ∧ s.out=σ.out
  let V (s : Env) := d+1-s.vars cutRankCursor
  have hb := layout.s_b
  have hnB : n<B := by omega
  have hRowsB : n^d<B := by omega
  have hOne : 1<B := by omega
  have hA {s : Env} {name : String} {v : ℕ} (hEq : s.vars name=v) (hBound : v<B) :
      (Expr.var name).evalB B s = some v := evalB_var_iff.mpr ⟨hEq.symm,hEq ▸ hBound⟩
  let σ₀ := σ.setVar cutRankCursor 0
  let σ₁ := σ₀.setVar cutRankAccept 1
  let σ₂ := σ₁.setVar retainedStride (n^d)
  have hRun₀ : Run B cutRankStart σ σ₂ 6 := by
    have r₀ : Run B (.assign cutRankCursor (.lit 0)) σ σ₀ 2 :=
      Run.assign (evalB_lit (by omega))
    have r₁ : Run B (.assign cutRankAccept (.lit 1)) σ₀ σ₁ 2 := Run.assign (evalB_lit hOne)
    have r₂ : Run B (.assign retainedStride (.var tNR)) σ₁ σ₂ 2 :=
      Run.assign (hA (by
        have ht := h.regs (tNR,n^d) (by simp [cutRankArgs])
        simpa [σ₀,σ₁,show tNR≠cutRankCursor by decide,show tNR≠cutRankAccept by decide] using ht) hRowsB)
    exact r₀.seq (r₁.seq r₂)
  have hInitial : I σ₂ := by
    have hS₀ := h.setVar F cutRankCursor 0 (by decide) (by decide) (by decide)
    have hS₁ := hS₀.setVar F cutRankAccept 1 (by decide) (by decide) (by decide)
    have hS₂ := hS₁.setVar F retainedStride (n^d) (by decide) (by decide) (by decide)
    refine ⟨hS₂,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
    · simp [σ₂,σ₁,σ₀,show cutRankCursor≠retainedStride by decide,show cutRankCursor≠cutRankAccept by decide]
    · simp [σ₂,σ₁,σ₀,liveCutStride,show cutRankCursor≠retainedStride by decide,
        show cutRankCursor≠cutRankAccept by decide]
    · simp [σ₂,σ₁,show cutRankAccept≠retainedStride by decide]
    · simp [σ₂,σ₁,σ₀,show cutRankAccept≠retainedStride by decide,
        show cutRankCursor≠retainedStride by decide,show cutRankCursor≠cutRankAccept by decide]
    · intro t ht
      simp only [σ₂,σ₁,σ₀,val_setVar F canonical (show retainedStride≠qN.WS by decide),
        val_setVar F canonical (show cutRankAccept≠qN.WS by decide),
        val_setVar F canonical (show cutRankCursor≠qN.WS by decide)]
    · intro r hr
      rcases hr with ⟨_,hi,ha,hs⟩
      simp [σ₂,σ₁,σ₀,hi,ha,hs]
  have guard (s : Env) (hs : I s) :
      cutRankGuard.evalB B s = some (decide (s.vars cutRankCursor<d+1)) := by
    have hLim := hs.1.regs (cutRankLimit,d+1) (by simp [cutRankArgs])
    exact evalB_condLt (evalB_var (hs.2.1.trans_lt hCount)) (hA hLim hCount)
  have each (s : Env) (hs : I s) (hg : cutRankGuard.evalB B s = some true) :
      ∃ u, Run B cutRankSweepBody s u (cutRankModeCost F L+20) ∧ I u ∧ V u<V s := by
    obtain ⟨hsBank,hsIdx,hsStride,hsBit,hsSpec,hsMem,hsVars,hsIn,hsOut⟩ := hs
    let j := s.vars cutRankCursor
    have hj : j<d+1 := by
      rw [guard s ⟨hsBank,hsIdx,hsStride,hsBit,hsSpec,hsMem,hsVars,hsIn,hsOut⟩] at hg
      simpa [j] using hg
    let i : Fin (d+1) := ⟨j,hj⟩
    have hStride : s.vars retainedStride = n^(d-i.val) := by
      rw [hsStride]
      simp [liveCutStride,j,i,show j≤d by omega]
    obtain ⟨t,rt,htBank,htMem,htVars,htIn,htOut,htK,htTest⟩ :=
      cutRankModeBank_run D F x i hd hn hL layout hSourceLow hSrcFit hDstFit hsBank hStride
    have hcc : t.vars cutRankCursor = j := htVars _ (by decide)
    have hca : t.vars cutRankAccept = s.vars cutRankAccept := htVars _ (by decide)
    have hcs : t.vars retainedStride = liveCutStride n d j := (htVars _ (by decide)).trans hsStride
    have htLen : t.vars tD = n := htBank.regs (tD,n) (by simp [cutRankArgs])
    let b := if t.vars kK=0 then t else t.setVar cutRankAccept 0
    let v := b.setVar retainedStride (liveCutStride n d (j+1))
    let u := v.setVar cutRankCursor (j+1)
    have hEv := evalB_condEq (evalB_var (σ := t) (x := kK) (htK.trans_lt hnB)) (evalB_lit (by omega : 0<B))
    have rbit : Run B (.ite (.eq (.var kK) (.lit 0)) .skip (.assign cutRankAccept (.lit 0))) t b 8 := by
      by_cases he : t.vars kK=0
      · have ee : (Cond.eq (.var kK) (.lit 0)).evalB B t = some true := by simpa [he] using hEv
        simpa only [b,if_pos he] using (Run.ite_true (d:=.assign cutRankAccept (.lit 0)) ee Run.skip).mono (by decide : _≤8)
      · have ee : (Cond.eq (.var kK) (.lit 0)).evalB B t = some false := by simpa [he] using hEv
        simpa only [b,if_neg he] using (Run.ite_false (c:=.skip) ee
          (Run.assign (x:=cutRankAccept) (evalB_lit (by omega)))).mono (by decide : _≤8)
    have bBank : bank b := by
      by_cases he : t.vars kK=0
      · simpa only [b,if_pos he] using htBank
      · simpa only [b,if_neg he] using htBank.setVar F cutRankAccept 0 (by decide) (by decide) (by decide)
    have eRow : b.vars retainedStride = liveCutStride n d j := by
      by_cases he : t.vars kK=0 <;> simpa [b,he,show retainedStride≠cutRankAccept by decide] using hcs
    have hStrideB : liveCutStride n d j < B := by
      have hpow : n^(d-j) ≤ n^d := Nat.pow_le_pow_right (by omega) (by omega)
      simpa [liveCutStride,show j≤d by omega] using hpow.trans_lt hRowsB
    have hQuot : liveCutStride n d j / n < B := (Nat.div_le_self ..).trans_lt hStrideB
    have hN := bBank.regs (tD,n) (by simp [cutRankArgs])
    have rdiv : Run B (.assign retainedStride (.bin .div (.var retainedStride) (.var tD))) b v 4 := by
      have ev := evalB_bin (op:=.div) (hA eRow hStrideB) (hA hN hnB) hQuot
      change (Expr.bin .div (.var retainedStride) (.var tD)).evalB B b = some (liveCutStride n d j/n) at ev
      rw [liveCutStride_next hn hj] at ev
      exact Run.assign ev
    have eIdx : v.vars cutRankCursor = j := by
      by_cases he : t.vars kK=0 <;>
        simpa [v,b,he,show cutRankCursor≠retainedStride by decide,show cutRankCursor≠cutRankAccept by decide] using hcc
    have rinc : Run B (.assign cutRankCursor (.add (.var cutRankCursor) (.lit 1))) v u 4 :=
      Run.assign (evalB_bin (op:=.add) (hA eIdx (hj.trans hCount)) (evalB_lit hOne) (show j+1<B by omega))
    have uIdx : u.vars cutRankCursor=j+1 := by simp [u]
    have uStride : u.vars retainedStride=liveCutStride n d (j+1) := by
      simp [u,v,show retainedStride≠cutRankCursor by decide]
    have hTests :
        (∀ q : Fin (d+1), q.val<j+1 → retainedCutPass x q=true) ↔
          (∀ q : Fin (d+1), q.val<j → retainedCutPass x q=true) ∧ retainedCutPass x i=true := by
      constructor
      · intro ha
        exact ⟨fun q hq => ha q (by omega),ha i (by simp [i])⟩
      · rintro ⟨a,b⟩ q hq
        by_cases he : q.val=j
        · have he' : q=i := Fin.ext he
          simpa [he'] using b
        · exact a q (by omega)
    have uBit : u.vars cutRankAccept =
        (if t.vars kK=0 then s.vars cutRankAccept else 0) := by
      by_cases he : t.vars kK=0 <;> simp [u,v,b,he,hca,
        show cutRankAccept≠retainedStride by decide,show cutRankAccept≠cutRankCursor by decide]
    have uValid : u.vars cutRankAccept=1 ↔ ∀ q : Fin (d+1), q.val<j+1 → retainedCutPass x q=true := by
      rw [uBit,hTests]
      by_cases he : t.vars kK=0
      · rw [if_pos he,hsSpec]
        simp [j,htTest.mp he]
      · rw [if_neg he]
        have hf : retainedCutPass x i ≠ true := fun he' => he (htTest.mpr he')
        simp [hf]
    have uBank : bank u :=
      (bBank.setVar F retainedStride _ (by decide) (by decide) (by decide)).setVar
        F cutRankCursor _ (by decide) (by decide) (by decide)
    have hMem₀ (k : ℕ) : val F canonical qN.WS u k = val F canonical qN.WS t k := by
      by_cases he : t.vars kK=0 <;> simp only [u,v,b,he,if_true,if_false,
        val_setVar F canonical (show retainedStride≠qN.WS by decide),
        val_setVar F canonical (show cutRankAccept≠qN.WS by decide),
        val_setVar F canonical (show cutRankCursor≠qN.WS by decide)]
    have hVars₀ (r : String) (hr : CutRankScalarFixed r) : u.vars r = s.vars r := by
      rcases hr with ⟨hr,ha,hb,hc⟩
      by_cases he : t.vars kK=0 <;> simp [u,v,b,he,ha,hb,hc,htVars r hr]
    have hRun : Run B cutRankSweepBody s u (cutRankModeCost F L+20) :=
      (rt.seq (rbit.seq (rdiv.seq rinc))).mono (by omega)
    refine ⟨u,hRun,⟨uBank,by rw [uIdx]; omega,by rw [uIdx]; exact uStride,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · rw [uBit]
      split <;> omega
    · rw [uIdx]
      exact uValid
    · rintro k ⟨a,b,c,d,e⟩
      exact (hMem₀ k).trans ((htMem k a b c d e).trans (hsMem k ⟨a,b,c,d,e⟩))
    · intro k hk
      exact (hVars₀ k hk).trans (hsVars k hk)
    · by_cases he : t.vars kK=0 <;> simp [u,v,b,he,htIn,hsIn]
    · by_cases he : t.vars kK=0 <;> simp [u,v,b,he,htOut,hsOut]
    · dsimp only [V]; rw [uIdx]; omega
  obtain ⟨τ,hLoop,ht,htEnd⟩ := Run.while_count I V (cutRankModeCost F L+20)
    (fun q hq => ⟨_,guard q hq⟩) each hInitial
  have htNo : ¬ τ.vars cutRankCursor<d+1 := by
    rw [guard τ ht] at htEnd
    simpa using htEnd
  obtain ⟨hτ,hi,hStride,hBit,hSpec,hMem,hVars,hIn,hOut⟩ := ht
  have htIdx : τ.vars cutRankCursor=d+1 := by omega
  have hZero : σ₂.vars cutRankCursor=0 := by
    simp [σ₂,σ₁,σ₀,show cutRankCursor≠retainedStride by decide,show cutRankCursor≠cutRankAccept by decide]
  have hBound : Run B cutRankSweep σ τ ((cutRankModeCost F L+24)*(d+1)+10) :=
    (hRun₀.seq hLoop).mono (by
      have hc : 4 + (cutRankModeCost F L + 20) = cutRankModeCost F L + 24 := by omega
      simp [V,hZero,cutRankGuard,Cond.size,hc]
      omega)
  refine ⟨τ,hBound,hτ,hBit,?_,hMem,hVars,hIn,hOut⟩
  rw [rawRetainedFullRank_eq_all,hSpec,htIdx]
  exact forall_congr' fun j => ⟨fun h => h j.isLt,fun h _ => h⟩

noncomputable instance (r : String) : Decidable (CutRankScalarFixed r) := by
  unfold CutRankScalarFixed
  infer_instance

def cutRankSavedCount : String := "even_compare_retained_saved_length"

noncomputable def cutRankSweepPreservingCount : Com :=
  .seq (.assign cutRankSavedCount (.var dL))
    (.seq cutRankSweep (.assign dL (.var cutRankSavedCount)))

/-- Restore the coefficient scan's shared dL register after the rank sweeps. -/
theorem cutRankSweepPreservingCount_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : ℕ} {σ : Env} (x : Coord (d+1) n → K)
    (hd : 1 ≤ d) (hn : 2 ≤ n) (hL : n^(d+1) ≤ L) (hCount : d+1 < B)
    (layout : KBLay (n^d) n AM OUT Z Sn B)
    (hSourceLow : (n+1)*XBs (n^d) n ≤ src)
    (hSrcFit : src+n^d*n ≤ RB) (hDstFit : RB+n^d*n ≤ AM)
    (h : CutRankBank F x src RB AM OUT Z Sn B σ)
    (hSaved : σ.vars dL<B) :
    ∃ τ, Run B cutRankSweepPreservingCount σ τ ((cutRankModeCost F L+24)*(d+1)+14) ∧
      CutRankBank F x src RB AM OUT Z Sn B τ ∧
      τ.vars dL=σ.vars dL ∧ τ.vars cutRankAccept ≤ 1 ∧
      (τ.vars cutRankAccept=1 ↔ rawRetainedFullRank x=true) ∧
      (∀ s, CutRankSlotFixed d n RB OUT Z Sn s →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, CutRankScalarFixed r → r ≠ cutRankSavedCount → τ.vars r = σ.vars r) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
  let ρ := σ.setVar cutRankSavedCount (σ.vars dL)
  have r₀ : Run B (.assign cutRankSavedCount (.var dL)) σ ρ 2 := Run.assign (evalB_var hSaved)
  have hρ : CutRankBank F x src RB AM OUT Z Sn B ρ :=
    h.setVar F cutRankSavedCount _ (by decide) (by decide) (by decide)
  obtain ⟨t,r₁,ht,hBit,hSpec,hMem,hVars,hIn,hOut⟩ :=
    cutRankSweep_run D F x hd hn hL hCount layout hSourceLow hSrcFit hDstFit hρ
  have he : t.vars cutRankSavedCount=σ.vars dL := (hVars _ (by decide)).trans (by simp [ρ])
  let τ := t.setVar dL (σ.vars dL)
  have r₂ : Run B (.assign dL (.var cutRankSavedCount)) t τ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨he.symm,he ▸ hSaved⟩)
  have hDL := ht.setVar F dL (σ.vars dL) (by decide) (by decide) (by decide)
  have hb : τ.vars cutRankAccept=t.vars cutRankAccept := by
    simp [τ,show cutRankAccept≠dL by decide]
  refine ⟨τ,(r₀.seq (r₁.seq r₂)).mono (by omega),hDL,by simp [τ],by rwa [hb],
    by rwa [hb],?_,?_,hIn,hOut⟩
  · intro s hs
    exact (val_setVar F canonical (by decide : dL≠qN.WS) t _ s).trans
      ((hMem s hs).trans (val_setVar F canonical (by decide : cutRankSavedCount≠qN.WS) σ _ s))
  · intro r hr hSaved'
    have hdL : r≠dL := hr.1.2.2.2.2.2.2.2.2.1
    simpa [τ,ρ,hdL,hSaved'] using (hVars r hr)

theorem cutRankSweepPreservingCount_arrays {B c : ℕ} {σ τ : Env}
    (h : Run B cutRankSweepPreservingCount σ τ c) (a : String)
    (hMem : a≠canonical.mem) (hScratch : a≠canonical.scratch) :
    τ.arrs a=σ.arrs a := by
  have hk : arrayWrites cutRankSweepPreservingCount ⊆ {canonical.mem, canonical.scratch} := by decide
  apply (run_frame h).2.1 a
  intro ha
  simpa [hMem,hScratch] using hk ha

#print axioms cutRankSweepPreservingCount_run
#print axioms cutRankSweepPreservingCount_arrays
#print axioms cutRankSweep_run
end EvenTI.P12ComparePrep
