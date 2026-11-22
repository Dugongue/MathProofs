import EvenP15TrialRecord

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P15Trial

open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites run_frame noRead)

structure TrialAxis where
  scan : String
  limit : String
  start : String
  stop : String

def TrialAxis.Valid (x : TrialAxis) : Prop :=
  x.start ≠ x.stop ∧ x.start ≠ x.scan ∧ x.stop ≠ x.scan ∧ x.start ≠ x.limit ∧
    x.stop ≠ x.limit ∧ x.scan ≠ x.limit

instance (x : TrialAxis) : Decidable x.Valid := by unfold TrialAxis.Valid; infer_instance

def TrialAxis.openBlock (x : TrialAxis) : Com :=
  .seq (.assign x.start (.add (.var x.scan) (.lit 1)))
    (.assign x.stop (.add (.var x.start) (.get "data" (.var x.scan))))

def TrialAxis.axisBody (x : TrialAxis) (visit : Com) : Com :=
  .seq x.openBlock (.seq visit (.assign x.scan (.var x.stop)))

def TrialAxis.guard (x : TrialAxis) : Cond := .lt (.var x.scan) (.var x.limit)

def TrialAxis.traverse (x : TrialAxis) (visit : Com) : Com :=
  .while x.guard (x.axisBody visit)

theorem flatBlocks_cons (z a : List ℕ) (tail : List (List ℕ)) {p stop : ℕ}
    (hp : p ≤ stop) (hStop : stop ≤ z.length)
    (h : slice z p stop = (a::tail).flatMap blockW) :
    ∃ hh : p < z.length, z[p]'hh=a.length ∧ p+1+a.length ≤ stop ∧
      slice z (p+1) (p+1+a.length)=a ∧ slice z (p+1+a.length) stop=tail.flatMap blockW := by
  have hL := congrArg List.length h
  rw [slice_length z hStop] at hL
  simp only [List.flatMap_cons,blockW,List.length_append,List.length_cons] at hL
  have hP : p < stop := by omega
  have hE : p+1+a.length ≤ stop := by omega
  rw [slice_cons z hP hStop] at h
  have hi : p < z.length := hP.trans_le hStop
  have h₀ : z[p]'hi::slice z (p+1) stop = a.length::(a++tail.flatMap blockW) := h
  obtain ⟨hHead,hTail⟩ := List.cons.inj h₀
  have hs := slice_pair z (show p+1 ≤ stop by omega) hStop a.length
  simp only [Nat.min_eq_left (show a.length ≤ stop-(p+1) by omega)] at hs
  rw [hTail] at hs
  exact ⟨hi,hHead,hE,by simpa using hs.1.symm,by simpa using hs.2.symm⟩

theorem openTrialBlock_run (z : List ℕ) (x : TrialAxis) (vx : x.Valid) {p l B : ℕ} {σ : Env}
    (a : List ℕ) (tail : List (List ℕ)) (hσ : σ.vars x.scan=p) (hL : l ≤ z.length)
    (hp : p ≤ l) (hLen : z.length < B) (hB : 1 < B) (hBank : σ.arrs "data"=sentinelWords z)
    (h : slice z p l=(a::tail).flatMap blockW) :
    let q := p+1+a.length
    ∃ τ, Run B x.openBlock σ τ 9 ∧ TrialWindow z τ x.start x.stop (p+1) q ∧ q ≤ l ∧
      slice z (p+1) q=a ∧ slice z q l=tail.flatMap blockW ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out ∧
      ∀ r, r ≠ x.start → r ≠ x.stop → τ.vars r=σ.vars r := by
  obtain ⟨hi,hHead,hE,hSlice,hTail⟩ := flatBlocks_cons z a tail hp hL h
  let σ₁ := σ.setVar x.start (p+1)
  let τ := σ₁.setVar x.stop (p+1+a.length)
  have hpB : p < B := (hp.trans hL).trans_lt hLen
  have h₁ : Run B (.assign x.start (.add (.var x.scan) (.lit 1))) σ σ₁ 4 :=
    Run.assign (evalB_bin (op := .add) (evalB_var_iff.mpr ⟨hσ.symm,hσ ▸ hpB⟩) (evalB_lit hB)
      (by change p+1 < B; have := hE.trans (hL.trans hLen.le); omega))
  have hs : σ₁.vars x.scan=p := by simpa [σ₁,Ne.symm vx.2.1] using hσ
  have hv : (Expr.get "data" (.var x.scan)).evalB B σ₁=some a.length := by
    apply evalB_get (evalB_var_iff.mpr ⟨hs.symm,hs ▸ hpB⟩) _ (by omega)
    change (σ.arrs "data")[p]? = some a.length
    rw [hBank,sentinelWords,List.getElem?_append_left hi,List.getElem?_eq_getElem hi,hHead]
  have h₂ : Run B (.assign x.stop (.add (.var x.start) (.get "data" (.var x.scan)))) σ₁ τ 5 :=
    Run.assign (evalB_bin (op := .add) (evalB_var_iff.mpr ⟨by simp [σ₁],by simp [σ₁]; omega⟩) hv
      (by have := hE.trans (hL.trans hLen.le); simp only [Bop.apply]; omega))
  refine ⟨τ,h₁.seq h₂,⟨by simp [τ,σ₁,vx.1],by simp [τ],by omega,hE.trans hL⟩,hE,
    hSlice,hTail,rfl,rfl,rfl,?_⟩
  intro r h1 h2
  simp [τ,σ₁,h1,h2]

theorem traverseTrialBlocks_run (z : List ℕ) (x : TrialAxis) (vx : x.Valid)
    {B l C : ℕ} (visit : Com) (render : List ℕ → List ℕ) (ctx : Env → Prop)
    (hUpdate : ∀ {s t : Env}, (∀ r, r ≠ x.start → r ≠ x.stop → r ≠ x.scan → t.vars r=s.vars r) →
      ctx s → ctx t)
    (hL : l ≤ z.length) (hLen : z.length < B) (hB : 2 < B)
    (hVisit : ∀ (s : Env) (a : List ℕ) (i j : ℕ),
      ctx s → s.vars x.limit=l → s.arrs "data"=sentinelWords z →
      TrialWindow z s x.start x.stop i j → slice z i j=a →
      ∃ t, Run B visit s t C ∧ ctx t ∧ t.vars x.limit=l ∧ t.vars x.stop=j ∧
        t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out++render a)
    (rows : List (List ℕ)) {p : ℕ} {σ : Env}
    (hP : p ≤ l) (hScan : σ.vars x.scan=p) (hLim : σ.vars x.limit=l)
    (hBank : σ.arrs "data"=sentinelWords z) (hCtx : ctx σ)
    (hRows : slice z p l=rows.flatMap blockW) :
    ∃ τ, Run B (x.traverse visit) σ τ ((C+15)*rows.length+4) ∧
      ctx τ ∧ τ.vars x.scan=l ∧ τ.vars x.limit=l ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out++rows.flatMap render := by
  have hE : l < B := hL.trans_lt hLen
  induction rows generalizing p σ with
  | nil =>
    have hLen0 : (slice z p l).length = 0 := by rw [hRows]; rfl
    rw [slice_length z hL] at hLen0
    have hEq : p=l := by omega
    have hg : x.guard.evalB B σ=some false := by
      have he := evalB_condLt (evalB_var_iff.mpr ⟨hScan.symm,hScan ▸ hP.trans_lt hE⟩)
        (evalB_var_iff.mpr ⟨hLim.symm,hLim ▸ hE⟩)
      simpa [TrialAxis.guard,hEq] using he
    exact ⟨σ,Run.while_false hg,hCtx,hScan.trans hEq,hLim,rfl,rfl,by simp⟩
  | cons a rows ih =>
    obtain ⟨ρ,r₁,hWindow,hEnd,hA,hTail,hArr,hInp,hOut,hs⟩ :=
      openTrialBlock_run z x vx a rows hScan hL hP hLen (by omega) hBank hRows
    let j := p+1+a.length
    have hCtxρ : ctx ρ := hUpdate (fun r h₁ h₂ _ => hs r h₁ h₂) hCtx
    have hLimρ : ρ.vars x.limit=l := (hs _ (Ne.symm vx.2.2.2.1) (Ne.symm vx.2.2.2.2.1)).trans hLim
    obtain ⟨η,r₂,hCtxη,hLimη,hStop,hArrη,hInη,hOutη⟩ :=
      hVisit ρ a (p+1) j hCtxρ hLimρ ((congrFun hArr "data").trans hBank) hWindow hA
    let t := η.setVar x.scan j
    have r₃ : Run B (.assign x.scan (.var x.stop)) η t 2 :=
      Run.assign (evalB_var_iff.mpr ⟨hStop.symm,hStop ▸ hEnd.trans_lt hE⟩)
    have hCtxT : ctx t := hUpdate (fun r _ _ hr => by simp [t,hr]) hCtxη
    have hLimT : t.vars x.limit=l := by simpa [t,Ne.symm vx.2.2.2.2.2] using hLimη
    obtain ⟨τ,r₄,hCtxτ,hScanτ,hLimτ,hArrτ,hInτ,hOutτ⟩ :=
      ih (p := j) (σ := t) hEnd (by simp [t]) hLimT
        (show t.arrs "data"=sentinelWords z from (congrFun (hArrη.trans hArr) "data").trans hBank)
        hCtxT hTail
    have hLt : p < l := by change p+1+a.length ≤ l at hEnd; omega
    have htrue : x.guard.evalB B σ=some true := by
      have he := evalB_condLt (evalB_var_iff.mpr ⟨hScan.symm,hScan ▸ hP.trans_lt hE⟩)
        (evalB_var_iff.mpr ⟨hLim.symm,hLim ▸ hE⟩)
      simpa [TrialAxis.guard,hLt] using he
    have rBody : Run B (x.axisBody visit) σ t (9+(C+2)) := r₁.seq (r₂.seq r₃)
    have rWhole : Run B (x.traverse visit) σ τ ((C+15)*(rows.length+1)+4) := by
      obtain ⟨k,hk,hK⟩ := rBody
      obtain ⟨v,hv,hV⟩ := r₄
      refine ⟨4+k+v,?_,BigStepB.while_true htrue hK hV⟩
      rw [Nat.mul_add,Nat.mul_one]
      omega
    refine ⟨τ,rWhole,hCtxτ,hScanτ,hLimτ,hArrτ.trans (hArrη.trans hArr),
      hInτ.trans (hInη.trans hInp),?_⟩
    rw [hOutτ,show t.out=η.out from rfl,hOutη,hOut]
    simp [List.append_assoc]

#print axioms traverseTrialBlocks_run
end EvenTI.P15Trial
