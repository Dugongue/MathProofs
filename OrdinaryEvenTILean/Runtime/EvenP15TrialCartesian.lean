import EvenP15TrialTraverse

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace EvenTI.P15Trial

open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning

def sourceAxis : TrialAxis :=
  ⟨"even_trial_source_cursor","even_trial_source_limit",sourceStart,sourceEnd⟩

def targetAxis : TrialAxis :=
  ⟨"even_trial_target_cursor","even_trial_target_limit",targetStart,targetEnd⟩

def targetFirst : String := "even_trial_target_first"

def trialTargetLoop : Com :=
  .seq (.assign targetAxis.scan (.var targetFirst)) (targetAxis.traverse trialRecordProgram)

def trialCartesian : Com := .seq (.write (.lit 0)) (sourceAxis.traverse trialTargetLoop)

def preparedComparisonRequest (raw src dst : List ℕ) : List ℕ := pairW raw (pairW src dst)

def requestWords (raw : List ℕ) (source target : List (List ℕ)) : List ℕ :=
  packSegments ([]::(source.product target).map (fun p => preparedComparisonRequest raw p.1 p.2))

def trialRecordBound (z : List ℕ) : ℕ := 15*(3*z.length)+44

def trialTargetBound (z : List ℕ) (ys : List (List ℕ)) : ℕ :=
  (trialRecordBound z+15)*ys.length+6

def trialCartesianBound (z : List ℕ) (xs ys : List (List ℕ)) : ℕ :=
  (trialTargetBound z ys+15)*xs.length+6

structure TrialBankContext (z : List ℕ) (σ : Env) (a A j J : ℕ) : Prop where
  raw : TrialWindow z σ rawStart rawEnd a A
  first : σ.vars targetFirst=j
  last : σ.vars targetAxis.limit=J

private theorem TrialBankContext.frame {z : List ℕ} {σ τ : Env} {a A j J : ℕ}
    (H : TrialBankContext z σ a A j J)
    (h₁ : τ.vars rawStart=σ.vars rawStart) (h₂ : τ.vars rawEnd=σ.vars rawEnd)
    (h₃ : τ.vars targetFirst=σ.vars targetFirst) (h₄ : τ.vars targetAxis.limit=σ.vars targetAxis.limit) :
    TrialBankContext z τ a A j J :=
  ⟨⟨h₁.trans H.raw.start,h₂.trans H.raw.stop,H.raw.bounds⟩,h₃.trans H.first,h₄.trans H.last⟩

theorem trialTargetLoop_run (z : List ℕ) (ys : List (List ℕ))
    {B a A b C j J : ℕ} {σ : Env}
    (hContext : TrialBankContext z σ a A j J)
    (hSource : TrialWindow z σ sourceStart sourceEnd b C)
    (hTarget : slice z j J=ys.flatMap blockW)
    (hTargetBounds : j ≤ J ∧ J ≤ z.length) (hLen : z.length+1 < B) (hLarge : 2 < B)
    (hWords : ∀ w ∈ z, w+1 < B) (hBank : σ.arrs "data"=sentinelWords z) :
    ∃ τ, Run B trialTargetLoop σ τ (trialTargetBound z ys) ∧
      TrialBankContext z τ a A j J ∧ TrialWindow z τ sourceStart sourceEnd b C ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out++
        packSegments (ys.map (preparedComparisonRequest (slice z a A) (slice z b C))) := by
  let ctx (t : Env) := TrialBankContext z t a A j J ∧ TrialWindow z t sourceStart sourceEnd b C
  let render (ys : List ℕ) := positiveWords
    (preparedComparisonRequest (slice z a A) (slice z b C) ys)++[0]
  let σ₁ := σ.setVar targetAxis.scan j
  have hHead : j < B := hTargetBounds.1.trans_lt (hTargetBounds.2.trans_lt (by omega))
  have r₀ : Run B (.assign targetAxis.scan (.var targetFirst)) σ σ₁ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hContext.first.symm,hContext.first ▸ hHead⟩)
  have hCtx : ctx σ₁ := by
    refine ⟨hContext.frame rfl rfl rfl rfl,⟨?_,?_,hSource.bounds⟩⟩
    · simpa only [σ₁,vars_setVar,show sourceStart ≠ targetAxis.scan by decide,if_false] using hSource.start
    · simpa only [σ₁,vars_setVar,show sourceEnd ≠ targetAxis.scan by decide,if_false] using hSource.stop
  have hUpdates {s t : Env} (hFr : ∀ r, r ≠ targetAxis.start → r ≠ targetAxis.stop →
      r ≠ targetAxis.scan → t.vars r=s.vars r) (h : ctx s) : ctx t :=
    ⟨h.1.frame (hFr _ (by decide) (by decide) (by decide)) (hFr _ (by decide) (by decide) (by decide))
      (hFr _ (by decide) (by decide) (by decide)) (hFr _ (by decide) (by decide) (by decide)),
      ⟨(hFr _ (by decide) (by decide) (by decide)).trans h.2.start,
        (hFr _ (by decide) (by decide) (by decide)).trans h.2.stop,h.2.bounds⟩⟩
  have hDo (s : Env) (u : List ℕ) (i k : ℕ) (h : ctx s)
      (hLim : s.vars targetAxis.limit=J) (hMem : s.arrs "data"=sentinelWords z)
      (hw : TrialWindow z s targetStart targetEnd i k) (hEq : slice z i k=u) :
      ∃ t, Run B trialRecordProgram s t (trialRecordBound z) ∧ ctx t ∧
        t.vars targetAxis.limit=J ∧ t.vars targetEnd=k ∧
        t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out++render u := by
    obtain ⟨t,r,ho,ha,hi,hv⟩ := trialRecordProgram_run z h.1.raw h.2 hw hLen hLarge hWords hMem
    have hFr : ctx t := ⟨h.1.frame (hv _ (by decide)) (hv _ (by decide))
      (hv _ (by decide)) (hv _ (by decide)),⟨(hv _ (by decide)).trans h.2.start,
        (hv _ (by decide)).trans h.2.stop,h.2.bounds⟩⟩
    refine ⟨t,r.mono ?_,hFr,(hv _ (by decide)).trans hLim,
      (hv _ (by decide)).trans hw.stop,ha,hi,?_⟩
    · have h₁ := h.1.raw.bounds.2
      have h₂ := h.2.bounds.2
      have h₃ := hw.bounds.2
      unfold trialRecordBound
      omega
    · rw [ho,hEq]
      simp [render,preparedComparisonRequest,List.append_assoc]
  obtain ⟨τ,hR,hKeep,_,_,hA,hI,hO⟩ := traverseTrialBlocks_run z targetAxis (by decide)
    trialRecordProgram render ctx hUpdates hTargetBounds.2 (by omega) hLarge hDo ys hTargetBounds.1
    (by simp [σ₁]) hCtx.1.last hBank hCtx hTarget
  have hRun : Run B trialTargetLoop σ τ (trialTargetBound z ys) :=
    (r₀.seq hR).mono (by unfold trialTargetBound; omega)
  exact ⟨τ,hRun,hKeep.1,hKeep.2,hA,hI,by simpa [σ₁,render,packSegments,List.flatMap_map,Function.comp_def] using hO⟩

private theorem flatMap_renderProduct (raw : List ℕ) (xs ys : List (List ℕ)) :
    xs.flatMap (fun a => packSegments (ys.map (preparedComparisonRequest raw a))) =
      packSegments ((xs.product ys).map (fun p => preparedComparisonRequest raw p.1 p.2)) := by
  induction xs with
  | nil => simp [packSegments]
  | cons a xs ih =>
    have hProd : (a::xs).product ys=(ys.map fun y => (a,y))++xs.product ys := rfl
    rw [List.flatMap_cons,ih,hProd,List.map_append]
    simp only [packSegments,List.flatMap_append,List.map_map,Function.comp_def]

/-- The actual nested loop emits the exact Cartesian product, including the
empty leading segment expected by mapZ. It never writes a materialized pair
table, only the final request stream. -/
theorem trialCartesian_run (z : List ℕ) (xs ys : List (List ℕ))
    {B a A b C j J : ℕ} {σ : Env}
    (hContext : TrialBankContext z σ a A j J)
    (hSrcScan : σ.vars sourceAxis.scan=b) (hSrcLim : σ.vars sourceAxis.limit=C)
    (hSource : slice z b C=xs.flatMap blockW) (hSrcBounds : b ≤ C ∧ C ≤ z.length)
    (hTarget : slice z j J=ys.flatMap blockW) (hTgtBounds : j ≤ J ∧ J ≤ z.length)
    (hLen : z.length+1 < B) (hLarge : 2 < B)
    (hWords : ∀ w ∈ z, w+1 < B) (hBank : σ.arrs "data"=sentinelWords z) :
    ∃ τ, Run B trialCartesian σ τ (trialCartesianBound z xs ys) ∧
      τ.out=σ.out++requestWords (slice z a A) xs ys ∧ τ.arrs=σ.arrs ∧ τ.inp=σ.inp := by
  let ctx (t : Env) := TrialBankContext z t a A j J
  let render (src : List ℕ) := packSegments (ys.map (preparedComparisonRequest (slice z a A) src))
  let σ₁ := {σ with out := σ.out++[0]}
  have h₀ : Run B (.write (.lit 0)) σ σ₁ 2 :=
    Run.write (evalB_lit (by omega))
  have hUpdates {s t : Env} (hFr : ∀ r, r ≠ sourceAxis.start → r ≠ sourceAxis.stop →
      r ≠ sourceAxis.scan → t.vars r=s.vars r) (h : ctx s) : ctx t :=
    h.frame (hFr _ (by decide) (by decide) (by decide))
      (hFr _ (by decide) (by decide) (by decide))
      (hFr _ (by decide) (by decide) (by decide))
      (hFr _ (by decide) (by decide) (by decide))
  have hDo (s : Env) (u : List ℕ) (i k : ℕ) (h : ctx s)
      (hLim : s.vars sourceAxis.limit=C) (hMem : s.arrs "data"=sentinelWords z)
      (hw : TrialWindow z s sourceStart sourceEnd i k) (hEq : slice z i k=u) :
      ∃ t, Run B trialTargetLoop s t (trialTargetBound z ys) ∧ ctx t ∧ t.vars sourceAxis.limit=C ∧
        t.vars sourceEnd=k ∧ t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out++render u := by
    obtain ⟨t,r,hCtx,hs,ha,hi,ho⟩ := trialTargetLoop_run z ys h hw hTarget hTgtBounds hLen hLarge hWords hMem
    have hf := (Mathproof.Problem18IMPFieldLayout20261001.run_frame r).1 sourceAxis.limit
      (by decide)
    refine ⟨t,r,hCtx,hf.trans hLim,hs.stop,ha,hi,?_⟩
    simpa only [hEq,render] using ho
  obtain ⟨τ,r,hKeep,_,_,ha,hi,ho⟩ := traverseTrialBlocks_run z sourceAxis (by decide)
    trialTargetLoop render ctx hUpdates hSrcBounds.2 (by omega) hLarge hDo xs (σ := σ₁) hSrcBounds.1
    hSrcScan hSrcLim hBank (hContext.frame rfl rfl rfl rfl) hSource
  have hr : Run B trialCartesian σ τ (trialCartesianBound z xs ys) := by
    have he : 2+((trialTargetBound z ys+15)*xs.length+4)=trialCartesianBound z xs ys := by
      unfold trialCartesianBound
      omega
    rw [← he]
    exact h₀.seq r
  refine ⟨τ,hr,?_,ha,hi⟩
  rw [ho,show σ₁.out=σ.out++[0] from rfl]
  have hOut := flatMap_renderProduct (slice z a A) xs ys
  change σ.out++[0]++xs.flatMap (fun src => packSegments (ys.map (preparedComparisonRequest (slice z a A) src)))=_
  rw [hOut]
  simp [requestWords,packSegments,positiveWords,List.append_assoc]

#print axioms trialTargetLoop_run
#print axioms trialCartesian_run
end EvenTI.P15Trial
