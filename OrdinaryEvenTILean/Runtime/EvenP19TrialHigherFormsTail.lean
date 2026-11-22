import EvenP19TrialModeFrame
import EvenP16TrialHigherEmit

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 18000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P17Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames NoVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots installed_scalar installed_arrays)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def installedFormWord (right : Bool) : String :=
  if right then projectionRightFormWord else projectionLeftFormWord

private def higherFormArgs (right : Bool) : List (String × Expr) :=
  [(emitFormModes,.var reciprocalSweepLimit),(reverseDigitBase,.var crossN),
    (fieldVectorStart,.var (installedFormWord right)),(fieldVectorLength,.var contractionTensorWidth)]

def higherFormTargets : List String :=
  [emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]

private theorem higherFormArgs_safe (right : Bool) :
    ∀ p ∈ higherFormArgs right, ∀ q ∈ higherFormArgs right, NoVar p.1 q.2 := by
  cases right <;>
    simp [higherFormArgs,NoVar,installedFormWord,emitFormModes,reverseDigitBase,
      fieldVectorStart,fieldVectorLength,reciprocalSweepLimit,crossN,projectionLeftFormWord,
      projectionRightFormWord,contractionTensorWidth]

noncomputable def emitInstalledHigherForm (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  .seq (commands (higherFormArgs right)) (emitHigherForm D F)

noncomputable def emitInstalledHigherFormCost (F : FieldPresentation K) (d m : ℕ) : ℕ :=
  9+emitHigherFormCost F d m

theorem emitInstalledHigherForm_run (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool)
    {B S l n src : ℕ} {s : Env} (form : Coord (l+1) n → K)
    (hs : Slots F canonical qN.WS S B s) (hn : 0 < n) (hNB : n<B)
    (hl : l+1<B) (hm : n^(l+1)<B) (hOne : 1<B) (hFit : src+n^(l+1)≤S)
    (hQ : Fintype.card K≤B) (hP : F.p<B)
    (hWidth : s.vars crossN=n) (hModes : s.vars reciprocalSweepLimit=l+1)
    (hLength : s.vars contractionTensorWidth=n^(l+1)) (hSrc : s.vars (installedFormWord right)=src)
    (hRead : ∀ x : Coord (l+1) n, val F canonical qN.WS s (src+(inputCoordOrder n (l+1) x).val)=form x) :
    ∃ t, Run B (emitInstalledHigherForm D F right) s t
      (emitInstalledHigherFormCost F (l+1) (n^(l+1))) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k, val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r∉higherFormTargets → r∉formClobbered → t.vars r=s.vars r) ∧
      t.inp=s.inp ∧ t.out=s.out++cutFormWords D form := by
  let V := [(emitFormModes,l+1),(reverseDigitBase,n),(fieldVectorStart,src),(fieldVectorLength,n^(l+1))]
  let σ := install V s
  have hS := hs.slots_word
  have r₁ : Run B (commands (higherFormArgs right)) s σ 9 :=
    commands_run (higherFormArgs right) [l+1,n,src,n^(l+1)] s rfl
      (.cons (ev_var hModes hl) (.cons (ev_var hWidth hNB) (.cons (ev_var hSrc (by omega))
        (.cons (ev_var hLength hm) .nil)))) (higherFormArgs_safe right)
  have hFixed : ∀ r∈higherFormTargets, canonical.e≠r ∧ canonical.p≠r ∧
      canonical.modBase≠r ∧ canonical.exp≠r ∧ qN.WS≠r := by decide
  have name (p : String × ℕ) (hp : p ∈ V) : p.1 ∈ higherFormTargets := by
    change p.1 ∈ V.map Prod.fst
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hSlots := installed_slots F V s hs (fun p hp => hFixed _ (name p hp))
  have keep (r : String) (hr : r∉higherFormTargets) : σ.vars r=s.vars r :=
    installed_scalar V s r (fun p hp e => hr (e ▸ name p hp))
  obtain ⟨hArr,hIn,hOut⟩ := installed_arrays V s
  have hMem (k : ℕ) : val F canonical qN.WS σ k=val F canonical qN.WS s k := by
    unfold val slice
    rw [keep _ (by decide),hArr]
  obtain ⟨t,r₂,hO,hA,hI,hR⟩ := emitHigherForm_run D F form hn hNB hl hm
    hSlots hQ hP hOne hFit (by rfl) (by rfl) (by rfl) (by rfl)
    (fun x => (hMem _).trans (hRead x))
  have canonicalSafe : ∀ r∈regNames canonical, r∉formClobbered := by decide
  have hT := slots_frame F hSlots (congrFun hA _) (congrFun hA _)
    (fun r hr => hR r (canonicalSafe r hr)) (hR _ (by decide))
  refine ⟨t,r₁.seq r₂,hT,?_,fun r h₁ h₂ => (hR r h₂).trans (keep r h₁),hI.trans hIn,?_⟩
  · intro k
    have hh : val F canonical qN.WS t k=val F canonical qN.WS σ k := by
      unfold val slice
      rw [hR _ (by decide),hA]
    exact hh.trans (hMem k)
  · rw [hO,hOut]

noncomputable def emitInstalledHigherFormPair (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (emitInstalledHigherForm D F false) (emitInstalledHigherForm D F true)

theorem emitInstalledHigherFormPair_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S l n ls rs : ℕ} {s : Env} (ell rho : Coord (l+1) n → K)
    (hs : Slots F canonical qN.WS S B s) (hn : 0 < n) (hNB : n<B)
    (hl : l+1<B) (hm : n^(l+1)<B) (hOne : 1<B) (hFitL : ls+n^(l+1)≤S) (hFitR : rs+n^(l+1)≤S)
    (hQ : Fintype.card K≤B) (hP : F.p<B)
    (hWidth : s.vars crossN=n) (hModes : s.vars reciprocalSweepLimit=l+1)
    (hLength : s.vars contractionTensorWidth=n^(l+1))
    (hL : s.vars projectionLeftFormWord=ls) (hR : s.vars projectionRightFormWord=rs)
    (hReadL : ∀ x : Coord (l+1) n, val F canonical qN.WS s (ls+(inputCoordOrder n (l+1) x).val)=ell x)
    (hReadR : ∀ x : Coord (l+1) n, val F canonical qN.WS s (rs+(inputCoordOrder n (l+1) x).val)=rho x) :
    ∃ t, Run B (emitInstalledHigherFormPair D F) s t
      (2*emitInstalledHigherFormCost F (l+1) (n^(l+1))) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k, val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r∉higherFormTargets → r∉formClobbered → t.vars r=s.vars r) ∧ t.inp=s.inp ∧
      t.out=s.out++(cutFormWords D ell++cutFormWords D rho) := by
  obtain ⟨α,r₁,hα,hM,hKeep,hI,hO⟩ := emitInstalledHigherForm_run D F false ell hs hn hNB hl hm hOne
    hFitL hQ hP hWidth hModes hLength hL hReadL
  obtain ⟨t,r₂,hT,hMT,hKT,hi,ho⟩ := emitInstalledHigherForm_run D F true rho hα hn hNB hl hm hOne
    hFitR hQ hP ((hKeep _ (by decide) (by decide)).trans hWidth)
    ((hKeep _ (by decide) (by decide)).trans hModes) ((hKeep _ (by decide) (by decide)).trans hLength)
    ((hKeep _ (by decide) (by decide)).trans hR) (fun x => (hM _).trans (hReadR x))
  refine ⟨t,by simpa only [two_mul,emitInstalledHigherFormPair] using r₁.seq r₂,hT,
    fun k => (hMT k).trans (hM k),fun r h₁ h₂ => (hKT r h₁ h₂).trans (hKeep r h₁ h₂),
    hi.trans hI,?_⟩
  rw [ho,hO,List.append_assoc]

#print axioms emitInstalledHigherForm_run
#print axioms emitInstalledHigherFormPair_run
end EvenTI.P19Trial
