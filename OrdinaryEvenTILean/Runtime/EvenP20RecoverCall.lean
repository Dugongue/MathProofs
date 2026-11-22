import EvenP19RecoverArchiveChart
import Mathproof.Meta.P15DecideIMPSplit20261007

/-! Preserve the live primary-kernel controls through a complete factor
chart call. The mutable register bank is saved and restored by paid IMP
assignments. -/
namespace EvenTI.P20Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial UniqueFactorizationMonoid EvenTI.P18Recover EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPMatPow20261007 (mpN mpNN mpP mpR mpT)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT XBs)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)
open Mathproof.P15GBFAffine20261007 (afSB)
open Mathproof.P15DecideIMPSplit20261007
  (asgL asgL_run setL setL_vars_of_not setL_slots setL_val)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth)
open Mathproof.Problem17Primary46Kernel (Geometry)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained retained_of_eq)
open Mathproof.Problem17Primary46Reload (key)

set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 150000

def primaryLayoutTag : String := "even.p20.recover.primary.saved."

def primaryPortNames : List String :=
  [dL,gRows,gCols,gOut,mpN,mpNN,afSB,mpP,mpR,mpT,tNR,tD,tRB,kAM,kOUT,dZ,rOs,dT,dU]

def primarySavePairs : List (String × String) :=
  primaryPortNames.map fun r => (key primaryLayoutTag r,r)

def savePrimaryPorts : Com := asgL primarySavePairs .skip

def restorePrimaryPorts : Com :=
  Mathproof.Problem17Primary46Reload.program primaryLayoutTag primaryPortNames

noncomputable def archivedFactorChart (O : Output) (address : String) : Com :=
  .seq savePrimaryPorts (.seq (archivedCompleteChart O address) restorePrimaryPorts)

private theorem setL_saved (ps : List (String × String)) (σ : Env)
    (hnd : (ps.map Prod.fst).Nodup)
    (hfree : ∀ p ∈ ps, ∀ q ∈ ps, p.2 ≠ q.1)
    (p : String × String) (hp : p ∈ ps) :
    (setL σ ps).vars p.1=σ.vars p.2 := by
  induction ps generalizing σ with
  | nil => simp at hp
  | cons q ps ih =>
    simp only [List.map_cons,List.nodup_cons] at hnd
    change (setL (σ.setVar q.1 (σ.vars q.2)) ps).vars p.1=σ.vars p.2
    rcases List.mem_cons.mp hp with rfl|hp
    · rw [setL_vars_of_not _ _ _ (by
        intro r hr e
        exact hnd.1 (by rw [e]; exact List.mem_map_of_mem hr)),vars_setVar,if_pos rfl]
    · have keep := hfree p (List.mem_cons_of_mem _ hp) q List.mem_cons_self
      rw [ih _ hnd.2 (fun r hr t ht => hfree r (List.mem_cons_of_mem _ hr) t
        (List.mem_cons_of_mem _ ht)) hp, vars_setVar, if_neg keep]

private theorem save_fixed : ∀ r ∈ primaryPortNames, r ∉ scalarWrites savePrimaryPorts := by decide

private theorem chart_layout_after_save : ∀ r ∈ chartLayoutNames,
    key chartLayoutTag r ∉ scalarWrites savePrimaryPorts := by decide

private theorem saved_after_chart : ∀ r ∈ primaryPortNames,
    key primaryLayoutTag r ∉ scalarWrites (archivedCompleteChart ⟨"","",""⟩ "") := by decide

private theorem chart_layout_after_call : ∀ r ∈ chartLayoutNames,
    key chartLayoutTag r ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ "") := by decide

private theorem chart_array_writes :
    arrayWrites (archivedFactorChart ⟨"","",""⟩ "") ⊆ {canonical.mem,canonical.scratch} := by decide

theorem primaryPorts_of_eq {s t : Env} {n d SB TB RB PB AM OB Z : ℕ}
    (P : PrimaryPorts s n d SB TB RB PB AM OB Z)
    (keep : ∀ r ∈ primaryPortNames, t.vars r=s.vars r) :
    PrimaryPorts t n d SB TB RB PB AM OB Z :=
  ⟨(keep _ (by decide)).trans P.dot,(keep _ (by decide)).trans P.rows,
    (keep _ (by decide)).trans P.cols,(keep _ (by decide)).trans P.output,
    (keep _ (by decide)).trans P.size,(keep _ (by decide)).trans P.sizeSq,
    (keep _ (by decide)).trans P.powers,(keep _ (by decide)).trans P.query,
    (keep _ (by decide)).trans P.powered,(keep _ (by decide)).trans P.work,
    (keep _ (by decide)).trans P.kerRows,(keep _ (by decide)).trans P.kerCols,
    (keep _ (by decide)).trans P.kerInput,(keep _ (by decide)).trans P.kerWork,
    (keep _ (by decide)).trans P.kerOutput,(keep _ (by decide)).trans P.zero,
    (keep _ (by decide)).trans P.one,(keep _ (by decide)).trans P.temp1,
    (keep _ (by decide)).trans P.temp2⟩

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem savePrimaryPorts_run (F : FieldPresentation K) {Sn B : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS Sn B σ)
    (hWords : ∀ r ∈ primaryPortNames, σ.vars r < B) :
    ∃ τ, Run B savePrimaryPorts σ τ 39 ∧ Slots F canonical qN.WS Sn B τ ∧
      (∀ r ∈ primaryPortNames, τ.vars (key primaryLayoutTag r)=σ.vars r) ∧
      (∀ k, val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      τ.arrs=σ.arrs ∧ Frame savePrimaryPorts σ τ := by
  let τ := setL σ primarySavePairs
  have readBound (p : String × String) (hp : p ∈ primarySavePairs) : σ.vars p.2 < B := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact hWords _ hr
  have hf : ∀ p ∈ primarySavePairs, ∀ q ∈ primarySavePairs, p.2 ≠ q.1 := by decide
  have run : Run B savePrimaryPorts σ τ 39 :=
    asgL_run primarySavePairs .skip readBound hf Run.skip
  have stable : ∀ p ∈ primarySavePairs, p.1 ∉ regNames canonical ∧ p.1≠qN.WS := by decide
  have fr := Frame.of_run run
  refine ⟨τ,run,setL_slots F primarySavePairs σ stable hS,?_,
    setL_val F primarySavePairs σ (fun p hp => (stable _ hp).2),?_,fr⟩
  · intro r hr
    have hm : (key primaryLayoutTag r,r) ∈ primarySavePairs := List.mem_map_of_mem hr
    exact setL_saved _ _ (by decide) hf _ hm
  · funext a
    exact fr.arrs _ (by rw [show arrayWrites savePrimaryPorts=∅ by decide]; simp)

theorem restorePrimaryPorts_run (F : FieldPresentation K) {Sn B : ℕ} {σ ρ : Env}
    (hS : Slots F canonical qN.WS Sn B ρ)
    (hSave : ∀ r ∈ primaryPortNames, ρ.vars (key primaryLayoutTag r)=σ.vars r)
    (hWords : ∀ r ∈ primaryPortNames, σ.vars r < B) :
    ∃ τ, Run B restorePrimaryPorts ρ τ 39 ∧ Slots F canonical qN.WS Sn B τ ∧
      (∀ r ∈ primaryPortNames, τ.vars r=σ.vars r) ∧
      (∀ k, val F canonical qN.WS τ k=val F canonical qN.WS ρ k) ∧
      Frame restorePrimaryPorts ρ τ := by
  obtain ⟨τ,r,s,installed,mem,fr⟩ := Mathproof.Problem17Primary46Reload.run F
    primaryLayoutTag primaryPortNames hS (by decide) (by decide) (by decide)
    (fun r hr => by rw [hSave _ hr]; exact hWords _ hr)
  exact ⟨τ,r,s,fun r hr => (installed r hr).trans (hSave r hr),mem,fr⟩

structure ChartCallStable (F : FieldPresentation K) (N n D SB TB RB PB AM OB Z AB QR QA QO QL QW QY QD :
    ℕ) (O : Output) (address : String) (S : Matrix (Fin n) (Fin n) K) (σ τ : Env) : Prop where
  archive : Retained F N O S.charpoly τ
  size : τ.vars O.size=σ.vars O.size
  cursor : τ.vars cursor=σ.vars cursor
  address : τ.vars address=σ.vars address
  tableBase : τ.vars tableBase=D
  tableWidth : τ.vars tableWidth=N+N
  resWidth : τ.vars rC=N+N
  workspace : τ.vars qN.WS=F.e+1
  ports : PrimaryPorts τ n n SB TB RB PB AM OB Z
  layout : ChartLayoutRegisters τ n AB OB QR QA QO QL QW QY Z QD
  words : τ.arrs O.words=σ.arrs O.words
  mult : τ.arrs O.mult=σ.arrs O.mult

theorem archivedFactorChart_run (F : FieldPresentation K) (O : Output) (address : String)
    {n N D SB TB RB PB AM OB Z Sn B i : ℕ} {σ : Env} (S : Matrix (Fin n) (Fin n) K)
    (hA : Retained F N O S.charpoly σ) (distinct : Distinct O)
    (hAddr : σ.vars address=D)
    (hFresh : address ≠ Mathproof.Problem17Primary48Install.cnt ∧
      address ≠ Mathproof.Problem17Primary48Install.src)
    (hSize : O.size ∉ scalarWrites (archivedFactorChart O address))
    (hKeepAddress : address ∉ scalarWrites (archivedFactorChart O address))
    (hWidth : σ.vars rC=N+N) (hS : Slots F canonical qN.WS Sn B σ)
    (hn : 0 < N) (hFit : D+N*(N+N) ≤ Sn)
    (hCap : F.e*(N*(N+N)) ≤ (σ.arrs O.words).length) (hCapB : (σ.arrs O.words).length < B)
    (hCursor : σ.vars cursor=i) (hi : i < σ.vars O.size)
    (hBase : σ.vars tableBase=D) (hTableWidth : σ.vars tableWidth=N+N)
    (hWS : σ.vars qN.WS = F.e+1)
    (G : Geometry n n (N+N) SB (D+i*(N+N)) TB RB PB AM OB Z Sn B)
    (C : PrimaryPorts σ n n SB TB RB PB AM OB Z)
    (hRegFit : ∀ r ∈ primaryPortNames, σ.vars r < B)
    (hPowersFirst : SB+(n+1)*(n*n) ≤ D) (hConstAfter : D+N*(N+N) ≤ Z)
    (hp : ∀ j ≤ n, MatBlock F σ (SB+j*(n*n)) (S^j))
    (hz : val F canonical qN.WS σ Z = 0) (ho : val F canonical qN.WS σ (Z+1) = 1)
    {AB QR QA QO QL QW QY QD : ℕ}
    (hMat : MatBlock F σ AB S) (hMatLow : (n+1)*XBs n n ≤ AB) (hMatHigh : AB+n*n≤D)
    (hLayout : ChartLayoutRegisters σ n AB OB QR QA QO QL QW QY Z QD)
    (hFitChart : ∀ p ∈ chartLayoutEntries n AB OB QR QA QO QL QW QY Z QD, p.2<B)
    (hForWidth : ∀ w ≤ n, ChartBankLayout w n AB OB QR QA QO QL QW QY Z QD Sn B) :
    ∃ (τ : Env) (L : List K[X]) (j : Fin L.length) (w : ℕ) (xs : Fin w → Fin n → K),
      j.val=i ∧ (L : Multiset K[X])=(normalizedFactors S.charpoly).dedup ∧ w≤n ∧
      Run B (archivedFactorChart O address) σ τ
        (39+(((Mathproof.Problem17Primary48Install.cost F N +
          (12+Mathproof.Problem17Primary46Kernel.cost F n n
             ((normalizedFactors S.charpoly).count (L.get j))))+
          (33+(8+chartBankCost F w n)))+39)) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs) =
        LinearMap.ker (aeval S ((L.get j)^((normalizedFactors S.charpoly).count (L.get j)))).mulVecLin ∧
      (∀ (a : Fin w) (b : Fin n), val F canonical qN.WS τ (OB+(a.val*n+b.val))=xs a b) ∧
      ChartPrefix F τ QD w S xs ∧ ChartCallStable F N n D SB TB RB PB AM OB Z AB QR QA QO QL QW QY QD
        O address S σ τ ∧
      (∀ k < Sn, (k < D ∨ D+N*(N+N) ≤ k) → (n+1)*XBs n n ≤ k →
        (k < TB ∨ OB+n*n ≤ k) → (w+1+1)*XBs n (w+1) ≤ k →
        (k < QR ∨ QY+w ≤ k) → (k < OB+w*n ∨ OB+w*n+n ≤ k) →
        (k < QD ∨ QD+w*w ≤ k) → k ≠ Z+2 → k ≠ Z+3 →
        val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame (archivedFactorChart O address) σ τ := by
  obtain ⟨u,r₀,s₀,stored,mem₀,arrays₀,fr₀⟩ := savePrimaryPorts_run F hS hRegFit
  have szSave : O.size ∉ scalarWrites savePrimaryPorts := fun h =>
    hSize (by simp only [archivedFactorChart,scalarWrites,Finset.mem_union]; exact Or.inl h)
  have szInstall : O.size ∉ scalarWrites (Mathproof.Problem17Primary48Install.program O address) :=
    fun h => hSize (by
      simp only [archivedFactorChart,archivedCompleteChart,archivedPrimary,scalarWrites,Finset.mem_union]
      exact Or.inr (Or.inl (Or.inl (Or.inl h))))
  have addrSave : address ∉ scalarWrites savePrimaryPorts := fun h =>
    hKeepAddress (by simp only [archivedFactorChart,scalarWrites,Finset.mem_union]; exact Or.inl h)
  have keep₀ (r : String) (h : r ∉ scalarWrites savePrimaryPorts) : u.vars r = σ.vars r :=
    fr₀.vars r h
  have hA₀ : Retained F N O S.charpoly u :=
    retained_of_eq F hA (congrFun arrays₀ _) (congrFun arrays₀ _) (keep₀ _ szSave)
  have hC₀ : PrimaryPorts u n n SB TB RB PB AM OB Z :=
    primaryPorts_of_eq C (fun r hr => keep₀ r (save_fixed r hr))
  have hLayout₀ : ChartLayoutRegisters u n AB OB QR QA QO QL QW QY Z QD := by
    intro p hp
    have hmem : p.1∈chartLayoutNames := by
      rw [← chartLayoutEntries_names n AB OB QR QA QO QL QW QY Z QD]
      exact List.mem_map_of_mem hp
    exact (keep₀ _ (chart_layout_after_save _ hmem)).trans (hLayout p hp)
  obtain ⟨v,L,j,w,xs,hj,hL,hw,r₁,s₁,hCur,hInd,hSpan,hBasis,hChart,mem₁,fr₁⟩ :=
    archivedCompleteChart_run F O address S hA₀ distinct ((keep₀ _ addrSave).trans hAddr) hFresh szInstall
      ((keep₀ _ (by decide)).trans hWidth) s₀ hn hFit (by rw [arrays₀]; exact hCap) (by rw [arrays₀]; exact hCapB)
      ((keep₀ _ (by decide)).trans hCursor) (by rw [keep₀ _ szSave]; exact hi)
      ((keep₀ _ (by decide)).trans hBase) ((keep₀ _ (by decide)).trans hTableWidth)
      ((keep₀ _ (by decide)).trans hWS) G hC₀ hPowersFirst hConstAfter
      (fun p h a b => (mem₀ _).trans (hp p h a b)) ((mem₀ _).trans hz) ((mem₀ _).trans ho)
      (fun a b => (mem₀ _).trans (hMat a b)) hMatLow hMatHigh hLayout₀ hFitChart hForWidth
  have preserved (r : String) (hr : r∈primaryPortNames) :
      v.vars (key primaryLayoutTag r)=σ.vars r :=
    (fr₁.vars _ (by
      change key primaryLayoutTag r ∉ scalarWrites (archivedCompleteChart ⟨"","",""⟩ "")
      exact saved_after_chart r hr)).trans (stored r hr)
  obtain ⟨τ,r₂,s₂,regs₂,mem₂,fr₂⟩ := restorePrimaryPorts_run F s₁ preserved hRegFit
  have r : Run B (archivedFactorChart O address) σ τ _ := r₀.seq (r₁.seq r₂)
  have fr := Frame.of_run r
  have fullKeep (a : String) (ha : a ≠ canonical.mem) (hb : a ≠ canonical.scratch) :
      τ.arrs a=σ.arrs a :=
    fr.arrs a (fun h => by
      change a ∈ arrayWrites (archivedFactorChart ⟨"","",""⟩ "") at h
      simpa [ha,hb] using chart_array_writes h)
  have words : τ.arrs O.words=σ.arrs O.words := fullKeep _ distinct.wordsMem distinct.wordsScratch
  have mult : τ.arrs O.mult=σ.arrs O.mult := fullKeep _ distinct.multMem distinct.multScratch
  have stable : ChartCallStable F N n D SB TB RB PB AM OB Z AB QR QA QO QL QW QY QD
      O address S σ τ := by
    refine ⟨retained_of_eq F hA words mult (fr.vars _ hSize),fr.vars _ hSize,?_,fr.vars _ hKeepAddress,
      ?_,?_,?_,?_,primaryPorts_of_eq C regs₂,?_,words,mult⟩
    · exact fr.vars _ (by change cursor ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ ""); decide)
    · exact (fr.vars _ (by change tableBase ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ ""); decide)).trans hBase
    · exact (fr.vars _ (by change tableWidth ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ ""); decide)).trans hTableWidth
    · exact (fr.vars _ (by change rC ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ ""); decide)).trans hWidth
    · exact (fr.vars _ (by change qN.WS ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ ""); decide)).trans hWS
    · intro p hp
      have hmem : p.1∈chartLayoutNames := by
        rw [← chartLayoutEntries_names n AB OB QR QA QO QL QW QY Z QD]
        exact List.mem_map_of_mem hp
      rw [fr.vars _ (by
        change key chartLayoutTag p.1 ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ "")
        exact chart_layout_after_call _ hmem)]
      exact hLayout p hp
  refine ⟨τ,L,j,w,xs,hj,hL,hw,r,s₂,(fr₂.vars _ (by decide)).trans hCur,hInd,hSpan,?_,?_,stable,?_,fr⟩
  · intro a b
    exact (mem₂ _).trans (hBasis a b)
  · intro p hp
    simp only [mem₂]
    exact hChart p hp
  · intro k hk ht hl ha hc hs hg hd hz₁ hz₂
    exact (mem₂ k).trans ((mem₁ k hk ht hl ha hc hs hg hd hz₁ hz₂).trans (mem₀ k))

#print axioms archivedFactorChart_run

#print axioms savePrimaryPorts_run
#print axioms restorePrimaryPorts_run
end EvenTI.P20Recover

