import EvenP20SweepStore
import EvenP20RecoverCall

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 150000

namespace EvenTI.P20Sweep

open EvenTI.P19Recover EvenTI.P20Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.Problem17Primary46FactorCursor (cursor)
open Mathproof.Problem17Primary48RawArchive (Output)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def framedStoreChartRow : Com :=
  .seq savePrimaryPorts (.seq storeChartRow restorePrimaryPorts)

private theorem savedPrimaryKeepsStore :
    ∀ r ∈ primaryPortNames, Mathproof.Problem17Primary46Reload.key primaryLayoutTag r ∉
      scalarWrites storeChartRow := by decide

private theorem storePortRegisters :
    ∀ r ∈ [chartCursor,savedAmbientSize,savedBasisSource,savedChartSource,dZ,rOs,dT,dU,
      savedOffset,cursor,savedBank,savedLane,savedStride], r ∉ scalarWrites savePrimaryPorts := by decide

private theorem restoreArray :
    arrayWrites restorePrimaryPorts=∅ := by decide

/-- Preserve the primary kernel's controls across the grid copy. -/
theorem framedStoreChartRow_run (F : FieldPresentation K) {B Sn n w srcX srcR Z offset i base lane : ℕ}
    {s : Env} {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {xs : Fin w → Fin n → K}
    (hs : Slots F canonical qN.WS Sn B s)
    (p : RowPorts s n w srcX srcR Z offset i base lane) (fit : ∀ r ∈ primaryPortNames, s.vars r < B) (hw : w≤n)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs)=LinearMap.ker (Polynomial.aeval A f).mulVecLin)
    (hBasis : ∀ j k, val F canonical qN.WS s (srcX+(j.val*n+k.val))=xs j k)
    (hChart : ChartPrefix F s srcR w A xs)
    (hLane : n*n≤lane) (hnB : n<B) (hiB : i<B) (hRowB : offset+i<B)
    (hStride : 2*lane<B) (hCapacity : offset+i<(s.arrs savedWidths).length)
    (hSourceX : srcX+n*n≤base) (hSourceR : srcR+n*n≤base)
    (hOutput : rowChart base lane (offset+i)+lane≤Z)
    (hZ : Z+4≤Sn) (hB : Sn+10<B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run B framedStoreChartRow s t (39+((16+publishChartCost F w n)+39)) ∧ Slots F canonical qN.WS Sn B t ∧
      SavedChart F A f (offset+i) (rowBasis base lane (offset+i)) (rowChart base lane (offset+i)) t ∧
      (∀ k < Sn, (k < rowBasis base lane (offset+i) ∨ rowChart base lane (offset+i)+lane≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ k, k≠offset+i → (t.arrs savedWidths)[k]?=(s.arrs savedWidths)[k]?) ∧
      (∀ r ∈ primaryPortNames, t.vars r=s.vars r) ∧ Frame framedStoreChartRow s t := by
  obtain ⟨u,r₀,hu,hSave,hMem,hArr,fs⟩ := savePrimaryPorts_run F hs fit
  have keep (r : String) (hr : r ∈ [chartCursor,savedAmbientSize,savedBasisSource,savedChartSource,dZ,rOs,dT,dU,
      savedOffset,cursor,savedBank,savedLane,savedStride]) :
      u.vars r=s.vars r := fs.vars _ (storePortRegisters r hr)
  have pu : RowPorts u n w srcX srcR Z offset i base lane :=
    ⟨(keep _ (by decide)).trans p.width,(keep _ (by decide)).trans p.ambient,
      (keep _ (by decide)).trans p.basisSource,(keep _ (by decide)).trans p.chartSource,
      (keep _ (by decide)).trans p.zero,(keep _ (by decide)).trans p.one,
      (keep _ (by decide)).trans p.temp1,(keep _ (by decide)).trans p.temp2,
      (keep _ (by decide)).trans p.offset,(keep _ (by decide)).trans p.index,
      (keep _ (by decide)).trans p.bank,(keep _ (by decide)).trans p.laneReg,
      (keep _ (by decide)).trans p.stride⟩
  have hyp : ChartPrefix F u srcR w A xs := by
    intro j hj
    simpa only [hMem] using hChart j hj
  obtain ⟨v,r₁,hv,hChartV,hKeepV,hWidthV,fv⟩ := storeChartRow_run F hu pu hw hInd hSpan
    (fun j k => (hMem _).trans (hBasis j k)) hyp hLane hnB hiB hRowB
    hStride (by rwa [hArr]) hSourceX hSourceR hOutput hZ hB ((hMem _).trans hz) ((hMem _).trans ho)
  obtain ⟨t,r₂,ht,hRest,hRead,ft⟩ := restorePrimaryPorts_run (σ:=s) F hv
    (fun r hr => (fv.vars _ (savedPrimaryKeepsStore r hr)).trans (hSave r hr)) fit
  have hWrite : t.arrs savedWidths=v.arrs savedWidths := ft.arrs _ (by simp [restoreArray])
  have r : Run B framedStoreChartRow s t _ := r₀.seq (r₁.seq r₂)
  refine ⟨t,r,ht,hChartV.frame F (by rw [hWrite])
    (fun _ _ => hRead _) (fun _ _ => hRead _),?_,?_,hRest,Frame.of_run r⟩
  · intro k hk hRange hT hU
    exact (hRead _).trans ((hKeepV k hk hRange hT hU).trans (hMem _))
  · intro k hk
    rw [hWrite,hWidthV k hk,hArr]



noncomputable def recoverArchiveRow (O : Output) (address : String) : Com :=
  .seq (archivedFactorChart O address) framedStoreChartRow

noncomputable def recoverArchiveFactors (O : Output) (address : String) : Com :=
  forLoop cursor O.size (recoverArchiveRow O address)

structure DurableBank (s : Env) (n srcX srcR offset base lane : ℕ) : Prop where
  ambient : s.vars savedAmbientSize=n
  basisSource : s.vars savedBasisSource=srcX
  chartSource : s.vars savedChartSource=srcR
  offsetReg : s.vars savedOffset=offset
  bankReg : s.vars savedBank=base
  laneReg : s.vars savedLane=lane
  strideReg : s.vars savedStride=2*lane

theorem chartSaveRegisters :
    ∀ r ∈ [savedAmbientSize,savedBasisSource,savedChartSource,savedOffset,savedBank,savedLane,savedStride],
    r ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ "") := by decide

private theorem chartSaveArray :
    savedWidths ∉ arrayWrites (archivedFactorChart ⟨"","",""⟩ "") := by decide

private theorem storeChartKeepCursor : cursor ∉ scalarWrites framedStoreChartRow := by decide

/-- The archive call and its numeric row publication form one actual IMP body.
The source chart is evaluated at the archive's current row, not a separate
model of the chart program. -/
theorem recoverArchiveRow_commit (F : FieldPresentation K) {O : Output} {address : String}
    {B Sn Pc n w srcX srcR Z offset i base lane : ℕ}
    {s u : Env} {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {xs : Fin w → Fin n → K}
    (call : Run B (archivedFactorChart O address) s u Pc)
    (hu : Slots F canonical qN.WS Sn B u) (bank : DurableBank s n srcX srcR offset base lane)
    (fit : ∀ r ∈ primaryPortNames, u.vars r < B) (hCursor : u.vars cursor=i) (hwCursor : u.vars chartCursor=w)
    (hZReg : u.vars dZ=Z) (hOneReg : u.vars rOs=Z+1)
    (hTReg : u.vars dT=Z+2) (hUReg : u.vars dU=Z+3)
    (hw : w≤n) (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs)=LinearMap.ker (Polynomial.aeval A f).mulVecLin)
    (hBasis : ∀ j k, val F canonical qN.WS u (srcX+(j.val*n+k.val))=xs j k)
    (hChart : ChartPrefix F u srcR w A xs)
    (hLane : n*n≤lane) (hnB : n<B) (hiB : i<B) (hRowB : offset+i<B)
    (hStride : 2*lane<B) (hCapacity : offset+i<(s.arrs savedWidths).length)
    (hSourceX : srcX+n*n≤base) (hSourceR : srcR+n*n≤base)
    (hOutput : rowChart base lane (offset+i)+lane≤Z)
    (hZ : Z+4≤Sn) (hB : Sn+10<B)
    (hz : val F canonical qN.WS u Z=0) (ho : val F canonical qN.WS u (Z+1)=1) :
    ∃ t, Run B (recoverArchiveRow O address) s t (Pc+(39+((16+publishChartCost F w n)+39))) ∧
      Slots F canonical qN.WS Sn B t ∧ t.vars cursor=i ∧
      SavedChart F A f (offset+i) (rowBasis base lane (offset+i)) (rowChart base lane (offset+i)) t ∧
      (∀ k < Sn, (k < rowBasis base lane (offset+i) ∨ rowChart base lane (offset+i)+lane≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS u k) ∧
      (∀ k, k≠offset+i → (t.arrs savedWidths)[k]?=(s.arrs savedWidths)[k]?) ∧
      (∀ r ∈ primaryPortNames, t.vars r=u.vars r) ∧ Frame framedStoreChartRow u t ∧ Frame (recoverArchiveRow O address) s t := by
  have fr := Frame.of_run call
  have stable (r : String) (hr : r ∈
      [savedAmbientSize,savedBasisSource,savedChartSource,savedOffset,savedBank,savedLane,savedStride]) :
      u.vars r=s.vars r := fr.vars r (by
    change r ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ "")
    exact chartSaveRegisters r hr)
  have hData : u.arrs savedWidths=s.arrs savedWidths := fr.arrs _ (by
    change savedWidths ∉ arrayWrites (archivedFactorChart ⟨"","",""⟩ "")
    exact chartSaveArray)
  have ports : RowPorts u n w srcX srcR Z offset i base lane :=
    ⟨hwCursor,(stable _ (by decide)).trans bank.ambient,
      (stable _ (by decide)).trans bank.basisSource,(stable _ (by decide)).trans bank.chartSource,
      hZReg,hOneReg,hTReg,hUReg,(stable _ (by decide)).trans bank.offsetReg,hCursor,
      (stable _ (by decide)).trans bank.bankReg,(stable _ (by decide)).trans bank.laneReg,
      (stable _ (by decide)).trans bank.strideReg⟩
  obtain ⟨t,rt,ht,hSaved,hKeep,hOther,hReg,fr₂⟩ := framedStoreChartRow_run F hu ports fit hw hInd hSpan hBasis
    hChart hLane hnB hiB hRowB hStride (by rwa [hData]) hSourceX hSourceR hOutput hZ hB hz ho
  have written : Run B (recoverArchiveRow O address) s t _ := call.seq rt
  refine ⟨t,written,ht,(fr₂.vars _ storeChartKeepCursor).trans hCursor,hSaved,hKeep,?_,hReg,fr₂,Frame.of_run written⟩
  intro k hk
  rw [hOther _ hk,hData]

/-- Reuse the existing counted loop with the actual archived-factor body. -/
theorem recoverArchiveFactors_of_replayed_rows (F : FieldPresentation K) {B n P m base lane offset : ℕ}
    (O : Output) (address : String) (hCount : cursor≠O.size)
    (A : Matrix (Fin n) (Fin n) K) (f : ℕ → Polynomial K) (Ready : Env → Prop)
    {s : Env} (hm : s.vars O.size=m) (hmB : m<B) (hs : Ready s)
    (hReady : ∀ u i, Ready u → Ready (u.setVar cursor i))
    (step : ∀ i < m, ∀ u, Ready u → u.vars cursor=i → u.vars O.size=m →
      ∃ v, Run B (recoverArchiveRow O address) u v P ∧ Ready v ∧
        v.vars cursor=i ∧ v.vars O.size=m ∧
        SavedChart F A (f i) (offset+i) (rowBasis base lane (offset+i)) (rowChart base lane (offset+i)) v ∧
        (∀ j < i, (v.arrs savedWidths)[offset+j]?=(u.arrs savedWidths)[offset+j]?) ∧
        (∀ j < i, ∀ k < n*n, val F canonical qN.WS v (rowBasis base lane (offset+j)+k)=
          val F canonical qN.WS u (rowBasis base lane (offset+j)+k)) ∧
        (∀ j < i, ∀ k < n*n, val F canonical qN.WS v (rowChart base lane (offset+j)+k)=
          val F canonical qN.WS u (rowChart base lane (offset+j)+k))) :
    ∃ t, Run B (recoverArchiveFactors O address) s t ((P+8)*m+6) ∧ Ready t ∧ t.vars cursor=m ∧
      ∀ i < m, SavedChart F A (f i) (offset+i) (rowBasis base lane (offset+i)) (rowChart base lane (offset+i)) t :=
  chartFactorLoop_run F A f (offset+·) (fun i => rowBasis base lane (offset+i))
    (fun i => rowChart base lane (offset+i)) O.size hCount (recoverArchiveRow O address) Ready
    hm hmB hs hReady step

end EvenTI.P20Sweep



