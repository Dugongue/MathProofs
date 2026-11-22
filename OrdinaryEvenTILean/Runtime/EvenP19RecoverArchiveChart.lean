import EvenP19RecoverReloadChart

/-! A literal archived factor row now drives both its physical annihilator
kernel and the complete restricted-anchor chart. -/
namespace EvenTI.P19Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial UniqueFactorizationMonoid EvenTI.P18Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kK XBs)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth)
open Mathproof.Problem17Primary46Kernel (Geometry)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained)
open Mathproof.Problem17Primary46Reload (key)

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 120000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def archivedCompleteChart (O : Output) (address : String) : Com :=
  .seq (archivedPrimary O address) reloadKernelChart

private theorem layout_key_fresh : ∀ r ∈ chartLayoutNames,
    key chartLayoutTag r ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ "") := by decide

theorem archivedCompleteChart_run (F : FieldPresentation K) (O : Output) (address : String)
    {n N D SB TB RB PB AM OB Z Sn B i : ℕ} {σ : Env} (S : Matrix (Fin n) (Fin n) K)
    (hA : Retained F N O S.charpoly σ) (distinct : Distinct O)
    (hAddr : σ.vars address=D)
    (hFresh : address ≠ Mathproof.Problem17Primary48Install.cnt ∧
      address ≠ Mathproof.Problem17Primary48Install.src)
    (sizeFresh : O.size ∉ scalarWrites (Mathproof.Problem17Primary48Install.program O address))
    (hWidth : σ.vars rC=N+N) (hS : Slots F canonical qN.WS Sn B σ)
    (hn : 0 < N) (hFit : D+N*(N+N) ≤ Sn)
    (hCap : F.e*(N*(N+N)) ≤ (σ.arrs O.words).length) (hCapB : (σ.arrs O.words).length < B)
    (hCursor : σ.vars cursor=i) (hi : i < σ.vars O.size)
    (hBase : σ.vars tableBase=D) (hTableWidth : σ.vars tableWidth=N+N)
    (hWS : σ.vars qN.WS = F.e+1)
    (G : Geometry n n (N+N) SB (D+i*(N+N)) TB RB PB AM OB Z Sn B)
    (C : PrimaryPorts σ n n SB TB RB PB AM OB Z)
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
      Run B (archivedCompleteChart O address) σ τ
        ((Mathproof.Problem17Primary48Install.cost F N +
          (12+Mathproof.Problem17Primary46Kernel.cost F n n
             ((normalizedFactors S.charpoly).count (L.get j))))+
          (33+(8+chartBankCost F w n))) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs) =
        LinearMap.ker (aeval S ((L.get j)^((normalizedFactors S.charpoly).count (L.get j)))).mulVecLin ∧
      (∀ (a : Fin w) (b : Fin n), val F canonical qN.WS τ (OB+(a.val*n+b.val))=xs a b) ∧
      ChartPrefix F τ QD w S xs ∧
      (∀ k < Sn, (k < D ∨ D+N*(N+N) ≤ k) → (n+1)*XBs n n ≤ k →
        (k < TB ∨ OB+n*n ≤ k) → (w+1+1)*XBs n (w+1) ≤ k →
        (k < QR ∨ QY+w ≤ k) → (k < OB+w*n ∨ OB+w*n+n ≤ k) →
        (k < QD ∨ QD+w*w ≤ k) → k ≠ Z+2 → k ≠ Z+3 →
        val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame (archivedCompleteChart O address) σ τ := by
  obtain ⟨u,L,j,hj,hList,r₁,s₁,dim,basis,_,mem₁,fr₁⟩ := archivedPrimaryFramed_run F O address S
    hA distinct hAddr hFresh sizeFresh hWidth hS hn hFit hCap hCapB hCursor hi hBase hTableWidth
    hWS G C hPowersFirst hConstAfter hp hz ho
  let w := u.vars kK
  obtain ⟨xs,xvals,xInd,xSpan⟩ := basis
  have hBound : w≤n := by
    have h := xInd.fintype_card_le_finrank
    simpa only [Fintype.card_fin,Module.finrank_fin_fun,w] using h
  have readLayout : ChartLayoutRegisters u n AB OB QR QA QO QL QW QY Z QD := by
    intro p hp
    have mem : p.1 ∈ chartLayoutNames := by
      rw [← chartLayoutEntries_names n AB OB QR QA QO QL QW QY Z QD]
      exact List.mem_map_of_mem hp
    rw [fr₁.vars _ (by
      change key chartLayoutTag p.1 ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ "")
      exact layout_key_fresh _ mem)]
    exact hLayout _ hp
  have knowWS : u.vars qN.WS=F.e+1 := by
    rw [fr₁.vars _ (by change qN.WS ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ ""); decide)]
    exact hWS
  have hZ := G.kernel.z_s
  have hOB := G.kernel.out_z
  have hTB := G.coefficients
  have holdAnchor : MatBlock F u AB S := by
    intro a b
    have hIdx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    have hLow : (n+1)*XBs n n≤AB+(a.val*n+b.val) := by omega
    have hHigh : AB+(a.val*n+b.val)<D := by omega
    exact (mem₁ _ (by omega) (Or.inl hHigh) hLow (Or.inl (by omega))
      (by omega) (by omega)).trans (hMat a b)
  have holdConst (k : ℕ) (hk : k=Z ∨ k=Z+1) :
      val F canonical qN.WS u k=val F canonical qN.WS σ k :=
    mem₁ k (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (by omega) (by omega)
  let chartGeometry := hForWidth w hBound
  obtain ⟨τ,r₂,s₂,hCur,chart,mem₂,_⟩ := reloadKernelChart_run (w:=w) F S
    ((L.get j)^((normalizedFactors S.charpoly).count (L.get j))) xs xInd xSpan
    s₁ readLayout hFitChart chartGeometry (rfl : u.vars kK=w) knowWS holdAnchor xvals
    ((holdConst Z (Or.inl rfl)).trans hz) ((holdConst (Z+1) (Or.inr rfl)).trans ho)
  have chartLo := chartGeometry.anchorLow
  have chartAnchor := chartGeometry.anchorHigh
  have chartRB := chartGeometry.solve.columns
  have chartAM := chartGeometry.solve.transpose
  have chartOUT := chartGeometry.solve.kernel.am_out
  have chartLB := chartGeometry.solve.out
  have chartW := chartGeometry.solve.labels
  have chartY := chartGeometry.solve.work
  have chartDest := chartGeometry.outLow
  have chartEnd := chartGeometry.outHigh
  have chartKeep (a : Fin w) (b : Fin n) :
      val F canonical qN.WS τ (OB+(a.val*n+b.val))=xs a b := by
    have hIdx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    rw [Nat.succ_mul] at chartRB
    exact (mem₂ _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (by omega) (by omega)).trans (xvals a b)
  have run : Run B (archivedCompleteChart O address) σ τ _ := r₁.seq r₂
  refine ⟨τ,L,j,w,xs,hj,hList,hBound,run,s₂,hCur,xInd,xSpan,chartKeep,chart,?_,Frame.of_run run⟩
  intro k hk ht hl ha hc hs hg hd hz₁ hz₂
  exact (mem₂ k hk hc hs hg hd hz₁ hz₂).trans (mem₁ k hk ht hl ha hz₁ hz₂)
#print axioms archivedCompleteChart_run
end EvenTI.P19Recover

