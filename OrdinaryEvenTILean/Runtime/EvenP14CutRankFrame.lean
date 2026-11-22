import EvenP12RecognizeLoadRank

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.LiveSpectral

open EvenTI.Action EvenTI.Contract Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007 Mathproof.P15RecogIMPTail20261007
open Mathproof.P15DecideIMPKerBasis20261007 Mathproof.P15DecideIMPRowKer20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Preserve the original source and canonical constants while the retained rank workspace is reused. -/
theorem paidCutRetainedLoadRank_run (F : FieldEncoding K) (FP : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : Nat} {σ : Env}
    (T : Tensor K (d+1) n) (i : Fin (d+1)) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hLength : n^(d+1) ≤ L) (layout : KBLay (n^d) n AM OUT Z Sn B)
    (hSourceLow : (n+1)*XBs (n^d) n ≤ src)
    (hLow : (n+1)*XBs (n^d) n ≤ RB)
    (hHigh : RB + n^d*n ≤ AM) (hSrcFit : src + n^d*n ≤ RB)
    (hDstFit : RB + n^d*n ≤ Z) (hScratch : Z+4 ≤ Sn) (hBound : Sn+3 < B)
    (hS : Slots FP canonical qN.WS Sn B σ)
    (hsrc : σ.vars retainedSrc = src) (hs : σ.vars retainedStride = n^(d-i.val))
    (hOne : σ.vars dL = 1) (hT : σ.vars dT = Z+2) (hU : σ.vars dU = Z+3)
    (hZ : σ.vars dZ = Z) (hO : σ.vars rOs = Z+1)
    (hRows : σ.vars gRows = n^d) (hCols : σ.vars gCols = n) (hDst : σ.vars gOut = RB)
    (hR : σ.vars tNR = n^d) (hD : σ.vars tD = n) (hRB : σ.vars tRB = RB)
    (hAM : σ.vars kAM = AM) (hOUT : σ.vars kOUT = OUT)
    (hws : σ.vars qN.WS = FP.e + 1)
    (hTensor : ∀ u : Coord (d+1) n,
      val FP canonical qN.WS σ (src+(inputCoordOrder n (d+1) u).val) = T u)
    (hz : val FP canonical qN.WS σ Z = 0)
    (ho : val FP canonical qN.WS σ (Z+1) = 1) :
    ∃ τ, Run B (.seq (gridProg Mac copyAE retainedIndex) rkProg) σ τ
        (300*(macroBudget FP*(L+2)^4) + 34500*(macroBudget FP*(6*L)^5)) ∧
      Slots FP canonical qN.WS Sn B τ ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      (∀ u : Coord (d+1) n, val FP canonical qN.WS τ
        (src+(inputCoordOrder n (d+1) u).val) = T u) ∧
      (∀ s < Sn, (n+1)*XBs (n^d) n ≤ s → s < RB ∨ OUT+n*n ≤ s → s ≠ Z+2 → s ≠ Z+3 →
        val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      val FP canonical qN.WS τ Z = 0 ∧ val FP canonical qN.WS τ (Z+1) = 1 ∧
      (∀ x, x ∉ scalarWrites rkProg → x ∉ regNames canonical → x ≠ dI →
        x ≠ gU → x ≠ gV → x ≠ dO → τ.vars x = σ.vars x) ∧
      τ.vars kK ≤ n ∧
      (τ.vars kK = 0 ↔
        (rawKernelVectors (retainedForm i T).transpose (cutOrder d n) (Equiv.refl (Fin n))).isEmpty
          = true) := by
  have hn' : 0 < n := by omega
  have hprod : n^i.val * n^(d-i.val) = n^d := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
  have hL : (n^i.val*n^(d-i.val))*n ≤ L := by rw [hprod,← pow_succ]; exact hLength
  obtain ⟨mid, hMove, hMid, hBank, hFrame, hVars, hIn, hOut⟩ :=
    paidRetainedLoad_run FP (a := n^i.val) (s := n^(d-i.val))
      (pow_pos hn' _) hn' (pow_pos hn' _) hL (by rwa [hprod]) (by rwa [hprod])
      hScratch hBound hS hsrc hs hOne hT hU hZ hO (by rwa [hprod]) hCols hDst hz ho
  have hR' : mid.vars tNR = n^d := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR
  have hD' : mid.vars tD = n := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD
  have hRB' : mid.vars tRB = RB := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRB
  have hAM' : mid.vars kAM = AM := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hAM
  have hOUT' : mid.vars kOUT = OUT := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOUT
  have hZ' : mid.vars dZ = Z := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hZ
  have hO' : mid.vars rOs = Z+1 := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hO
  have hT' : mid.vars dT = Z+2 := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hT
  have hU' : mid.vars dU = Z+3 := (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hU
  have hws' : mid.vars qN.WS = FP.e + 1 :=
    (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hws
  have hz' : val FP canonical qN.WS mid Z = 0 := by
    rw [hFrame _ (by omega)]; exact hz
    rw [hprod]
    rintro (⟨_,_⟩ | h | h) <;> omega
  have ho' : val FP canonical qN.WS mid (Z+1) = 1 := by
    rw [hFrame _ (by omega)]; exact ho
    rw [hprod]
    rintro (⟨_,_⟩ | h | h) <;> omega
  have hTensorRows (u : Fin (n^d)) (j : Fin n) :
      val FP canonical qN.WS mid (RB+(u.val*n+j.val)) =
        (retainedForm i T).transpose ((inputCoordOrder n d).symm u) j := by
    rw [hBank _ (by rw [hprod]; exact u.isLt) _ j.isLt]
    let x := (inputCoordOrder n d).symm u
    have hx : inputCoordOrder n d x = u := Equiv.apply_symm_apply _ _
    have haddress := EvenTI.P12Compare.inputCoord_retained n d hn' i j x
    rw [hx] at haddress
    change val FP canonical qN.WS σ
      (src + EvenTI.P12Compare.insertWordIndex n (n^(d-i.val)) j.val u.val) =
      T (retainedMode i (j,x))
    rw [← haddress]
    exact hTensor _
  let M := (retainedForm i T).transpose
  let rowOrder := inputCoordOrder n d
  let colOrder := Equiv.refl (Fin n)
  obtain ⟨τ,hRank,hSlots,_,⟨xs,hBasis,hInd,hSpan⟩,hRankSlots,hRankVars,hIn',hOut'⟩ :=
    rk_run FP layout (kernelInputMatrix M rowOrder colOrder) hMid hR' hD' hRB' hAM' hOUT'
      hZ' hO' hT' hU' hws' hLow hHigh hTensorRows hz' ho'
  obtain ⟨hInd',hSpan'⟩ := kernelInputMatrix_basis M rowOrder colOrder xs hInd hSpan
  let e := frameFromVectors M.mulVecLin (fun j k => xs j (colOrder k)) hInd' hSpan'
  have hDim : τ.vars kK = Module.finrank K M.mulVecLin.ker := by simpa using e.finrank_eq
  have hKerBound : τ.vars kK ≤ n := by
    rw [hDim]
    simpa using Submodule.finrank_le M.mulVecLin.ker
  have hSrc {s : ℕ} (hss : src ≤ s) (hsr : s < RB) :
      val FP canonical qN.WS τ s = val FP canonical qN.WS σ s := by
    have h1 : s < Sn := by omega
    rw [hRankSlots s h1 (by omega) (Or.inl (by omega)) (by omega) (by omega)]
    apply hFrame s h1
    rw [hprod]
    rintro (⟨_,_⟩ | h | h) <;> omega
  have hZlo := layout.out_z
  have hZsn := layout.z_s
  have hSZ (s : ℕ) (hs : Z ≤ s ∧ s ≤ Z+1) :
      val FP canonical qN.WS τ s = val FP canonical qN.WS mid s :=
    hRankSlots s (by omega) (by omega) (Or.inr (Or.inr (by omega))) (by omega) (by omega)
  refine ⟨τ,hMove.seq (hRank.mono (retainedRankCost_le FP hd hn L hLength)),hSlots,
    hIn'.trans hIn,hOut'.trans hOut,?_,?_,(hSZ Z (by omega)).trans hz',
    (hSZ (Z+1) (by omega)).trans ho',?_,hKerBound,?_⟩
  · intro u
    have hu : (inputCoordOrder n (d+1) u).val < n^d*n :=
      (inputCoordOrder n (d+1) u).isLt.trans_le (Nat.le_of_eq (pow_succ n d))
    exact (hSrc (by omega) (by omega)).trans (hTensor u)
  · intro s hs hLower hOutside ht hu
    have hDisjoint : s < AM ∨ (AM+n*(n^d+n) ≤ s ∧ s < OUT) ∨ OUT+n*n ≤ s := by
      rcases hOutside with hb | hb
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr hb)
    rw [hRankSlots s hs hLower hDisjoint ht hu]
    apply hFrame s hs
    rw [hprod]
    have hAMout := layout.am_out
    rcases hOutside with hb | hb <;> rintro (⟨_,_⟩ | h | h) <;> omega
  · intro x hx hc hi hu hv ho
    exact (hRankVars x hx).trans (hVars x hc hi hu hv ho)
  · rw [hDim,List.isEmpty_iff_length_eq_zero,rawKernelVectors_length]

/-- Reinstall the grid ABI on every call. Rank elimination may reuse
these grid registers between retained modes. -/
noncomputable def cutRankModeCall : Com :=
  .seq (setGrid (v tNR) (v tD) (lit 1) (v tRB))
    (.seq (gridProg Mac copyAE retainedIndex) rkProg)

theorem cutRankModeCall_run (F : FieldEncoding K) (FP : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : Nat} {σ : Env}
    (T : Tensor K (d+1) n) (i : Fin (d+1)) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hLength : n^(d+1) ≤ L) (layout : KBLay (n^d) n AM OUT Z Sn B)
    (hSourceLow : (n+1)*XBs (n^d) n ≤ src)
    (hLow : (n+1)*XBs (n^d) n ≤ RB) (hHigh : RB + n^d*n ≤ AM)
    (hSrcFit : src + n^d*n ≤ RB) (hDstFit : RB + n^d*n ≤ Z)
    (hScratch : Z+4 ≤ Sn) (hBound : Sn+3 < B)
    (hS : Slots FP canonical qN.WS Sn B σ)
    (hsrc : σ.vars retainedSrc = src) (hstride : σ.vars retainedStride = n^(d-i.val))
    (hT : σ.vars dT = Z+2) (hU : σ.vars dU = Z+3)
    (hZ : σ.vars dZ = Z) (hO : σ.vars rOs = Z+1)
    (hR : σ.vars tNR = n^d) (hD : σ.vars tD = n) (hRB : σ.vars tRB = RB)
    (hAM : σ.vars kAM = AM) (hOUT : σ.vars kOUT = OUT)
    (hws : σ.vars qN.WS = FP.e + 1)
    (hTensor : ∀ u : Coord (d+1) n,
      val FP canonical qN.WS σ (src+(inputCoordOrder n (d+1) u).val) = T u)
    (hz : val FP canonical qN.WS σ Z = 0) (ho : val FP canonical qN.WS σ (Z+1) = 1) :
    ∃ τ, Run B cutRankModeCall σ τ
        (8 + (300*(macroBudget FP*(L+2)^4) + 34500*(macroBudget FP*(6*L)^5))) ∧
      Slots FP canonical qN.WS Sn B τ ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      (∀ u : Coord (d+1) n, val FP canonical qN.WS τ
        (src+(inputCoordOrder n (d+1) u).val) = T u) ∧
      (∀ s < Sn, (n+1)*XBs (n^d) n ≤ s → s < RB ∨ OUT+n*n ≤ s → s ≠ Z+2 → s ≠ Z+3 →
        val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      val FP canonical qN.WS τ Z = 0 ∧ val FP canonical qN.WS τ (Z+1) = 1 ∧
      (∀ x, x ∉ scalarWrites rkProg → x ∉ regNames canonical → x ≠ dI →
        x ≠ gU → x ≠ gV → x ≠ dO → x ≠ gRows → x ≠ gCols → x ≠ dL → x ≠ gOut →
        τ.vars x = σ.vars x) ∧
      τ.vars kK ≤ n ∧
      (τ.vars kK = 0 ↔
        (rawKernelVectors (retainedForm i T).transpose (cutOrder d n) (Equiv.refl (Fin n))).isEmpty
          = true) := by
  have hsB := layout.s_b
  have hnB : n < B := by omega
  have hRowB : n^d < B := by omega
  have hRBb : RB < B := by omega
  let s := (((σ.setVar gRows (n^d)).setVar gCols n).setVar dL 1).setVar gOut RB
  have evR : (v tNR).evalB B σ = some (n^d) :=
    evalB_var_iff.mpr ⟨hR.symm,hR ▸ hRowB⟩
  have evN : (v tD).evalB B σ = some n :=
    evalB_var_iff.mpr ⟨hD.symm,hD ▸ hnB⟩
  have evB : (v tRB).evalB B σ = some RB :=
    evalB_var_iff.mpr ⟨hRB.symm,hRB ▸ hRBb⟩
  have hSetup : Run B (setGrid (v tNR) (v tD) (lit 1) (v tRB)) σ s 8 :=
    setGrid_run (σ := σ) (B := B) (v tNR) (v tD) (lit 1) (v tRB) [tNR,tD,tRB]
      (by decide) (by simp [v,VarsIn]) (by simp [v,VarsIn]) (by simp [lit,VarsIn])
      (by simp [v,VarsIn]) evR evN (evalB_lit (by omega)) evB
  have hv (x : String) (h1 : x ≠ gRows) (h2 : x ≠ gCols) (h3 : x ≠ dL) (h4 : x ≠ gOut) :
      s.vars x = σ.vars x := vars_setGrid σ _ _ _ _ x h1 h2 h3 h4
  have hvv (x : ℕ) : val FP canonical qN.WS s x = val FP canonical qN.WS σ x := by
    dsimp only [s]
    rw [val_setGrid]
  obtain ⟨τ,hRun,hSlots,hIn,hOut,hPres,hMem,hzero,hone,hVars,hKB,hKer⟩ :=
    paidCutRetainedLoadRank_run F FP (σ := s) T i hd hn hLength layout hSourceLow hLow
      hHigh hSrcFit hDstFit hScratch hBound (slots_setGrid FP hS _ _ _ _)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hsrc)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hstride)
      (by simp [s,dL,gOut])
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hT)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hU)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hZ)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hO)
      (by simp [s,gRows,gCols,dL,gOut]) (by simp [s,gCols,dL,gOut]) (by simp [s])
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hR)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hD)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hRB)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hAM)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hOUT)
      ((hv _ (by decide) (by decide) (by decide) (by decide)).trans hws)
      (fun u => (hvv _).trans (hTensor u)) ((hvv _).trans hz) ((hvv _).trans ho)
  refine ⟨τ,hSetup.seq hRun,hSlots,(by simpa [s] using hIn),(by simpa [s] using hOut),
    hPres,?_,hzero,hone,?_,hKB,hKer⟩
  · intro j hj hLo hFar ht hu
    exact (hMem j hj hLo hFar ht hu).trans (hvv j)
  · intro x hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10
    exact (hVars x hx1 hx2 hx3 hx4 hx5 hx6).trans (hv x hx7 hx8 hx9 hx10)

#print axioms paidCutRetainedLoadRank_run
#print axioms cutRankModeCall_run
end EvenTI.LiveSpectral
