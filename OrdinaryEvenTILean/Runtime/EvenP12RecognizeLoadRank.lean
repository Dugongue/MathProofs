import EvenP12RecognizeRankLoad
import EvenP12CompareRetainedLayout

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.LiveSpectral

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007 Mathproof.P15RecogIMPTail20261007
open Mathproof.P15DecideIMPKerBasis20261007 Mathproof.P15DecideIMPRowKer20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Materialize a retained flattening in the physical rank bank and run the
original rank code. The input field slots are still in raw dense tensor order. -/
theorem paidRetainedLoadRank_run (F : FieldEncoding K) (FP : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : Nat} {σ : Env}
    (T : Tensor K (d+1) n) (i : Fin (d+1)) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hLength : n^(d+1) ≤ L) (layout : KBLay (n^d) n AM OUT Z Sn B)
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
  obtain ⟨τ,hRank,hSlots,hIn',hOut',hZero⟩ := paidRetainedRank_run F FP T i hd hn L hLength
    layout hMid hR' hD' hRB' hAM' hOUT' hZ' hO' hT' hU' hws' hLow hHigh hTensorRows hz' ho'
  exact ⟨τ, Run.seq hMove hRank, hSlots, hIn'.trans hIn, hOut'.trans hOut, hZero⟩

#print axioms paidRetainedLoadRank_run
end EvenTI.LiveSpectral
