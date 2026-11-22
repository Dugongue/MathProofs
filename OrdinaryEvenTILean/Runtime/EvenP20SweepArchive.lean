import EvenP19RecoverChartBank
import Mathproof.Meta.P15DecideIMPSplit20261007
import Mathproof.Meta.P15GEInit20261007

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1850000

namespace EvenTI.P20Sweep

open scoped BigOperators Matrix Polynomial
open EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15DecideIMPEGens20261007 (ev_mul ev_var)
open Mathproof.P15DecideIMPSplit20261007 (cpBlk cpBlk_run)
open Mathproof.P15DecideIMPCopy20261007 (copyCost)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)

def savedBasisSource : String := "even.recover.save.basis-source"
def savedChartSource : String := "even.recover.save.chart-source"
def savedBasisDestination : String := "even.recover.save.basis-destination"
def savedChartDestination : String := "even.recover.save.chart-destination"
def savedAmbientSize : String := "even.recover.save.ambient-size"
def savedBasisWords : String := "even.recover.save.basis-words"
def savedChartWords : String := "even.recover.save.chart-words"
def savedRow : String := "even.recover.save.row"
def savedWidths : String := "even.recover.save.widths"

noncomputable def publishChart : Com :=
  .seq (.assign savedBasisWords (.mul (.var chartCursor) (.var savedAmbientSize)))
    (.seq (.assign savedChartWords (.mul (.var chartCursor) (.var chartCursor)))
      (.seq (cpBlk savedBasisSource savedBasisDestination savedBasisWords)
        (.seq (cpBlk savedChartSource savedChartDestination savedChartWords)
          (.store savedWidths (.var savedRow) (.var chartCursor)))))

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def publishChartCost (F : FieldPresentation K) (w n : ℕ) : ℕ :=
  23+copyCost F (w*n)+copyCost F (w*w)

structure PublishPorts (s : Env) (n w srcX srcR dstX dstR row Z : ℕ) : Prop where
  width : s.vars chartCursor=w
  ambient : s.vars savedAmbientSize=n
  basisSource : s.vars savedBasisSource=srcX
  chartSource : s.vars savedChartSource=srcR
  basisDestination : s.vars savedBasisDestination=dstX
  chartDestination : s.vars savedChartDestination=dstR
  rowIndex : s.vars savedRow=row
  zero : s.vars dZ=Z
  one : s.vars rOs=Z+1
  temp1 : s.vars dT=Z+2
  temp2 : s.vars dU=Z+3

def SavedChart (F : FieldPresentation K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : Polynomial K) (row outX outR : ℕ) (t : Env) : Prop :=
  ∃ (w : ℕ) (xs : Fin w → Fin n → K), w≤n ∧
    (t.arrs savedWidths)[row]?=some w ∧
    LinearIndependent K xs ∧
    Submodule.span K (Set.range xs) = LinearMap.ker (Polynomial.aeval A f).mulVecLin ∧
    (∀ j k, val F canonical qN.WS t (outX+(j.val*n+k.val))=xs j k) ∧
    ChartPrefix F t outR w A xs

private theorem keepCopy₁ :
    ∀ r ∈ [chartCursor,savedChartSource,savedChartDestination,savedChartWords,savedRow,dZ,rOs,dT,dU],
       r∉scalarWrites (cpBlk savedBasisSource savedBasisDestination savedBasisWords) := by decide

private theorem keepCopy₂ :
    ∀ r ∈ [chartCursor,savedRow],
       r∉scalarWrites (cpBlk savedChartSource savedChartDestination savedChartWords) := by decide

/-- Persist the live primary restriction and its basis in disjoint blocks.
The stored width is a natural word, so it is not reduced in the field. -/
theorem publishChart_run (F : FieldPresentation K)
    {B Sn n w srcX srcR dstX dstR row Z : ℕ} {s : Env}
    (hs : Slots F canonical qN.WS Sn B s)
    (P : PublishPorts s n w srcX srcR dstX dstR row Z)
    (hw : w ≤ n) (hnB : n<B)
    (hSrcX : srcX+w*n≤dstX) (hSrcR : srcR+w*w≤dstX)
    (hApart : dstX+w*n≤dstR) (hDst : dstR+w*w≤Z)
    (hZ : Z+4≤Sn) (hB : Sn+10<B)
    (hRow : row<(s.arrs savedWidths).length) (hRowB : row<B)
    (hz : val F canonical qN.WS s Z=0) (hOne : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run B publishChart s t (publishChartCost F w n) ∧
      Slots F canonical qN.WS Sn B t ∧ (t.arrs savedWidths)[row]?=some w ∧
      (∀ k < w*n, val F canonical qN.WS t (dstX+k)=val F canonical qN.WS s (srcX+k)) ∧
      (∀ k < w*w, val F canonical qN.WS t (dstR+k)=val F canonical qN.WS s (srcR+k)) ∧
      (∀ k < Sn, (k < dstX ∨ dstX+w*n ≤ k) → (k < dstR ∨ dstR+w*w ≤ k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ k, k≠row → (t.arrs savedWidths)[k]?=(s.arrs savedWidths)[k]?) ∧
      Frame publishChart s t := by
  let a := s.setVar savedBasisWords (w*n)
  let b := a.setVar savedChartWords (w*w)
  have r₀ : Run B (.assign savedBasisWords (.mul (.var chartCursor) (.var savedAmbientSize))) s a 4 :=
    Run.assign (ev_mul (ev_var P.width (hw.trans_lt hnB)) (ev_var P.ambient hnB) (by omega))
  have hWa : a.vars chartCursor=w := P.width
  have r₁ : Run B (.assign savedChartWords (.mul (.var chartCursor) (.var chartCursor))) a b 4 :=
    Run.assign (ev_mul (ev_var hWa (hw.trans_lt hnB)) (ev_var hWa (hw.trans_lt hnB)) (by omega))
  have hb : Slots F canonical qN.WS Sn B b :=
    Slots.setVar F canonical (Slots.setVar F canonical hs (by decide) (by decide) _)
      (by decide) (by decide) _
  have vb (k : ℕ) : val F canonical qN.WS b k=val F canonical qN.WS s k :=
    (val_setVar F canonical (by decide : savedChartWords≠qN.WS) a _ k).trans
      (val_setVar F canonical (by decide : savedBasisWords≠qN.WS) s _ k)
  obtain ⟨u,ru,hu,hX,hOutsideX,hRegsX,_,_⟩ :=
    cpBlk_run F (len := w*n) savedBasisSource savedBasisDestination savedBasisWords hb
      (by decide) (by decide) (by decide)
      (show b.vars savedBasisSource=srcX from P.basisSource)
      (show b.vars savedBasisDestination=dstX from P.basisDestination) rfl
      (show b.vars dZ=Z from P.zero) (show b.vars rOs=Z+1 from P.one)
      (show b.vars dT=Z+2 from P.temp1) (show b.vars dU=Z+3 from P.temp2)
      ((vb _).trans hz) ((vb _).trans hOne) (Or.inl hSrcX) (by omega) (by omega) hZ hB
  have hMemX (k : ℕ) (hk : k<Sn) (hkeep : k<dstX ∨ dstX+w*n≤k)
      (ht : k≠Z+2) (hU : k≠Z+3) :
      val F canonical qN.WS u k=val F canonical qN.WS s k :=
    (hOutsideX k hk hkeep ht hU).trans (vb _)
  obtain ⟨v,rv,hv,hR,hOutsideR,hRegsR,_,_⟩ :=
    cpBlk_run F (len := w*w) savedChartSource savedChartDestination savedChartWords hu
      (by decide) (by decide) (by decide)
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans
        (show b.vars savedChartSource=srcR from P.chartSource))
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans
        (show b.vars savedChartDestination=dstR from P.chartDestination))
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans rfl)
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars dZ=Z from P.zero))
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars rOs=Z+1 from P.one))
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars dT=Z+2 from P.temp1))
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars dU=Z+3 from P.temp2))
      ((hMemX Z (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans hz)
      ((hMemX (Z+1) (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans hOne)
      (Or.inl (by omega)) (by omega) hDst hZ hB
  have hvRow : v.vars savedRow=row :=
    (hRegsR _ (keepCopy₂ _ (by decide))).trans
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars savedRow=row from P.rowIndex))
  have hvW : v.vars chartCursor=w :=
    (hRegsR _ (keepCopy₂ _ (by decide))).trans
      ((hRegsX _ (keepCopy₁ _ (by decide))).trans (show b.vars chartCursor=w from P.width))
  have hvWidths : v.arrs savedWidths=s.arrs savedWidths :=
    ((Frame.of_run rv).arrs _ (by decide)).trans ((Frame.of_run ru).arrs _ (by decide))
  let t := v.setArr savedWidths row w
  have r₄ : Run B (.store savedWidths (.var savedRow) (.var chartCursor)) v t 3 :=
    Run.store (ev_var hvRow hRowB) (ev_var hvW (hw.trans_lt hnB)) (by rwa [hvWidths])
  have rt : Run B publishChart s t (publishChartCost F w n) :=
    (r₀.seq (r₁.seq (ru.seq (rv.seq r₄)))).mono (by unfold publishChartCost; omega)
  have hMem : t.arrs canonical.mem=v.arrs canonical.mem := by simp [t,arrs_setArr,show canonical.mem≠savedWidths by decide]
  have hScratch : t.arrs canonical.scratch=v.arrs canonical.scratch := by simp [t,arrs_setArr,show canonical.scratch≠savedWidths by decide]
  have ht : Slots F canonical qN.WS Sn B t := slots_frame F hv hMem hScratch (fun _ _ => rfl) rfl
  have vt (k : ℕ) : val F canonical qN.WS t k=val F canonical qN.WS v k := by
    unfold val
    apply congrArg (Mathproof.Problem18IMPFieldPresentation20261001.decode F)
    funext i
    change (t.arrs canonical.mem).getD (v.vars qN.WS+k*F.e+i.val) 0 =
      (v.arrs canonical.mem).getD (v.vars qN.WS+k*F.e+i.val) 0
    rw [hMem]
  refine ⟨t,rt,ht,?_,?_,?_,?_,?_,Frame.of_run rt⟩
  · simp [t, hvWidths, hRow]
  · intro k hk
    exact (vt _).trans ((hOutsideR _ (by omega) (Or.inl (by omega)) (by omega) (by omega)).trans
      ((hX k hk).trans (vb _)))
  · intro k hk
    exact (vt _).trans ((hR k hk).trans (hMemX _ (by omega) (Or.inl (by omega)) (by omega) (by omega)))
  · intro k hk hx hr ht' hu'
    exact (vt _).trans ((hOutsideR _ hk hr ht' hu').trans (hMemX _ hk hx ht' hu'))
  · intro k hk
    simp [t, hvWidths, List.getElem?_set_ne, Ne.symm hk]

/-- A successful copy retains the exact primary subspace and its action matrix. -/
theorem savedChart_of_publish (F : FieldPresentation K) {n w srcX srcR dstX dstR row : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {xs : Fin w → Fin n → K} {s t : Env}
    (hw : w≤n) (hWidth : (t.arrs savedWidths)[row]?=some w)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (Polynomial.aeval A f).mulVecLin)
    (hBasis : ∀ j k, val F canonical qN.WS s (srcX+(j.val*n+k.val))=xs j k)
    (hChart : ChartPrefix F s srcR w A xs)
    (hX : ∀ k < w*n, val F canonical qN.WS t (dstX+k)=val F canonical qN.WS s (srcX+k))
    (hR : ∀ k < w*w, val F canonical qN.WS t (dstR+k)=val F canonical qN.WS s (srcR+k)) :
    SavedChart F A f row dstX dstR t := by
  have idx (j : Fin w) (q : ℕ) (k : Fin q) : j.val*q+k.val<w*q := by
    have h := Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr j.isLt)
    rw [Nat.succ_mul] at h
    omega
  refine ⟨w,xs,hw,hWidth,hInd,hSpan,?_,?_⟩
  · intro j k
    exact (hX _ (idx j n k)).trans (hBasis j k)
  · intro j hj
    rw [← hChart j hj]
    apply Finset.sum_congr rfl
    intro i _
    rw [hR _ (idx j w i)]

end EvenTI.P20Sweep

