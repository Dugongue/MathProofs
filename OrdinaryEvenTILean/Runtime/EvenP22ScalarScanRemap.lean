import EvenP21ScalarScanSelect
import EvenP20ScalarPositiveSites
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1000000

namespace EvenTI.P21ScalarScan

open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P20Scalar (positiveSiteCount)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

def siteReindexWords : String := "even.p22.scalar.site.reindex.words"
def siteReindexCursor : String := "even.p22.scalar.site.reindex.cursor"

private def rewriteSite : Com :=
  .store stencilSitesBank (.var siteReindexCursor)
    (.get siteReindexWords (.get stencilSitesBank (.var siteReindexCursor)))

def remapSelectedSites : Com := forLoop siteReindexCursor positiveSiteCount rewriteSite

/-- Apply the archived-to-incidence address table to the native physical
site prefix in place. The untouched tail and every unrelated bank survive. -/
theorem remapSelectedSites_run {W R : ℕ} {s : Env}
    (hLimit : s.vars positiveSiteCount=R) (hR : R < W)
    (hFit : R ≤ (s.arrs stencilSitesBank).length)
    (hAddr : ∀ k < R, (s.arrs stencilSitesBank).getD k 0 < (s.arrs siteReindexWords).length)
    (hMapLen : (s.arrs siteReindexWords).length < W)
    (hWords : ∀ a ∈ s.arrs siteReindexWords, a < W) :
    ∃ t, Run W remapSelectedSites s t (13*R+6) ∧ Frame remapSelectedSites s t ∧
      SegInv (s.arrs stencilSitesBank) (t.arrs stencilSitesBank) 0 R
        (fun k => (s.arrs siteReindexWords).getD ((s.arrs stencilSitesBank).getD k 0) 0) := by
  let orig := s.arrs stencilSitesBank
  let ren := s.arrs siteReindexWords
  let map (k : ℕ) := ren.getD (orig.getD k 0) 0
  let I (j : ℕ) (u : Env) := SegInv orig (u.arrs stencilSitesBank) 0 j map ∧
    (u.arrs stencilSitesBank).length=orig.length ∧ u.arrs siteReindexWords=ren
  have init : I 0 (s.setVar siteReindexCursor 0) := ⟨SegInv.zero _ _ _,rfl,rfl⟩
  have step : ∀ k < R, ∀ u, I k u → u.vars siteReindexCursor=k → u.vars positiveSiteCount=R →
      ∃ t, Run W rewriteSite u t 5 ∧ t.vars siteReindexCursor=k ∧ t.vars positiveSiteCount=R ∧
        I (k+1) (t.setVar siteReindexCursor (k+1)) := by
    intro k hk u hu hI hC
    have hBefore : k < (u.arrs stencilSitesBank).length := by rw [hu.2.1]; exact hk.trans_le hFit
    have old : (u.arrs stencilSitesBank).getD k 0=orig.getD k 0 := hu.1.outside k (.inr (by omega))
    have addr : orig.getD k 0 < ren.length := hAddr k hk
    have addrWord := addr.trans hMapLen
    have idx : (Expr.var siteReindexCursor).evalB W u=some k := ev_var hI (hk.trans hR)
    have atSite : (Expr.get stencilSitesBank (.var siteReindexCursor)).evalB W u=some (orig.getD k 0) := by
      refine evalB_get idx ?_ addrWord
      rw [List.getElem?_eq_getElem hBefore,←List.getD_eq_getElem _ _ hBefore,old]
    have atMap : (Expr.get siteReindexWords (.get stencilSitesBank (.var siteReindexCursor))).evalB W u=some (map k) := by
      refine evalB_get atSite ?_ ?_
      · rw [hu.2.2,List.getElem?_eq_getElem addr,← List.getD_eq_getElem _ _ addr]
      · unfold map
        rw [List.getD_eq_getElem _ _ addr]
        exact hWords _ (List.getElem_mem addr)
    let t := u.setArr stencilSitesBank k (map k)
    have rr : Run W rewriteSite u t 5 := Run.store idx atMap hBefore
    have f := Frame.of_run rr
    refine ⟨t,rr,hI,hC,?_,(f.len _).trans hu.2.1,(f.arrs _ (by decide)).trans hu.2.2⟩
    simpa only [t,arrs_setVar,arrs_setArr,if_true,Nat.zero_add] using hu.1.step (by simpa using hBefore) rfl
  obtain ⟨t,rr,h,_⟩ := forLoop_run siteReindexCursor positiveSiteCount rewriteSite
    (by decide) I hLimit hR init step
  refine ⟨t,rr.mono (by omega),Frame.of_run rr,h.1⟩

#print axioms remapSelectedSites_run
end EvenTI.P21ScalarScan
