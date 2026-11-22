import EvenP18ScalarStencil
import EvenP17ScalarActiveSlotVisit
import EvenP17ScalarActiveLoop

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 12000

namespace EvenTI.P19Scalar.PrefixStencil

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P17Scalar (activeSlotBank)
open EvenTI.P17Scalar.ActiveProducer (installSlot installSlot_run)

def stencilChartBank : String := "even.scalar.stencil.chart"
def stencilSitesBank : String := "even.scalar.stencil.sites"
def stencilCursor : String := "even.scalar.stencil.cursor"
def stencilLimit : String := "even.scalar.stencil.limit"
def stencilColumns : String := "even.scalar.stencil.columns"
def stencilZero : String := "even.scalar.stencil.zero"
def stencilReference : String := "even.scalar.stencil.reference"

def stencilValue (chart sites : List ℕ) (columns zero reference k : ℕ) : ℕ :=
  if chart.getD k 0=zero then reference else sites.getD (k/columns) 0

private def stencilGuard : Cond := .lt (.var stencilCursor) (.var stencilLimit)
private def stencilBody : Com :=
  .seq (installSlot stencilChartBank stencilSitesBank activeSlotBank stencilCursor
    stencilColumns stencilZero stencilReference)
    (.assign stencilCursor (.add (.var stencilCursor) (.lit 1)))

def installActiveStencil : Com :=
  .seq (.assign stencilCursor (.lit 0)) (.while stencilGuard stencilBody)

private structure StencilState (s : Env) (chart sites : List ℕ)
    (L columns zero reference : ℕ) (u : Env) : Prop where
  bound : u.vars stencilCursor ≤ L
  limit : u.vars stencilLimit=L
  cols : u.vars stencilColumns=columns
  zeroEq : u.vars stencilZero=zero
  referenceEq : u.vars stencilReference=reference
  chartEq : u.arrs stencilChartBank=chart
  sitesEq : u.arrs stencilSitesBank=sites
  length : (u.arrs activeSlotBank).length=(s.arrs activeSlotBank).length
  segment : SegInv (s.arrs activeSlotBank) (u.arrs activeSlotBank) 0
    (u.vars stencilCursor) (stencilValue chart sites columns zero reference)
  other : ∀ a, a ≠ activeSlotBank → u.arrs a=s.arrs a
  input : u.inp=s.inp
  output : u.out=s.out

/-- Construct the complete active-slot stencil from actual chart and site
banks. Every zero entry receives the harmless reference slot. Every nonzero
entry receives its row's site slot. All other arrays and both tapes survive. -/
theorem installActiveStencil_run
    {W L columns zero reference : ℕ} {s : Env} (chart sites : List ℕ)
    (hOne : 1 < W) (hL : L < W) (hColumns : columns < W)
    (hZero : zero < W) (hReference : reference < W)
    (hChartFit : L ≤ chart.length)
    (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : L ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero) (hRef : s.vars stencilReference=reference) :
    ∃ t, Run W installActiveStencil s t (34*L+20) ∧
      (∀ k < L, (t.arrs activeSlotBank).getD k 0 = stencilValue chart sites columns zero reference k) ∧
      (t.arrs activeSlotBank).length=(s.arrs activeSlotBank).length ∧
      (∀ k, L ≤ k → (t.arrs activeSlotBank).getD k 0 = (s.arrs activeSlotBank).getD k 0) ∧
      (∀ a, a ≠ activeSlotBank → t.arrs a=s.arrs a) ∧
      t.inp=s.inp ∧ t.out=s.out ∧ t.vars stencilCursor=L := by
  let z := s.setVar stencilCursor 0
  let I := StencilState s chart sites L columns zero reference
  let potential (u : Env) := L-u.vars stencilCursor
  have rz : Run W (.assign stencilCursor (.lit 0)) s z 2 :=
    Run.assign (evalB_lit (by omega))
  have hzCursor : z.vars stencilCursor=0 := by simp [z]
  have iz : I z := by
    refine ⟨by rw [hzCursor]; omega,?_,?_,?_,?_,hChart,hSites,rfl,?_,
      fun _ _ => rfl,rfl,rfl⟩
    · simpa only [z,vars_setVar,show stencilLimit ≠ stencilCursor by decide,if_false] using hLimit
    · simpa only [z,vars_setVar,show stencilColumns ≠ stencilCursor by decide,if_false] using hCols
    · simpa only [z,vars_setVar,show stencilZero ≠ stencilCursor by decide,if_false] using hZ
    · simpa only [z,vars_setVar,show stencilReference ≠ stencilCursor by decide,if_false] using hRef
    · rw [hzCursor]
      exact SegInv.zero _ _ _
  have guard (u : Env) (hu : I u) :
      stencilGuard.evalB W u=some (decide (u.vars stencilCursor < L)) := by
    have e := evalB_condLt (evalB_var (hu.bound.trans_lt hL))
      (evalB_var_iff.mpr ⟨hu.limit.symm,by rw [hu.limit]; exact hL⟩)
    simpa only [stencilGuard,hu.limit] using e
  have step (u : Env) (hu : I u) (hg : stencilGuard.evalB W u=some true) :
      ∃ v, Run W stencilBody u v 24 ∧ I v ∧ potential v < potential u := by
    rw [guard u hu] at hg
    have hk : u.vars stencilCursor < L := by simpa using hg
    let k := u.vars stencilCursor
    have hkChart : k < chart.length := hk.trans_le hChartFit
    have hkSite := hSiteFit k hk
    have hLabel : (u.arrs stencilChartBank)[k]?=some (chart.getD k 0) := by
      rw [hu.chartEq,List.getElem?_eq_getElem hkChart,List.getD_eq_getElem _ _ hkChart]
    have hSite : (u.arrs stencilSitesBank)[k/columns]?=some (sites.getD (k/columns) 0) := by
      rw [hu.sitesEq,List.getElem?_eq_getElem hkSite,List.getD_eq_getElem _ _ hkSite]
    have hLabelWord : chart.getD k 0 < W := by
      rw [List.getD_eq_getElem _ _ hkChart]
      exact hChartWords _ (List.getElem_mem hkChart)
    have hSiteWord : sites.getD (k/columns) 0 < W := by
      rw [List.getD_eq_getElem _ _ hkSite]
      exact hSiteWords _ (List.getElem_mem hkSite)
    have hStore : k < (u.arrs activeSlotBank).length := by rw [hu.length]; exact hk.trans_le hTarget
    let w := u.setArr activeSlotBank k (stencilValue chart sites columns zero reference k)
    have r0 : Run W (installSlot stencilChartBank stencilSitesBank activeSlotBank stencilCursor
        stencilColumns stencilZero stencilReference) u w 20 :=
      installSlot_run _ _ _ _ _ _ _ rfl (hk.trans hL) hu.cols hColumns
        ((Nat.div_le_self k columns).trans_lt (hk.trans hL))
        hLabel hLabelWord hu.zeroEq hZero hu.referenceEq hReference hSite hSiteWord hStore
    let v := w.setVar stencilCursor (k+1)
    have ew : (Expr.var stencilCursor).evalB W w=some k :=
      evalB_var_iff.mpr ⟨rfl,hk.trans hL⟩
    have r1 : Run W (.assign stencilCursor (.add (.var stencilCursor) (.lit 1))) w v 4 :=
      Run.assign (evalB_bin (op:=.add) ew (evalB_lit hOne)
        ((Nat.succ_le_of_lt hk).trans_lt hL))
    have hvCursor : v.vars stencilCursor=k+1 := by simp [v]
    refine ⟨v,r0.seq r1,?_,?_⟩
    · refine ⟨by rw [hvCursor]; omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,hu.input,hu.output⟩
      · simpa only [v,w,vars_setVar,vars_setArr,show stencilLimit ≠ stencilCursor by decide,if_false] using hu.limit
      · simpa only [v,w,vars_setVar,vars_setArr,show stencilColumns ≠ stencilCursor by decide,if_false] using hu.cols
      · simpa only [v,w,vars_setVar,vars_setArr,show stencilZero ≠ stencilCursor by decide,if_false] using hu.zeroEq
      · simpa only [v,w,vars_setVar,vars_setArr,show stencilReference ≠ stencilCursor by decide,if_false] using hu.referenceEq
      · simpa only [v,w,arrs_setVar,arrs_setArr,show stencilChartBank ≠ activeSlotBank by decide,if_false] using hu.chartEq
      · simpa only [v,w,arrs_setVar,arrs_setArr,show stencilSitesBank ≠ activeSlotBank by decide,if_false] using hu.sitesEq
      · simpa only [v,w,arrs_setVar,arrs_setArr,if_true,List.length_set] using hu.length
      · have hs := hu.segment.step (by simpa only [Nat.zero_add] using hStore) rfl
        simpa only [v,w,arrs_setVar,arrs_setArr,vars_setVar,vars_setArr,if_true,hvCursor,Nat.zero_add] using hs
      · intro a ha
        simpa only [v,w,arrs_setVar,arrs_setArr,ha,if_false] using hu.other a ha
    · change L-(k+1) < L-k
      omega
  obtain ⟨t,rt,ht,hEnd⟩ := Run.while_count I potential 24
    (fun u hu => ⟨_,guard u hu⟩) step iz
  rw [guard t ht] at hEnd
  have hDone : t.vars stencilCursor=L :=
    le_antisymm ht.bound (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hEnd)))
  have hPotential : potential z=L := by change L-z.vars stencilCursor=L; rw [hzCursor,Nat.sub_zero]
  have hGuardSize : stencilGuard.size=3 := rfl
  have hArray : ∀ k < L, (t.arrs activeSlotBank).getD k 0 =
      stencilValue chart sites columns zero reference k := by
    intro k hk
    have hh := ht.segment.inside k (by rwa [hDone])
    simpa only [Nat.zero_add] using hh
  have hTail : ∀ k, L ≤ k → (t.arrs activeSlotBank).getD k 0 =
      (s.arrs activeSlotBank).getD k 0 := by
    intro k hk
    apply ht.segment.outside k
    right
    simpa only [Nat.zero_add,hDone] using hk
  refine ⟨t,(rz.seq rt).mono ?_,hArray,ht.length,hTail,ht.other,ht.input,ht.output,hDone⟩
  change 2+((1+stencilGuard.size+24)*potential z+1+stencilGuard.size) ≤ _
  rw [hGuardSize,hPotential]
  omega

theorem installActiveStencil_eq : installActiveStencil =
    EvenTI.P18Scalar.installActiveStencil := rfl

#print axioms installActiveStencil_run
end EvenTI.P19Scalar.PrefixStencil
