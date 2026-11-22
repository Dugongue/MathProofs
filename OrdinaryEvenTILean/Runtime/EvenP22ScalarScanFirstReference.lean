import EvenP21PadPrepare

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 25000

namespace EvenTI.P21ScalarScan

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_div)
open EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad

private def refGuard : Cond :=
  .lt (.var supportCursor) (.var stencilLimit)

private def noEntry : Cond :=
  .eq (.get stencilChartBank (.var supportCursor)) (.var stencilZero)

private def nextRef : Com :=
  .assign supportCursor (.add (.var supportCursor) (.lit 1))

private def setReference : Com :=
  .seq (.assign stencilReference (.get stencilSitesBank (.div (.var supportCursor) (.var stencilColumns))))
    (.assign supportCursor (.var stencilLimit))

private def refVisit : Com :=
  .ite noEntry nextRef setReference

private structure FirstRefState (s u : Env) (L columns zero : ℕ) : Prop where
  bound : u.vars supportCursor ≤ L
  limit : u.vars stencilLimit=L
  cols : u.vars stencilColumns=columns
  zeroEq : u.vars stencilZero=zero
  arrays : u.arrs=s.arrs
  examined : (∀ k < u.vars supportCursor, (s.arrs stencilChartBank).getD k 0=zero) ∨
    (u.vars supportCursor=L ∧ ∃ k < L, (∀ j < k, (s.arrs stencilChartBank).getD j 0=zero) ∧
      (s.arrs stencilChartBank).getD k 0≠zero ∧
      u.vars stencilReference=(s.arrs stencilSitesBank).getD (k/columns) 0)

/-- Choose a supported reference index from the physical masked chart.
The scan preserves all banks and stops as soon as it sees a nonzero label. -/
theorem findPadReference_first_run {W L columns zero : ℕ} {s : Env}
    (hOne : 1 < W) (hL : L < W) (hC : columns < W) (hZ : zero < W)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZero : s.vars stencilZero=zero)
    (hChart : L ≤ (s.arrs stencilChartBank).length)
    (hChartWords : ∀ a ∈ s.arrs stencilChartBank, a < W)
    (hSite : ∀ k < L, k/columns < (s.arrs stencilSitesBank).length)
    (hSiteWords : ∀ a ∈ s.arrs stencilSitesBank, a < W) :
    ∃ t, Run W findPadReference s t (24*L+6) ∧ Frame findPadReference s t ∧
      t.arrs=s.arrs ∧
      ((∀ k < L, (s.arrs stencilChartBank).getD k 0=zero) ∨
        ∃ k < L, (∀ j < k, (s.arrs stencilChartBank).getD j 0=zero) ∧
      (s.arrs stencilChartBank).getD k 0≠zero ∧
          t.vars stencilReference=(s.arrs stencilSitesBank).getD (k/columns) 0) := by
  let z := s.setVar supportCursor 0
  let I (u : Env) := FirstRefState s u L columns zero
  let pot (u : Env) := L-u.vars supportCursor
  have rZ : Run W (.assign supportCursor (.lit 0)) s z 2 := Run.assign (evalB_lit (by omega))
  have hz : z.vars supportCursor=0 := rfl
  have hI : I z :=
    ⟨by rw [hz]; omega,hLimit,hCols,hZero,rfl,Or.inl (fun k hk => by rw [hz] at hk; omega)⟩
  have guard (u : Env) (hu : I u) :
      refGuard.evalB W u=some (decide (u.vars supportCursor<L)) :=
    evalB_condLt (evalB_var (hu.bound.trans_lt hL)) (ev_var hu.limit hL)
  have visit (u : Env) (hu : I u) (hg : refGuard.evalB W u=some true) :
      ∃ t, Run W refVisit u t 20 ∧ I t ∧ pot t < pot u := by
    rw [guard u hu] at hg
    let k := u.vars supportCursor
    have hk : k < L := of_decide_eq_true (Option.some.inj hg)
    let chart := s.arrs stencilChartBank
    let sites := s.arrs stencilSitesBank
    have hfit : k < chart.length := hk.trans_le hChart
    have hfitSite : k/columns < sites.length := hSite k hk
    have ek := ev_var (x := supportCursor) (show u.vars supportCursor=k from rfl) (hk.trans hL)
    have ez := ev_var hu.zeroEq hZ
    have eColumns := ev_var hu.cols hC
    have hRead : (u.arrs stencilChartBank)[k]?=some (chart.getD k 0) := by
      rw [hu.arrays]
      change chart[k]?=some (chart.getD k 0)
      rw [List.getElem?_eq_getElem hfit,List.getD_eq_getElem _ _ hfit]
    have hReadWord : chart.getD k 0 < W := by
      rw [List.getD_eq_getElem _ _ hfit]
      exact hChartWords _ (List.getElem_mem hfit)
    have eChart := evalB_get ek hRead hReadWord
    have hc : noEntry.evalB W u=some (chart.getD k 0 == zero) := evalB_condEq eChart ez
    by_cases hEmpty : chart.getD k 0=zero
    · let t := u.setVar supportCursor (k+1)
      have r₁ : Run W nextRef u t 4 :=
        Run.assign (ev_add ek (evalB_lit hOne) ((Nat.succ_le_of_lt hk).trans_lt hL))
      have hTrue : noEntry.evalB W u=some true := by
        have hBit : (chart.getD k 0 == zero)=true := beq_iff_eq.mpr hEmpty
        rwa [hBit] at hc
      have rr : Run W refVisit u t 20 := (Run.ite_true (d:=setReference) hTrue r₁).mono (by decide)
      have ht : t.vars supportCursor=k+1 := rfl
      have hPast : ∀ j < k, chart.getD j 0=zero := by
        rcases hu.examined with ha | hFound
        · exact ha
        · exact False.elim (by have hh := hFound.1; change k=L at hh; omega)
      refine ⟨t,rr,⟨by rw [ht]; omega,hu.limit,hu.cols,hu.zeroEq,hu.arrays,Or.inl ?_⟩,?_⟩
      · intro j hj
        rw [ht] at hj
        by_cases he : j=k
        · simpa only [he] using hEmpty
        · exact hPast j (by omega)
      · change L-(k+1) < L-k
        omega
    · have hReadSite : (u.arrs stencilSitesBank)[k/columns]?=some (sites.getD (k/columns) 0) := by
        rw [hu.arrays]
        change sites[k/columns]?=some (sites.getD (k/columns) 0)
        rw [List.getElem?_eq_getElem hfitSite,List.getD_eq_getElem _ _ hfitSite]
      have hSiteWord : sites.getD (k/columns) 0 < W := by
        rw [List.getD_eq_getElem _ _ hfitSite]
        exact hSiteWords _ (List.getElem_mem hfitSite)
      have eq := ev_div ek eColumns ((Nat.div_le_self k columns).trans_lt (hk.trans hL))
      let x := u.setVar stencilReference (sites.getD (k/columns) 0)
      let t := x.setVar supportCursor L
      have r₀ : Run W (.assign stencilReference (.get stencilSitesBank (.div (.var supportCursor)
            (.var stencilColumns)))) u x 5 := Run.assign (evalB_get eq hReadSite hSiteWord)
      have r₁ : Run W (.assign supportCursor (.var stencilLimit)) x t 2 :=
        Run.assign (ev_var (show x.vars stencilLimit=L from hu.limit) hL)
      have hFalse : noEntry.evalB W u=some false := by
        have hBit : (chart.getD k 0 == zero)=false := beq_eq_false_iff_ne.mpr hEmpty
        rwa [hBit] at hc
      have rr : Run W refVisit u t 20 := (Run.ite_false (c:=nextRef) hFalse (r₀.seq r₁)).mono (by decide)
      have hPast : ∀ j < k, chart.getD j 0=zero := by
        rcases hu.examined with ha | hFound
        · exact ha
        · exact False.elim (by have hh := hFound.1; change k=L at hh; omega)
      refine ⟨t,rr,⟨by change L≤L; exact le_rfl,hu.limit,hu.cols,hu.zeroEq,hu.arrays,
        Or.inr ⟨rfl,k,hk,hPast,hEmpty,rfl⟩⟩,?_⟩
      change L-L < L-k
      omega
  obtain ⟨t,rT,ht,hStop⟩ := Run.while_count I pot 20
    (fun u hu => ⟨_,guard u hu⟩) visit hI
  rw [guard t ht] at hStop
  have hEnd : t.vars supportCursor=L :=
    le_antisymm ht.bound (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hStop)))
  have hPot : pot z=L := by change L-z.vars supportCursor=L; rw [hz,Nat.sub_zero]
  have r : Run W findPadReference s t (24*L+6) := by
    apply (rZ.seq rT).mono
    change 2+((1+refGuard.size+20)*pot z+1+refGuard.size) ≤ _
    rw [show refGuard.size=3 from rfl,hPot]
    omega
  refine ⟨t,r,Frame.of_run r,ht.arrays,?_⟩
  rcases ht.examined with he | hw
  · rw [hEnd] at he
    exact Or.inl he
  · exact Or.inr hw.2

/-- The fixed record can name the first supported address before execution. -/
theorem existsFirstChartEntry {L zero : ℕ} (chart : List ℕ)
    (active : ∃ k : Fin L, chart.getD k.val 0 ≠ zero) :
    ∃ first : Fin L, chart.getD first.val 0 ≠ zero ∧ ∀ j < first.val, chart.getD j 0 = zero := by
  classical
  let good : ℕ → Prop := fun k => k < L ∧ chart.getD k 0 ≠ zero
  have found : ∃ k, good k := by
    obtain ⟨i,hi⟩ := active
    exact ⟨i.val,i.isLt,hi⟩
  let k := Nat.find found
  have hk : good k := Nat.find_spec found
  refine ⟨⟨k,hk.1⟩,hk.2,?_⟩
  intro j hj
  by_contra hne
  exact Nat.find_min found hj ⟨hj.trans hk.1,hne⟩

#print axioms existsFirstChartEntry
#print axioms findPadReference_first_run
end EvenTI.P21ScalarScan
