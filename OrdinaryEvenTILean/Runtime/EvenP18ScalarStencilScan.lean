import EvenP18ScalarStencil

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 12000

namespace EvenTI.P18Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare (coordinateBank)
open EvenTI.P17Scalar (activeSlotBank activeWordLimit activeReferenceSlot
  activeWordAnswer checkActiveResidueWords checkActiveResidueWords_run)

def checkInstalledChartResidues : Com :=
  .seq installActiveStencil
    (.seq (.assign activeWordLimit (.var stencilLimit))
      (.seq (.assign activeReferenceSlot (.var stencilReference)) checkActiveResidueWords))

/-- The whole installed-chart scalar test constructs the actual stencil
and reads the actual recovered residue bank. Its bit enforces the site-word
equality at every nonzero chart entry, with a single linear clock. -/
theorem checkInstalledChartResidues_run
    {W L columns zero reference : ℕ} {s : Env} (chart sites coords : List ℕ)
    (hOne : 1 < W) (hL : L < W) (hColumns : columns < W) (hZero : zero < W)
    (hChartFit : L ≤ chart.length)
    (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : (s.arrs activeSlotBank).length=L)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero) (hRef : s.vars stencilReference=reference)
    (hCoords : s.arrs coordinateBank=coords) (hCoordsWord : coords.length < W)
    (hCoordValues : ∀ a ∈ coords, a < W) (hReference : reference < coords.length)
    (hSiteIndices : ∀ k < L, sites.getD (k/columns) 0 < coords.length) :
    ∃ t, Run W checkInstalledChartResidues s t (70*L+70) ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔ ∀ k < L, chart.getD k 0 ≠ zero →
        coords.getD (sites.getD (k/columns) 0) 0=coords.getD reference 0) ∧
      (∀ a, a ≠ activeSlotBank → t.arrs a=s.arrs a) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let slots := (List.range L).map (stencilValue chart sites columns zero reference)
  have hSlotLength : slots.length=L := by simp [slots]
  have hRefWord : reference < W := hReference.trans hCoordsWord
  obtain ⟨u,r0,hOutput,hOther,hIn,hOut,hDone⟩ :=
    installActiveStencil_run chart sites hOne hL hColumns hZero hRefWord hChartFit
      hSiteFit hChartWords hSiteWords hChart hSites hTarget hLimit hCols hZ hRef
  have f0 := Frame.of_run r0
  have huLimit : u.vars stencilLimit=L := (f0.vars _ (by decide)).trans hLimit
  have huRef : u.vars stencilReference=reference := (f0.vars _ (by decide)).trans hRef
  let v := u.setVar activeWordLimit L
  let w := v.setVar activeReferenceSlot reference
  have r1 : Run W (.assign activeWordLimit (.var stencilLimit)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨huLimit.symm,by rw [huLimit]; exact hL⟩)
  have hvRef : v.vars stencilReference=reference := by
    simpa only [v,vars_setVar,show stencilReference ≠ activeWordLimit by decide,if_false] using huRef
  have r2 : Run W (.assign activeReferenceSlot (.var stencilReference)) v w 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hvRef.symm,by rw [hvRef]; exact hRefWord⟩)
  have hwCoords : w.arrs coordinateBank=coords :=
    (hOther coordinateBank (by decide)).trans hCoords
  have hwSlots : w.arrs activeSlotBank=slots := hOutput
  have hwLimit : w.vars activeWordLimit=slots.length := by
    rw [hSlotLength]
    simp [w,v,activeWordLimit,activeReferenceSlot]
  have hwRef : w.vars activeReferenceSlot=reference := by simp [w]
  have hIndices : ∀ a ∈ slots, a < coords.length := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    have hkL : k < L := List.mem_range.mp hk
    by_cases hz : chart.getD k 0=zero
    · simpa only [stencilValue,hz,if_true] using hReference
    · simpa only [stencilValue,hz,if_false] using hSiteIndices k hkL
  obtain ⟨t,r3,hBit,hAnswer,hArrays,hInput,hTape⟩ :=
    checkActiveResidueWords_run coords slots hOne hCoordsWord
      (by rwa [hSlotLength]) hCoordValues hIndices hReference hwCoords hwSlots hwLimit hwRef
  have hAt (k : ℕ) (hk : k < L) : slots.getD k 0=stencilValue chart sites columns zero reference k := by
    rw [List.getD_eq_getElem _ _ (by rwa [hSlotLength])]
    simp only [slots,List.getElem_map,List.getElem_range]
  have hPredicate :
      (∀ j < slots.length, coords.getD (slots.getD j 0) 0=coords.getD reference 0) ↔
      ∀ k < L, chart.getD k 0 ≠ zero →
        coords.getD (sites.getD (k/columns) 0) 0=coords.getD reference 0 := by
    constructor
    · intro h k hk hz
      have hh := h k (by rwa [hSlotLength])
      rw [hAt k hk] at hh
      simpa only [stencilValue,hz,if_false] using hh
    · intro h k hk
      have hkL : k < L := by rwa [hSlotLength] at hk
      rw [hAt k hkL]
      by_cases hz : chart.getD k 0=zero
      · simp only [stencilValue,hz,if_true]
      · simpa only [stencilValue,hz,if_false] using h k hkL hz
  refine ⟨t,(r0.seq (r1.seq (r2.seq r3))).mono ?_,hBit,hAnswer.trans hPredicate,
    ?_,hInput.trans hIn,hTape.trans hOut⟩
  · rw [hSlotLength]
    omega
  · intro a ha
    rw [hArrays]
    exact hOther a ha

#print axioms checkInstalledChartResidues_run
end EvenTI.P18Scalar
