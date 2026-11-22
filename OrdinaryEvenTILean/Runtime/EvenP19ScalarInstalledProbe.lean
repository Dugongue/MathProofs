import EvenP18ScalarInstalledProbe
import EvenP19ScalarPrefixStencilScan
import EvenP18ScalarProbeVisit
import EvenP18ScalarArrayWords

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000

namespace EvenTI.P19Scalar.InstalledProbe

open EvenTI.P18Scalar (runScalarProbeWith runScalarProbeWith_run arrayWords_of_run)
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P19Scalar.PrefixStencilScan (checkInstalledChartResidues checkInstalledChartResidues_run)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

def chartResidueTest {M L n : ℕ} (chart : List ℕ) (zero : ℕ)
    (site : Fin L → Fin n) (reference : Fin n) (x : Fin n → ZMod M) : Bool :=
  decide (∀ k : Fin L, chart.getD k.val 0 ≠ zero →
    (x (site k)).val=(x reference).val)

def runInstalledChartProbe : Com :=
  runScalarProbeWith checkInstalledChartResidues activeWordAnswer

def runInstalledChartProbeCost (M m n L : ℕ) : ℕ :=
  runScalarKernelProbeCost M m n+70*L+76

/-- The complete paid homogeneous prefix probe now recovers actual CRT
coordinates, constructs the installed chart stencil, and evaluates exact
residue equalities in that bank. There is no action-matrix callback premise. -/
theorem runInstalledChartProbe_run
    {M W m n L columns zero : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (chart sites : List ℕ) (site : Fin L → Fin n) (reference : Fin n)
    (hSiteIndex : ∀ k : Fin L, sites.getD (k.val/columns) 0=(site k).val)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCapacity : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length=m+n)
    (hIndex : s.vars probeIndex=i.val) (hValue : s.vars probeValue=a.val)
    (hL : L < W) (hColumns : columns < W) (hZero : zero < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : L ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero) (hRef : s.vars stencilReference=reference.val)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W runInstalledChartProbe s t
      (runInstalledChartProbeCost M m n L) ∧
      Frame runInstalledChartProbe s t ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        chartResidueTest chart zero site reference (selection.getD 0)=true) ∧
      (selection.isSome=true ↔ ∃ x, C.mulVec x=rhs) ∧
      (∀ x, selection=some x → C.mulVec x=rhs) := by
  have hOne : 1 < W := by omega
  let test := chartResidueTest (M:=M) chart zero site reference
  have hIdentity : test 0=true := by simp [test,chartResidueTest]
  have hUse (u : Env) (x : Fin n → ZMod M)
      (r0 : Run W runScalarKernelProbe s u (runScalarKernelProbeCost M m n))
      (f : Frame runScalarKernelProbe s u)
      (hu : RecoveryLayout M m n u) (hc : Canonical M (u.arrs constraintMatrix))
      (ha : u.vars crtActive=1)
      (hx : ∀ j, (u.arrs coordinateBank).getD j.val 0=(x j).val) :
      ∃ v, Run W checkInstalledChartResidues u v (70*L+70) ∧
        v.vars activeWordAnswer ≤ 1 ∧
        (v.vars activeWordAnswer=1 ↔ test x=true) := by
    let coords := u.arrs coordinateBank
    have hCoordsWord : coords.length < W := (f.len coordinateBank).trans_lt hCoordLength
    have hCoordsValues : ∀ v ∈ coords, v < W := arrayWords_of_run r0 coordinateBank hCoordWords
    have hReference : reference.val < coords.length := reference.isLt.trans_le hu.destLen
    have hIndices (k : ℕ) (hk : k < L) :
        sites.getD (k/columns) 0 < coords.length := by
      rw [hSiteIndex ⟨k,hk⟩]
      exact (site ⟨k,hk⟩).isLt.trans_le hu.destLen
    obtain ⟨v,rv,hBit,hVerdict,hOther,hInput,hOutput⟩ :=
      checkInstalledChartResidues_run chart sites coords hOne hL hColumns hZero
        hChartFit hSiteFit hChartWords hSiteWords
        ((f.arrs _ (by decide)).trans hChart)
        ((f.arrs _ (by decide)).trans hSites)
        (by rw [f.len]; exact hTarget)
        ((f.vars _ (by decide)).trans hLimit)
        ((f.vars _ (by decide)).trans hCols)
        ((f.vars _ (by decide)).trans hZ)
        ((f.vars _ (by decide)).trans hRef)
        rfl hCoordsWord hCoordsValues hReference hIndices
    have he :
        (∀ k < L, chart.getD k 0 ≠ zero →
          coords.getD (sites.getD (k/columns) 0) 0=coords.getD reference.val 0) ↔ test x=true := by
      simp only [test,chartResidueTest,decide_eq_true_eq]
      constructor
      · intro h k hk
        have hh := h k.val k.isLt hk
        rw [hSiteIndex k,hx,hx] at hh
        exact hh
      · intro h k hk hz
        rw [hSiteIndex ⟨k,hk⟩,hx,hx]
        exact h ⟨k,hk⟩ hz
    exact ⟨v,rv,hBit,hVerdict.trans he⟩
  obtain ⟨t,selection,hr,hf,hBit,hVerdict,hSome,hSolution⟩ :=
    runScalarProbeWith_run src i a checkInstalledChartResidues activeWordAnswer test hIdentity
      hW hRows hLayoutSize hLayout hSrc hCanonical hCapacity hRhs hIndex hValue hUse
  refine ⟨t,selection,hr.mono ?_,hf,hBit,hVerdict,hSome,hSolution⟩
  unfold runInstalledChartProbeCost
  omega

theorem runInstalledChartProbe_eq : runInstalledChartProbe =
    EvenTI.P18Scalar.runInstalledChartProbe := rfl

#print axioms runInstalledChartProbe_run
end EvenTI.P19Scalar.InstalledProbe
