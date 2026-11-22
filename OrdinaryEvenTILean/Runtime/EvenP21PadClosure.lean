import EvenP21PadSite
import EvenP19ScalarLiveChart

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace EvenTI.P21Pad

open scoped Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Action EvenTI.Contract EvenTI.CellPreparation EvenTI.P16Recover
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem17Primary46ModePadding (start stop)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The existing bounded label exporter can read the actual inverse-gauge
square directly, with a literal row-major address and no projector product. -/
theorem materializeInverseGaugeLabels_run (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) {W S a w : ℕ} {s : Env} (V : Matrix (Fin w) (Fin w) K)
    (hSlots : Slots F canonical qN.WS S W s)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W) (hOne : 1 < W)
    (hStart : s.vars (start lower)=a) (hStop : s.vars (stop lower)=a+w*w)
    (hRead : a+w*w ≤ S) (hTarget : w*w ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < W)
    (hInverse : ∀ r c, val F canonical qN.WS s (a+inverseAddress r c)=V r c) :
    ∃ t, Run W (EvenTI.P19Scalar.LiveChart.materializeSweptChart D F lower) s t
        (8+installScalarLabelsCost F (w*w)) ∧
      Slots F canonical qN.WS S W t ∧
      (∀ r c, (t.arrs stencilChartBank).getD (inverseAddress r c) 0=(D (V r c)).val) ∧
      (∀ b, b≠stencilChartBank → t.arrs b=s.arrs b) ∧ t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,r,hs,hChart,_,_,hArr,hInp,hOut⟩ :=
    EvenTI.P19Scalar.LiveChart.materializeSweptChart_run D F lower hSlots hQ hP hOne
      hStart hStop hRead hTarget hWord
  refine ⟨t,r,hs,?_,hArr,hInp,hOut⟩
  intro i j
  change (t.arrs EvenTI.P18Scalar.stencilChartBank).getD (inverseAddress i j) 0=(D (V i j)).val
  rw [hChart _ (inverseAddress_lt i j),hInverse]

/-- The existing physical P20 mask and reference search, specialized to
the live inverse source gauge. The fixed/pinned and free slot table may be
installed separately; its exact row-to-origin meaning is used here. -/
theorem runInverseSupportProbe_run (D : FieldEncoding K)
    {d blocks rows M W m n : ℕ} [NeZero M] {s : Env}
    {C : Fin blocks → Type}
    (ell rho : Coord 2 d → K) (j : Fin (2+2)) (hd : 0 < d)
    (U : (Matrix (Fin (fourRecoveryWidth ell rho j)) (Fin (fourRecoveryWidth ell rho j)) K)ˣ)
    (e : (Σ v, C v) ≃ Fin (fourRecoveryWidth ell rho j))
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (chart sites : List ℕ) (site : Fin blocks → Fin n)
    (hSite : ∀ r : Fin (fourRecoveryWidth ell rho j), sites.getD r.val 0=(site (e.symm r).1).val)
    (hChartMeaning : ∀ r c, chart.getD (inverseAddress r c) 0=(D (U.inv r c)).val)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCapacity : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length=m+n)
    (hIndex : s.vars probeIndex=i.val) (hValue : s.vars probeValue=a.val)
    (hWidth : fourRecoveryWidth ell rho j < W)
    (hCut : siteCutoff ell rho j < W)
    (hL : fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j < W)
    (hZero : (D 0).val < W)
    (hChartFit : fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j ≤ chart.length)
    (hSiteFit : fourRecoveryWidth ell rho j ≤ sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j)
    (hCols : s.vars stencilColumns=fourRecoveryWidth ell rho j)
    (hZ : s.vars stencilZero=(D 0).val)
    (hWidthWord : s.vars maskWidth=fourRecoveryWidth ell rho j)
    (hCutWord : s.vars maskCutoff=siteCutoff ell rho j)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let B := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ t selection v, Run W (runAutoMaskedChartProbe (fourSiteOrder j).2) s t
      (runAutoMaskedChartProbeCost M m n (fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j)) ∧
      Frame (runAutoMaskedChartProbe (fourSiteOrder j).2) s t ∧
      inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j) e U.inv v ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        ∀ u, inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j) e U.inv u →
          ((selection.getD 0) (site u)).val=((selection.getD 0) (site v)).val) ∧
      (selection.isSome=true ↔ ∃ x, B.mulVec x=rhs) ∧
      (∀ x, selection=some x → B.mulVec x=rhs) := by
  dsimp only
  let w := fourRecoveryWidth ell rho j
  let side := (fourSiteOrder j).2
  let cut := siteCutoff ell rho j
  have hw : 0 < w := hd.trans_le (orderFourWidth_bounds ell rho j).1
  let sitesAt := inverseBankSite hw e site
  have hFit (k : ℕ) (hk : k < w*w) : k/w < sites.length :=
    ((Nat.div_lt_iff_lt_mul hw).mpr hk).trans_le hSiteFit
  have hActive : ∃ k : Fin (w*w), columnKept side cut (k.val%w)=true ∧
      chart.getD k.val 0≠(D 0).val := by
    obtain ⟨r,c,hKeep,hNZ⟩ := exists_supportedInverseEntry ell rho j hd U
    let k : Fin (w*w) := ⟨inverseAddress r c,inverseAddress_lt r c⟩
    refine ⟨k,?_,?_⟩
    · have hRem : k.val%w=c.val := inverseAddress_col r c
      rw [hRem]
      exact hKeep
    · change chart.getD (inverseAddress r c) 0≠_
      rw [hChartMeaning]
      exact fun he => hNZ (D.injective (Fin.ext he))
  obtain ⟨t,selection,k,hr,hFrame,hKeep,hNZ,hBit,hTest,hSome,hSol⟩ :=
    runAutoMaskedChartProbe_run side src i a chart sites sitesAt
      (inverseBankSite_words hw e site sites hSite) hActive hW hRows hLayoutSize hLayout
      hSrc hCanonical hCapacity hRhs hIndex hValue hL hWidth hZero hWidth hCut hChartFit hFit
      hChartWords hSiteWords hChart hSites hTarget hLimit hCols hZ hWidthWord hCutWord
      hCoordLength hCoordWords
  let r := inverseRow hw k
  let c := inverseCol hw k
  let v := (e.symm r).1
  have hEntry : U.inv r c≠0 := by
    intro he
    apply hNZ
    rw [←inverseAddress_indices hw k,hChartMeaning]
    exact congrArg (fun x => (D x).val) he
  have hSupported : inverseBlockSupported side cut e U.inv v :=
    ⟨(e.symm r).2,c,hKeep,by simpa only [v,Sigma.eta,Equiv.apply_symm_apply] using hEntry⟩
  refine ⟨t,selection,v,hr,hFrame,hSupported,hBit,?_,hSome,hSol⟩
  have h := inverseBankMask_test hw D side cut e U.inv chart site (site v)
    (selection.getD 0) hChartMeaning
  exact hTest.trans h

#print axioms materializeInverseGaugeLabels_run
#print axioms runInverseSupportProbe_run
end EvenTI.P21Pad

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 24000

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover
open EvenTI.P20Pad

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section NativeCoordinates

variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p))
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance nativeWordLaws (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance nativeField (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

def physicalNativeOrder (hw : ∀ p, (m p).n=w.width p) (i : Fin (w.sites+2)) :
    (Σ v : Fin (CodeWidth w m (w.mode i)), numberedCoordinate (m (w.mode i)) v) ≃ Fin (w.width (w.mode i)) :=
  (numberedModeSlots (m (w.mode i)) (h (w.mode i))).trans (finCongr (hw (w.mode i)))

def physicalSourceChartUnit (hw : ∀ p, (m p).n=w.width p)
    (U : SiteUnits w m) (i : Fin (w.sites+2)) :
    (Matrix (Fin (w.width (w.mode i))) (Fin (w.width (w.mode i))) K)ˣ :=
  transportMatrixUnit (finCongr (hw (w.mode i))) (U i)

/-- This is the literal conjugation performed by homogeneous recovery.
The slot order is the old numbered native order followed by its actual width cast. -/
theorem recoverTrialSites_nativeConjugate
    (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m)
    (x : BranchAssignment w m) (i : Fin (w.sites+2)) :
    let V := physicalSourceChartUnit w m hw U i
    let e := physicalNativeOrder w m h hw i
    let B := liveActionMatrix (branchTables w m) (branchDecode w m) i
      (fun v => (branchOccurrenceUnits w m x i v).val)
    (recoverTrialSites w m h hw U U x i).val=V.val*B.submatrix e.symm e.symm*V.inv := by
  dsimp only
  let f := finCongr (hw (w.mode i))
  let R := Units.map (Matrix.reindexAlgEquiv K K f).toMonoidHom
  have hm : transportMatrixUnit f (U i * recoveredChartUnits w m h x i * (U i)⁻¹) =
        transportMatrixUnit f (U i) * transportMatrixUnit f (recoveredChartUnits w m h x i) *
          (transportMatrixUnit f (U i))⁻¹ := by
    change R (U i * recoveredChartUnits w m h x i * (U i)⁻¹) =
      R (U i) * R (recoveredChartUnits w m h x i) * (R (U i))⁻¹
    simp only [map_mul,map_inv]
  unfold recoverTrialSites
  change (transportMatrixUnit f _).val=_
  rw [hm]
  simp only [Units.val_mul]
  have hc : (transportMatrixUnit f (recoveredChartUnits w m h x i)).val =
      (liveActionMatrix (branchTables w m) (branchDecode w m) i
        (fun v => (branchOccurrenceUnits w m x i v).val)).submatrix
          (physicalNativeOrder w m h hw i).symm (physicalNativeOrder w m h hw i).symm := by
    ext r s
    rw [transportMatrixUnit_apply]
    unfold recoveredChartUnits
    rw [transportMatrixUnit_apply] <;> rfl
  rw [hc] <;> rfl

end NativeCoordinates

#print axioms recoverTrialSites_nativeConjugate
end EvenTI.P21Pad
