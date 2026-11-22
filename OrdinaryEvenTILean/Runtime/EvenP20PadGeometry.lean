import Mathlib.LinearAlgebra.Matrix.Bilinear
import EvenP20ScalarNativeCRTMeaning
import EvenP20PadOrderFour
import EvenP16RecoverCrop
import EvenP9RawAffine

set_option autoImplicit false

namespace EvenTI.P20Pad

open EvenTI.Action EvenTI.TrialProducer EvenTI.CellPreparation EvenTI.P16Recover

variable {K : Type} [Field K] [DecidableEq K] {d : ℕ}

theorem orderFourWidth_bounds (ell rho : Coord 2 d → K) (i : Fin (2+2)) :
    d ≤ fourRecoveryWidth ell rho i ∧ fourRecoveryWidth ell rho i ≤ 2*d := by
  rw [fourSiteAmbientWidth_eq,ambientWidth_eq]
  have h := Nat.sub_le d (rawFrameWidth (if (fourSiteOrder i).1 then rho else ell))
  omega

theorem orderFourChartSize_le (ell rho : Coord 2 d → K) (i : Fin (2+2)) (rows : ℕ) :
    rows*(fourRecoveryWidth ell rho i*fourRecoveryWidth ell rho i) ≤ rows*(4*(d*d)) := by
  have h := (orderFourWidth_bounds ell rho i).2
  calc
    _ ≤ rows*((2*d)*(2*d)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h h)
    _ = _ := by ring

#print axioms orderFourWidth_bounds
#print axioms orderFourChartSize_le
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 18000

namespace EvenTI.P20Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open EvenTI.CellPreparation EvenTI.PrimaryAlignment EvenTI.P16Recover
open Mathproof.EvenTI.GlobalCoverage

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

/-- The numeric source-frame crop is the left inverse of the exact
padding used by the registered order-four trial. -/
theorem targetCropNumeric_sourcePad_left (ell rho : Coord 2 n → K) (i : Fin (2+2)) :
    targetCropNumeric ell rho ell rho rfl rfl i * sourcePadNumeric ell rho i=1 := by
  unfold targetCropNumeric sourcePadNumeric
  rw [fourTargetOrder_self]
  change (fourCrop ell rho (fourSiteOrder i)).submatrix id (fourNumericOrder ell rho i) *
    (fourPad ell rho (fourSiteOrder i)).submatrix (fourNumericOrder ell rho i) id = 1
  rw [Matrix.submatrix_mul_equiv,fourCrop_left,Matrix.submatrix_id_id]

/-- Exact numeric intertwining of a homogeneous action from the old
padded form and the cropped action. Full retained rank supplies
support invariance, via the checked, representation-independent theorem. -/
theorem numericPad_invariant (ell rho : Coord 2 n → K) (G : FourNumericUnits ell rho)
    (T : Tensor K 4 n) (hRank : rawRetainedFullRank (l:=3) T=true)
    (hG : wordAction (fun i => (G i).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (i : Fin (2+2)) :
    (G i).val * sourcePadNumeric ell rho i =
      sourcePadNumeric ell rho i * (targetCropNumeric ell rho ell rho rfl rfl i *
        (G i).val * sourcePadNumeric ell rho i) := by
  let a := fourNumericOrder ell rho
  let P := fourPad ell rho
  let Q := fourCrop ell rho
  let A := reindexWords fourSiteOrder.symm (fun _ => Equiv.refl (Fin n)) T
  let N := relabelRectangular fourSiteOrder a a G
  let j := fourSiteOrder i
  have hP : rectGridAction N (rectGridAction P A)=rectGridAction P A := by
    rw [←words_rect ell rho T]
    exact relabelRectangular_action fourSiteOrder a a G _ _ hG
  have hFull (W : ModeMatrices K (fun _ : FourSite => Fin n))
      (he : wordAction W A=A) (j : FourSite) : IsUnit (W j) := by
    have hu := retainedRank_target_wordAction_isUnit T hRank
      (fun j => W (fourSiteOrder j)) T
      (wordAction_unpermute_sites fourSiteOrder.symm W T T he) (fourSiteOrder.symm j)
    exact (congrArg (fun k : FourSite => IsUnit (W k)) (fourSiteOrder.apply_symm_apply j)) ▸ hu
  have hSup : N j * P j=P j*(Q j*N j*P j) :=
    padding_support_of_full_target P P Q N (fourCrop_left ell rho) A A hP hFull j
  have hAt := congrArg (fun U => U.submatrix (a i) id) hSup
  rw [←Matrix.submatrix_mul_equiv (N j) (P j) (a i) (a i) id,
    ←Matrix.submatrix_mul_equiv (P j) (Q j*N j*P j) (a i) (Equiv.refl (Fin n)) id] at hAt
  have hN : (N j).submatrix (a i) (a i)=(G i).val := by
    ext r s
    simp only [N,j,relabelRectangular,Equiv.piCongr_apply_apply,Matrix.reindex_apply,
      Matrix.submatrix_apply,Equiv.symm_apply_apply]
  have hSmall : Q j*N j*P j = targetCropNumeric ell rho ell rho rfl rfl i *
      (G i).val * sourcePadNumeric ell rho i := by
    apply Eq.trans _ (recoverFourMatrices_numeric ell rho ell rho rfl rfl G i)
    change Q j*N j*P j = Q j *
      relabelRectangular fourSiteOrder a (fourTargetOrder ell rho ell rho rfl rfl) G j * P j
    rw [fourTargetOrder_self]
  rw [hN,hSmall] at hAt
  exact hAt

#print axioms targetCropNumeric_sourcePad_left
#print axioms numericPad_invariant
end EvenTI.P20Pad

set_option autoImplicit false

namespace EvenTI.P20Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.Part8
open EvenTI.CellPreparation EvenTI.P16Recover EvenTI.P20Scalar
open EvenOrdinaryTI.LiveRows
open Lax13Proofs.Imp
open EvenTI.P17Scalar (activeWordAnswer)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Read the actual order-four CRT verdict as scalarity of its native
source crop. The shared signed-label normalization can be positive or
inverse, and none labels the fixed block. -/
theorem orderFourNativeAnswer_iff_crop {n rows labels joints degree : ℕ}
    (ell rho : Coord 2 n → K) (i : Fin (2+2))
    (G : FourNumericUnits ell rho) (T : Tensor K 4 n)
    (hRank : rawRetainedFullRank (l:=3) T=true)
    (hG : wordAction (fun i => (G i).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (X : Fin rows → Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)
    (L : BaseUnitLog K) (rowKey : Fin rows → Option (Fin labels)) (negative : Bool)
    (z : Fin (VarCount (labels*2+1) (joints+labels+1) (degree+2)) → ZMod (Fintype.card K-1))
    (reference : Fin rows) (u : Env)
    (hRef : X reference*sourcePadNumeric ell rho i≠0)
    (hSpan : (1 : Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K) ∈
      Submodule.span K (Set.range X))
    (hEigen : ∀ r, X r*(G i).val=(L.decode
      (if negative then -(z (nativeSourcePhysicalSlot joints degree (rowKey r)) -
          z (nativePinPhysicalSlot labels joints degree))
        else z (nativeSourcePhysicalSlot joints degree (rowKey r)) -
          z (nativePinPhysicalSlot labels joints degree)) : K) • X r)
    (hAnswer : u.vars activeWordAnswer=1 ↔
      ∀ r, X r*sourcePadNumeric ell rho i≠0 →
        (z (nativeSourcePhysicalSlot joints degree (rowKey r))).val=
          (z (nativeSourcePhysicalSlot joints degree (rowKey reference))).val) :
    u.vars activeWordAnswer=1 ↔
      ∃ a : K, recoverFourMatrices ell rho ell rho rfl rfl G i=a • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [recoverFourMatrices_numeric ell rho ell rho rfl rfl G i]
  exact hAnswer.trans (scalarCrop_iff_nativePositiveWords
    (sourcePadNumeric ell rho i) (targetCropNumeric ell rho ell rho rfl rfl i)
    (G i).val X L rowKey negative z reference hRef
    (targetCropNumeric_sourcePad_left ell rho i) (numericPad_invariant ell rho G T hRank hG i)
    hSpan hEigen).symm

#print axioms orderFourNativeAnswer_iff_crop
end EvenTI.P20Pad


namespace EvenTI.P20Pad

open scoped Matrix

/-- A full row frame of any nonempty original space contains a row
surviving the rectangular pad. This justifies a first-active reference. -/
theorem exists_activePadRow {K : Type} [Field K] {I : Type} {p r : ℕ} (hp : 0 < p)
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (X : I → Matrix (Fin r) (Fin r) K)
    (hLeft : Q*P=1)
    (hSpan : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X)) :
    ∃ a, X a*P ≠ 0 := by
  classical
  by_contra! hn
  let f := mulRightLinearMap (Fin r) K P
  have hKer : Submodule.span K (Set.range X) ≤ f.ker := Submodule.span_le.mpr (by
    rintro _ ⟨a,rfl⟩
    exact LinearMap.mem_ker.mpr (hn a))
  have hOne := LinearMap.mem_ker.mp (hKer hSpan)
  change (1 : Matrix (Fin r) (Fin r) K)*P=0 at hOne
  have h0 : P=0 := by simpa only [Matrix.one_mul] using hOne
  have hh : (0 : Matrix (Fin p) (Fin p) K) =1 := by
    rw [h0,Matrix.mul_zero] at hLeft
    exact hLeft
  let j : Fin p := ⟨0,hp⟩
  have h := congrArg (fun A : Matrix (Fin p) (Fin p) K => A j j) hh
  simpa only [Matrix.zero_apply,Matrix.one_apply_eq,zero_ne_one] using h

#print axioms exists_activePadRow
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 18000

namespace EvenTI.P20Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_div)
open EvenTI.P19Scalar.PrefixStencil

def supportCursor : String := "even.scalar.pad.reference.cursor"

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

def findPadReference : Com :=
  .seq (.assign supportCursor (.lit 0)) (.while refGuard refVisit)

private structure RefState (s u : Env) (L columns zero : ℕ) : Prop where
  bound : u.vars supportCursor ≤ L
  limit : u.vars stencilLimit=L
  cols : u.vars stencilColumns=columns
  zeroEq : u.vars stencilZero=zero
  arrays : u.arrs=s.arrs
  examined : (∀ k < u.vars supportCursor, (s.arrs stencilChartBank).getD k 0=zero) ∨
    (u.vars supportCursor=L ∧ ∃ k < L, (s.arrs stencilChartBank).getD k 0≠zero ∧
      u.vars stencilReference=(s.arrs stencilSitesBank).getD (k/columns) 0)

/-- Choose a supported reference index from the physical masked chart.
The scan preserves all banks and stops as soon as it sees a nonzero label. -/
theorem findPadReference_run {W L columns zero : ℕ} {s : Env}
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
        ∃ k < L, (s.arrs stencilChartBank).getD k 0≠zero ∧
          t.vars stencilReference=(s.arrs stencilSitesBank).getD (k/columns) 0) := by
  let z := s.setVar supportCursor 0
  let I (u : Env) := RefState s u L columns zero
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
      refine ⟨t,rr,⟨by change L≤L; exact le_rfl,hu.limit,hu.cols,hu.zeroEq,hu.arrays,
        Or.inr ⟨rfl,k,hk,hEmpty,rfl⟩⟩,?_⟩
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

#print axioms findPadReference_run
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 18000

namespace EvenTI.P20Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P19Scalar.PrefixStencil EvenTI.P19Scalar.InstalledProbe
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)

def runAutoMaskedChartProbe (right : Bool) : Com :=
  .seq (applyPaddingMask right) (.seq findPadReference runInstalledChartProbe)

def runAutoMaskedChartProbeCost (M m n L : ℕ) : ℕ :=
  (38*L+6)+((24*L+6)+runInstalledChartProbeCost M m n L)

private theorem refWrites : scalarWrites findPadReference={supportCursor,stencilReference} := by
  decide

private theorem maskWrites (right : Bool) : scalarWrites (applyPaddingMask right)={maskCursor} := by
  cases right <;> decide

private theorem maskBankWrites (right : Bool) :
    arrayWrites (applyPaddingMask right)={stencilChartBank} := by
  cases right <;> decide

/-- Execute exactly one physical padding mask, choose one of its supported
entries as the common reference, and verify the actual CRT probe result.
A compatible nonzero retained coefficient suffices to initialize the reference. -/
theorem runAutoMaskedChartProbe_run (right : Bool)
    {M W m n L columns width cutoff zero : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (chart sites : List ℕ) (site : Fin L → Fin n)
    (hSiteIndex : ∀ k : Fin L, sites.getD (k.val/columns) 0=(site k).val)
    (hActive : ∃ k : Fin L, columnKept right cutoff (k.val%width)=true ∧ chart.getD k.val 0≠zero)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCapacity : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length=m+n)
    (hIndex : s.vars probeIndex=i.val) (hValue : s.vars probeValue=a.val)
    (hL : L < W) (hColumns : columns < W) (hZero : zero < W)
    (hWidth : width < W) (hCutoff : cutoff < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : L ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero)
    (hWidthVar : s.vars maskWidth=width) (hCutoffVar : s.vars maskCutoff=cutoff)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ (t : Env) (selection : Option (Fin n → ZMod M)) (k : Fin L), Run W (runAutoMaskedChartProbe right) s t
      (runAutoMaskedChartProbeCost M m n L) ∧ Frame (runAutoMaskedChartProbe right) s t ∧
      columnKept right cutoff (k.val%width)=true ∧ chart.getD k.val 0≠zero ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        maskedResidueTest right width cutoff chart zero site (site k) (selection.getD 0)=true) ∧
      (selection.isSome=true ↔ ∃ x, C.mulVec x=rhs) ∧
      (∀ x, selection=some x → C.mulVec x=rhs) := by
  dsimp only
  have hOne : 1 < W := by omega
  obtain ⟨u,ru,fu,hMask,_,hMaskedWords,_,_,_⟩ :=
    applyPaddingMask_run right hOne hL hWidth hCutoff hZero
      (by rw [hChart]; exact hChartFit) (by rw [hChart]; exact hChartWords)
      hLimit hWidthVar hCutoffVar hZ
  have regU (r : String) (h : r≠maskCursor) : u.vars r=s.vars r :=
    fu.vars r (by rw [maskWrites]; simpa using h)
  have arrU (r : String) (h : r≠stencilChartBank) : u.arrs r=s.arrs r :=
    fu.arrs r (by rw [maskBankWrites]; simpa using h)
  let masked := u.arrs stencilChartBank
  have hFit : L ≤ masked.length := by
    change L≤(u.arrs stencilChartBank).length
    rw [fu.len,hChart]
    exact hChartFit
  have hSiteBank : u.arrs stencilSitesBank=sites := (arrU _ (by decide)).trans hSites
  have active (j : Fin L) : masked.getD j.val 0≠zero ↔
      columnKept right cutoff (j.val%width)=true ∧ chart.getD j.val 0≠zero := by
    change (u.arrs stencilChartBank).getD j.val 0≠zero ↔ _
    rw [hMask j.val j.isLt,hChart]
    cases hc : columnKept right cutoff (j.val%width) <;> simp [maskedWord,hc]
  obtain ⟨v,rr,fr,hSame,hSelected⟩ :=
    findPadReference_run hOne hL hColumns hZero ((regU _ (by decide)).trans hLimit)
      ((regU _ (by decide)).trans hCols) ((regU _ (by decide)).trans hZ) hFit hMaskedWords
      (by rw [hSiteBank]; exact hSiteFit) (by rw [hSiteBank]; exact hSiteWords)
  obtain ⟨idx,hi,hNZ,hRefWord⟩ : ∃ j < L, masked.getD j 0≠zero ∧
      v.vars stencilReference=(u.arrs stencilSitesBank).getD (j/columns) 0 := by
    rcases hSelected with hAll | h
    · obtain ⟨k,hk⟩ := hActive
      exact False.elim (((active k).mpr hk) (hAll k.val k.isLt))
    · exact h
  let k : Fin L := ⟨idx,hi⟩
  have hKept := (active k).mp hNZ
  have hRef : v.vars stencilReference=(site k).val := by
    rw [hRefWord,hSiteBank]
    exact hSiteIndex k
  have reg (r : String) (h : r≠maskCursor) (h' : r≠supportCursor) (h'' : r≠stencilReference) :
      v.vars r=s.vars r :=
    (fr.vars r (by rw [refWrites]; simp [h',h''])).trans (regU r h)
  have arr (r : String) (h : r≠stencilChartBank) : v.arrs r=s.arrs r :=
    (congrFun hSame r).trans (arrU r h)
  have lens (r : String) : (v.arrs r).length=(s.arrs r).length :=
    (fr.len r).trans (fu.len r)
  have hLayoutV : RecoveryLayout M m n v := by
    exact ⟨(reg _ (by decide) (by decide) (by decide)).trans hLayout.rows,
      (reg _ (by decide) (by decide) (by decide)).trans hLayout.cols,
      (reg _ (by decide) (by decide) (by decide)).trans hLayout.modWord,
      (reg _ (by decide) (by decide) (by decide)).trans hLayout.base,
      by rw [arr _ (by decide)]; exact hLayout.sourceLen,
      by rw [arr _ (by decide)]; exact hLayout.workLen,
      by rw [arr _ (by decide)]; exact hLayout.workCanon,
      by rw [arr _ (by decide)]; exact hLayout.coLen,
      by rw [arr _ (by decide)]; exact hLayout.tgLen,
      by rw [arr _ (by decide)]; exact hLayout.modLen,
      by rw [arr _ (by decide)]; exact hLayout.destLen⟩
  obtain ⟨t,selection,rt,_,hBit,hVerdict,hSome,hSol⟩ :=
    runInstalledChartProbe_run src i a masked sites site (site k) hSiteIndex hW hRows hLayoutSize
      hLayoutV (hSrc.congr_env (arr _ (by decide))) (by rw [arr _ (by decide)]; exact hCanonical)
      (by rw [lens]; exact hCapacity) (by rw [lens]; exact hRhs)
      ((reg _ (by decide) (by decide) (by decide)).trans hIndex)
      ((reg _ (by decide) (by decide) (by decide)).trans hValue)
      hL hColumns hZero hFit hSiteFit hMaskedWords hSiteWords
      (congrFun hSame _) ((arr _ (by decide)).trans hSites) (by rw [lens]; exact hTarget)
      ((reg _ (by decide) (by decide) (by decide)).trans hLimit)
      ((reg _ (by decide) (by decide) (by decide)).trans hCols)
      ((reg _ (by decide) (by decide) (by decide)).trans hZ) hRef
      (by rw [lens]; exact hCoordLength) (by rw [arr _ (by decide)]; exact hCoordWords)
  have hTest (x : Fin n → ZMod M) :
      chartResidueTest masked zero site (site k) x=true ↔
      maskedResidueTest right width cutoff chart zero site (site k) x=true := by
    simp only [chartResidueTest,maskedResidueTest,decide_eq_true_eq]
    exact ⟨fun h j hc hz => h j ((active j).mpr ⟨hc,hz⟩),
      fun h j ha => h j ((active j).mp ha).1 ((active j).mp ha).2⟩
  have r := ru.seq (rr.seq rt)
  exact ⟨t,selection,k,r,Frame.of_run r,hKept.1,hKept.2,hBit,
    hVerdict.trans (hTest _),hSome,hSol⟩

#print axioms runAutoMaskedChartProbe_run
end EvenTI.P20Pad
