import EvenP20PadMask
import EvenP16RecoverCrop
import EvenP19ScalarInstalledProbe
import EvenP19ScalarFrameMeaning
import Mathproof.Meta.Problem18IMPMatrixMemory20261001

set_option autoImplicit false
set_option maxHeartbeats 780000
set_option maxRecDepth 18000

namespace EvenTI.P20Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open EvenTI.CellPreparation EvenTI.PrimaryAlignment EvenTI.P16Recover
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

def retainedCutoff (right : Bool) (a k : ℕ) : ℕ := if right then k else k+a

private theorem normalLeftVal {a k : ℕ} (right : Bool) (i : Fin a) :
    (enlargedOrder a k (normalEmbed right (Sum.inl i))).val=k+i.val := rfl

private theorem normalRightVal {a k : ℕ} (right : Bool) (i : Fin k) :
    (enlargedOrder a k (normalEmbed right (Sum.inr i))).val=
      if right then k+(a+i.val) else i.val := by
  cases right <;> rfl

/-- The columns retained by native order-four embedding form the prefix
[k,a] for the false side and the suffix [a,k] for the true side. -/
theorem columnKept_iff_normalEmbed {a k : ℕ} (right : Bool) (j : Fin (k+(a+k))) :
    columnKept right (retainedCutoff right a k) j.val=true ↔
      ∃ u : Fin a ⊕ Fin k, enlargedOrder a k (normalEmbed right u)=j := by
  cases right with
  | false =>
    simp only [columnKept,retainedCutoff,Bool.false_eq_true,if_false,decide_eq_true_eq]
    constructor
    · intro hj
      by_cases h : j.val < k
      · refine ⟨.inr ⟨j.val,h⟩,Fin.ext ?_⟩
        simp only [normalRightVal,Bool.false_eq_true,if_false]
      · have h' : j.val-k < a := by omega
        refine ⟨.inl ⟨j.val-k,h'⟩,Fin.ext ?_⟩
        rw [normalLeftVal]
        change k+(j.val-k)=j.val
        omega
    · rintro ⟨u,rfl⟩
      cases u with
      | inl i =>
        rw [normalLeftVal]
        have := i.isLt
        omega
      | inr i =>
        simp only [normalRightVal,Bool.false_eq_true,if_false]
        have := i.isLt
        omega
  | true =>
    simp only [columnKept,retainedCutoff,if_true,decide_eq_true_eq]
    constructor
    · intro hj
      by_cases h : j.val < k+a
      · have h' : j.val-k < a := by omega
        refine ⟨.inl ⟨j.val-k,h'⟩,Fin.ext ?_⟩
        rw [normalLeftVal]
        change k+(j.val-k)=j.val
        omega
      · have h' : j.val-(k+a) < k := by have := j.isLt; omega
        refine ⟨.inr ⟨j.val-(k+a),h'⟩,Fin.ext ?_⟩
        rw [normalRightVal,if_pos rfl]
        change k+(a+(j.val-(k+a)))=j.val
        omega
    · rintro ⟨u,rfl⟩
      cases u with
      | inl i => rw [normalLeftVal]; omega
      | inr i => rw [normalRightVal,if_pos rfl]; omega

variable {K : Type} [Field K] [DecidableEq K] {n a k : ℕ}

def numericPad {ell : Coord 2 n → K} (F : NormalPair ell a k) (right : Bool) :
    Matrix (Fin (k+(a+k))) (Fin n) K :=
  fun i j => paddedMode F right ((enlargedOrder a k).symm i) j

def numberedEmbedding {ell : Coord 2 n → K} (F : NormalPair ell a k) (right : Bool) :
    Fin n → Fin (k+(a+k)) :=
  fun j => enlargedOrder a k (normalEmbed right (F.indices j))

private def numberedInjection {ell : Coord 2 n → K} (F : NormalPair ell a k) (right : Bool) :
    Matrix (Fin (k+(a+k))) (Fin n) K :=
  fun i j => if i=numberedEmbedding F right j then 1 else 0

theorem numericPad_mul_unit {ell : Coord 2 n → K} (F : NormalPair ell a k) (right : Bool) :
    numericPad F right = numberedInjection F right * (frameModeUnit F right).val := by
  ext i j
  unfold numericPad paddedMode
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  change (if (enlargedOrder a k).symm i=normalEmbed right (F.indices c) then (1:K) else 0)*
      (frameModeUnit F right).val c j =
    (if i=numberedEmbedding F right c then (1:K) else 0)*(frameModeUnit F right).val c j
  by_cases h : i=numberedEmbedding F right c
  · have h' : (enlargedOrder a k).symm i=normalEmbed right (F.indices c) := by
      simp only [h,numberedEmbedding,Equiv.symm_apply_apply]
    simp only [if_pos h,if_pos h']
  · have h' : (enlargedOrder a k).symm i≠normalEmbed right (F.indices c) := by
      intro eq
      apply h
      simpa only [Equiv.apply_symm_apply,numberedEmbedding] using congrArg (enlargedOrder a k) eq
    simp only [if_neg h,if_neg h']

private theorem numericInjection_product {ell : Coord 2 n → K} (F : NormalPair ell a k)
    (right : Bool) {r : ℕ} (X : Matrix (Fin r) (Fin (k+(a+k))) K) :
    X * numberedInjection F right = X.submatrix id (numberedEmbedding F right) := by
  ext i j
  simp [Matrix.mul_apply,numberedInjection,Matrix.submatrix_apply,mul_ite]

/-- A chart row is active exactly when at least one retained numeric
column has a nonzero coefficient. The normal-frame unit is invertible. -/
theorem mul_numericPad_ne_zero_iff {ell : Coord 2 n → K} (F : NormalPair ell a k)
    (right : Bool) {r : ℕ} (X : Matrix (Fin r) (Fin (k+(a+k))) K) :
    X*numericPad F right≠0 ↔
      ∃ (i : Fin r) (j : Fin (k+(a+k))),
        columnKept right (retainedCutoff right a k) j.val=true ∧ X i j≠0 := by
  have hZero : X*numericPad F right=0 ↔ X.submatrix id (numberedEmbedding F right)=0 := by
    rw [numericPad_mul_unit,←Matrix.mul_assoc,numericInjection_product]
    constructor
    · intro h
      have hh := congrArg (fun M => M*(frameModeUnit F right).inv) h
      rw [Matrix.mul_assoc,(frameModeUnit F right).val_inv,Matrix.mul_one,Matrix.zero_mul] at hh
      exact hh
    · intro h
      rw [h,Matrix.zero_mul]
  rw [ne_eq,hZero]
  constructor
  · intro h
    by_contra! h'
    apply h
    ext i j
    exact h' i (numberedEmbedding F right j)
      ((columnKept_iff_normalEmbed right _).mpr ⟨F.indices j,rfl⟩)
  · rintro ⟨i,j,hKeep,hNonzero⟩ h
    obtain ⟨u,hu⟩ := (columnKept_iff_normalEmbed right j).mp hKeep
    have hin : numberedEmbedding F right (F.indices.symm u)=j := by
      simpa [numberedEmbedding] using hu
    have hAt := congrFun (congrFun h i) (F.indices.symm u)
    exact hNonzero (by simpa only [Matrix.submatrix_apply,id_eq,hin,Matrix.zero_apply] using hAt)

def siteRank (ell rho : Coord 2 n → K) (i : Fin (2+2)) : ℕ :=
  rawFrameWidth (if (fourSiteOrder i).1 then rho else ell)

def siteCutoff (ell rho : Coord 2 n → K) (i : Fin (2+2)) : ℕ :=
  retainedCutoff (fourSiteOrder i).2 (siteRank ell rho i) (n-siteRank ell rho i)

theorem sourcePadNumeric_nonzero_iff (ell rho : Coord 2 n → K) (i : Fin (2+2)) {r : ℕ}
    (X : Matrix (Fin r) (Fin (fourRecoveryWidth ell rho i)) K) :
    X * sourcePadNumeric ell rho i≠0 ↔
      ∃ (u : Fin r) (v : Fin (fourRecoveryWidth ell rho i)),
        columnKept (fourSiteOrder i).2 (siteCutoff ell rho i) v.val=true ∧ X u v≠0 := by
  fin_cases i
  · exact mul_numericPad_ne_zero_iff (rawNormalFrame ell) false X
  · exact mul_numericPad_ne_zero_iff (rawNormalFrame ell) true X
  · exact mul_numericPad_ne_zero_iff (rawNormalFrame rho) false X
  · exact mul_numericPad_ne_zero_iff (rawNormalFrame rho) true X

#print axioms columnKept_iff_normalEmbed
#print axioms mul_numericPad_ne_zero_iff
#print axioms sourcePadNumeric_nonzero_iff
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 17000

namespace EvenTI.P20Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P19Scalar.PrefixStencil EvenTI.P19Scalar.InstalledProbe
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)

def maskedResidueTest {M L n : ℕ} (right : Bool) (width cutoff : ℕ) (chart : List ℕ)
    (zero : ℕ) (site : Fin L → Fin n) (reference : Fin n) (x : Fin n → ZMod M) : Bool :=
  decide (∀ j : Fin L, columnKept right cutoff (j.val%width)=true →
    chart.getD j.val 0≠zero → (x (site j)).val=(x reference).val)

def runMaskedChartProbe (right : Bool) : Com :=
  .seq (applyPaddingMask right) runInstalledChartProbe

def runMaskedChartProbeCost (M m n L : ℕ) : ℕ :=
  (38*L+6)+runInstalledChartProbeCost M m n L

private theorem maskScalar (right : Bool) : scalarWrites (applyPaddingMask right)={maskCursor} := by
  cases right <;> decide

private theorem maskArrays (right : Bool) : arrayWrites (applyPaddingMask right)={stencilChartBank} := by
  cases right <;> decide

private theorem maskKeepsLayout {M m n : ℕ} {s t : Env}
    (h : RecoveryLayout M m n s)
    (hKeep : ∀ r, r≠maskCursor → t.vars r=s.vars r)
    (hArr : ∀ a, a≠stencilChartBank → t.arrs a=s.arrs a) : RecoveryLayout M m n t := by
  exact ⟨(hKeep _ (by decide)).trans h.rows,(hKeep _ (by decide)).trans h.cols,
    (hKeep _ (by decide)).trans h.modWord,(hKeep _ (by decide)).trans h.base,
    by rw [hArr _ (by decide)]; exact h.sourceLen,
    by rw [hArr _ (by decide)]; exact h.workLen,
    by rw [hArr _ (by decide)]; exact h.workCanon,
    by rw [hArr _ (by decide)]; exact h.coLen,
    by rw [hArr _ (by decide)]; exact h.tgLen,
    by rw [hArr _ (by decide)]; exact h.modLen,
    by rw [hArr _ (by decide)]; exact h.destLen⟩

/-- The padding mask feeds the existing physical stencil and CRT probe.
The returned bit covers exactly those nonzero entries in retained
physical columns; the CRT representative and its certificate are shared. -/
theorem runMaskedChartProbe_run (right : Bool)
    {M W m n L columns width cutoff zero : ℕ} [NeZero M] {s : Env}
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
    (hWidth : width < W) (hCutoff : cutoff < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : L ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero) (hRef : s.vars stencilReference=reference.val)
    (hWidthVar : s.vars maskWidth=width) (hCutoffVar : s.vars maskCutoff=cutoff)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W (runMaskedChartProbe right) s t
      (runMaskedChartProbeCost M m n L) ∧ Frame (runMaskedChartProbe right) s t ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        maskedResidueTest right width cutoff chart zero site reference (selection.getD 0)=true) ∧
      (selection.isSome=true ↔ ∃ x, C.mulVec x=rhs) ∧
      (∀ x, selection=some x → C.mulVec x=rhs) := by
  dsimp only
  obtain ⟨u,r₀,hFrame,hMask,_,hMaskedWords,_,_,_⟩ :=
    applyPaddingMask_run right (by omega) hL hWidth hCutoff hZero
      (by rw [hChart]; exact hChartFit) (by rw [hChart]; exact hChartWords)
      hLimit hWidthVar hCutoffVar hZ
  have reg (r : String) (hr : r≠maskCursor) : u.vars r=s.vars r :=
    hFrame.vars r (by rw [maskScalar]; simpa using hr)
  have arr (r : String) (hr : r≠stencilChartBank) : u.arrs r=s.arrs r :=
    hFrame.arrs r (by rw [maskArrays]; simpa using hr)
  let masked := u.arrs stencilChartBank
  have hLayoutU := maskKeepsLayout hLayout reg arr
  have hInputU : IncidenceInput u src := hSrc.congr_env (arr _ (by decide))
  have hCanonicalU : Canonical M (u.arrs constraintMatrix) := by
    rw [arr _ (by decide)]
    exact hCanonical
  have hFit : L ≤ masked.length := by
    change L ≤ (u.arrs stencilChartBank).length
    rw [hFrame.len,hChart]
    exact hChartFit
  obtain ⟨t,selection,r₁,_,hBit,hVerdict,hSome,hSol⟩ :=
    runInstalledChartProbe_run src i a masked sites site reference hSiteIndex hW hRows hLayoutSize
      hLayoutU hInputU hCanonicalU (by rw [hFrame.len]; exact hCapacity)
      (by rw [hFrame.len]; exact hRhs)
      ((reg _ (by decide)).trans hIndex) ((reg _ (by decide)).trans hValue)
      hL hColumns hZero hFit hSiteFit hMaskedWords hSiteWords rfl
      ((arr _ (by decide)).trans hSites) (by rw [hFrame.len]; exact hTarget)
      ((reg _ (by decide)).trans hLimit) ((reg _ (by decide)).trans hCols)
      ((reg _ (by decide)).trans hZ) ((reg _ (by decide)).trans hRef)
      (by rw [hFrame.len]; exact hCoordLength) (by rw [arr _ (by decide)]; exact hCoordWords)
  have active (j : Fin L) : masked.getD j.val 0≠zero ↔
      columnKept right cutoff (j.val%width)=true ∧ chart.getD j.val 0≠zero := by
    change (u.arrs stencilChartBank).getD j.val 0≠zero ↔ _
    rw [hMask j.val j.isLt,hChart]
    cases hc : columnKept right cutoff (j.val%width) <;> simp [maskedWord,hc]
  have hTest (x : Fin n → ZMod M) :
      chartResidueTest masked zero site reference x=true ↔
        maskedResidueTest right width cutoff chart zero site reference x=true := by
    simp only [chartResidueTest,maskedResidueTest,decide_eq_true_eq]
    exact ⟨fun h j hc hz => h j ((active j).mpr ⟨hc,hz⟩),
      fun h j ha => h j ((active j).mp ha).1 ((active j).mp ha).2⟩
  have r := r₀.seq r₁
  exact ⟨t,selection,r,Frame.of_run r,hBit,hVerdict.trans (hTest _),hSome,hSol⟩

#print axioms runMaskedChartProbe_run
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 17000

namespace EvenTI.P20Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.Part8 EvenTI.CellPreparation
open EvenTI.PrimaryAlignment EvenTI.P16Recover
open Mathproof.Problem18IMPMatrixMemory20261001 (index_lt)

def chartAddress {rows width : ℕ} (r : Fin rows) (u v : Fin width) : ℕ :=
  r.val*(width*width)+(u.val*width+v.val)

theorem chartAddress_lt {rows width : ℕ} (r : Fin rows) (u v : Fin width) :
    chartAddress r u v < rows*(width*width) :=
  index_lt r (⟨u.val*width+v.val,index_lt u v⟩ : Fin (width*width))

def chartRow {rows width : ℕ} (hw : 0 < width) (j : Fin (rows*(width*width))) : Fin rows :=
  ⟨j.val/(width*width),(Nat.div_lt_iff_lt_mul (Nat.mul_pos hw hw)).mpr j.isLt⟩

def chartSite {rows width sites : ℕ} (hw : 0 < width) (source : Fin rows → Fin sites)
    (j : Fin (rows*(width*width))) : Fin sites := source (chartRow hw j)

theorem chartSite_words {rows width sites : ℕ} (hw : 0 < width) (source : Fin rows → Fin sites)
    (bank : List ℕ) (hBank : ∀ r : Fin rows, bank.getD r.val 0=(source r).val)
    (j : Fin (rows*(width*width))) :
    bank.getD (j.val/(width*width)) 0=(chartSite hw source j).val :=
  hBank (chartRow hw j)

private theorem chartRow_address {rows width : ℕ} (hw : 0 < width) (r : Fin rows) (u v : Fin width) :
    chartRow hw ⟨chartAddress r u v,chartAddress_lt r u v⟩=r := by
  apply Fin.ext
  change (r.val*(width*width)+(u.val*width+v.val))/(width*width)=r.val
  rw [Nat.mul_comm r.val (width*width),Nat.mul_add_div (Nat.mul_pos hw hw),
    Nat.div_eq_of_lt (index_lt u v),Nat.add_zero]

private theorem chartAddress_mod {rows width : ℕ} (r : Fin rows) (u v : Fin width) :
    chartAddress r u v%width=v.val := by
  have h : chartAddress r u v = (r.val*width+u.val)*width+v.val := by unfold chartAddress; ring
  rw [h]
  simp [Nat.add_mod,Nat.mod_eq_of_lt v.isLt]

private theorem chartAddress_decompose {rows width : ℕ} (hw : 0 < width)
    (j : Fin (rows*(width*width))) :
    ∃ u v : Fin width, chartAddress (chartRow hw j) u v=j.val ∧ j.val%width=v.val := by
  let off := j.val%(width*width)
  have hoff : off < width*width := Nat.mod_lt _ (Nat.mul_pos hw hw)
  let u : Fin width := ⟨off/width,(Nat.div_lt_iff_lt_mul hw).mpr hoff⟩
  let v : Fin width := ⟨off%width,Nat.mod_lt _ hw⟩
  have hRem : off/width*width+off%width=off := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod off width
  have hAddr : chartAddress (chartRow hw j) u v=j.val := by
    change j.val/(width*width)*(width*width)+(off/width*width+off%width)=j.val
    rw [hRem]
    simpa only [off,Nat.mul_comm] using Nat.div_add_mod j.val (width*width)
  exact ⟨u,v,hAddr,by rw [←hAddr,chartAddress_mod]⟩

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Apply the literal column mask to a bank containing row-major square
coefficient matrices. The resulting residue predicate ranges over exactly
the rows whose action survives the source padding embedding. -/
theorem orderFourMask_test {d rows c M : ℕ} (D : FieldEncoding K)
    (ell rho : Coord 2 d → K) (i : Fin (2+2))
    (hw : 0 < fourRecoveryWidth ell rho i)
    (X : Fin rows → Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)
    (chart : List ℕ) (rowSite : Fin rows → Fin c) (reference : Fin c)
    (x : Fin c → ZMod M)
    (hChart : ∀ (r : Fin rows) (u v : Fin (fourRecoveryWidth ell rho i)),
      chart.getD (chartAddress r u v) 0=(D (X r u v)).val) :
    maskedResidueTest (fourSiteOrder i).2 (fourRecoveryWidth ell rho i) (siteCutoff ell rho i)
      chart (D 0).val (chartSite hw rowSite) reference x=true ↔
      ∀ r, X r*sourcePadNumeric ell rho i≠0 → (x (rowSite r)).val=(x reference).val := by
  simp only [maskedResidueTest,decide_eq_true_eq]
  constructor
  · intro h r hr
    obtain ⟨u,v,hKeep,hNZ⟩ := (sourcePadNumeric_nonzero_iff ell rho i (X r)).mp hr
    let j := (⟨chartAddress r u v,chartAddress_lt r u v⟩ :
      Fin (rows*(fourRecoveryWidth ell rho i*fourRecoveryWidth ell rho i)))
    have hCol : j.val%(fourRecoveryWidth ell rho i)=v.val := chartAddress_mod r u v
    have hTest : chart.getD j.val 0≠(D 0).val := by
      change chart.getD (chartAddress r u v) 0≠_
      rw [hChart r u v]
      exact fun eq => hNZ (D.injective (Fin.ext eq))
    have hOut := h j (by rw [hCol]; exact hKeep) hTest
    simpa only [chartSite,j,chartRow_address] using hOut
  · intro h j hc hz
    obtain ⟨u,v,hAddr,hCol⟩ := chartAddress_decompose hw j
    have hNZ : X (chartRow hw j) u v≠0 := by
      intro eq
      apply hz
      rw [←hAddr,hChart,eq]
    have active := (sourcePadNumeric_nonzero_iff ell rho i (X (chartRow hw j))).mpr
      ⟨u,v,by rwa [hCol] at hc,hNZ⟩
    exact h (chartRow hw j) active

/-- Consume the verified mask predicate with the supported-frame scalarity
theorem. Source and target crop can be supplied by existing padded layouts. -/
theorem orderFourMask_scalarCrop {d rows c : ℕ} (D : FieldEncoding K)
    (ell rho : Coord 2 d → K) (i : Fin (2+2)) (hw : 0 < fourRecoveryWidth ell rho i)
    (X : Fin rows → Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)
    (Q : Matrix (Fin d) (Fin (fourRecoveryWidth ell rho i)) K)
    (N : Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)
    (L : BaseUnitLog K) (rowSite : Fin rows → Fin c) (reference : Fin rows)
    (x : Fin c → ZMod (Fintype.card K-1)) (chart : List ℕ)
    (hChart : ∀ (r : Fin rows) (u v : Fin (fourRecoveryWidth ell rho i)),
      chart.getD (chartAddress r u v) 0=(D (X r u v)).val)
    (hRef : X reference*sourcePadNumeric ell rho i≠0)
    (hLeft : Q*sourcePadNumeric ell rho i=1)
    (hInvariant : N*sourcePadNumeric ell rho i=
      sourcePadNumeric ell rho i*(Q*N*sourcePadNumeric ell rho i))
    (hSpan : (1 : Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K) ∈
      Submodule.span K (Set.range X))
    (hEigen : ∀ r, X r*N=(L.decode (x (rowSite r)) : K) • X r) :
    maskedResidueTest (fourSiteOrder i).2 (fourRecoveryWidth ell rho i) (siteCutoff ell rho i)
      chart (D 0).val (chartSite hw rowSite) (rowSite reference) x=true ↔
      ∃ a : K, Q*N*sourcePadNumeric ell rho i=a • (1 : Matrix (Fin d) (Fin d) K) :=
  (orderFourMask_test D ell rho i hw X chart rowSite (rowSite reference) x hChart).trans
    (EvenTI.P19Scalar.scalarCrop_iff_supportedFrameWords _ Q N X L rowSite x reference hRef
      hLeft hInvariant hSpan hEigen).symm

#print axioms chartSite_words
#print axioms orderFourMask_test
#print axioms orderFourMask_scalarCrop
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace EvenTI.P20Pad

open EvenTI.Action EvenTI.TrialProducer EvenTI.CellPreparation EvenTI.P16Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

variable {K : Type} [Field K] [DecidableEq K] {n : ℕ}

theorem ambientWidth_eq {ell : Coord 2 n → K} :
    enlargedWidth ell=(n-rawFrameWidth ell)+n := by
  have h := Fintype.card_congr (rawNormalFrame ell).indices
  simp only [Fintype.card_fin,Fintype.card_sum] at h
  unfold enlargedWidth
  rw [←h]

theorem fourSiteAmbientWidth_eq (ell rho : Coord 2 n → K) (i : Fin (2+2)) :
    fourRecoveryWidth ell rho i=enlargedWidth (if (fourSiteOrder i).1 then rho else ell) := by
  change (if finTwoEquiv (finTwoEquiv.symm (fourSiteOrder i).1) then enlargedWidth rho else enlargedWidth ell)=_
  rw [Equiv.apply_symm_apply]
  cases h : (fourSiteOrder i).1 <;> simp [h]

/-- Native padding thresholds can be read from the original and padded
widths, without rerunning any frame/rank computation. -/
theorem siteCutoff_from_width (ell rho : Coord 2 n → K) (i : Fin (2+2)) :
    siteCutoff ell rho i=if (fourSiteOrder i).2 then fourRecoveryWidth ell rho i-n else n := by
  let p := if (fourSiteOrder i).1 then rho else ell
  let a := rawFrameWidth p
  let k := n-a
  have h := Fintype.card_congr (rawNormalFrame p).indices
  simp only [Fintype.card_fin,Fintype.card_sum] at h
  have hRank : a+k=n := h.symm
  have hWidth : fourRecoveryWidth ell rho i=k+n :=
    (fourSiteAmbientWidth_eq ell rho i).trans ambientWidth_eq
  change retainedCutoff (fourSiteOrder i).2 a k=_
  rw [hWidth]
  cases hSide : (fourSiteOrder i).2
  · change k+a=n
    omega
  · change k=k+n-n
    omega

def originalWidthWord : String := "even.scalar.pad.original-width"
def ambientWidthWord : String := "even.scalar.pad.ambient-width"

private def cutoffExpr (right : Bool) : Expr :=
  if right then .sub (.var ambientWidthWord) (.var originalWidthWord) else .var originalWidthWord

def installPaddingWidths (right : Bool) : Com :=
  .seq (.assign maskWidth (.var ambientWidthWord)) (.assign maskCutoff (cutoffExpr right))

/-- Physically load the two mask controls from the widths already in
the caller. All unrelated chart, incidence, site and coordinate storage survives. -/
theorem installPaddingWidths_run (right : Bool) {B n w : ℕ} {s : Env}
    (hOrig : s.vars originalWidthWord=n) (hAmbient : s.vars ambientWidthWord=w)
    (hN : n < B) (hW : w < B) :
    ∃ t, Run B (installPaddingWidths right) s t 6 ∧
      t.vars maskWidth=w ∧ t.vars maskCutoff=(if right then w-n else n) ∧
      (∀ r, r≠maskWidth → r≠maskCutoff → t.vars r=s.vars r) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  let u := s.setVar maskWidth w
  let t := u.setVar maskCutoff (if right then w-n else n)
  have r₀ : Run B (.assign maskWidth (.var ambientWidthWord)) s u 2 :=
    Run.assign (ev_var hAmbient hW)
  have eu : (Expr.var originalWidthWord).evalB B u=some n :=
    ev_var (show u.vars originalWidthWord=n from hOrig) hN
  have ew : (Expr.var ambientWidthWord).evalB B u=some w :=
    ev_var (show u.vars ambientWidthWord=w from hAmbient) hW
  have r₁ : Run B (.assign maskCutoff (cutoffExpr right)) u t 4 := by
    cases right
    · exact (Run.assign eu).mono (by decide)
    · exact Run.assign (evalB_bin (op:=.sub) ew eu ((Nat.sub_le _ _).trans_lt hW))
  refine ⟨t,r₀.seq r₁,rfl,rfl,?_,rfl,rfl,rfl⟩
  intro r hr₁ hr₂
  simp only [t,u,vars_setVar,if_neg hr₁,if_neg hr₂]

#print axioms siteCutoff_from_width
#print axioms installPaddingWidths_run
end EvenTI.P20Pad

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace EvenTI.P20Pad

open scoped Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Action EvenTI.Contract EvenTI.Part8 EvenTI.CellPreparation EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.P16Recover
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

def orderFourSiteProbe (j : Fin (2+2)) : Com :=
  .seq (installPaddingWidths (fourSiteOrder j).2) (runMaskedChartProbe (fourSiteOrder j).2)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Initialize the order-four padding controls and run the physical CRT
test. The returned bit concerns exactly the chart rows surviving the native
rectangular source pad. -/
theorem orderFourSiteProbe_run (D : FieldEncoding K)
    {d rows M W m n : ℕ} [NeZero M] {s : Env}
    (ell rho : Coord 2 d → K) (j : Fin (2+2))
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (X : Fin rows → Matrix (Fin (fourRecoveryWidth ell rho j)) (Fin (fourRecoveryWidth ell rho j)) K)
    (chart sites : List ℕ) (rowSite : Fin rows → Fin n) (reference : Fin n)
    (hWidth : 0 < fourRecoveryWidth ell rho j)
    (hSiteIndex : ∀ r : Fin rows, sites.getD r.val 0=(rowSite r).val)
    (hChartMeaning : ∀ (r : Fin rows) (u v : Fin (fourRecoveryWidth ell rho j)),
      chart.getD (chartAddress r u v) 0=(D (X r u v)).val)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCapacity : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length=m+n)
    (hIndex : s.vars probeIndex=i.val) (hValue : s.vars probeValue=a.val)
    (hOrig : d < W) (hAmbient : fourRecoveryWidth ell rho j < W)
    (hOrigWord : s.vars originalWidthWord=d)
    (hAmbientWord : s.vars ambientWidthWord=fourRecoveryWidth ell rho j)
    (hL : rows*(fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j) < W)
    (hColumns : fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j < W)
    (hZero : (D 0).val < W)
    (hChartFit : rows*(fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j) ≤ chart.length)
    (hSiteFit : rows ≤ sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : rows*(fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j) ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=rows*(fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j))
    (hCols : s.vars stencilColumns=fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j)
    (hZ : s.vars stencilZero=(D 0).val) (hRef : s.vars stencilReference=reference.val)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W (orderFourSiteProbe j) s t
      (6+runMaskedChartProbeCost M m n (rows*(fourRecoveryWidth ell rho j*fourRecoveryWidth ell rho j))) ∧
      Frame (orderFourSiteProbe j) s t ∧ t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        ∀ r, X r * sourcePadNumeric ell rho j≠0 →
          ((selection.getD 0) (rowSite r)).val=((selection.getD 0) reference).val) ∧
      (selection.isSome=true ↔ ∃ x, C.mulVec x=rhs) ∧
      (∀ x, selection=some x → C.mulVec x=rhs) := by
  dsimp only
  let side := (fourSiteOrder j).2
  let width := fourRecoveryWidth ell rho j
  let cols := width*width
  let count := rows*cols
  have hExact : siteCutoff ell rho j=(if side then width-d else d) :=
    siteCutoff_from_width ell rho j
  have hCutoff : siteCutoff ell rho j < W := by
    rw [hExact]
    by_cases hSide : side=true
    · rw [if_pos hSide]
      exact (Nat.sub_le _ _).trans_lt hAmbient
    · rw [if_neg hSide]
      exact hOrig
  obtain ⟨u,r₀,hWidthWord,hCutoffWord,hReg,hArr,_,_⟩ :=
    installPaddingWidths_run side hOrigWord hAmbientWord hOrig hAmbient
  have hKeep (r : String) (hr : r≠maskWidth) (hc : r≠maskCutoff) :
      u.vars r=s.vars r := hReg r hr hc
  have hLayoutU : RecoveryLayout M m n u := by
    exact ⟨(hKeep _ (by decide) (by decide)).trans hLayout.rows,
      (hKeep _ (by decide) (by decide)).trans hLayout.cols,
      (hKeep _ (by decide) (by decide)).trans hLayout.modWord,
      (hKeep _ (by decide) (by decide)).trans hLayout.base,
      by rw [hArr]; exact hLayout.sourceLen,
      by rw [hArr]; exact hLayout.workLen,
      by rw [hArr]; exact hLayout.workCanon,
      by rw [hArr]; exact hLayout.coLen,
      by rw [hArr]; exact hLayout.tgLen,
      by rw [hArr]; exact hLayout.modLen,
      by rw [hArr]; exact hLayout.destLen⟩
  have hInputU : IncidenceInput u src := hSrc.congr_env (congrFun hArr _)
  have hSitesFit (k : ℕ) (hk : k < count) : k/cols < sites.length :=
    ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hWidth hWidth)).mpr hk).trans_le hSiteFit
  obtain ⟨t,selection,r₁,_,hBit,hVerdict,hSome,hSol⟩ :=
    runMaskedChartProbe_run side src i a chart sites (chartSite hWidth rowSite) reference
      (chartSite_words hWidth rowSite sites hSiteIndex) hW hRows hLayoutSize
      hLayoutU hInputU (by rw [hArr]; exact hCanonical) (by rw [hArr]; exact hCapacity)
      (by rw [hArr]; exact hRhs)
      ((hKeep _ (by decide) (by decide)).trans hIndex)
      ((hKeep _ (by decide) (by decide)).trans hValue)
      hL hColumns hZero hAmbient hCutoff hChartFit hSitesFit hChartWords hSiteWords
      ((congrFun hArr _).trans hChart) ((congrFun hArr _).trans hSites)
      (by rw [hArr]; exact hTarget)
      ((hKeep _ (by decide) (by decide)).trans hLimit)
      ((hKeep _ (by decide) (by decide)).trans hCols)
      ((hKeep _ (by decide) (by decide)).trans hZ)
      ((hKeep _ (by decide) (by decide)).trans hRef)
      hWidthWord (hCutoffWord.trans hExact.symm)
      (by rw [hArr]; exact hCoordLength) (by rw [hArr]; exact hCoordWords)
  have r := r₀.seq r₁
  exact ⟨t,selection,r,Frame.of_run r,hBit,
    hVerdict.trans (orderFourMask_test D ell rho j hWidth X chart rowSite reference _ hChartMeaning),
    hSome,hSol⟩

#print axioms orderFourSiteProbe_run
end EvenTI.P20Pad
