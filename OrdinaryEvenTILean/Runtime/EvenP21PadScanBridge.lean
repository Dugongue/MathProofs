import EvenP21PadNamed
import EvenP21ScalarOccurrence
import EvenP20SweepArchive
import EvenP6AlignSourceChart
import EvenP21PadPrepare

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 18000

namespace EvenTI.P21Pad

open scoped BigOperators Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover
open EvenTI.P20Pad EvenTI.P20Scalar EvenTI.P21Scalar EvenTI.Part8 EvenOrdinaryTI.LiveRows

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable (h : ∀ p, ModeLayout (m p))
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance selectedLaws (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance selectedModel (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "S" => (∑ p, CodeWidth w m p)
local notation "keyOf" => (commonKey w.mode (branchIsFree w m))

/-- The machine's selected-reference word comparison is precisely
scalarity of the original order-four crop. The occurrence equation is
the base-unit decoding already furnished by the signed CRT branch. -/
theorem orderFour_cropScalar_iff_selectedWords {t d : ℕ}
    (hw : ∀ p, (m p).n=w.width p) (U : SiteUnits w m)
    (L : BaseUnitLog K) (x : BranchAssignment w m)
    (z : Fin (VarCount (S*2+1) (t+S+1) (d+2)) → ZMod (Fintype.card K-1))
    (i : Fin (w.sites+2))
    (hBase : ∀ v, branchOccurrenceUnits w m x i v =
      baseUnit (L.decode (occurrenceExponent (K:=K) z (keyOf i v) (w.minus i))))
    {n : ℕ} (ell rho : Coord 2 n → K) (j : Fin (2+2))
    (G : FourNumericUnits ell rho) (T : Tensor K 4 n)
    (hRank : rawRetainedFullRank (l:=3) T=true)
    (hAction : wordAction (fun j => (G j).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (hwSite : w.width (w.mode i)=fourRecoveryWidth ell rho j)
    (hUnit : G j=transportMatrixUnit (finCongr hwSite) (recoverTrialSites w m h hw U U x i))
    (reference : Fin (CodeWidth w m (w.mode i)))
    (hRef : inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j)
      ((physicalNativeOrder w m h hw i).trans (finCongr hwSite))
      (transportMatrixUnit (finCongr hwSite) (physicalSourceChartUnit w m hw U i)).inv reference) :
    (∃ c : K, recoverFourMatrices ell rho ell rho rfl rfl G j=c • 1) ↔
      ∀ v, inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j)
        ((physicalNativeOrder w m h hw i).trans (finCongr hwSite))
        (transportMatrixUnit (finCongr hwSite) (physicalSourceChartUnit w m hw U i)).inv v →
        (z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t d i v)).val=
          (z (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t d i reference)).val := by
  let supported := inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j)
    ((physicalNativeOrder w m h hw i).trans (finCongr hwSite))
    (transportMatrixUnit (finCongr hwSite) (physicalSourceChartUnit w m hw U i)).inv
  let slot := sharedBlockPhysicalSlot w.mode (branchIsFree w m) t d i
  let cAt (v : Fin (CodeWidth w m (w.mode i))) : K :=
    (L.decode (occurrenceExponent (K:=K) z (keyOf i v) (w.minus i)) : K)
  letI : NeZero (Fintype.card K-1) := ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩
  have hAlgebra := exists_congr (fun c =>
    orderFour_cropScalar_iff_recoveredMode w m h hw U x i ell rho j G T
      hRank hAction hwSite hUnit c)
  have localScalar (c : K) (v : Fin (CodeWidth w m (w.mode i))) :
      (branchOccurrenceUnits w m x i v).val=c • (1 : CodeField w m (w.mode i) v) ↔
        cAt v=c := by
    rw [hBase v]
    change algebraMap K (CodeField w m (w.mode i) v) (cAt v)=c • 1 ↔ _
    rw [←Algebra.algebraMap_eq_smul_one c]
    exact (algebraMap K (CodeField w m (w.mode i) v)).injective.eq_iff
  have equal (v u : Fin (CodeWidth w m (w.mode i))) : cAt v=cAt u ↔
      z (slot v)=z (slot u) :=
    (show Function.Injective (fun a : ZMod (Fintype.card K-1) => (L.decode a : K))
      from fun _ _ he => congrArg Multiplicative.toAdd (L.mulEquiv.injective (Units.ext he))).eq_iff.trans
      (occurrenceExponent_eq_iff (K:=K) z (keyOf i v) (keyOf i u) (w.minus i))
  apply hAlgebra.trans
  change (∃ c : K, ∀ v, supported v →
      (branchOccurrenceUnits w m x i v).val=c • (1 : CodeField w m (w.mode i) v)) ↔
    ∀ v, supported v → (z (slot v)).val=(z (slot reference)).val
  constructor
  · rintro ⟨c,hc⟩ v hv
    exact congrArg ZMod.val ((equal v reference).mp
      (((localScalar c v).mp (hc v hv)).trans ((localScalar c reference).mp (hc reference hRef)).symm))
  · intro he
    exact ⟨cAt reference,fun v hv => (localScalar _ _).mpr
      ((equal _ _).mpr (ZMod.val_injective _ (he v hv)))⟩

#print axioms orderFour_cropScalar_iff_selectedWords
end EvenTI.P21Pad

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 18000

namespace EvenTI.P21Pad

open scoped Polynomial
open Matrix EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.PrimaryProducer EvenTI.P20Sweep
open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem columnRange_cast {n u v : ℕ} (C : Matrix (Fin n) (Fin u) K)
    (e : Fin u ≃ Fin v) : (C.submatrix id e.symm).mulVecLin.range=C.mulVecLin.range := by
  have h (x : Fin v → K) : (C.submatrix id e.symm).mulVec x=C.mulVec (x ∘ e) := by
    simpa only [Equiv.symm_symm,Function.comp_id] using
      Matrix.submatrix_mulVec_equiv C x id e.symm
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y ∘ e,(h y).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨y ∘ e.symm,?_⟩
    change (C.submatrix id e.symm).mulVec (y ∘ e.symm)=C.mulVec y
    rw [h]
    simp [Function.comp_def]

/-- The archive's physically computed vectors span the same primary
space as the reference source chart. The archive can use an arbitrary
echelon basis; its columns do not have to reproduce the Krylov gauge. -/
theorem archivedChart_referenceSpan
    (D : FieldEncoding K) (F : FieldPresentation K) (budget : ℕ)
    (A B : NumberedAnchor K) (m : PreparedMode K)
    (hm : prepareAnchorPair D budget A B=some m) :
    ∃ (hn : m.n=A.width) (hc : m.blocks.length=(anchorFactors D A.matrix).length),
      ∀ (i : Fin m.blocks.length) (row outX outR : ℕ) (s : Env),
        SavedChart F A.matrix (livePower D A.matrix (finCongr hc i)) row outX outR s →
        ∃ (w : ℕ) (xs : Fin w → Fin A.width → K), w≤A.width ∧
          (s.arrs savedWidths)[row]?=some w ∧ LinearIndependent K xs ∧
          (∀ j k, val F canonical qN.WS s (outX+(j.val*A.width+k.val))=xs j k) ∧
          Submodule.span K (Set.range xs)=
            ((m.blocks.get i).sourceColumns.submatrix (finCongr hn).symm id).mulVecLin.range := by
  obtain ⟨hn,hc,hCharts⟩ := prepareAnchorPair_sourceCharts D budget A B m hm
  refine ⟨hn,hc,?_⟩
  intro i row outX outR s hSaved
  obtain ⟨w,xs,hw,hSize,hInd,hSpan,hWords,_⟩ := hSaved
  obtain ⟨hb,hBasis⟩ := hCharts i
  let j := finCongr hc i
  let C := (m.blocks.get i).sourceColumns.submatrix (finCongr hn).symm id
  have hColumns : C.submatrix id (finCongr hb).symm =
      (livePrimaryBlock D A.matrix j).columns*liveCanonicalGauge D A.matrix j := by
    dsimp only [C]
    rw [Matrix.submatrix_submatrix]
    simpa only [C,j,Function.comp_id,Function.id_comp] using hBasis
  have hRange :
      C.mulVecLin.range=((Polynomial.aeval A.matrix (livePower D A.matrix j)).mulVecLin).ker := by
    rw [←columnRange_cast C (finCongr hb),hColumns,
      inclusion_rightUnit_range _ _ (liveCanonicalGauge_isUnit D A.matrix j)]
    exact inclusion_range A.matrix (liveFactor D A.matrix j).1 (liveFactor D A.matrix j).2
  exact ⟨w,xs,hw,hSize,hInd,hWords,hSpan.trans hRange.symm⟩

#print axioms archivedChart_referenceSpan
end EvenTI.P21Pad

set_option autoImplicit false

namespace EvenTI.P21Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad

/-- The mask/reference producer preserves all chart capacity beyond the
live prefix. This holds for the same concrete run used by its consumer. -/
theorem prepareMaskedProbeStorage_tail_of_run (right : Bool)
    {W L width cutoff zero budget : ℕ} {s t : Env}
    (hRun : Run W (prepareMaskedProbeStorage right) s t budget)
    (hOne : 1 < W) (hL : L < W) (hWidth : width < W) (hCut : cutoff < W) (hZero : zero < W)
    (hFit : L ≤ (s.arrs stencilChartBank).length)
    (hWords : ∀ a ∈ s.arrs stencilChartBank, a < W)
    (hLimit : s.vars stencilLimit=L) (hWidthWord : s.vars maskWidth=width)
    (hCutWord : s.vars maskCutoff=cutoff) (hZ : s.vars stencilZero=zero)
    (j : ℕ) (hj : L ≤ j) :
    (t.arrs stencilChartBank).getD j 0=(s.arrs stencilChartBank).getD j 0 := by
  obtain ⟨u,⟨_,_,hMask⟩,_,_,hTail,_,_,_,_⟩ :=
    applyPaddingMask_run right hOne hL hWidth hCut hZero hFit hWords hLimit hWidthWord hCutWord hZ
  obtain ⟨clock,_,hWhole⟩ := hRun
  change BigStepB W (.seq (applyPaddingMask right) findPadReference) s t clock at hWhole
  cases hWhole with
  | seq h₁ h₂ =>
    have hMid := (hMask.bigStep.unique h₁.bigStep).1
    rw [(Frame.of_bigStepB h₂).arrs stencilChartBank (by decide),←hMid]
    exact hTail j hj

#print axioms prepareMaskedProbeStorage_tail_of_run
end EvenTI.P21Pad
