import EvenP22PadAssembly
import EvenP21PadInverseCall
import Mathproof.Meta.Problem18IMPSlotsMemory20261001

set_option autoImplicit false
set_option maxRecDepth 26000
set_option maxHeartbeats 1500000

namespace EvenTI.P22Pad

open scoped BigOperators
open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.P20Sweep
open EvenTI.P15Execution EvenTI.P15Scalar EvenTI.P21Pad
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open EvenTI.P19Scalar.PrefixStencil (stencilChartBank)
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def invertArchivedFrame (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) : Com :=
  .seq (installArchivedFrame F)
    (.seq Mathproof.Problem18IMPSlotsMemory20261001.program (invertAndExportFrame D F lower))

noncomputable def invertArchivedFrameCost (F : FieldPresentation K) (n m : ℕ) : ℕ :=
  installArchivedFrameCost F n m+
    (3+(63+loadedInverseCost (Fintype.card K) F.e n+installScalarLabelsCost F (n*n)))

private noncomputable def inverseSample : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem installArchivePreservesInverseRegisters (F : FieldPresentation K) :
    ∀ r ∈ [inverseSizeWord,inverseInputWord,inverseOutputWord,qN.WS,canonical.modBase],
      r ∉ scalarWrites (installArchivedFrame F) := by
  change ∀ r ∈ [inverseSizeWord,inverseInputWord,inverseOutputWord,qN.WS,canonical.modBase],
    r ∉ scalarWrites (installArchivedFrame inverseSample)
  decide

/-- The raw primary archive supplies the source matrix, its inverse is
computed by the actual field call, and the inverse labels are written to
the chart consumed by the padding probe. -/
theorem invertArchivedFrame_run (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) {B S n off base lane src input Z a : ℕ} {s : Env}
    (A : Matrix (Fin n) (Fin n) K) (L : List (Polynomial K))
    (hL : (L : Multiset (Polynomial K))=(normalizedFactors A.charpoly).dedup)
    (hArchive : ∀ i < L.length,
      SavedChart F A (factorAt A L i) (off+i) (rowBasis base lane (off+i))
        (rowChart base lane (off+i)) s)
    (hs : Slots F canonical qN.WS S B s)
    (p : ArchivePorts s n off L.length base (2*lane) src Z)
    (hSize : s.vars inverseSizeWord=n) (hInput : s.vars inverseInputWord=input)
    (hOutput : s.vars inverseOutputWord=a)
    (hOrigin : s.vars qN.WS=F.e+1) (hMod : s.vars canonical.modBase=0)
    (hMem : (s.arrs canonical.mem).length=F.e+1+S*F.e)
    (hPositive : 0 < n) (hn : n+1 < B) (hm : L.length < B)
    (hi : ∀ i < L.length, off+i < B) (hStride : 2*lane < B)
    (hBefore : ∀ i < L.length, rowBasis base lane (off+i)+n*n ≤ src)
    (hApart : src+n*n ≤ input) (hFits : input+n*n ≤ Z)
    (hZ : Z+4 ≤ S) (hB : S+10 < B)
    (hInvApart : input+n*n ≤ a) (hInvFit : a+4*(n*n)+3 ≤ S)
    (hExp : Fintype.card K^(n*n+n+2) < B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hChart : n*n ≤ (s.arrs stencilChartBank).length)
    (hChartW : (s.arrs stencilChartBank).length < B) :
    ∃ (t : Env) (width : Fin L.length → ℕ)
      (C : ∀ i : Fin L.length, Matrix (Fin n) (Fin (width i)) K)
      (hSum : (∑ i, width i)=n) (U : (Matrix (Fin n) (Fin n) K)ˣ),
      Run B (invertArchivedFrame D F lower) s t (invertArchivedFrameCost F n L.length) ∧
      Slots F canonical qN.WS S B t ∧ U.val=concatenateFrame C hSum ∧
      (∀ r c, (t.arrs stencilChartBank).getD (inverseAddress r c) 0=(D (U.inv r c)).val) ∧
      (∀ i, (C i).mulVecLin.range=
        ((Polynomial.aeval A (factorAt A L i.val)).mulVecLin).ker) ∧
      Frame (invertArchivedFrame D F lower) s t := by
  obtain ⟨u,width,C,hSum,r₀,hu,hUnit,hLiteral,_,_,hRange,_,fu⟩ :=
    installArchivedFrame_run F A L hL hArchive hs p hInput hn hm hi hStride hBefore
      hApart hFits hZ hB hz ho
  have hKeep (r : String) (hr : r ∈ [inverseSizeWord,inverseInputWord,inverseOutputWord,
      qN.WS,canonical.modBase]) : u.vars r=s.vars r :=
    fu.vars r (installArchivePreservesInverseRegisters F r hr)
  have uWS : u.vars qN.WS=F.e+1 := (hKeep _ (by decide)).trans hOrigin
  have uMod : u.vars canonical.modBase=0 := (hKeep _ (by decide)).trans hMod
  obtain ⟨v,r₁,hv,hSlots,hVal,hRegs,_,_⟩ :=
    Mathproof.Problem18IMPSlotsMemory20261001.reset_run F hu uMod uWS ((fu.len _).trans hMem)
  let U := hUnit.unit
  have hU : U.val=concatenateFrame C hSum := hUnit.unit_spec
  have hFitInput : input+n*n ≤ S := by omega
  have hAt (r c : Fin n) : val F canonical qN.WS v (input+inverseAddress r c)=U.val r c := by
    have ha := inverseAddress_lt r c
    rw [hVal _ (by omega),hLiteral,hU]
  have vs : v.vars inverseSizeWord=n := (hRegs _).trans ((hKeep _ (by decide)).trans hSize)
  have vi : v.vars inverseInputWord=input := (hRegs _).trans ((hKeep _ (by decide)).trans hInput)
  have va : v.vars inverseOutputWord=a := (hRegs _).trans ((hKeep _ (by decide)).trans hOutput)
  have fieldFits : v.vars canonical.modBase+F.e ≤ v.vars qN.WS := by
    rw [hRegs canonical.modBase,hRegs qN.WS,uMod,uWS]
    omega
  have vLen : (v.arrs stencilChartBank).length=(s.arrs stencilChartBank).length :=
    ((Frame.of_run r₁).len _).trans (fu.len _)
  obtain ⟨t,r₂,ht,hLabels,_⟩ := invertAndExportFrame_run D F lower U hPositive (by omega)
    hInvApart hInvFit hv hSlots vs vi va fieldFits hExp hAt hQ hP
    (by rwa [vLen]) (by rwa [vLen])
  have rr : Run B (invertArchivedFrame D F lower) s t (invertArchivedFrameCost F n L.length) :=
    r₀.seq (r₁.seq r₂)
  exact ⟨t,width,C,hSum,U,rr,ht,hU,hLabels,hRange,Frame.of_run rr⟩

#print axioms invertArchivedFrame_run
end EvenTI.P22Pad

