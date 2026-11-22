import EvenP12ComparePrepKernel

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPRowKer20261007 (rkCost)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs kK)
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def runOneCut (D : FieldEncoding K) (F : FieldPresentation K)
    (left target : Bool) (idx : Fin 4) : Com :=
  .seq (oneCutSetup D F target idx)
    (if left then comparisonLeftKernel D F rawPairIO.array
     else comparisonRightKernel D F rawPairIO.array)

noncomputable def selectedKernel {a n : Nat} (left : Bool) (T : Tensor K (a+a) n) :
    Submodule K (Coord a n → K) :=
  if left then (leftCutKernel T).ker else (flatten T).mulVecLin.ker

/-- A cut run returns its real row-major bank with a complete basis and the
computed nullity. Separate output bank numbers can be allocated to all four cuts. -/
theorem runOneCut_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n B : Nat} (T S : Tensor K (a+a) n) (left target : Bool) (idx : Fin 4) {σ : Env}
    (hn : 0 < n) (hm : σ.vars shapePower.out = n^a)
    (hBank : σ.arrs rawPairIO.array = comparisonInput D T S)
    (hS : Slots F canonical qN.WS (pairCutSlotCount.value (n^a)) B σ)
    (hWS : σ.vars qN.WS = F.e+1)
    (hFits : ∀ v ∈ kernelBindings target idx, v.2.value (n^a) < B)
    (hCard : Fintype.card K ≤ B) (hB : 1 < B)
    (hMemory : pairCutSlotCount.value (n^a)+(n^a)+(n^a)+10 < B)
    (hInput : (comparisonInput D T S).length < B)
    (hz : val F canonical qN.WS σ (constantsBase.value (n^a)) = 0) :
    let m := n^a
    let cost := (((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+
      installEncodedDigitCost F+encodedBankLoadCost F
       (if left then transposeAddress else contiguousAddress) (n^(a+a))+rkCost F m m
    ∃ τ, Run B (runOneCut D F left target idx) σ τ cost ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars kK = Module.finrank K (selectedKernel left (if target then S else T)) ∧
      (∃ xs : Fin (τ.vars kK) → Coord a n → K, LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = selectedKernel left (if target then S else T) ∧
          ∀ i j, val F canonical qN.WS τ ((outputBase idx).value m+
              (i.val*m+(inputCoordOrder n a j).val)) = xs i j) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let m := n^a
  have hPos : 0 < m := pow_pos hn _
  have lay := concreteKernelLayout m idx hPos hMemory
  have hO : constantsBase.value m+1 < pairCutSlotCount.value m := by have := lay.z_s; omega
  obtain ⟨r,hr,hR,hWS',hRegs,hZ,hOne,hArr,hIn,hOut⟩ :=
    oneCutSetup_run D F target idx m hm hPos hS hWS hFits hCard hO hz
  have hMem : rawPairIO.array ≠ canonical.mem := by decide
  have hRaw : r.arrs rawPairIO.array = comparisonInput D T S :=
    (hArr _ hMem).trans hBank
  have hSquare : m*m = n^(a+a) := (pow_add ..).symm
  have hOffset : tensorOffset (n^(a+a)) target+n^(a+a) < B := by
    have hLen : (comparisonInput D T S).length = 2+n^(a+a)+n^(a+a) := by
      simp [comparisonInput,tensorWords_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hLen] at hInput
    cases target <;> simp [tensorOffset] <;> omega
  have hLoad := hRegs.hLength.trans hSquare
  have hInBase : r.vars inputBase = tensorOffset (n^(a+a)) target := by
    rw [← hSquare]
    exact hRegs.hInpBase
  have hBase : (m+1)*XBs m m ≤ rawMatrixBase.value m := by
    simp [rawMatrixBase,Address.value,rowKernelBlock_value]
  have hAm : rawMatrixBase.value m+n^(a+a) ≤ augmentedMatrixBase.value m := by
    rw [← hSquare]
    simp [augmentedMatrixBase,Address.value,cutArea_value]
  cases left
  · obtain ⟨τ,rr,hRun,hNull,hBasis,hi,ho⟩ := comparisonRightKernel_run D F T S target
      rawPairIO.array lay hR hMem hRaw hCard hB hOffset hRegs.hBase hLoad hInBase
      hRegs.hNR hRegs.hD hRegs.hRB hRegs.hAM hRegs.hOUT hRegs.hZ hRegs.hO hRegs.hT
      hRegs.hU hWS' hBase hAm hZ hOne
    exact ⟨τ,(hr.seq rr).mono (by simp [m]; omega),hRun,by exact hNull,
      by exact hBasis,hi.trans hIn,ho.trans hOut⟩
  · obtain ⟨τ,rr,hRun,hNull,hBasis,hi,ho⟩ := comparisonLeftKernel_run D F hn T S target
      rawPairIO.array lay hR hMem hRaw hCard hB hOffset hRegs.hBase hLoad hInBase
      hRegs.hRows hRegs.hCols hRegs.hNR hRegs.hD hRegs.hRB hRegs.hAM hRegs.hOUT
      hRegs.hZ hRegs.hO hRegs.hT hRegs.hU hWS' hBase hAm hZ hOne
    exact ⟨τ,(hr.seq rr).mono (by simp [m]; omega),hRun,by exact hNull,
      by exact hBasis,hi.trans hIn,ho.trans hOut⟩

#print axioms runOneCut_run
end EvenTI.P12ComparePrep
