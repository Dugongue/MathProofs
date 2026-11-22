import EvenP12ComparePrepRaw
import EvenP12ComparePrepShape
import EvenP12ComparePrepField

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The finite program starts with the binary word encoding's ordinary length
header and raw pair, supplying the canonical field ABI from fixed metadata. -/
def comparisonInitProgram (FP : FieldPresentation K) : Com :=
  .seq (.read rawPairIO.limit) (.seq rawPairLoad (.seq rawShapeProgram (fieldInitProgram FP)))

def comparisonInitExt (FP : FieldPresentation K) (Sn len : Nat) (other : String → Nat) : String → Nat :=
  canonicalInitExt FP Sn (fun name => if name = rawPairIO.array then len else other name)

theorem comparisonInitProgram_run (F : FieldEncoding K) (FP : FieldPresentation K)
    (w : List Nat) {p : ParsedPair K} (hp : decodePair F w = some p)
    (Sn B : Nat) (other : String → Nat)
    (hLen : w.length < B) (hWords : ∀ x ∈ w, x < B)
    (hMemFit : FP.e+1+Sn*FP.e < B) (hScratchFit : 16*(FP.e+1) < B)
    (hSquare : (FP.p+1)^2 < B) (hPower : (FP.p+1)^(FP.e+1) < B)
    (hSlotFit : Sn < B) :
    ∃ τ, Run B (comparisonInitProgram FP)
      (initEnv (comparisonInitExt FP Sn w.length other) (w.length::w)) τ
      (40*(w.length+1)+3*FP.e+25) ∧
      PairShape τ (comparisonInput F p.source p.target) p.d p.n ∧
      Slots FP canonical qN.WS Sn B τ ∧ τ.vars qN.WS = FP.e+1 ∧
      (∀ j < Sn, val FP canonical qN.WS τ j = 0) ∧ τ.inp = [] ∧ τ.out = [] := by
  let σ := initEnv (comparisonInitExt FP Sn w.length other) (w.length::w)
  let σ₁ := {σ.setVar rawPairIO.limit w.length with inp := w}
  have hRead : Run B (.read rawPairIO.limit) σ σ₁ 1 := Run.read rfl
  have hBase : σ₁.vars rawPairIO.base = 0 := rfl
  have hLimit : σ₁.vars rawPairIO.limit = w.length := by simp [σ₁]
  have hArray : (σ₁.arrs rawPairIO.array).length = w.length := by
    simp [σ₁,σ,initEnv,comparisonInitExt,canonicalInitExt,rawPairIO,canonical]
  obtain ⟨u,hu,hRaw,hOthers,hVars,hIn,hOut⟩ :=
    rawPairLoad_run w [] (σ := σ₁) (by simp [σ₁]) hBase hLimit hArray hLen hWords
  obtain ⟨v,hv,hShape,hArrays,hIn',hOut'⟩ := rawShapeProgram_run F w hp hRaw hLen
  have hMem : v.arrs canonical.mem = List.replicate (FP.e+1+Sn*FP.e) 0 := by
    rw [hArrays,hOthers _ (by decide)]
    simp [σ₁,σ,initEnv,comparisonInitExt,canonicalInitExt]
  have hScratch : (v.arrs canonical.scratch).length = 16*(FP.e+1) := by
    rw [hArrays,hOthers _ (by decide)]
    simp [σ₁,σ,initEnv,comparisonInitExt,canonicalInitExt,canonical]
  obtain ⟨hField,hSlots,hWS,hZeros,hPreserve,hVP,hIn'',hOut''⟩ :=
    fieldInitProgram_run FP Sn B v hMem hScratch hMemFit hScratchFit hSquare hPower hSlotFit
  let τ := fieldInitState FP v
  have hCombined : Run B (comparisonInitProgram FP) σ τ (40*(w.length+1)+3*FP.e+25) :=
    (hRead.seq (hu.seq (hv.seq hField))).mono (by omega)
  have hCanon : τ.arrs rawPairIO.array = comparisonInput F p.source p.target :=
    (hPreserve _ (by decide)).trans (hShape.bank.trans (decodePair_reencode F w hp).symm)
  have hPres (x : String) (h : x ≠ canonical.e ∧ x ≠ canonical.p ∧ x ≠ canonical.modBase ∧
      x ≠ canonical.exp ∧ x ≠ qN.WS) : τ.vars x = v.vars x :=
    hVP x h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact ⟨τ,hCombined,
    ⟨hCanon,(hPres _ (by decide)).trans hShape.order,(hPres _ (by decide)).trans hShape.dimension,
      (hPres _ (by decide)).trans hShape.half,(hPres _ (by decide)).trans hShape.side⟩,
    hSlots,hWS,hZeros,hIn''.trans (hIn'.trans hIn),hOut''.trans (hOut'.trans hOut)⟩

#print axioms comparisonInitProgram_run
end EvenTI.P12ComparePrep
