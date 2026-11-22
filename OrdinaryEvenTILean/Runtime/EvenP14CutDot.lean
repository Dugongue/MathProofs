import EvenP12ComparePrepFour
import Mathproof.Meta.P15RecogIMPDot20261007
import Mathproof.Meta.Problem18Claude.Problem18ClaudeFieldMacrosInstancePow20261001

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007

variable {K : Type} [Field K] [Fintype K]

/-- Logical addresses in the verified Problem 1.8 field workspace. -/
def cutCoeffStart : String := "even_compare_choice_coeff_start"
def cutBasisStart : String := "even_compare_choice_basis_start"
def cutFormStart : String := "even_compare_choice_form_start"
def cutEntry : String := "even_compare_choice_entry"

def cutCoeffAddress : Expr := .add (.var cutCoeffStart) (.var dI)
def cutBasisAddress : Expr := .add (.var cutBasisStart)
  (.add (.mul (.var dI) (.var shapePower.out)) (.var cutEntry))

def cutDotRegisters : List String :=
  [dL,dO,dT,dU,dZ,cutCoeffStart,cutBasisStart,cutEntry,shapePower.out]

noncomputable def cutDotProgram (F : FieldPresentation K) : Com :=
  .seq (.assign dO (.add (.var cutFormStart) (.var cutEntry)))
    (dotProg (fieldMacros F) cutCoeffAddress cutBasisAddress)

noncomputable def cutDotCost (F : FieldPresentation K) (c : ℕ) : ℕ :=
  4 + dotCost (fieldMacros F) cutCoeffAddress cutBasisAddress c

structure CutDotLayout (a b o c m z t u Sn : ℕ) : Prop where
  coefficient_before : a+c ≤ o
  output_before : o+m ≤ b
  basis_before : b+m*m ≤ z
  zero_before : z < t
  scratch_order : t < u
  fit : u < Sn
  nullity : c ≤ m

/-- Actual strided field dot at one output coordinate. Coefficient and
basis rows are inputs from live field slots. All other form coordinates,
cut basis rows, and frozen scalars survive the calculation. -/
theorem cutDotProgram_run (F : FieldPresentation K)
    {a b o c m z t u Sn B col : ℕ} {σ : Env}
    (hSlot : Slots F canonical qN.WS Sn B σ) (L : CutDotLayout a b o c m z t u Sn)
    (hCol : col < m) (hCB : c+1 < B)
    (ha : σ.vars cutCoeffStart = a) (hb : σ.vars cutBasisStart = b)
    (ho : σ.vars cutFormStart = o) (hm : σ.vars shapePower.out = m) (hi : σ.vars cutEntry = col)
    (hc : σ.vars dL = c) (hz : σ.vars dZ = z) (ht : σ.vars dT = t) (hu : σ.vars dU = u)
    (hzero : val F canonical qN.WS σ z = 0) :
    ∃ τ, Run B (cutDotProgram F) σ τ (cutDotCost F c) ∧ Slots F canonical qN.WS Sn B τ ∧
      val F canonical qN.WS τ (o+col) =
        ∑ j ∈ Finset.range c, val F canonical qN.WS σ (a+j) * val F canonical qN.WS σ (b+(j*m+col)) ∧
      (∀ s < Sn, s ≠ o+col → s ≠ t → s ≠ u → val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, r ∉ regNames canonical → r ≠ dI → r ≠ dO → τ.vars r = σ.vars r) ∧
      (∀ aName, aName ≠ canonical.mem → aName ≠ canonical.scratch → τ.arrs aName = σ.arrs aName) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hSnB := hSlot.slots_word
  have hOut := L.output_before
  have hBasis := L.basis_before
  have hZero := L.zero_before
  have hScratch := L.scratch_order
  have hFit := L.fit
  have hAfter := L.coefficient_before
  have eVar {ρ : Env} {r : String} {v : ℕ} (h : ρ.vars r = v) (hv : v < B) :
      (Expr.var r).evalB B ρ = some v := evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩
  have eOut : (Expr.add (.var cutFormStart) (.var cutEntry)).evalB B σ = some (o+col) :=
    evalB_bin (op := .add) (eVar ho (by omega)) (eVar hi (by omega)) (by change o+col<B; omega)
  let ρ := σ.setVar dO (o+col)
  have hPrefix : Run B (.assign dO (.add (.var cutFormStart) (.var cutEntry))) σ ρ 4 := Run.assign eOut
  have hFresh : dO ≠ qN.WS := by decide
  have hSlot' : Slots F canonical qN.WS Sn B ρ := Slots.setVar F canonical hSlot (by decide) hFresh _
  have hVM (s : ℕ) : val F canonical qN.WS ρ s = val F canonical qN.WS σ s :=
    val_setVar F canonical hFresh σ _ s
  have hStatic {r : String} (hr : r ≠ dO) : ρ.vars r = σ.vars r := by
    simp [ρ,vars_setVar,hr]
  have hρO : ρ.vars dO = o+col := by simp [ρ]
  have hp (j : ℕ) (hj : j < c) : j*m+col < m*m := by
    have H := Nat.mul_le_mul_right m (show j+1 ≤ m from hj.trans_le L.nullity)
    rw [Nat.succ_mul] at H
    omega
  have hNames : ∀ r ∈ cutDotRegisters, r ∉ regNames canonical ∧ r ≠ dI := by decide
  have hEvalA (η : Env) (hf : ∀ r ∈ cutDotRegisters, η.vars r = ρ.vars r)
      (i : ℕ) (hil : i<c) (hI : η.vars dI = i) : cutCoeffAddress.evalB B η = some (a+i) := by
    have h := (hf cutCoeffStart (by decide)).trans ((hStatic (by decide)).trans ha)
    exact evalB_bin (op := .add) (eVar h (by omega)) (eVar hI (by omega)) (by change a+i<B; omega)
  have hEvalB (η : Env) (hf : ∀ r ∈ cutDotRegisters, η.vars r = ρ.vars r)
      (i : ℕ) (hil : i<c) (hI : η.vars dI = i) : cutBasisAddress.evalB B η = some (b+(i*m+col)) := by
    have h := (hf cutBasisStart (by decide)).trans ((hStatic (by decide)).trans hb)
    have hs := (hf shapePower.out (by decide)).trans ((hStatic (by decide)).trans hm)
    have hr := (hf cutEntry (by decide)).trans ((hStatic (by decide)).trans hi)
    have hv := hp i hil
    have hMul : (Expr.mul (.var dI) (.var shapePower.out)).evalB B η = some (i*m) :=
      evalB_bin (op := .mul) (eVar hI (by omega)) (eVar hs (by omega)) (by change i*m<B; omega)
    have hAdd := evalB_bin (op := .add) hMul (eVar hr (by omega)) (by change i*m+col<B; omega)
    exact evalB_bin (op := .add) (eVar h (by omega)) hAdd (by change b+(i*m+col)<B; omega)
  have hIA (i : ℕ) (hil : i<c) : a+i < Sn ∧ a+i ≠ o+col ∧ a+i ≠ t ∧ a+i ≠ u := by
    omega
  have hIB (i : ℕ) (hil : i<c) : b+(i*m+col) < Sn ∧ b+(i*m+col) ≠ o+col ∧
      b+(i*m+col) ≠ t ∧ b+(i*m+col) ≠ u := by
    have h := hp i hil
    omega
  obtain ⟨τ,hBody,hFinal,hValue,hMem,hRegs,hArr,hInp,hOut'⟩ :=
    dot_run (fieldMacros F) cutDotRegisters hNames (by decide) (by decide) (by decide)
      (by decide) (by decide) cutCoeffAddress cutBasisAddress
      (by simp [cutCoeffAddress,cutDotRegisters,VarsIn])
      (by simp [cutBasisAddress,cutDotRegisters,VarsIn])
      hSlot' ((hStatic (by decide)).trans hc) hρO ((hStatic (by decide)).trans ht)
      ((hStatic (by decide)).trans hu) ((hStatic (by decide)).trans hz)
      hEvalA hEvalB hIA hIB (by omega) (by omega) hFit (by omega)
      (by omega) (by omega) (by omega) (by omega) ((hVM z).trans hzero) hCB
  exact ⟨τ, hPrefix.seq hBody, hFinal, by simpa only [hVM] using hValue,
    fun s hs hco hct hcu => (hMem s hs hco hct hcu).trans (hVM s),
    fun r hr hI hO => (hRegs r hr hI).trans (hStatic hO), hArr, hInp,hOut'⟩

#print axioms cutDotProgram_run
end EvenTI.P12ComparePrep
