import EvenP12CompareDigitLoad
import EvenP12CompareRetainedLayout

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15FactorIMP20261007 (rCv rTd)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEDigitLoad20261007 (destination)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def loadIndex : String := "even_compare_load_index"
def loadLength : String := "even_compare_load_length"
def loadBase : String := "even_compare_load_base"
def inputBase : String := "even_compare_input_base"

noncomputable def encodedBankLoadStep (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) (address : Expr) : Com :=
  .seq (.assign inputLabel (.get bank address))
    (.seq (.assign destination (.add (.var loadBase) (.var loadIndex)))
      (.seq (installEncodedDigit D FP) (.assign loadIndex (.add (.var loadIndex) (.lit 1)))))

def encodedBankLoadGuard : Cond := .lt (.var loadIndex) (.var loadLength)

noncomputable def encodedBankLoad (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) (address : Expr) : Com :=
  .seq (.assign loadIndex (.lit 0))
    (.while encodedBankLoadGuard (encodedBankLoadStep D FP bank address))

def encodedBankLoadStepCost (FP : FieldPresentation K) (address : Expr) : ℕ :=
  address.size + 10 + installEncodedDigitCost FP

def encodedBankLoadCost (FP : FieldPresentation K) (address : Expr) (len : ℕ) : ℕ :=
  (encodedBankLoadStepCost FP address + 4) * len + 6

/-- Runtime register names available to a load address expression, other than
the current cursor, have the same values throughout this phase. -/
abbrev loadChanges (r : String) : Prop :=
  r = loadIndex ∨ r = inputLabel ∨ r = destination ∨ r = rCv ∨ r = rTd

theorem encodedBankLoad_run (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) (address : Expr) (location : ℕ → ℕ) (data : ℕ → K)
    {Sn B base len : ℕ} {σ : Env} (hBankMem : bank ≠ canonical.mem)
    (hS : Slots FP canonical qN.WS Sn B σ) (hField : Fintype.card K ≤ B)
    (hB : 1 < B) (hLen : len < B)
    (hBase : σ.vars loadBase = base) (hLength : σ.vars loadLength = len)
    (hfit : base + len ≤ Sn)
    (hAddr : ∀ ρ k, ρ.vars loadIndex = k →
      (∀ r, ¬loadChanges r → ρ.vars r = σ.vars r) → k < len →
      address.evalB B ρ = some (location k))
    (hData : ∀ k < len, (σ.arrs bank)[location k]? = some (D (data k)).val) :
    ∃ τ, Run B (encodedBankLoad D FP bank address) σ τ (encodedBankLoadCost FP address len) ∧
      Slots FP canonical qN.WS Sn B τ ∧
      (∀ k < len, val FP canonical qN.WS τ (base+k) = data k) ∧
      (∀ s, s < base ∨ base+len ≤ s → val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      (∀ r, ¬loadChanges r → τ.vars r = σ.vars r) ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  have nBase : ¬loadChanges loadBase := by decide
  have nLen : ¬loadChanges loadLength := by decide
  let I (ρ : Env) : Prop :=
    Slots FP canonical qN.WS Sn B ρ ∧
    ρ.vars loadIndex ≤ len ∧
    (∀ k < ρ.vars loadIndex, val FP canonical qN.WS ρ (base+k) = data k) ∧
    (∀ s, s < base ∨ base+len ≤ s → val FP canonical qN.WS ρ s = val FP canonical qN.WS σ s) ∧
    (∀ r, ¬loadChanges r → ρ.vars r = σ.vars r) ∧
    (∀ a, a ≠ canonical.mem → ρ.arrs a = σ.arrs a) ∧ ρ.inp = σ.inp ∧ ρ.out = σ.out
  let V (ρ : Env) : ℕ := len - ρ.vars loadIndex
  let σ₀ := σ.setVar loadIndex 0
  have r₀ : Run B (.assign loadIndex (.lit 0)) σ σ₀ 2 := Run.assign (evalB_lit (by omega))
  have z₀ : σ₀.vars loadIndex = 0 := by simp [σ₀]
  have I₀ : I σ₀ := by
    refine ⟨Slots.setVar FP canonical hS (by decide) (by decide) 0, by omega, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · rw [z₀]; intro k hk; omega
    · intro s _; exact val_setVar FP canonical (by decide) σ _ s
    · intro r hr
      simp [loadChanges] at hr
      simp [σ₀,vars_setVar,hr.1]
    · intro a _; rfl
  have g (ρ : Env) (hρ : I ρ) :
      encodedBankLoadGuard.evalB B ρ = some (decide (ρ.vars loadIndex < len)) := by
    have hN := (hρ.2.2.2.2.1 loadLength nLen).trans hLength
    have hI : ρ.vars loadIndex < B := hρ.2.1.trans_lt hLen
    have hNL : ρ.vars loadLength < B := hN ▸ hLen
    simpa [encodedBankLoadGuard,hN] using
      evalB_condLt (σ := ρ) (e := .var loadIndex) (f := .var loadLength)
        (evalB_var hI) (evalB_var hNL)
  have step (ρ : Env) (hρ : I ρ) (hg : encodedBankLoadGuard.evalB B ρ = some true) :
      ∃ η, Run B (encodedBankLoadStep D FP bank address) ρ η (encodedBankLoadStepCost FP address) ∧
        I η ∧ V η < V ρ := by
    obtain ⟨hslots,hcur,hinstalled,houtside,hvars,harr,hin,hout⟩ := hρ
    rw [g ρ ⟨hslots,hcur,hinstalled,houtside,hvars,harr,hin,hout⟩] at hg
    let k := ρ.vars loadIndex
    have hk : k < len := by simpa [k] using hg
    have eAddr := hAddr ρ k rfl hvars hk
    have eLoad : (Expr.get bank address).evalB B ρ = some (D (data k)).val := by
      exact evalB_get eAddr (by rw [harr bank hBankMem]; exact hData k hk)
        ((D (data k)).isLt.trans_le hField)
    let ρ₁ := ρ.setVar inputLabel (D (data k)).val
    have r₁ : Run B (.assign inputLabel (.get bank address)) ρ ρ₁ (address.size+2) :=
      (Run.assign eLoad).mono (by simp only [Expr.size]; omega)
    have Bbase : ρ₁.vars loadBase = base := by
      simp [ρ₁,vars_setVar,show loadBase ≠ inputLabel by decide,hvars loadBase nBase,hBase]
    have Bind : ρ₁.vars loadIndex = k := by
      simp [ρ₁,vars_setVar,show loadIndex ≠ inputLabel by decide,k]
    have hslot : base+k < Sn := by omega
    have hSB := hslots.slots_word
    have eSlot : (Expr.add (.var loadBase) (.var loadIndex)).evalB B ρ₁ = some (base+k) := by
      have ee := evalB_bin (B := B) (σ := ρ₁) (op := .add)
        (evalB_var (x := loadBase) (by rw [Bbase]; omega))
        (evalB_var (x := loadIndex) (by rw [Bind]; omega))
        (by change ρ₁.vars loadBase + ρ₁.vars loadIndex < B; rw [Bbase,Bind]; omega)
      simpa [Bbase,Bind] using ee
    let ρ₂ := ρ₁.setVar destination (base+k)
    have r₂ : Run B (.assign destination (.add (.var loadBase) (.var loadIndex))) ρ₁ ρ₂ 4 :=
      Run.assign eSlot
    have hslots₂ : Slots FP canonical qN.WS Sn B ρ₂ :=
      Slots.setVar FP canonical (Slots.setVar FP canonical hslots (by decide) (by decide) _)
        (by decide) (by decide) _
    have hLabel₂ : ρ₂.vars inputLabel = (D (data k)).val := by
      simp [ρ₂,ρ₁,vars_setVar,show inputLabel ≠ destination by decide]
    have hDest₂ : ρ₂.vars destination = base+k := by simp [ρ₂]
    obtain ⟨ρ₃,r₃,hslots₃,hval₃,hother₃,hvars₃,harr₃,hin₃,hout₃⟩ :=
      installEncodedDigit_run D FP (data k) hslots₂ hField hLabel₂ hDest₂ hslot
    have hIndex₃ : ρ₃.vars loadIndex = k := by
      rw [hvars₃ _ (by decide) (by decide)]
      simp [ρ₂,vars_setVar,show loadIndex ≠ destination by decide,Bind]
    have eInc : (Expr.add (.var loadIndex) (.lit 1)).evalB B ρ₃ = some (k+1) := by
      have ev := evalB_bin (B := B) (σ := ρ₃) (op := .add)
        (evalB_var (x := loadIndex) (by rw [hIndex₃]; omega))
        (evalB_lit (n := 1) hB) (by change ρ₃.vars loadIndex + 1 < B; rw [hIndex₃]; omega)
      simpa [hIndex₃] using ev
    let η := ρ₃.setVar loadIndex (k+1)
    have r₄ : Run B (.assign loadIndex (.add (.var loadIndex) (.lit 1))) ρ₃ η 4 :=
      Run.assign eInc
    have hkη : η.vars loadIndex = k+1 := by simp [η]
    have hMem₂ (s : ℕ) : val FP canonical qN.WS ρ₂ s = val FP canonical qN.WS ρ s := by
      rw [show ρ₂ = ρ₁.setVar destination (base+k) from rfl, val_setVar FP canonical (by decide),
        show ρ₁ = ρ.setVar inputLabel (D (data k)).val from rfl, val_setVar FP canonical (by decide)]
    have hMemη (s : ℕ) : val FP canonical qN.WS η s = val FP canonical qN.WS ρ₃ s :=
      val_setVar FP canonical (by decide) _ _ _
    have hrun := r₁.seq (r₂.seq (r₃.seq r₄))
    refine ⟨η,hrun.mono (by unfold encodedBankLoadStepCost; omega), ?_, ?_⟩
    · refine ⟨Slots.setVar FP canonical hslots₃ (by decide) (by decide) _, by omega,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [hMemη]
        by_cases he : t = k
        · simpa [he] using hval₃
        · rw [hother₃ _ (by omega),hMem₂]
          exact hinstalled t (by omega)
      · intro s hss
        rw [hMemη,hother₃ _ (by omega),hMem₂]
        exact houtside s hss
      · intro r hr
        simp only [loadChanges,not_or] at hr
        rw [show η.vars r = ρ₃.vars r by simp [η,vars_setVar,hr.1],
          hvars₃ _ hr.2.2.2.1 hr.2.2.2.2]
        simpa [ρ₂,ρ₁,vars_setVar,hr.2.2.1,hr.2.1] using hvars r (by simpa [loadChanges] using hr)
      · intro a ha
        simpa [η,ρ₂,ρ₁] using (harr₃ a ha).trans (harr a ha)
      · simpa [η,ρ₂,ρ₁] using hin₃.trans hin
      · simpa [η,ρ₂,ρ₁] using hout₃.trans hout
    · simp only [V,hkη]; change len - (k+1) < len - k; omega
  obtain ⟨τ,hr,hτ,hstop⟩ := Run.while_count I V (encodedBankLoadStepCost FP address)
    (fun ρ h => ⟨_,g ρ h⟩) step I₀
  rw [g τ hτ] at hstop
  obtain ⟨hsτ,hcur,hinstalled,houtside,hvars,harr,hin,hout⟩ := hτ
  have hge : ¬ τ.vars loadIndex < len := by simpa using hstop
  have hlast : τ.vars loadIndex = len := by omega
  exact ⟨τ,(r₀.seq hr).mono (by simp [V,z₀,encodedBankLoadGuard,Cond.size,Expr.size,encodedBankLoadCost, Nat.add_comm 4]; omega),
    hsτ,(by simpa [hlast] using hinstalled),houtside,hvars,harr,hin,hout⟩

def contiguousAddress : Expr := .add (.var inputBase) (.var loadIndex)

/-- Install an entire balanced flattening from consecutive raw input words. -/
theorem contiguousBankLoad_run (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) (data : ℕ → K) {Sn B base offset len : ℕ} {σ : Env}
    (hBankMem : bank ≠ canonical.mem)
    (hS : Slots FP canonical qN.WS Sn B σ) (hField : Fintype.card K ≤ B)
    (hB : 1 < B) (hLen : len < B) (hOffset : offset + len < B)
    (hBase : σ.vars loadBase = base) (hLength : σ.vars loadLength = len)
    (hInputBase : σ.vars inputBase = offset) (hfit : base + len ≤ Sn)
    (hData : ∀ k < len, (σ.arrs bank)[offset+k]? = some (D (data k)).val) :
    ∃ τ, Run B (encodedBankLoad D FP bank contiguousAddress) σ τ
        (encodedBankLoadCost FP contiguousAddress len) ∧
      Slots FP canonical qN.WS Sn B τ ∧
      (∀ k < len, val FP canonical qN.WS τ (base+k) = data k) ∧
      (∀ s, s < base ∨ base+len ≤ s → val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      (∀ r, ¬loadChanges r → τ.vars r = σ.vars r) ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  refine encodedBankLoad_run D FP bank contiguousAddress (fun k => offset+k) data hBankMem
    hS hField hB hLen hBase hLength hfit ?_ hData
  intro ρ k hk hρ hkl
  have hOff := (hρ inputBase (by decide)).trans hInputBase
  have ee := evalB_bin (B := B) (σ := ρ) (op := .add)
    (evalB_var (x := inputBase) (by rw [hOff]; omega))
    (evalB_var (x := loadIndex) (by rw [hk]; omega))
    (by change ρ.vars inputBase + ρ.vars loadIndex < B; rw [hOff,hk]; omega)
  simpa [contiguousAddress,hk,hOff] using ee

#print axioms contiguousBankLoad_run

end EvenTI.P12Compare
