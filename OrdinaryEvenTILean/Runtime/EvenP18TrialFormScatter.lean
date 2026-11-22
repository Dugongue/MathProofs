import EvenP16TrialHigherEmit
import EvenP14CutRankOne
import EvenP14CutCoeffInstall

set_option autoImplicit false
set_option maxHeartbeats 2100000

namespace EvenTI.P18Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial
open EvenTI.P12ComparePrep (cutSlot_value_frame)
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames val_setVar)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def publicFormStart : String := "even.trial.readback.start"
def publicFormTarget : String := "even.trial.readback.target"
def publicFormCursor : String := "even.trial.readback.cursor"

def publicFormReadAt : Expr := .add (.var publicFormStart) (.var publicFormCursor)
def publicFormWriteAt : Expr := .add (.var publicFormTarget) (.var reverseDigitResult)

noncomputable def scatterPublicFormWord (D : FieldEncoding K) (F : FieldPresentation K) (bank : String) : Com :=
  .seq (.assign reverseDigitRemain (.var emitFormModes)) <|
    .seq (.assign reverseDigitQuotient (.var publicFormCursor)) <|
      .seq reverseDigits <|
        .seq (.assign inputLabel (.get bank publicFormReadAt)) <|
          .seq (.assign destination publicFormWriteAt) (installEncodedDigit D F)

def scatterScratch : List String :=
  [reverseDigitRemain,reverseDigitQuotient,reverseDigitResult,inputLabel,destination,rCv,rTd]

private theorem reverseCoreFresh : ∀ r∈regNames canonical,
    r≠reverseDigitRemain ∧ r≠reverseDigitQuotient ∧ r≠reverseDigitResult := by decide

/-- Read the actual public field label at one index and scatter it to the
exact physical mixed-radix coordinate used by the higher anchor grid. -/
theorem scatterPublicFormWord_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn d n start dest : ℕ} {σ : Env} (bank : String) (hBank : bank≠canonical.mem)
    (p : Coord d n → K) (j : Fin (n^d))
    (hn : 0<n) (hnB : n<B) (hdB : d<B) (hmB : n^d<B) (hQ : Fintype.card K≤B)
    (hFit : dest+n^d≤Sn) (hS : Slots F canonical qN.WS Sn B σ)
    (hStart : σ.vars publicFormStart=start) (hD : σ.vars publicFormTarget=dest)
    (hCursor : σ.vars publicFormCursor=j.val)
    (hModes : σ.vars emitFormModes=d) (hN : σ.vars reverseDigitBase=n)
    (hReadAddr : start+j.val<B)
    (hRead : (σ.arrs bank)[start+j.val]?=some (D (p ((cutOrder d n).symm j))).val) :
    let target := dest+(inputCoordOrder n d ((cutOrder d n).symm j)).val
    ∃ τ, Run B (scatterPublicFormWord D F bank) σ τ (24*d+19+installEncodedDigitCost F) ∧
      Slots F canonical qN.WS Sn B τ ∧
      val F canonical qN.WS τ target=p ((cutOrder d n).symm j) ∧
      (∀ k, k≠target → val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      (∀ r, r∉scatterScratch → τ.vars r=σ.vars r) ∧
      τ.arrs bank=σ.arrs bank ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  dsimp only
  let α := σ.setVar reverseDigitRemain d
  let β := α.setVar reverseDigitQuotient j.val
  have r₀ : Run B (.assign reverseDigitRemain (.var emitFormModes)) σ α 2 :=
    Run.assign (ev_var hModes hdB)
  have r₁ : Run B (.assign reverseDigitQuotient (.var publicFormCursor)) α β 2 :=
    Run.assign (ev_var (show α.vars publicFormCursor=j.val from hCursor) (j.isLt.trans hmB))
  obtain ⟨γ,r₂,hRev,hArr,hIn,hOut,hRegs⟩ := reverseDigits_run hn hnB hdB hmB j.isLt
    (show β.vars reverseDigitBase=n from hN) (show β.vars reverseDigitRemain=d from rfl) rfl
  have hR (r : String) (hr : r≠reverseDigitRemain) (hq : r≠reverseDigitQuotient)
      (hz : r≠reverseDigitResult) : γ.vars r=σ.vars r := by
    rw [hRegs r hr hq hz]
    simp [β,α,hr,hq]
  have hGSlots : Slots F canonical qN.WS Sn B γ :=
    slots_frame F hS (congrFun hArr _) (congrFun hArr _)
      (fun r hr => hR r (reverseCoreFresh r hr).1 (reverseCoreFresh r hr).2.1 (reverseCoreFresh r hr).2.2)
      (hR _ (by decide) (by decide) (by decide))
  let x := (cutOrder d n).symm j
  let k := dest+(inputCoordOrder n d x).val
  have hRev' : γ.vars reverseDigitResult=(inputCoordOrder n d x).val := by
    rw [hRev,←reverseModeNumber_eq hn d j]
  have hk : k<Sn := by
    have h := (inputCoordOrder n d x).isLt
    omega
  have eRead : publicFormReadAt.evalB B γ=some (start+j.val) :=
    ev_add (ev_var ((hR _ (by decide) (by decide) (by decide)).trans hStart) (by omega))
      (ev_var ((hR _ (by decide) (by decide) (by decide)).trans hCursor) (j.isLt.trans hmB)) hReadAddr
  let δ := γ.setVar inputLabel (D (p x)).val
  have r₃ : Run B (.assign inputLabel (.get bank publicFormReadAt)) γ δ 5 :=
    Run.assign (evalB_get eRead (by rw [hArr]; exact hRead) ((D (p x)).isLt.trans_le hQ))
  have eWrite : publicFormWriteAt.evalB B δ=some k := by
    have hd : δ.vars publicFormTarget=dest := (hR _ (by decide) (by decide) (by decide)).trans hD
    have hi : δ.vars reverseDigitResult=(inputCoordOrder n d x).val := hRev'
    exact ev_add (ev_var hd (by have := hGSlots.slots_word; omega))
      (ev_var hi ((inputCoordOrder n d x).isLt.trans hmB)) (hk.trans hGSlots.slots_word)
  let η := δ.setVar destination k
  have r₄ : Run B (.assign destination publicFormWriteAt) δ η 4 := Run.assign eWrite
  have hSlotsη := Slots.setVar F canonical
    (Slots.setVar F canonical hGSlots (by decide : inputLabel ∉ regNames canonical)
      (by decide : inputLabel≠qN.WS) (D (p x)).val)
    (by decide : destination ∉ regNames canonical) (by decide : destination≠qN.WS) k
  obtain ⟨τ,r₅,hs,hk',hMem,hVar,hArr',hI,hO⟩ := installEncodedDigit_run D F (σ := η)
    (p x) hSlotsη hQ rfl rfl hk
  refine ⟨τ,(r₀.seq (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅))))).mono (by omega),
    hs,hk',?_,?_,(hArr' _ hBank).trans (congrFun hArr _),hI.trans hIn,hO.trans hOut⟩
  · intro m hm
    refine (hMem m hm).trans ?_
    rw [show η=δ.setVar destination k from rfl,val_setVar F canonical (by decide),
      show δ=γ.setVar inputLabel (D (p x)).val from rfl,val_setVar F canonical (by decide)]
    exact cutSlot_value_frame F (congrFun hArr _) (hR _ (by decide) (by decide) (by decide)) m
  · intro r hr
    have hf (u : String) (hu : u∈scatterScratch) : r≠u := fun e => hr (e ▸ hu)
    rw [hVar r (hf _ (by decide)) (hf _ (by decide))]
    simp [η,δ,hf inputLabel (by decide),hf destination (by decide),
      hR r (hf _ (by decide)) (hf _ (by decide)) (hf _ (by decide))]

#print axioms scatterPublicFormWord_run
end EvenTI.P18Trial


