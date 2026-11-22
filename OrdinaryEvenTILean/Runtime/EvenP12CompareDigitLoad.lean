import EvenP11InputCoordOrder
import Mathproof.Meta.P15GEDigitLoad20261007
import Mathproof.Meta.P15DecideRefRepOf20261007

namespace EvenTI.P12Compare

open EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical noRead run_frame)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15FactorIMP20261007 (eltF eltF_inj rCv rTd)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private noncomputable def literalEquiv (FP : FieldPresentation K) : Fin (FP.p^FP.e) ≃ K :=
  Equiv.ofBijective (fun i => eltF FP i.val)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => Fin.ext (eltF_inj FP a.isLt b.isLt h), by
        rw [Fintype.card_fin, Mathproof.P15DecideRef20261007.card_eq_pow FP]⟩)

/-- Fixed lookup table implementing the transition from public field labels to
the base-p literal format consumed by the existing field-slot installer. -/
noncomputable def literalCode (FP : FieldPresentation K) (x : K) : ℕ :=
  ((literalEquiv FP).symm x).val

theorem literalCode_lt (FP : FieldPresentation K) (x : K) :
    literalCode FP x < Fintype.card K := by
  rw [Mathproof.P15DecideRef20261007.card_eq_pow FP]
  exact ((literalEquiv FP).symm x).isLt

theorem eltF_literalCode (FP : FieldPresentation K) (x : K) :
    eltF FP (literalCode FP x) = x := (literalEquiv FP).apply_symm_apply x

def inputLabel : String := "even_compare_label"

def literalDispatch : List (ℕ × ℕ) → Com
  | [] => .assign rCv (.lit 0)
  | (key,c) :: xs =>
    .ite (.eq (.var inputLabel) (.lit key)) (.assign rCv (.lit c)) (literalDispatch xs)

private theorem literalDispatch_run (rows : List (ℕ × ℕ)) {B k v : ℕ}
    {σ : Env} (hword : σ.vars inputLabel = k) (hk : k < B)
    (hB : ∀ p ∈ rows, p.1 < B ∧ p.2 < B)
    (hval : ∀ p ∈ rows, p.1 = k → p.2 = v) (hmem : (k,v) ∈ rows) :
    Run B (literalDispatch rows) σ (σ.setVar rCv v) (4*rows.length + 2) := by
  induction rows with
  | nil => simp at hmem
  | cons p rows ih =>
    rcases p with ⟨a,c⟩
    have ha := hB (a,c) List.mem_cons_self
    have eLabel : (Expr.var inputLabel).evalB B σ = some k := by
      have hv := evalB_var (σ := σ) (x := inputLabel) (by rwa [hword])
      simpa only [hword] using hv
    have ee := evalB_condEq eLabel (evalB_lit ha.1)
    by_cases he : k = a
    · subst a
      have hcv := hval (k,c) List.mem_cons_self rfl
      change c = v at hcv
      subst c
      have hTrue : (Cond.eq (.var inputLabel) (.lit k)).evalB B σ = some true := by simpa using ee
      exact (Run.ite_true (d := literalDispatch rows) hTrue
        (Run.assign (evalB_lit ha.2))).mono (by simp [Cond.size] <;> omega)
    · have hFalse : (Cond.eq (.var inputLabel) (.lit a)).evalB B σ = some false := by
        simpa [he] using ee
      have htail : (k,v) ∈ rows := (List.mem_cons.mp hmem).resolve_left (by
        intro h; exact he (congrArg Prod.fst h))
      exact (Run.ite_false (c := .assign rCv (.lit c)) hFalse
        (ih (fun p hp => hB p (List.mem_cons_of_mem _ hp))
          (fun p hp => hval p (List.mem_cons_of_mem _ hp)) htail)).mono
        (by simp [Cond.size] <;> omega)

private theorem literalDispatch_io (rows : List (ℕ × ℕ)) :
    noRead (literalDispatch rows) ∧ (literalDispatch rows).NoWrite := by
  induction rows with
  | nil => simp [literalDispatch,noRead,Com.NoWrite]
  | cons p rows ih =>
    rcases p with ⟨a,c⟩
    simpa [literalDispatch,noRead,Com.NoWrite] using ih

noncomputable def literalTable (D : FieldEncoding K) (FP : FieldPresentation K) :
    List (ℕ × ℕ) :=
  List.ofFn fun i : Fin (Fintype.card K) => (i.val, literalCode FP (D.symm i))

open Mathproof.P15GEDigitLoad20261007 (destination loadCost)

/-- A natural-word machine decodes a legal public field label at runtime and
installs its field value into the requested slot using Problem 1.8. -/
noncomputable def installEncodedDigit (D : FieldEncoding K) (FP : FieldPresentation K) : Com :=
  .seq (literalDispatch (literalTable D FP)) Mathproof.P15GEDigitLoad20261007.prog

def installEncodedDigitCost (FP : FieldPresentation K) : ℕ :=
  4 * Fintype.card K + 2 + loadCost FP (.var destination)

theorem installEncodedDigit_run (D : FieldEncoding K) (FP : FieldPresentation K)
    {Sn B sv : ℕ} {σ : Env} (x : K)
    (hs : Slots FP canonical qN.WS Sn B σ) (hB : Fintype.card K ≤ B)
    (hlabel : σ.vars inputLabel = (D x).val)
    (hdest : σ.vars destination = sv) (hsv : sv < Sn) :
    ∃ τ, Run B (installEncodedDigit D FP) σ τ (installEncodedDigitCost FP) ∧
      Slots FP canonical qN.WS Sn B τ ∧ val FP canonical qN.WS τ sv = x ∧
      (∀ s, s ≠ sv → val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      (∀ r, r ≠ rCv → r ≠ rTd → τ.vars r = σ.vars r) ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let ρ := σ.setVar rCv (literalCode FP x)
  have hslots : Slots FP canonical qN.WS Sn B ρ :=
    Slots.setVar FP canonical hs (by decide) (by decide) _
  have hb : literalCode FP x < B := (literalCode_lt FP x).trans_le hB
  have hdι : ((D x).val, literalCode FP x) ∈ literalTable D FP := by
    simp only [literalTable,List.mem_ofFn]
    exact ⟨D x, by simp⟩
  have hι : Run B (literalDispatch (literalTable D FP)) σ ρ (4 * Fintype.card K + 2) := by
    rw [show Fintype.card K = (literalTable D FP).length by simp [literalTable]]
    refine literalDispatch_run _ hlabel ((D x).isLt.trans_le hB) ?_ ?_ hdι
    · intro p hp
      simp only [literalTable,List.mem_ofFn] at hp
      obtain ⟨i,rfl⟩ := hp
      exact ⟨i.isLt.trans_le hB,(literalCode_lt FP _).trans_le hB⟩
    · intro p hp h
      simp only [literalTable,List.mem_ofFn] at hp
      obtain ⟨i,rfl⟩ := hp
      change i.val = (D x).val at h
      rw [show i = D x from Fin.ext h, Equiv.symm_apply_apply]
  obtain ⟨τ,hr,hτ,hv,hoth,hvars,harr⟩ := Mathproof.P15GEDigitLoad20261007.run FP hslots
    (show ρ.vars destination = sv by simpa [ρ,vars_setVar,show destination ≠ rCv by decide] using hdest)
    hsv (show ρ.vars rCv = literalCode FP x by simp [ρ]) hb
  refine ⟨τ,hι.seq hr,hτ,hv.trans (eltF_literalCode FP x),?_,?_,?_,?_,?_⟩
  · intro s hne
    rw [hoth s hne, show ρ = σ.setVar rCv (literalCode FP x) from rfl]
    exact val_setVar FP canonical (by decide) σ _ s
  · intro r hcv htd
    simpa [ρ,vars_setVar,hcv] using hvars r hcv htd
  · intro a ha
    simpa [ρ] using harr a ha

  · exact ((run_frame hr).2.2.2.1 (by simp [Mathproof.P15GEDigitLoad20261007.prog,Mathproof.P15GEDigitLoad20261007.literalCall,noRead])).trans
      ((run_frame hι).2.2.2.1 (literalDispatch_io _).1)
  · exact (hr.out_eq (by simp [Mathproof.P15GEDigitLoad20261007.prog,Mathproof.P15GEDigitLoad20261007.literalCall,Com.NoWrite])).trans (hι.out_eq (literalDispatch_io _).2)

#print axioms installEncodedDigit_run

end EvenTI.P12Compare
