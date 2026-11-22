import EvenP12CompareLiveCRTScan

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

set_option maxRecDepth 25000

def initCRT : Com :=
  .seq (.assign crtCursor (.lit 0))
    (.seq (.assign crtRepresentative (.lit 0))
      (.seq (.assign crtPeriod (.lit 1)) (.assign crtActive (.lit 1))))

private theorem initCRT_run (es : List UnaryEquation) {M W : ℕ} {σ : Env} (hW : 1 < W)
    (h : CRTInputs es σ) :
    ∃ τ, Run W initCRT σ τ 8 ∧ CRTInputs es τ ∧ τ.vars crtCursor = 0 ∧ CRTState M es 0 τ := by
  let σ₁ := σ.setVar crtCursor 0
  let σ₂ := σ₁.setVar crtRepresentative 0
  let σ₃ := σ₂.setVar crtPeriod 1
  let τ := σ₃.setVar crtActive 1
  have z : 0 < W := by omega
  have r₁ : Run W (.assign crtCursor (.lit 0)) σ σ₁ 2 := Run.assign (evalB_lit z)
  have r₂ : Run W (.assign crtRepresentative (.lit 0)) σ₁ σ₂ 2 := Run.assign (evalB_lit z)
  have r₃ : Run W (.assign crtPeriod (.lit 1)) σ₂ σ₃ 2 := Run.assign (evalB_lit hW)
  have r₄ : Run W (.assign crtActive (.lit 1)) σ₃ τ 2 := Run.assign (evalB_lit hW)
  have hr : Run W initCRT σ τ 8 := r₁.seq (r₂.seq (r₃.seq r₄))
  have hf := Frame.of_run hr
  have hCursor : τ.vars crtCursor = 0 := by
    simp [τ,σ₃,σ₂,σ₁,vars_setVar,show crtCursor ≠ crtActive by decide,
      show crtCursor ≠ crtPeriod by decide,show crtCursor ≠ crtRepresentative by decide]
  have hRep : τ.vars crtRepresentative = 0 := by
    simp [τ,σ₃,σ₂,vars_setVar,show crtRepresentative ≠ crtActive by decide,
      show crtRepresentative ≠ crtPeriod by decide]
  have hPeriod : τ.vars crtPeriod = 1 := by
    simp [τ,σ₃,vars_setVar,show crtPeriod ≠ crtActive by decide]
  refine ⟨τ,hr,⟨(hf.vars _ (by decide)).trans h.1, (hf.arrs _ (by decide)).trans h.2.1,
    (hf.arrs _ (by decide)).trans h.2.2.1,(hf.arrs _ (by decide)).trans h.2.2.2⟩,hCursor,?_⟩
  refine Or.inl ⟨by simp [τ],by rw [hRep,hPeriod]; decide,by rw [hPeriod]; exact one_dvd _,?_⟩
  simp [PrefixSolutions,hRep,hPeriod,Nat.ModEq,Nat.mod_one]

private theorem solvesAll_iff (es : List UnaryEquation) (s : ℕ) :
    PrefixSolutions es es.length s ↔ ∀ e ∈ es, e.Satisfied s := by
  constructor
  · intro h e he
    obtain ⟨i,heq⟩ := List.mem_iff_get.mp he
    rw [← heq]
    exact h i i.isLt
  · intro h i _
    exact h _ (List.get_mem _ _)

private theorem activeRepresentative {M : ℕ} (es : List UnaryEquation) (hM : 0 < M)
    (hData : ∀ i : Fin es.length, (es.get i).modulus ∣ M) (σ : Env)
    (hs : CRTState M es es.length σ) :
    (∃ w, solveUnaryList es = some w ∧ σ.vars crtActive = 1 ∧
      σ.vars crtRepresentative = w.1 ∧ w.1 < M) ∨
    (solveUnaryList es = none ∧ σ.vars crtActive = 0) := by
  have hd (e) (he : e ∈ es) : e.modulus ∣ M := by
    obtain ⟨i,heq⟩ := List.mem_iff_get.mp he
    rw [← heq]
    exact hData i
  have hp (e) (he : e ∈ es) : 0 < e.modulus := Nat.pos_of_dvd_of_pos (hd e he) hM
  rcases hs with ⟨hA,hLt,hPer,hs⟩ | ⟨hA,hs⟩
  · let r := σ.vars crtRepresentative
    let p := σ.vars crtPeriod
    have hSolv := (solvesAll_iff es r).mp ((hs r).mpr (Nat.ModEq.refl _))
    obtain ⟨w,hw,hr⟩ := (solveUnaryList_correct es hp r).mpr hSolv
    have hW := solveUnaryList_bounds es hM hd hw
    have hSw : PrefixSolutions es es.length w.1 := (solvesAll_iff es w.1).mpr
      ((solveUnaryList_correct es hp w.1).mp ⟨w,hw,Nat.ModEq.refl _⟩)
    have hr' : w.1 ≡ r [MOD p] := (hs w.1).mp hSw
    have h₁ : w.1 ≤ r := by
      change r % w.2 = w.1 % w.2 at hr
      rw [Nat.mod_eq_of_lt hW.2.2] at hr
      rw [←hr]
      exact Nat.mod_le _ _
    have h₂ : r ≤ w.1 := by
      change w.1%p = r%p at hr'
      rw [Nat.mod_eq_of_lt hLt] at hr'
      change w.1%p = r at hr'
      rw [←hr']
      exact Nat.mod_le _ _
    exact Or.inl ⟨w,hw,hA,Nat.le_antisymm h₂ h₁,hW.2.2.trans_le (Nat.le_of_dvd hM hW.2.1)⟩
  · refine Or.inr ⟨?_,hA⟩
    cases h : solveUnaryList es with
    | none => rfl
    | some w =>
      have he := (solveUnaryList_correct es hp w.1).mp ⟨w,h,Nat.ModEq.refl _⟩
      exact False.elim (hs w.1 ((solvesAll_iff es w.1).mpr he))

def coordinateSlot : String := "even_recover_coordinate_slot"
def coordinateBank : String := "even_recover_coordinate_bank"

def commitCoordinate : Com :=
  .ite (.eq (.var crtActive) (.lit 1))
    (.store coordinateBank (.var coordinateSlot) (.var crtRepresentative)) .skip

def recoverAndCommitCoordinate : Com :=
  .seq initCRT (.seq crtScan commitCoordinate)

/-- Compute the least extending residue from the installed unary payload,
then store the exact resulting coordinate into its selected assignment slot. -/
theorem recoverAndCommitCoordinate_run (es : List UnaryEquation)
    {M W slot : ℕ} {σ : Env} (hM : 0 < M) (hW : 4*M*M+4*M+10 < W)
    (hLen : es.length < W) (h : CRTInputs es σ)
    (hSlot : σ.vars coordinateSlot = slot) (hSlotW : slot < W)
    (hIn : slot < (σ.arrs coordinateBank).length)
    (hData : ∀ j : Fin es.length, (es.get j).coefficient ≤ M ∧ (es.get j).value ≤ M ∧
      0 < (es.get j).modulus ∧ (es.get j).modulus ∣ M) :
    ∃ τ, Run W recoverAndCommitCoordinate σ τ (crtScanCost M es.length+20) ∧
      Frame recoverAndCommitCoordinate σ τ ∧
      (match solveUnaryList es with
       | some w => τ.vars crtActive = 1 ∧
           τ.arrs coordinateBank = (σ.arrs coordinateBank).set slot w.1
       | none => τ.vars crtActive = 0 ∧ τ.arrs coordinateBank = σ.arrs coordinateBank) := by
  have h1 : 1 < W := by omega
  obtain ⟨η,hInit,hInputs,hCursor,hState⟩ := initCRT_run es h1 h
  obtain ⟨ρ,hRun,_,_,hS,_⟩ := crtScan_run es hM hW hLen hInputs hCursor hState hData
  have hf := Frame.of_run (hInit.seq hRun)
  have hSlotρ : ρ.vars coordinateSlot = slot := (hf.vars _ (by decide)).trans hSlot
  have hBankρ : ρ.arrs coordinateBank = σ.arrs coordinateBank := hf.arrs _ (by decide)
  let g := Cond.eq (.var crtActive) (.lit 1)
  let c := Com.store coordinateBank (.var coordinateSlot) (.var crtRepresentative)
  rcases activeRepresentative es hM (fun j => (hData j).2.2.2) ρ hS with
    ⟨w,hw,ha,hrep,hm⟩ | ⟨hn,ha⟩
  · let τ := ρ.setArr coordinateBank slot w.1
    have eg : g.evalB W ρ = some true :=
      evalB_condEq (ev_var ha h1) (evalB_lit h1)
    have rs : Run W c ρ τ 3 :=
      Run.store (ev_var hSlotρ hSlotW) (ev_var hrep (by omega)) (by rwa [hBankρ])
    have rr : Run W recoverAndCommitCoordinate σ τ (crtScanCost M es.length+20) :=
      (hInit.seq (hRun.seq (Run.ite_true (d := .skip) eg rs))).mono (by simp [g,Cond.size,Expr.size]; omega)
    exact ⟨τ,rr,Frame.of_run rr,by simp [hw,τ,vars_setArr,arrs_setArr,ha,hBankρ]⟩
  · have eg : g.evalB W ρ = some false :=
      evalB_condEq (ev_var ha (by omega)) (evalB_lit (n := 1) h1)
    have rr : Run W recoverAndCommitCoordinate σ ρ (crtScanCost M es.length+20) :=
      (hInit.seq (hRun.seq (Run.ite_false (c := c) eg Run.skip))).mono (by simp [g,Cond.size,Expr.size]; omega)
    exact ⟨ρ,rr,Frame.of_run rr,by simp [hn,ha,hBankρ]⟩

#print axioms recoverAndCommitCoordinate_run

end EvenTI.P12Compare
