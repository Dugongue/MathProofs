import EvenP14CutScanEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace EvenTI.P17Trial

open EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def cutVisitRegs : List String :=
  [qN.WS, cutCoeffStart, cutBasisStart, cutFormStart, shapePower.out,
   dL,dZ,dT,dU,coeffLength,loadBase,loadLength]

private theorem cutVisitInput_frame (F : FieldPresentation K)
    {B Sn a b o c m z t u : ℕ} {σ τ : Env}
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c m z t u)
    (hArr : τ.arrs = σ.arrs)
    (hRegs : ∀ r ∈ cutVisitRegs, τ.vars r = σ.vars r)
    (hCore : ∀ r ∈ regNames canonical, τ.vars r = σ.vars r) :
    CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u := by
  have hWS := hRegs qN.WS (by decide)
  have hSlots := slots_frame F h.frame.slots (congrFun hArr _) (congrFun hArr _) hCore hWS
  refine ⟨⟨hSlots,h.frame.layout,h.frame.count_word,
    (hRegs _ (by decide)).trans h.frame.coeff_start,
    (hRegs _ (by decide)).trans h.frame.basis_start,
    (hRegs _ (by decide)).trans h.frame.form_start,
    (hRegs _ (by decide)).trans h.frame.side,
    (hRegs _ (by decide)).trans h.frame.count,
    (hRegs _ (by decide)).trans h.frame.zero,
    (hRegs _ (by decide)).trans h.frame.scratch₁,
    (hRegs _ (by decide)).trans h.frame.scratch₂,?_⟩,
    by simpa only [hArr] using h.coefficient_bank,
    (hRegs _ (by decide)).trans h.coefficient_count,
    (hRegs _ (by decide)).trans h.load_base,
    (hRegs _ (by decide)).trans h.load_count⟩
  exact (cutSlot_value_frame F (congrFun hArr canonical.mem) hWS _).trans h.frame.zero_value

private theorem cutVisitInput_setIndex (F : FieldPresentation K)
    {B Sn a b o c m z t u : ℕ} {σ : Env}
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c m z t u) (n : ℕ) :
    CutVisitInput (B := B) (Sn := Sn) F (σ.setVar cutChoiceIndex n) a b o c m z t u := by
  have hRegs : cutChoiceIndex ∉ cutVisitRegs := by decide
  have hCore : cutChoiceIndex ∉ regNames canonical := by decide
  exact cutVisitInput_frame F h rfl
    (fun r hr => by simp [vars_setVar,show r ≠ cutChoiceIndex from fun he => hRegs (he ▸ hr)])
    (fun r hr => by simp [vars_setVar,show r ≠ cutChoiceIndex from fun he => hCore (he ▸ hr)])

private structure CutScanInvariant {B Sn : ℕ} (F : FieldPresentation K) (render : ℕ → List ℕ) (stable : Env → Prop)
    (σ τ : Env) (a b o c m z t u count keepFrom : ℕ) : Prop where
  work : CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u
  stays : stable τ
  countLive : τ.vars cutChoiceLength = count
  cursor : τ.vars cutChoiceIndex ≤ count
  bank : ∀ s < z, keepFrom ≤ s → val F canonical qN.WS τ s = val F canonical qN.WS σ s
  inp : τ.inp = σ.inp
  out : τ.out = σ.out ++ (List.range (τ.vars cutChoiceIndex)).flatMap render

/-- Visit every capped coefficient code in order and append its complete encoded block. -/
theorem cappedCutBlockScan_run (F : FieldPresentation K) (visit : Com) (cost : ℕ) (render : ℕ → List ℕ)
    (stable : Env → Prop) (keepFrom : ℕ) {B Sn a b o c m z t u budget : ℕ} {σ : Env} (j : Fin 4)
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c m z t u)
    (hLive : σ.vars (nullityAt j) = c) (hb : σ.vars cutChoiceBudget = budget)
    (hbM : budget ≤ m) (hWord : (m+Fintype.card K+1)*(m+Fintype.card K+1) < B)
    (hStable : ∀ ρ, ρ.arrs = σ.arrs →
      (∀ r, r ∉ ["left","d","n","i","r",cutChoiceLength] → ρ.vars r = σ.vars r) → stable ρ)
    (hSetIndex : ∀ ρ k, stable ρ → stable (ρ.setVar cutChoiceIndex k))
    (hVisit : ∀ ρ (v : Fin (Fintype.card K^c)), stable ρ →
      CutVisitInput (B := B) (Sn := Sn) F ρ a b o c m z t u →
      (∀ s < z, keepFrom ≤ s → val F canonical qN.WS ρ s = val F canonical qN.WS σ s) →
      Fintype.card K < B → Fintype.card K^c < B → ρ.vars cutChoiceIndex = v.val →
      ∃ τ, Run B visit ρ τ cost ∧ CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u ∧ stable τ ∧
        τ.vars cutChoiceIndex = v.val ∧ τ.vars cutChoiceLength = ρ.vars cutChoiceLength ∧
        (∀ s < z, keepFrom ≤ s → val F canonical qN.WS τ s = val F canonical qN.WS ρ s) ∧
        τ.inp = ρ.inp ∧ τ.out = ρ.out ++ render v.val) :
    let q := Fintype.card K
    let count := cappedCutChoiceCount q c budget
    ∃ τ, Run B (cappedCutScanWith q visit j) σ τ
      (30*(m+q)+42 + ((cost+8)*count+6)) ∧
      CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u ∧
      (∀ s < z, keepFrom ≤ s → val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      stable τ ∧ τ.vars cutChoiceIndex = count ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ (List.range count).flatMap render := by
  let q := Fintype.card K
  let N := cappedCutChoiceCount q c budget
  have hq : 1 ≤ q := Fintype.card_pos
  have hLarge : m+q+1 < B :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < m+q+1)).trans_lt hWord
  have hNB : N < B := by
    unfold N cappedCutChoiceCount
    split <;> omega
  have hScratch₁ := h.frame.layout.zero_before
  have hScratch₂ := h.frame.layout.scratch_order
  have hFit := h.frame.layout.fit
  have hAfter := h.frame.layout.coefficient_before
  have hOne : 1 < B := by omega
  obtain ⟨ρ,hr,hN,hPres,hArrays,hIn,hOut⟩ := capChoiceProgram_run q m c budget B j σ
    hq h.frame.layout.nullity hbM hWord h.frame.side hLive hb
  let damaged := ["left","d","n","i","r",cutChoiceLength]
  have hW1 : ∀ x ∈ damaged, x ∉ cutVisitRegs := by decide
  have hW2 : ∀ x ∈ damaged, x ∉ regNames canonical := by decide
  have hPres1 (r : String) (hR : r ∈ cutVisitRegs) : ρ.vars r = σ.vars r :=
    hPres r (fun hw => hW1 r hw hR)
  have hPres2 (r : String) (hR : r ∈ regNames canonical) : ρ.vars r = σ.vars r :=
    hPres r (fun hw => hW2 r hw hR)
  have hWork := cutVisitInput_frame F h hArrays hPres1 hPres2
  have hρV (s : ℕ) : val F canonical qN.WS ρ s = val F canonical qN.WS σ s := by
    exact cutSlot_value_frame F (congrFun hArrays canonical.mem) (hPres1 qN.WS (by decide)) s
  let ρ₀ := ρ.setVar cutChoiceIndex 0
  have hZero : ρ₀.vars cutChoiceIndex = 0 := by simp [ρ₀]
  have r0 : Run B (.assign cutChoiceIndex (.lit 0)) ρ ρ₀ 2 := Run.assign (evalB_lit (by omega))
  let I (τ : Env) := CutScanInvariant (B := B) (Sn := Sn) F render stable σ τ a b o c m z t u N keepFrom
  let V (τ : Env) := N - τ.vars cutChoiceIndex
  have h0 : I ρ₀ := by
    refine ⟨cutVisitInput_setIndex F hWork 0,hSetIndex ρ 0 (hStable ρ hArrays hPres),?_,by simp [hZero],?_,hIn,?_⟩
    · simpa [ρ₀,vars_setVar,show cutChoiceLength ≠ cutChoiceIndex by decide] using hN
    · intro s _ _
      exact (val_setVar F canonical (by decide : cutChoiceIndex ≠ qN.WS) ρ 0 s).trans (hρV s)
    · simpa [ρ₀,hZero] using hOut
  have guard (τ : Env) (hτ : I τ) : cutScanGuard.evalB B τ = some (decide (τ.vars cutChoiceIndex < N)) := by
    unfold cutScanGuard
    simpa only [hτ.countLive] using evalB_condLt
      (evalB_var (σ := τ) (x := cutChoiceIndex) (hτ.cursor.trans_lt hNB))
      (evalB_var (σ := τ) (x := cutChoiceLength) (hτ.countLive ▸ hNB))
  have step (τ : Env) (hτ : I τ) (hg : cutScanGuard.evalB B τ = some true) :
      ∃ ν, Run B (cutScanBody visit) τ ν (cost+4) ∧ I ν ∧ V ν < V τ := by
    let v := τ.vars cutChoiceIndex
    have hv : v < N := by rw [guard τ hτ] at hg; simpa [v] using hg
    have hYes : q^c ≤ budget := by
      by_contra hn
      have h0 : N = 0 := if_neg hn
      omega
    have hEq : N = q^c := if_pos hYes
    let w : Fin (q^c) := ⟨v,hEq ▸ hv⟩
    obtain ⟨ζ,hs,hW,hStable',hCode,hCount,hMem,hIn',hOut'⟩ :=
      hVisit τ w hτ.stays hτ.work hτ.bank (by omega) (hYes.trans_lt (by omega)) rfl
    let ν := ζ.setVar cutChoiceIndex (v+1)
    have hCode' : ζ.vars cutChoiceIndex = v := hCode
    have hInc : Run B cutScanIncrement ζ ν 4 := Run.assign
      (evalB_bin (op := .add) (evalB_var_iff.mpr ⟨hCode'.symm,hCode' ▸ hv.trans hNB⟩)
        (evalB_lit hOne) (by change v+1 < B; omega))
    have hPos : ν.vars cutChoiceIndex = v+1 := by simp [ν]
    refine ⟨ν,hs.seq hInc,⟨cutVisitInput_setIndex F hW (v+1),hSetIndex ζ (v+1) hStable',?_,by omega,?_,hIn'.trans hτ.inp,?_⟩,?_⟩
    · simpa [ν,vars_setVar,show cutChoiceLength ≠ cutChoiceIndex by decide] using
        hCount.trans hτ.countLive
    · intro s hS hO
      have hV := val_setVar F canonical (by decide : cutChoiceIndex ≠ qN.WS) ζ (v+1) s
      exact hV.trans ((hMem s hS hO).trans (hτ.bank s hS hO))
    · change ζ.out = _
      rw [hPos,hOut',hτ.out,show τ.vars cutChoiceIndex = v from rfl,
        show w.val = v from rfl,List.range_succ,List.flatMap_append]
      simp [List.append_assoc]
    · change N-ν.vars cutChoiceIndex < N-v
      omega
  obtain ⟨τ,hRun,hInv,hEnd⟩ := Run.while_count I V (cost+4)
    (fun τ hτ => ⟨_,guard τ hτ⟩) step h0
  have hFin : τ.vars cutChoiceIndex = N := by
    rw [guard _ hInv] at hEnd
    have hf : ¬τ.vars cutChoiceIndex < N := by simpa using hEnd
    exact le_antisymm hInv.cursor (by omega)
  refine ⟨τ,(hr.seq (r0.seq hRun)).mono ?_,hInv.work,hInv.bank,hInv.stays,hFin,hInv.inp,?_⟩
  · simp [V,hZero,cutScanGuard,Cond.size,N,q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
  · simpa only [hFin] using hInv.out

#print axioms cappedCutBlockScan_run
end EvenTI.P17Trial
