import EvenP18TrialRankBlocks

set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 18000

namespace EvenTI.P18Trial

open EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.LiveSpectral
open EvenTI.P15Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def readFormRegisters : List String := [emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]

private theorem formRankRegisters : ∀ r ∈ readFormRegisters, RankedRegisterFixed r := by decide

private theorem fieldsStableOnEmit : ∀ r ∈ regNames canonical, r ∉ formClobbered := by decide

private theorem rankStableOnEmit : ∀ r ∈ cutRankArgNames, r ∉ formClobbered := by decide

private theorem rankArgName {d n src R A O Z e : ℕ} {p : String × ℕ}
    (h : p ∈ cutRankArgs d n src R A O Z e) : p.1 ∈ cutRankArgNames := by
  change p.1 ∈ (cutRankArgs d n src R A O Z e).map Prod.fst
  exact List.mem_map.mpr ⟨p,h,rfl⟩

private theorem moveFormMetadata {s t : Env} {d n o : ℕ}
    (h : FormScanReady s d n o) (hKeep : ∀ r ∈ readFormRegisters, t.vars r=s.vars r) :
    FormScanReady t d n o :=
  ⟨(hKeep _ (by decide)).trans h.modes,(hKeep _ (by decide)).trans h.base,
    (hKeep _ (by decide)).trans h.start,(hKeep _ (by decide)).trans h.length⟩

noncomputable def rankedFormScan (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  cappedCutScanWith (Fintype.card K) (rankedCutBlockVisit D F (emitHigherForm D F)) j

/-- The installed higher-cut scan outputs the actual accessible field
vectors of every and only retained-full-rank capped coefficient code. -/
theorem rankedFormScan_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B d n c budget : ℕ} {σ : Env} (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1)) + n^(d+1) + n^(d+1) + 10 < B)
    (hChoice : (n^(d+1)+Fintype.card K+1)*(n^(d+1)+Fintype.card K+1) < B)
    (hLive : σ.vars (nullityAt j)=c) (hBudget : σ.vars cutChoiceBudget=budget) (hnB : budget ≤ n^(d+1))
    (hRank : CutRankStable (d := d) (n := n) F σ)
    (hMeta : FormScanReady σ (d+1) n (placedRankSource (n^(d+1)))) :
    let m := n^(d+1); let z := constantsBase.value m
    let C (ρ : Env) := CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) F ρ
      (augmentedMatrixBase.value m) ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3)
    C σ →
    let q := Fintype.card K
    let N := cappedCutChoiceCount q c budget
    ∃ τ, Run B (rankedFormScan D F j) σ τ
      (30*(m+q)+42+(((rankReadyVisitCost F d m c+(5+emitHigherFormCost F (d+1) m))+8)*N+6)) ∧
      C τ ∧ CutRankStable (d := d) (n := n) F τ ∧ FormScanReady τ (d+1) n (placedRankSource m) ∧
      (∀ s < z, firstOutputBase.value m ≤ s → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      τ.inp=σ.inp ∧
      τ.out=σ.out++(List.range N).flatMap (rankedBlockWords D F (d := d) (n := n) (c := c) σ j (cutFormWords D)) := by
  dsimp only
  intro hW
  let m := n^(d+1)
  let Sn := pairCutSlotCount.value m
  let o := placedRankSource m
  have hm : 0 < m := pow_pos (by omega) _
  have hDim : d+1 ≤ m := (Nat.lt_two_pow_self (n:=d+1)).le.trans (Nat.pow_le_pow_left hn _)
  have hnM : n ≤ m := by simpa [m] using Nat.pow_le_pow_right (by omega : 0<n) (by omega : 1 ≤ d+1)
  have hQ : Fintype.card K ≤ B := by
    have hp : 0 < m+Fintype.card K+1 := by omega
    have h := (Nat.le_mul_of_pos_right _ hp).trans_lt hChoice
    omega
  exact scanRankedBlocks_run D F j hd hn hB hChoice hLive hBudget hnB hRank
    (emitHigherForm D F) (emitHigherFormCost F (d+1) m) (cutFormWords D)
    (fun ρ => FormScanReady ρ (d+1) n o) (by
      intro ρ _ hr
      exact moveFormMetadata hMeta (by
        intro r hx
        simp only [readFormRegisters,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl <;> exact hr _ (by decide))) (by
      intro ρ k h
      exact moveFormMetadata h (by
        intro r hx
        simp only [readFormRegisters,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl <;> rfl)) (by
      intro ρ η hKeep h
      exact moveFormMetadata h (fun r hr => hKeep r (formRankRegisters _ hr))) hW (by
      intro ρ x hCut hRankρ hS hX _
      have hg₁ := hCut.frame.layout.output_before
      have hg₂ := hCut.frame.layout.basis_before
      have hg₃ := hCut.frame.layout.zero_before
      have hg₄ := hCut.frame.layout.fit
      have hp : F.p < B := by
        have h := Nat.le_mul_of_pos_right (F.p+1) (by omega : 0 < F.p+1)
        have he := hCut.frame.slots.base.arithmetic_word
        rw [pow_two] at he
        omega
      obtain ⟨τ,r,hOut,hArr,hIn,hKeeps⟩ := emitHigherForm_run D F x (by omega) (by omega) (by omega)
        (by omega) hCut.frame.slots hQ hp (by omega) (by dsimp only [o,m,Sn]; omega)
        hS.start hS.length hS.base hS.modes hX
      have hSlots := slots_frame F hCut.frame.slots (congrFun hArr _) (congrFun hArr _)
        (fun v hv => hKeeps v (fieldsStableOnEmit _ hv)) (hKeeps _ (by decide))
      have hMem (s : ℕ) : val F canonical qN.WS τ s=val F canonical qN.WS ρ s :=
        cutSlot_value_frame F (congrFun hArr canonical.mem) (hKeeps _ (by decide)) s
      have hNext := by
        exact (show CutVisitInput (B := B) (Sn := Sn) F τ (augmentedMatrixBase.value m)
          ((outputBase j).value m) o c m (constantsBase.value m) (constantsBase.value m+2)
          (constantsBase.value m+3) from
          ⟨⟨hSlots,hCut.frame.layout,hCut.frame.count_word,
            (hKeeps _ (by decide)).trans hCut.frame.coeff_start,
            (hKeeps _ (by decide)).trans hCut.frame.basis_start,
            (hKeeps _ (by decide)).trans hCut.frame.form_start,
            (hKeeps _ (by decide)).trans hCut.frame.side,
            (hKeeps _ (by decide)).trans hCut.frame.count,
            (hKeeps _ (by decide)).trans hCut.frame.zero,
            (hKeeps _ (by decide)).trans hCut.frame.scratch₁,
            (hKeeps _ (by decide)).trans hCut.frame.scratch₂,(hMem _).trans hCut.frame.zero_value⟩,
            by rw [hArr]; exact hCut.coefficient_bank,
            (hKeeps _ (by decide)).trans hCut.coefficient_count,
            (hKeeps _ (by decide)).trans hCut.load_base,(hKeeps _ (by decide)).trans hCut.load_count⟩)
      have hRankτ : CutRankStable (d := d) (n := n) F τ :=
        ⟨fun p hp => (hKeeps _ (rankStableOnEmit _ (rankArgName hp))).trans (hRankρ.regs p hp),
          (hMem _).trans hRankρ.one⟩
      have hReadyτ : FormScanReady τ (d+1) n o := moveFormMetadata hS (by
        intro x hx
        simp only [readFormRegisters,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl <;> exact hKeeps _ (by decide))
      exact ⟨τ,r,hNext,hRankτ,hReadyτ,hKeeps _ (by decide),hKeeps _ (by decide),
        fun s _ _ => hMem s,hIn,hOut⟩)

#print axioms rankedFormScan_run
end EvenTI.P18Trial
