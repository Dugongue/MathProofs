import EvenP18TrialRankReady

set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 18000

namespace EvenTI.P18Trial

open EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rankedCutBlockVisit (D : FieldEncoding K) (F : FieldPresentation K) (emit : Com) : Com :=
  .seq (rankReadyVisit D F) (.ite (.eq (.var cutRankAccept) (.lit 1)) emit .skip)

private theorem rankArgName {d n src R A O Z e : ℕ} {p : String × ℕ}
    (h : p ∈ cutRankArgs d n src R A O Z e) : p.1 ∈ cutRankArgNames := by
  change p.1 ∈ (cutRankArgs d n src R A O Z e).map Prod.fst
  exact List.mem_map.mpr ⟨p,h,rfl⟩

private theorem rankArgCapFresh : ∀ r ∈ cutRankArgNames,
    r ∉ ["left","d","n","i","r",cutChoiceLength] := by decide

private theorem rankArgCursorFresh : cutChoiceIndex ∉ cutRankArgNames := by decide

noncomputable def rankedBlockWords (D : FieldEncoding K) (F : FieldPresentation K) {d n c : ℕ}
    (σ : Env) (j : Fin 4) (render : (Coord (d+1) n → K) → List ℕ) (i : ℕ) : List ℕ :=
  if h : i < Fintype.card K^c then
    let x := cutIndexedForm D F (d := d) (n := n) σ j ⟨i,h⟩
    if rawRetainedFullRank x then render x else []
  else []

/-- The cap loop reconstructs a shared-basis form, checks every retained
rank, and emits an arbitrary verified renderer's block on the good branch.
The renderer receives the actual live form and a proved true rank gate. -/
theorem scanRankedBlocks_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B d n c budget : ℕ} {σ : Env} (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1)) + n^(d+1) + n^(d+1) + 10 < B)
    (hChoice : (n^(d+1)+Fintype.card K+1)*(n^(d+1)+Fintype.card K+1) < B)
    (hLive : σ.vars (nullityAt j)=c) (hBudget : σ.vars cutChoiceBudget=budget) (hnB : budget ≤ n^(d+1))
    (hRank : CutRankStable (d := d) (n := n) F σ) (emit : Com) (cost : ℕ)
    (render : (Coord (d+1) n → K) → List ℕ) (extra : Env → Prop)
    (hExtra : ∀ ρ, ρ.arrs=σ.arrs →
      (∀ r, r ∉ ["left","d","n","i","r",cutChoiceLength] → ρ.vars r=σ.vars r) → extra ρ)
    (hSetExtra : ∀ ρ k, extra ρ → extra (ρ.setVar cutChoiceIndex k))
    (hRankExtra : ∀ ρ η, (∀ r, RankedRegisterFixed r → η.vars r=ρ.vars r) → extra ρ → extra η) :
    let m := n^(d+1); let z := constantsBase.value m
    let C (ρ : Env) := CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) F ρ
      (augmentedMatrixBase.value m) ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3)
    C σ →
    (∀ ρ (x : Coord (d+1) n → K),
      C ρ → CutRankStable (d := d) (n := n) F ρ → extra ρ →
      (∀ u, val F canonical qN.WS ρ
        (placedRankSource m+(inputCoordOrder n (d+1) u).val)=x u) →
      rawRetainedFullRank x=true →
      ∃ τ, Run B emit ρ τ cost ∧ C τ ∧ CutRankStable (d := d) (n := n) F τ ∧ extra τ ∧
        τ.vars cutChoiceIndex=ρ.vars cutChoiceIndex ∧ τ.vars cutChoiceLength=ρ.vars cutChoiceLength ∧
        (∀ s < z, firstOutputBase.value m ≤ s → val F canonical qN.WS τ s=val F canonical qN.WS ρ s) ∧
        τ.inp=ρ.inp ∧ τ.out=ρ.out++render x) →
    let q := Fintype.card K
    let N := cappedCutChoiceCount q c budget
    ∃ τ, Run B (cappedCutScanWith q (rankedCutBlockVisit D F emit) j) σ τ
      (30*(m+q)+42 + (((rankReadyVisitCost F d m c+(5+cost))+8)*N+6)) ∧
      C τ ∧ CutRankStable (d := d) (n := n) F τ ∧ extra τ ∧
      (∀ s < z, firstOutputBase.value m ≤ s → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out++(List.range N).flatMap (rankedBlockWords D F (c := c) σ j render) := by
  dsimp only
  intro hW hEmit
  let m := n^(d+1)
  let z := constantsBase.value m
  let pivot := firstOutputBase.value m
  let b := (outputBase j).value m
  let stable := fun (ρ : Env) => CutRankStable (d := d) (n := n) F ρ ∧ extra ρ
  have hb : pivot ≤ b := by rw [show b = _ from outputBase_value m j]; omega
  have hCutM : b+m*m ≤ z := outputBank_point_upper m j
  have hLarge : 1 < B := by omega
  have hInit (ρ : Env) (ha : ρ.arrs=σ.arrs)
      (hf : ∀ r, r ∉ ["left","d","n","i","r",cutChoiceLength] → ρ.vars r=σ.vars r) : stable ρ := by
    refine ⟨⟨fun p hp => (hf _ (rankArgCapFresh _ (rankArgName hp))).trans (hRank.regs p hp),?_⟩,
      hExtra ρ ha hf⟩
    exact (cutSlot_value_frame F (congrFun ha canonical.mem) (hf _ (by decide)) _).trans hRank.one
  have hSet (ρ : Env) (k : ℕ) (h : stable ρ) : stable (ρ.setVar cutChoiceIndex k) := by
    refine ⟨⟨fun p hp => ?_,(val_setVar F canonical (by decide : cutChoiceIndex≠qN.WS) ρ k _).trans h.1.one⟩,
      hSetExtra ρ k h.2⟩
    have hne : p.1 ≠ cutChoiceIndex := fun e => rankArgCursorFresh (e ▸ rankArgName hp)
    simpa only [vars_setVar,if_neg hne] using h.1.regs p hp
  obtain ⟨τ,r,hC,hMem,hS,_,hIn,hOut⟩ := cappedCutBlockScan_run F (rankedCutBlockVisit D F emit)
    (rankReadyVisitCost F d m c+(5+cost)) (rankedBlockWords D F (c := c) σ j render) stable pivot
    j hW hLive hBudget hnB hChoice hInit hSet (by
      intro ρ v hs hρ hBank hq hPow hIdx
      let x := cutIndexedForm D F (d := d) (n := n) σ j v
      have hx : cutIndexedForm D F (d := d) (n := n) ρ j v=x := by
        funext u
        unfold x cutIndexedForm
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val*m+(inputCoordOrder n (d+1) u).val < m*m :=
          outputPoint_lt hρ.frame.layout.nullity i (inputCoordOrder n (d+1) u)
        let p := b+(i.val*m+(inputCoordOrder n (d+1) u).val)
        have hLo : pivot ≤ p := hb.trans (Nat.le_add_right _ _)
        have hHi : p<z := (Nat.add_lt_add_left hi b).trans_le hCutM
        exact congrArg (fun y => coefficients D c v i*y) (hBank p hHi hLo)
      obtain ⟨α,hr,hA,hR,hX,hBit,hDec,hKeep,hVars,hI,hO⟩ :=
        rankReadyVisit_run D F j hd hn hB hs.1 hρ v hIdx hq hPow
      rw [hx] at hX hDec
      have hEx := hRankExtra ρ α hVars hs.2
      have hIdxα := (hVars cutChoiceIndex (by decide)).trans hIdx
      have hLenα := hVars cutChoiceLength (by decide)
      have hGuard := evalB_condEq
        (evalB_var (σ := α) (x := cutRankAccept) (hBit.trans_lt hLarge)) (evalB_lit hLarge)
      have hPayload : rankedBlockWords D F (c := c) σ j render v.val =
          if rawRetainedFullRank x then render x else [] := by
        simp only [rankedBlockWords,dif_pos v.isLt,x]
      by_cases hYes : α.vars cutRankAccept=1
      · have hTrue := hDec.mp hYes
        have hGuard' : (Cond.eq (.var cutRankAccept) (.lit 1)).evalB B α=some true := by
          simpa [hYes] using hGuard
        obtain ⟨η,re,hη,hStableη,hExtraη,hIdxη,hLenη,hKeepη,hInη,hOutη⟩ :=
          hEmit α x hA hR hEx hX hTrue
        have r := hr.seq (Run.ite_true (d := .skip) hGuard' re)
        refine ⟨η,r.mono (by simp only [m,Cond.size,Expr.size]; omega),hη,⟨hStableη,hExtraη⟩,hIdxη.trans hIdxα,hLenη.trans hLenα,
          fun s hi hlo => (hKeepη s hi hlo).trans (hKeep s hi hlo),hInη.trans hI,?_⟩
        rw [hOutη,hO,hPayload,hTrue,if_pos rfl]
      · have hFalse := Bool.eq_false_iff.mpr (fun hTrue => hYes (hDec.mpr hTrue))
        have hGuard' : (Cond.eq (.var cutRankAccept) (.lit 1)).evalB B α=some false := by
          simpa [hYes] using hGuard
        have r := hr.seq (Run.ite_false (c := emit) hGuard' Run.skip)
        refine ⟨α,r.mono (by simp only [m,Cond.size,Expr.size]; omega),hA,⟨hR,hEx⟩,hIdxα,hLenα,hKeep,hI,?_⟩
        rw [hO,hPayload,hFalse]
        simp)
  exact ⟨τ,r,hC,hS.1,hS.2,hMem,hIn,hOut⟩

#print axioms scanRankedBlocks_run
end EvenTI.P18Trial
