import Mathproof.MinimumGenerationVirtualMarkerScan
import Mathproof.MinimumGenerationRankPhysicalSubtract

namespace Mathproof.MinimumGeneration.CayleyQueryGuard

open SearchTransducer
open InputPosition (work)
open Connectivity (AdjBits ustconCell ustconHeaderLength)
open Lax51Proofs.RamToTM (subBits)
open VirtualMarkerScan (boundaryAddresses boundarySymbol)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {W : ℕ} (address : Fin W) (markers : Fin 5 → Fin W) (banks : Fin 2 ↪ Fin W)

private abbrev M := VirtualMarkerScan.machine address markers 0
private abbrev S := RankPhysicalSubtract.machine

private def marked (q : Fin 35) : Option InputCell :=
  let (i,k) := (finProdFinEquiv : Fin 5 × Fin 7 ≃ Fin 35).symm q
  if k = TapeRegisters.done true then some (boundarySymbol i) else none

private def borrow (q : Fin 35) : Bool := decide (q.val = (RankPhysicalSubtract.done true).val)

/-- Literal marker lookup, then a physical comparison for an unmarked address.
A final no-return result marks the adjacency matrix case. -/
abbrev stages : Stages 2 35 W where
  first := 0
  entry i := if i = 0 then (M address markers).initialState else 0
  transition i := if i = 0 then (M address markers).transition else S.padTransition (by decide) banks
  next i q := if i = 0 ∧ (marked q).isNone then some 1 else none

abbrev machine := (stages address markers banks).machine

def result (c : (machine address markers banks).Config) : Option InputCell :=
  let (i,q) := finProdFinEquiv.symm c.state
  if i = 0 then marked q else if borrow q then some (.data true) else none

def start (input : Int) (cells : Fin W → Int → Option Bool) (out : List Bool) :
    (machine address markers banks).Config :=
  (stages address markers banks).tag 0
    ((VirtualMarkerScan.stages address markers 0).tag 0
      (VirtualMarkerScan.entry address markers 0 0 input (fun _ => 0) cells out))

private theorem resultUnique {P : SearchTransducer} {word : List Bool}
    {c d e : P.Config} {a b : ℕ} (ha : P.runFrom word c a = some d) (hb : P.runFrom word c b = some e)
    (da : P.step word d = none) (db : P.step word e = none) : d = e := by
  wlog hab : a ≤ b generalizing a b d e
  · exact (this hb ha db da (by omega)).symm
  by_cases he : a = b
  · subst b
    exact Option.some.inj (ha.symm.trans hb)
  · have h : b = a + 1 + (b - (a + 1)) := by omega
    rw [h, runFrom_add, runFrom, ha, Option.bind_some, da] at hb
    simp at hb

private theorem markerResult (d : (M address markers).Config) :
    marked d.state = (VirtualMarkerScan.verdict address markers 0 d).map boundarySymbol := by
  generalize h : (finProdFinEquiv : Fin 5 × Fin 7 ≃ Fin 35).symm d.state = code
  obtain ⟨i,k⟩ := code
  simp only [marked, VirtualMarkerScan.verdict, h]
  split <;> rfl

private theorem semanticResult {m : ℕ} (bits : AdjBits (Fin m)) (s t : Fin m)
    {word out : List Bool} {B w p : ℕ} {input : Int} {cells : Fin W → Int → Option Bool}
    {d : (M address markers).Config} {a : ℕ}
    (L : VirtualMarkerScan.Layout address markers word B w p (boundaryAddresses s t)
      input (fun _ => 0) cells)
    (run : (M address markers).BoundedSegment word B
      ((VirtualMarkerScan.stages address markers 0).tag 0
        (VirtualMarkerScan.entry address markers 0 0 input (fun _ => 0) cells out)) d a)
    (halt : (M address markers).step word d = none)
    (scope : p ≤ ustconHeaderLength s t ∨ p = ustconHeaderLength s t + m*m + 1) :
    (marked d.state).getD (.data true) = ustconCell bits s t ((p : Int)-1) := by
  obtain ⟨b,e,hRun,hHalt,hCell,_,_,_,_⟩ :=
    VirtualMarkerScan.executeHeader bits s t address markers out L scope
  have he := resultUnique run.1 hRun.1 halt hHalt
  subst e
  change (let (i,k) := (finProdFinEquiv : Fin 5 × Fin 7 ≃ Fin 35).symm d.state
    if k = TapeRegisters.done true then boundarySymbol i else .data true) = _ at hCell
  cases h : (finProdFinEquiv : Fin 5 × Fin 7 ≃ Fin 35).symm d.state with
  | mk i k =>
    simp only [h] at hCell
    simp only [marked, h]
    by_cases b : k = TapeRegisters.done true <;> simpa [b] using hCell

private theorem eqConfig {P : SearchTransducer} (c d : P.Config)
    (a : c.state = d.state) (b : c.inputHead = d.inputHead)
    (h : c.workHead = d.workHead) (s : c.workCell = d.workCell)
    (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem guardEntry (d : (M address markers).Config) (p h w : ℕ)
    (heads : d.workHead = fun _ => 0)
    (source : d.workCell (banks 0) = work (encodeLabel w h))
    (trial : d.workCell (banks 1) = work (encodeLabel w p)) :
    (stages address markers banks).enter (i := 0) 1 d =
      S.padConfig (by decide) banks
        (S.bankConfig banks (RankPhysicalSubtract.cfg 0 0 (encodeLabel w p) (encodeLabel w h)
          d.outputReversed d.inputHead) d.workHead d.workCell) := by
  let c := RankPhysicalSubtract.cfg 0 0 (encodeLabel w p) (encodeLabel w h)
    d.outputReversed d.inputHead
  let e := S.padConfig (by decide : S.states ≤ 35) banks (S.bankConfig banks c d.workHead d.workCell)
  change (stages address markers banks).enter (i := 0) 1 d = e
  refine eqConfig ((stages address markers banks).enter (i := 0) 1 d) e rfl rfl ?_ ?_ rfl
  · funext j
    change d.workHead j = (S.bankConfig banks c d.workHead d.workCell).workHead j
    by_cases hj : j ∈ Set.range banks
    · obtain ⟨i,rfl⟩ := hj
      rw [bankConfig_head_image, heads]
      rfl
    · exact (bankConfig_frame S banks c d.workHead d.workCell hj).1.symm
  · funext j
    change d.workCell j = (S.bankConfig banks c d.workHead d.workCell).workCell j
    by_cases hj : j ∈ Set.range banks
    · obtain ⟨i,rfl⟩ := hj
      rw [bankConfig_cell_image]
      fin_cases i
      · exact source
      · exact trial
    · exact (bankConfig_frame S banks c d.workHead d.workCell hj).2.symm

private theorem subResult (w p h : ℕ) (hp : p < 2^w) (ge : h ≤ p) :
    subBits (encodeLabel w p) (encodeLabel w h) false = encodeLabel w (p-h) := by
  rw [← RankPhysicalSubtract.fixedBits_eq_encodeLabel w p hp,
    ← RankPhysicalSubtract.fixedBits_eq_encodeLabel w h (ge.trans_lt hp),
    ← Lax51Proofs.RamToTM.fixedBits_sub_of_le w ge,
    RankPhysicalSubtract.fixedBits_eq_encodeLabel w (p-h) ((Nat.sub_le _ _).trans_lt hp)]

private theorem resultMarker (d : (M address markers).Config) :
    result address markers banks ((stages address markers banks).tag 0 d) = marked d.state := by
  simp only [result, Stages.tag, Equiv.symm_apply_apply, if_true, eq_self]

private theorem resultGuard (q : Fin 7) (input : Int) (head : Fin W → Int)
    (tape : Fin W → Int → Option Bool) (out : List Bool) :
    let d : ((stages address markers banks).component 1).Config := ⟨q.castLE (by decide : 7 ≤ 35),input,head,tape,out⟩
    result address markers banks ((stages address markers banks).tag 1 d) =
      if q = RankPhysicalSubtract.done true then some (.data true) else none := by
  simp [result, Stages.tag, borrow, Fin.ext_iff]

/-- The lesser-than decision and exact remainder of one raw finite guard. -/
theorem guardSegment {raw : List Bool} {B w p h : ℕ} (d : (M address markers).Config)
    (heads : d.workHead = fun _ => 0)
    (source : d.workCell (banks 0) = work (encodeLabel w h))
    (trial : d.workCell (banks 1) = work (encodeLabel w p))
    (inputGood : (-1 : Int) ≤ d.inputHead ∧ d.inputHead ≤ raw.length)
    (space : w+1 ≤ B) (fitP : p < 2^w) (fitH : h < 2^w) :
    let T := stages address markers banks
    ∃ e : (T.component 1).Config,
      (T.component 1).BoundedSegment raw B (T.enter (i := 0) 1 d) e (2*w+3) ∧
      (T.component 1).step raw e = none ∧
      result address markers banks (T.tag 1 e) = (if p < h then some (.data true) else none) ∧
      e.inputHead = d.inputHead ∧ e.outputReversed = d.outputReversed ∧ e.workHead = (fun _ => 0) ∧
      (∀ j ≠ banks 1, e.workCell j = d.workCell j) ∧
      (h ≤ p → e.workCell (banks 1) = work (encodeLabel w (p-h))) := by
  let T := stages address markers banks
  let z₁ := RankPhysicalSubtract.cfg (RankPhysicalSubtract.done (decide (p<h))) 0
    (subBits (encodeLabel w p) (encodeLabel w h) false) (encodeLabel w h)
    d.outputReversed d.inputHead
  obtain ⟨sub, stopped⟩ := RankPhysicalSubtract.execute_encoded raw d.outputReversed d.inputHead w p h
    inputGood fitP fitH
  let b₁ := S.bankConfig banks z₁ d.workHead d.workCell
  let b := S.padConfig (by decide : S.states ≤ 35) banks b₁
  have lifted := relocateBanks_segment S banks (heads := d.workHead) (cells := d.workCell)
    (PhysicalEntry.segment_mono sub space) (by simp [heads])
  have padded := S.padMachine_segment (by decide : S.states ≤ 35) banks lifted
  have entry := guardEntry address markers banks d p h w heads source trial
  have stop := relocateBanks_step S banks raw z₁ d.workHead d.workCell
  have padStop := S.padMachine_step (by decide : S.states ≤ 35) banks raw b₁
  have bstop : (T.component 1).step raw b = none :=
    padStop.trans (congrArg _ (stop.trans (congrArg _ stopped)))
  have tagAnswer := resultGuard address markers banks (RankPhysicalSubtract.done (decide (p<h)))
    b.inputHead b.workHead b.workCell b.outputReversed
  refine ⟨b, entry ▸ padded, bstop, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tagAnswer.trans (by by_cases h' : p<h <;> simp [h', RankPhysicalSubtract.done])
  · funext j
    by_cases hj : j ∈ Set.range banks
    · obtain ⟨k,rfl⟩ := hj
      exact bankConfig_head_image S banks z₁ d.workHead d.workCell k
    · exact (bankConfig_frame S banks z₁ d.workHead d.workCell hj).1.trans (congrFun heads j)
  · intro j neq
    by_cases hj : j ∈ Set.range banks
    · obtain ⟨k,rfl⟩ := hj
      fin_cases k
      · exact (bankConfig_cell_image S banks z₁ d.workHead d.workCell 0).trans source.symm
      · exact (neq rfl).elim
    · exact (bankConfig_frame S banks z₁ d.workHead d.workCell hj).2
  · intro ge
    exact (bankConfig_cell_image S banks z₁ d.workHead d.workCell 1).trans
      (congrArg work (subResult w p h fitP ge))

/-- On any prepared virtual address, route header and endmarker returns.
The matrix branch prepares its relative address in the actual scratch bank. -/
theorem execute {m : ℕ} (bits : AdjBits (Fin m)) (s t : Fin m)
    {raw prior : List Bool} {B w p : ℕ} {input : Int} {cells : Fin W → Int → Option Bool}
    (L : VirtualMarkerScan.Layout address markers raw B w p (boundaryAddresses s t)
      input (fun _ => 0) cells) (space : w+1 ≤ B)
    (liveHeader : cells (banks 0) = work (encodeLabel w (ustconHeaderLength s t + 1)))
    (liveTrial : cells (banks 1) = work (encodeLabel w p)) :
    ∃ len z, (machine address markers banks).BoundedSegment raw B
        (start address markers banks input cells prior) z len ∧
      (machine address markers banks).step raw z = none ∧
      z.inputHead = input ∧ z.outputReversed = prior ∧ z.workHead = (fun _ => 0) ∧
      (∀ j ≠ banks 1, z.workCell j = cells j) ∧
      if p ≤ ustconHeaderLength s t ∨ p = ustconHeaderLength s t + m*m + 1 then
        result address markers banks z = some (ustconCell bits s t ((p : Int)-1))
      else result address markers banks z = none ∧
        z.workCell (banks 1) = work (encodeLabel w (p-(ustconHeaderLength s t+1))) := by
  let T := stages address markers banks
  let h := ustconHeaderLength s t + 1
  obtain ⟨a,d,markRun,markStop,inp,head,tapes,prints,positive,negative⟩ :=
    VirtualMarkerScan.execute address markers prior L (0 : Fin 5) (0 : Fin 5)
  have walk := T.segment_component 0 markRun
  cases hm : marked d.state with
  | some value =>
    have hn : T.next 0 d.state = none := by simp [T, hm]
    have hstop := T.step_halt 0 markStop
    rw [hn] at hstop
    have position : p ≤ ustconHeaderLength s t ∨ p = ustconHeaderLength s t + m*m + 1 := by
      rw [markerResult address markers] at hm
      obtain ⟨j, hj, _⟩ := Option.map_eq_some_iff.mp hm
      have jHits := positive j hj
      fin_cases j <;> simp [boundaryAddresses] at jHits ⊢ <;> unfold ustconHeaderLength at * <;> omega
    have hvalue := semanticResult address markers bits s t L markRun markStop position
    rw [hm] at hvalue
    exact ⟨a, T.tag 0 d, walk, hstop, inp, prints, head, fun j _ => congrFun tapes j,
      by rw [if_pos position, resultMarker address markers banks d, hm]; exact congrArg some hvalue⟩
  | none =>
    have nohit : VirtualMarkerScan.verdict address markers 0 d = none := by
      rw [markerResult address markers] at hm
      exact Option.map_eq_none_iff.mp hm
    have endNotEq : p ≠ ustconHeaderLength s t + m*m + 1 := by
      simpa [boundaryAddresses] using negative nohit (4 : Fin 5) (by decide)
    have next : T.next 0 d.state = some 1 := by simp [T, hm]
    have transition := T.segment_handoff (i := 0) (j := 1) markStop next (markRun.2 _ le_rfl _ markRun.1)
    have fitH : h < 2^w := by
      dsimp [h]
      have cap := L.markerFit (4 : Fin 5)
      simp [boundaryAddresses] at cap
      omega
    have inputGood : (-1 : Int) ≤ d.inputHead ∧ d.inputHead ≤ raw.length := by rw [inp]; exact L.realBounds
    obtain ⟨b,sub,bstop,dest,bInput,bOutput,bHeads,bKeep,scratch⟩ :=
      guardSegment address markers banks d head
        ((congrFun tapes _).trans liveHeader) ((congrFun tapes _).trans liveTrial)
        inputGood space L.addressFit fitH
    have terminal : T.next 1 b.state = none := rfl
    have finishHalt := T.step_halt 1 bstop
    rw [terminal] at finishHalt
    have total := BoundedSegment.append _ (BoundedSegment.append _ walk transition)
      (T.segment_component 1 sub)
    refine ⟨a+1+(2*w+3), T.tag 1 b,total,finishHalt,bInput.trans inp,bOutput.trans prints,bHeads,
      (fun j neq => (bKeep j neq).trans (congrFun tapes j)),?_⟩
    by_cases isHeader : p ≤ ustconHeaderLength s t
    · rw [if_pos (.inl isHeader)]
      have hlt : p < h := by dsimp [h]; omega
      have exactCell := semanticResult address markers bits s t L markRun markStop (.inl isHeader)
      rw [hm] at exactCell
      rw [dest, if_pos hlt]
      exact congrArg some exactCell
    · rw [if_neg (not_or.mpr ⟨isHeader,endNotEq⟩)]
      have hge : h ≤ p := by dsimp [h]; omega
      exact ⟨dest.trans (if_neg (Nat.not_lt.mpr hge)), scratch hge⟩

end Mathproof.MinimumGeneration.CayleyQueryGuard
