import Mathproof.MinimumGenerationGreedyGenerator
import Mathproof.MinimumGenerationTapeRegisters
import Mathproof.MinimumGenerationPhysicalEntry
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.GreedyTapeScan

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

variable {S W : Nat}

structure BitCall (S W : Nat) where
  entry : Fin S
  transition : MacroTransition S W
  answer : Fin S → Bool

private def identityBanks : Fin W ↪ Fin W := Function.Embedding.refl _

private abbrev comparator (label order : Fin W) := TapeRegisters.machine label order .compare

private abbrev incrementer (label : Fin W) := TapeArithmetic.machine label .increment

/-- Compare against the order, test eligibility, query membership in the
eligible prefix, and increment on rejection. Both callbacks use the live
candidate bank. The loop keeps no list of earlier labels. -/
abbrev stages (label order : Fin W) (widthStates : 7 ≤ S)
    (allowed member : BitCall S W) : Stages 4 S W where
  first := 0
  entry i := if i = 0 then (comparator label order).initialState.castLE widthStates
    else if i = 1 then allowed.entry
    else if i = 2 then member.entry
    else (incrementer label).initialState.castLE (by change 5 ≤ S; omega)
  transition i := if i = 0 then (comparator label order).padTransition widthStates identityBanks
    else if i = 1 then allowed.transition
    else if i = 2 then member.transition
    else (incrementer label).padTransition (by change 5 ≤ S; omega) identityBanks
  next i q := if i = 0 then
    if q.val = (TapeRegisters.done true).val then none else some 1
    else if i = 1 then if allowed.answer q then some 2 else some 3
    else if i = 2 then if member.answer q then some 3 else none
    else some 0

variable (label order : Fin W) (widthStates : 7 ≤ S) (allowed member : BitCall S W)

abbrev machine := (stages label order widthStates allowed member).machine

def found (c : (machine label order widthStates allowed member).Config) : Bool :=
  decide ((finProdFinEquiv.symm c.state).1 = (2 : Fin 4))

/-- A prepared cursor describes data already on the physical tapes. All heads
are parked while transferring control between the callbacks. -/
structure Prepared {M : SearchTransducer} (word : List Bool) (n k : Nat)
    (atLabel atOrder : Fin M.workTapes) (c : M.Config) : Prop where
  inputLo : (-1 : Int) ≤ c.inputHead
  inputHi : c.inputHead ≤ (word.length : Int)
  heads : c.workHead = fun _ => 0
  cursor : c.workCell atLabel = work (encodeLabel (TableIO.width n) k)
  order : c.workCell atOrder = work (encodeLabel (TableIO.width n) n)

/-- Callback contracts bound physical prefixes from the designated entry. They preserve only the
specified frame, including the live candidate and order banks. -/
def Leaf {n B : Nat} (word : List Bool) (i : Fin 4)
    (test : Fin n → Bool) (answer : Fin S → Bool) (keep : Set (Fin W)) :=
  let T := stages label order widthStates allowed member
  let P := T.component i
  ∀ (x : Fin n) (c : P.Config),
    c.state = T.entry i → Prepared word n x.val label order c →
    ∃ (k : Nat) (d : P.Config), P.BoundedSegment word B c d k ∧ P.step word d = none ∧
      answer d.state = test x ∧ Prepared word n x.val label order d ∧
      d.outputReversed = c.outputReversed ∧
      ∀ j ∈ keep, d.workCell j = c.workCell j

private theorem work_left (xs : List Bool) : work xs 0 = none := by simp [work]

private theorem work_right (xs : List Bool) : work xs ((xs.length : Int) + 1) = none := by
  simp [work, show ¬ ((xs.length : Int) + 1 ≤ 0) by omega]

private theorem work_block (xs : List Bool) : TapeArithmetic.block (work xs) 1 xs := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem update_exact (old new : List Bool) (hWidth : old.length = new.length)
    (cell : Int → Option Bool) (hNew : TapeArithmetic.block cell 1 new)
    (hOutside : ∀ p, p < 1 ∨ (old.length : Int) + 1 ≤ p → cell p = work old p) :
    cell = work new := by
  funext p
  by_cases hlo : p < 1
  · simp [hOutside p (.inl hlo), work, show p ≤ 0 by omega]
  by_cases hhi : (old.length : Int) + 1 ≤ p
  · rw [hOutside p (.inr hhi)]
    have hpos : ¬ p ≤ 0 := by omega
    simp only [work, if_neg hpos, List.getElem?_eq_none (show old.length ≤ (p - 1).toNat by omega),
      List.getElem?_eq_none (show new.length ≤ (p - 1).toNat by omega)]
  let i : Fin new.length := ⟨(p - 1).toNat, by omega⟩
  have hp : (1 : Int) + i.val = p := by dsimp [i]; omega
  rw [← hp]
  exact (hNew i).trans ((work_block new) i).symm

private theorem label_eq_iff (n k : Nat) (hk : k ≤ n) :
    encodeLabel (TableIO.width n) k = encodeLabel (TableIO.width n) n ↔ k = n := by
  constructor
  · intro h
    have hz : n < 2 ^ TableIO.width n := Nat.lt_log2_self
    have := congrArg InputPosition.digits h
    rw [InputPosition.digits_encodeLabel _ _ (hk.trans_lt hz),
      InputPosition.digits_encodeLabel _ _ hz] at this
    exact this
  · rintro rfl
    rfl

private theorem cfg_eq {P : SearchTransducer} (c d : P.Config)
    (hs : c.state = d.state) (hi : c.inputHead = d.inputHead)
    (hh : c.workHead = d.workHead) (hc : c.workCell = d.workCell)
    (ho : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem wholeBankHead (P : SearchTransducer) (c : P.Config) (h : Fin P.workTapes → Int)
    (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig identityBanks c h m).workHead = c.workHead := by
  funext i
  exact P.bankConfig_head_image identityBanks c h m i

private theorem wholeBankCell (P : SearchTransducer) (c : P.Config) (h : Fin P.workTapes → Int)
    (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig identityBanks c h m).workCell = c.workCell := by
  funext i
  exact P.bankConfig_cell_image identityBanks c h m i

private theorem projectPad (P : SearchTransducer) (hS : P.states ≤ S)
    (c : P.Config) (h : Fin P.workTapes → Int) (m : Fin P.workTapes → Int → Option Bool) :
    let d := P.padConfig hS identityBanks (P.bankConfig identityBanks c h m)
    d.workHead = c.workHead ∧ d.workCell = c.workCell :=
  ⟨wholeBankHead P c h m, wholeBankCell P c h m⟩

private theorem compareSegment {word : List Bool} {n k B : Nat}
    (hK : k ≤ n) (hB : TableIO.width n + 1 ≤ B)
    (c : ((stages label order widthStates allowed member).component 0).Config)
    (hState : c.state = (stages label order widthStates allowed member).entry 0)
    (hc : Prepared word n k label order c) :
    let T := stages label order widthStates allowed member
    ∃ d : (T.component 0).Config,
      (T.component 0).BoundedSegment word B c d (2 * TableIO.width n + 3) ∧
      (T.component 0).step word d = none ∧
      (d.state.val = (TapeRegisters.done true).val ↔ k = n) ∧
      d.inputHead = c.inputHead ∧ d.workHead = c.workHead ∧ d.workCell = c.workCell ∧
      d.outputReversed = c.outputReversed := by
  let w := TableIO.width n
  let a := encodeLabel w k
  let b := encodeLabel w n
  let M := comparator label order
  let entry : M.Config := ⟨0, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩
  have hwₐ : a.length = w := length_encodeLabel _ _
  have hwᵦ : b.length = w := length_encodeLabel _ _
  obtain ⟨z, yes, run, state, v, hh, cells, input, output⟩ :=
    TapeRegisters.executeCompare (source := label) (target := order) word entry a b
      (hwₐ.trans hwᵦ.symm) rfl
      (by simp [entry, hc.heads, hc.order])
      (by simpa [entry, hc.heads, hc.cursor, hwₐ, w] using work_right a)
      (by simpa [entry, hc.heads, hc.order, hwₐ, hwᵦ, w] using work_right b)
      (by simpa [entry, hc.heads, hc.cursor] using work_block a)
      (by simpa [entry, hc.heads, hc.order] using work_block b)
  have hseg := run.boundedSegment (B := B) (by exact ⟨hc.inputLo, hc.inputHi⟩) (by
    intro i j hlo hhi
    have hlo' : 0 ≤ j := by simpa [entry, hc.heads] using hlo
    have hu : j ≤ (w : Int) + 1 := by
      unfold TapeRegisters.finish at hhi
      split at hhi
      · simpa [entry, hc.heads, hwₐ] using hhi
      · simp [entry, hc.heads] at hhi
        omega
    have habs := Int.natAbs_of_nonneg hlo'
    omega)
  rw [hwₐ] at hseg
  let h := c.workHead
  let m := c.workCell
  let entry' := M.padConfig widthStates identityBanks (M.bankConfig identityBanks entry h m)
  let exit := M.padConfig widthStates identityBanks (M.bankConfig identityBanks z h m)
  have hf : ∀ i ∉ Set.range identityBanks, (h i).natAbs ≤ B := by simp [h, hc.heads]
  have hs := M.padMachine_segment widthStates identityBanks
    (M.relocateBanks_segment identityBanks hseg (heads := h) (cells := m) hf)
  have he : entry' = c := cfg_eq _ _ (by exact hState.symm) rfl
    (projectPad M widthStates entry h m).1 (projectPad M widthStates entry h m).2 rfl
  change ((stages label order widthStates allowed member).component 0).BoundedSegment word B entry' exit _ at hs
  rw [he] at hs
  refine ⟨exit, hs, ?_, ?_, input,
    (projectPad M widthStates z h m).1.trans hh,
    (projectPad M widthStates z h m).2.trans cells, output⟩
  · change (M.padMachine widthStates identityBanks).step word exit = none
    unfold exit
    rw [M.padMachine_step, M.relocateBanks_step, TapeRegisters.step_done word z yes state]
    rfl
  · change z.state.val = (TapeRegisters.done true).val ↔ _
    rw [state]
    have hFlag : (TapeRegisters.done yes).val = (TapeRegisters.done true).val ↔ yes = true := by
      cases yes <;> decide
    exact hFlag.trans (v.trans (label_eq_iff n k hK))

private theorem incrementSegment {word : List Bool} {n k B : Nat}
    (hB : TableIO.width n + 1 ≤ B)
    (c : ((stages label order widthStates allowed member).component 3).Config)
    (hState : c.state = (stages label order widthStates allowed member).entry 3)
    (hc : Prepared word n k label order c) (different : label ≠ order) :
    let T := stages label order widthStates allowed member
    ∃ d : (T.component 3).Config,
      (T.component 3).BoundedSegment word B c d (2 * TableIO.width n + 3) ∧
      (T.component 3).step word d = none ∧
      Prepared word n (k + 1) label order d ∧
      d.outputReversed = c.outputReversed ∧
      ∀ j, j ≠ label → d.workCell j = c.workCell j := by
  let w := TableIO.width n
  let a := encodeLabel w k
  let a' := encodeLabel w (k + 1)
  let M := incrementer label
  let hFit : M.states ≤ S := by change 5 ≤ S; omega
  let entry : M.Config := ⟨0, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩
  have hwₐ : a.length = w := length_encodeLabel _ _
  have hwᵦ : a'.length = w := length_encodeLabel _ _
  obtain ⟨z, run, state, head, content, frame⟩ :=
    TapeArithmetic.executeIncrement (bank := label) word entry w k rfl
      (by simp [entry, hc.heads, hc.cursor])
      (by simpa [entry, hc.heads, hc.cursor, hwₐ, w] using work_right a)
      (by simpa [entry, hc.heads, hc.cursor] using work_block a)
  have hseg := TapeRegisters.arithmeticBoundedSegment (B := B) run
    (by exact ⟨hc.inputLo, hc.inputHi⟩)
    (by
      intro j hlo hhi
      have hj : 0 ≤ j := by simpa [entry, hc.heads] using hlo
      have hu : j ≤ (w : Int) + 1 := by simpa [entry, hc.heads] using hhi
      have habs := Int.natAbs_of_nonneg hj
      omega)
    (by simp [entry, hc.heads])
  have hContent : z.workCell label = work a' := by
    apply update_exact a a' (hwₐ.trans hwᵦ.symm)
    · simpa [entry, hc.heads] using content
    · intro j hj
      rw [← hc.cursor]
      exact frame.cells label j (Or.inr (by simpa [entry, hc.heads, hwₐ] using hj))
  let h := c.workHead
  let m := c.workCell
  let entry' := M.padConfig hFit identityBanks (M.bankConfig identityBanks entry h m)
  let exit := M.padConfig hFit identityBanks (M.bankConfig identityBanks z h m)
  have hf : ∀ i ∉ Set.range identityBanks, (h i).natAbs ≤ B := by simp [h, hc.heads]
  have hs := M.padMachine_segment hFit identityBanks
    (M.relocateBanks_segment identityBanks hseg (heads := h) (cells := m) hf)
  have he : entry' = c := cfg_eq _ _ (by exact hState.symm) rfl
    (projectPad M hFit entry h m).1 (projectPad M hFit entry h m).2 rfl
  change ((stages label order widthStates allowed member).component 3).BoundedSegment word B entry' exit _ at hs
  rw [he] at hs
  have hFixed (j : Fin W) (hj : j ≠ label) : exit.workCell j = c.workCell j :=
    (congrFun (projectPad M hFit z h m).2 j).trans (funext fun p => frame.cells j p (.inl hj))
  refine ⟨exit, hs, ?_, ?_, frame.output, hFixed⟩
  · change (M.padMachine hFit identityBanks).step word exit = none
    unfold exit
    rw [M.padMachine_step, M.relocateBanks_step, TapeArithmetic.step_done word z state]
    rfl
  · refine ⟨by change (-1 : Int) ≤ z.inputHead; rw [frame.input]; exact hc.inputLo,
      by change z.inputHead ≤ (word.length : Int); rw [frame.input]; exact hc.inputHi,
      ?_, ?_, (hFixed order different.symm).trans hc.order⟩
    · rw [(projectPad M hFit z h m).1]
      funext j
      by_cases hj : j = label
      · subst j
        exact head.trans (congrFun hc.heads _)
      · exact (frame.heads j hj).trans (congrFun hc.heads _)
    · exact (congrFun (projectPad M hFit z h m).2 label).trans hContent


private theorem next_step {n k : Nat} (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Fin n → Bool) (hk : k < n) :
    GreedyGenerator.next query eligible k =
      if GreedyGenerator.accept query eligible ⟨k, hk⟩ then some ⟨k, hk⟩
      else GreedyGenerator.next query eligible (k+1) := by
  unfold GreedyGenerator.next
  conv_lhs => rw [show n - k = (n - (k+1)) + 1 by omega]
  simp only [ChiefExecution.firstHitFrom, dif_pos hk]

private theorem foundAt (i : Fin 4) (c : ((stages label order widthStates allowed member).component i).Config) :
    found label order widthStates allowed member ((stages label order widthStates allowed member).tag i c)
      = decide (i = (2 : Fin 4)) := by
  simp [found, Stages.tag]

private theorem scanRoute {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (hKeep : label ∉ keep) (different : label ≠ order)
    (hB : TableIO.width n + 1 ≤ B)
    (hEligible : Leaf label order widthStates allowed member (B := B) word 1 eligible allowed.answer keep)
    (hMember : Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer keep)
    (k : Nat) (hk : k ≤ n)
    (c : ((stages label order widthStates allowed member).component 0).Config)
    (hEntry : c.state = (stages label order widthStates allowed member).entry 0)
    (hc : Prepared word n k label order c) :
    let T := stages label order widthStates allowed member
    let expected := GreedyGenerator.next query eligible k
    ∃ (ticks : Nat) (phase : Fin 4) (d : (T.component phase).Config),
      T.Routed word B 0 c phase d ticks ∧ (T.component phase).step word d = none ∧
      T.next phase d.state = none ∧
      found label order widthStates allowed member (T.tag phase d) = expected.isSome ∧
      (∀ x : Fin n, expected = some x → Prepared word n x.val label order d) ∧
      (expected = none → Prepared word n n label order d) ∧
      d.outputReversed = c.outputReversed ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  let T := stages label order widthStates allowed member
  obtain ⟨tested, hCmp, hStop, hEqual, hInput, hHeads, hCells, hOut⟩ :=
    compareSegment label order widthStates allowed member hk hB c hEntry hc
  have hData : Prepared word n k label order tested :=
    ⟨hInput.symm ▸ hc.inputLo, hInput.symm ▸ hc.inputHi, hHeads.trans hc.heads,
      (congrFun hCells label).trans hc.cursor, (congrFun hCells order).trans hc.order⟩
  by_cases hEnd : k = n
  · have hDone : T.next 0 tested.state = none := by simp [T, stages, hEqual.mpr hEnd]
    have expected : GreedyGenerator.next query eligible k = none := by
      simp [GreedyGenerator.next, hEnd, ChiefExecution.firstHitFrom]
    refine ⟨_, 0, tested, .finish hCmp, hStop, hDone, ?_, ?_, ?_, hOut, fun j _ => congrFun hCells j⟩
    · rw [foundAt, expected]
      rfl
    · intro x hx
      rw [expected] at hx
      contradiction
    · intro _
      simpa [hEnd] using hData
  have hlt : k < n := by omega
  let x : Fin n := ⟨k, hlt⟩
  have goAllow : T.next 0 tested.state = some 1 := by
    simp [T, stages, hEqual, hEnd]
  have advance (v : (T.component 3).Config) (he : v.state = T.entry 3)
      (hv : Prepared word n k label order v) :
      ∃ (l : Nat) (f : Fin 4) (z : (T.component f).Config),
        T.Routed word B 3 v f z l ∧ (T.component f).step word z = none ∧ T.next f z.state = none ∧
        found label order widthStates allowed member (T.tag f z) =
          (GreedyGenerator.next query eligible (k+1)).isSome ∧
        (∀ a : Fin n, GreedyGenerator.next query eligible (k+1) = some a → Prepared word n a.val label order z) ∧
        (GreedyGenerator.next query eligible (k+1) = none → Prepared word n n label order z) ∧
        z.outputReversed = v.outputReversed ∧ ∀ j ∈ keep, z.workCell j = v.workCell j := by
    obtain ⟨inc, run, stop, prep, out, fixed⟩ :=
      incrementSegment label order widthStates allowed member hB v he hv different
    have routeBack : T.next 3 inc.state = some 0 := by rfl
    have prep' : Prepared word n (k+1) label order (T.enter 0 inc) :=
      ⟨prep.inputLo, prep.inputHi, prep.heads, prep.cursor, prep.order⟩
    obtain ⟨rest, f, z, hRun, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hFrame⟩ :=
      scanRoute query eligible keep hKeep different hB hEligible hMember
        (k+1) (by omega) (T.enter 0 inc) rfl prep'
    exact ⟨_, f, z, .call run stop routeBack hRun, hHalt, hFinal, hFound, hLabel, hNone,
      hOutput.trans out, fun j hj => (hFrame j hj).trans (fixed j (fun he => hKeep (he ▸ hj)))⟩
  let a := T.enter 1 tested
  have hEligibleIn : Prepared word n x.val label order a :=
    ⟨hData.inputLo, hData.inputHi, hData.heads, hData.cursor, hData.order⟩
  obtain ⟨p, d, hAllowRun, hAllowStop, hAllowAns, hAllowPrep, hAllowOut, hAllowFrame⟩ :=
    hEligible x a rfl hEligibleIn
  cases hAllow : eligible x with
  | false =>
    have goInc : T.next 1 d.state = some 3 := by
      simp [T, stages, hAllowAns, hAllow, show (1 : Fin 4) ≠ 0 by decide]
    have prep : Prepared word n k label order (T.enter 3 d) :=
      ⟨hAllowPrep.inputLo, hAllowPrep.inputHi, hAllowPrep.heads, hAllowPrep.cursor, hAllowPrep.order⟩
    obtain ⟨l, f, z, tail, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hFrame⟩ :=
      advance (T.enter 3 d) rfl prep
    have hNext : GreedyGenerator.next query eligible k = GreedyGenerator.next query eligible (k+1) := by
      rw [next_step query eligible hlt]
      change (if GreedyGenerator.accept query eligible x then _ else _) = _
      simp [GreedyGenerator.accept, hAllow]
    refine ⟨_, f, z, .call hCmp hStop goAllow (.call hAllowRun hAllowStop goInc tail),
      hHalt, hFinal, ?_, ?_, ?_, hOutput.trans (hAllowOut.trans hOut), ?_⟩
    · rwa [hNext]
    · rwa [hNext]
    · rwa [hNext]
    · intro j hj
      exact (hFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j))
  | true =>
    have goMember : T.next 1 d.state = some 2 := by
      simp [T, stages, hAllowAns, hAllow, show (1 : Fin 4) ≠ 0 by decide]
    let m := T.enter 2 d
    have prepMem : Prepared word n x.val label order m :=
      ⟨hAllowPrep.inputLo, hAllowPrep.inputHi, hAllowPrep.heads, hAllowPrep.cursor, hAllowPrep.order⟩
    obtain ⟨r, checked, hQueryRun, hQueryStop, hQueryAns, hQueryPrep, hQueryOut, hQueryFrame⟩ :=
      hMember x m rfl prepMem
    cases hQuery : query (GreedyGenerator.before eligible x.val) x with
    | false =>
      have halt : T.next 2 checked.state = none := by
        simp [T, stages, hQueryAns, hQuery, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
      have hNext : GreedyGenerator.next query eligible k = some x := by
        rw [next_step query eligible hlt]
        change (if GreedyGenerator.accept query eligible x then _ else _) = _
        simp [GreedyGenerator.accept, hAllow, hQuery]
        rfl
      refine ⟨_, 2, checked, .call hCmp hStop goAllow (.call hAllowRun hAllowStop goMember (.finish hQueryRun)),
        hQueryStop, halt, ?_, ?_, ?_, hQueryOut.trans (hAllowOut.trans hOut), ?_⟩
      · rw [foundAt, hNext]
        rfl
      · intro a ha
        rw [hNext] at ha
        cases ha
        exact hQueryPrep
      · intro ha
        rw [hNext] at ha
        contradiction
      · intro j hj
        exact (hQueryFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j))
    | true =>
      have goInc : T.next 2 checked.state = some 3 := by
        simp [T, stages, hQueryAns, hQuery, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
      have prep : Prepared word n k label order (T.enter 3 checked) :=
        ⟨hQueryPrep.inputLo, hQueryPrep.inputHi, hQueryPrep.heads, hQueryPrep.cursor, hQueryPrep.order⟩
      obtain ⟨l, f, z, tail, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hFrame⟩ :=
        advance (T.enter 3 checked) rfl prep
      have hNext : GreedyGenerator.next query eligible k = GreedyGenerator.next query eligible (k+1) := by
        rw [next_step query eligible hlt]
        change (if GreedyGenerator.accept query eligible x then _ else _) = _
        simp [GreedyGenerator.accept, hAllow, hQuery]
      refine ⟨_, f, z, .call hCmp hStop goAllow
          (.call hAllowRun hAllowStop goMember (.call hQueryRun hQueryStop goInc tail)),
        hHalt, hFinal, ?_, ?_, ?_, hOutput.trans (hQueryOut.trans (hAllowOut.trans hOut)), ?_⟩
      · rwa [hNext]
      · rwa [hNext]
      · rwa [hNext]
      · intro j hj
        exact (hFrame j hj).trans ((hQueryFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j)))
termination_by n - k
decreasing_by omega

/-- The fixed controller executes the entire candidate scan. The two leaves
decide eligibility and prefix membership for one live candidate each. The scan
installs no oracle for the least acceptable candidate. -/
theorem execute {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (hKeep : label ∉ keep) (different : label ≠ order)
    (hB : TableIO.width n + 1 ≤ B)
    (hEligible : Leaf label order widthStates allowed member (B := B) word 1 eligible allowed.answer keep)
    (hMember : Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer keep)
    (k : Nat) (hk : k ≤ n)
    (c : ((stages label order widthStates allowed member).component 0).Config)
    (hEntry : c.state = (stages label order widthStates allowed member).entry 0)
    (hc : Prepared word n k label order c) :
    let T := stages label order widthStates allowed member
    let expected := GreedyGenerator.next query eligible k
    ∃ (ticks : Nat) (d : T.machine.Config),
      T.machine.BoundedSegment word B (T.tag 0 c) d ticks ∧ T.machine.step word d = none ∧
      found label order widthStates allowed member d = expected.isSome ∧
      (∀ x : Fin n, expected = some x → Prepared word n x.val label order d) ∧
      (expected = none → Prepared word n n label order d) ∧
      d.outputReversed = c.outputReversed ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  let T := stages label order widthStates allowed member
  obtain ⟨ticks, i, d, route, stop, done, answer, foundPrep, nonePrep, out, frame⟩ :=
    scanRoute label order widthStates allowed member query eligible keep hKeep different hB hEligible hMember
       k hk c hEntry hc
  obtain ⟨run, halt⟩ := T.routed_stop route stop done
  refine ⟨ticks, T.tag i d, run, halt, answer, ?_, ?_, out, frame⟩
  · intro x hx
    obtain ⟨a, b, h, p, q⟩ := foundPrep x hx
    exact ⟨a, b, h, p, q⟩
  · intro hx
    obtain ⟨a, b, h, p, q⟩ := nonePrep hx
    exact ⟨a, b, h, p, q⟩
end Mathproof.MinimumGeneration.GreedyTapeScan
