import Mathproof.MinimumGenerationPhysicalEntry
import Mathproof.MinimumGenerationTapeRegisters
import Mathproof.MinimumGenerationMacroDispatch
import Mathlib.Tactic.FinCases

namespace Mathproof.MinimumGeneration.PhysicalInverse

open Mathproof.Multitape
open SearchTransducer
open InputPosition (cfg work)
open PhysicalEntry (reader readerConfig reader_segment reader_step segment_of_prefix segment_mono)

private abbrev compareMachine := TapeRegisters.machine (0 : Fin 3) 1 .compare
private abbrev incrementMachine := TapeArithmetic.machine (2 : Fin 3) .increment

private def native (i : Fin 3) : SearchTransducer :=
  if i = 0 then reader else if i = 1 then compareMachine else incrementMachine

private theorem nativeStates (i : Fin 3) : (native i).states ≤ 10 := by
  fin_cases i <;> decide

private def captureBank : Fin reader.workTapes ↪ Fin 3 :=
  ⟨fun _ => 0, fun i j _ => by
    change Fin 1 at i j
    exact Subsingleton.elim i j⟩

private def banks (i : Fin 3) : Fin (native i).workTapes ↪ Fin 3 := by
  by_cases h : i = 0
  · subst i
    exact captureBank
  · by_cases h' : i = 1
    · subst i
      exact Function.Embedding.refl (Fin 3)
    · have h'' : i = 2 := by fin_cases i <;> simp_all
      subst i
      exact Function.Embedding.refl (Fin 3)

private def next (i : Fin 3) (q : Fin (native i).states) : Option (Fin 3) :=
  if i = 0 then some 1 else if i = 1 then
    if q.val = 6 then some 2 else none
  else some 0

/-- The three actual stages are contiguous input capture, fixed-width
comparison against the identity bank, and incrementing the candidate label. -/
def stages : Stages 3 10 3 :=
  Stages.ofMachines 0 native nativeStates banks next

abbrev machine : SearchTransducer := stages.machine

private def cells (capture identity candidate : List Bool) (t : Fin 3) : Int → Option Bool :=
  if t = 0 then work capture else if t = 1 then work identity else work candidate

private def stageCfg (i : Fin 3) (q : Fin 10) (a : ℕ) (capture identity candidate out : List Bool) :
    (stages.component i).Config :=
  ⟨q, a, fun _ => 0, cells capture identity candidate, out⟩

/-- Prepared three-bank entry for the row scan, with the input head at the
first bit of the first candidate's entry. -/
def entry (a : ℕ) (capture identity candidate out : List Bool) :
    (stages.component 0).Config :=
  stageCfg 0 6 a capture identity candidate out

private def compared (equal : Bool) (a : ℕ) (capture identity candidate out : List Bool) :
    (stages.component 1).Config :=
  stageCfg 1 ((TapeRegisters.done equal).castLE (by decide)) a capture identity candidate out

private def compareEntry (a : ℕ) (capture identity candidate out : List Bool) :
    (stages.component 1).Config :=
  stageCfg 1 0 a capture identity candidate out

private def incrementEntry (a : ℕ) (capture identity candidate out : List Bool) :
    (stages.component 2).Config :=
  stageCfg 2 0 a capture identity candidate out

private def lifted (i : Fin 3) (c : (native i).Config) (xs : Fin 3 → Int → Option Bool) :
    (stages.component i).Config :=
  (native i).padConfig (nativeStates i) (banks i)
    ((native i).bankConfig (banks i) c (fun _ => 0) xs)

private theorem liftSegment (i : Fin 3) {word : List Bool} {B k : ℕ}
    {c d : (native i).Config} (xs : Fin 3 → Int → Option Bool)
    (hr : (native i).BoundedSegment word B c d k) :
    (stages.component i).BoundedSegment word B (lifted i c xs) (lifted i d xs) k := by
  exact (native i).padMachine_segment (nativeStates i) (banks i)
    ((native i).relocateBanks_segment (banks i) hr (fun _ _ => by simp))

private theorem liftStop (i : Fin 3) {word : List Bool} {c : (native i).Config}
    (xs : Fin 3 → Int → Option Bool) (hr : (native i).step word c = none) :
    (stages.component i).step word (lifted i c xs) = none := by
  change ((native i).padMachine (nativeStates i) (banks i)).step word
    ((native i).padConfig (nativeStates i) (banks i)
      ((native i).bankConfig (banks i) c (fun _ => 0) xs)) = none
  rw [(native i).padMachine_step, (native i).relocateBanks_step, hr]
  rfl

private theorem capLift (q : Fin 10) (a : ℕ) (capture old identity candidate out : List Bool) :
    lifted 0 (readerConfig (cfg capture q a 0 out)) (cells old identity candidate) =
      stageCfg 0 q a capture identity candidate out := by
  simp only [lifted, padConfig, bankConfig, stageCfg]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl

private def cmpCfg (q : Fin 7) (a : ℕ) (capture identity candidate out : List Bool) :
    compareMachine.Config :=
  ⟨q, a, fun _ => 0, cells capture identity candidate, out⟩

private theorem cmpLift (q : Fin 7) (a : ℕ) (capture identity candidate out : List Bool) :
    lifted 1 (cmpCfg q a capture identity candidate out) (cells capture identity candidate) =
      stageCfg 1 (q.castLE (by decide)) a capture identity candidate out := by
  simp only [lifted, padConfig, bankConfig, stageCfg, cmpCfg]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl

private def incCfg (q : Fin 5) (a : ℕ) (capture identity candidate out : List Bool) :
    incrementMachine.Config :=
  ⟨q, a, fun _ => 0, cells capture identity candidate, out⟩

private theorem incLift (q : Fin 5) (a : ℕ) (capture identity candidate out : List Bool) :
    lifted 2 (incCfg q a capture identity candidate out) (cells capture identity candidate) =
      stageCfg 2 (q.castLE (by decide)) a capture identity candidate out := by
  simp only [lifted, padConfig, bankConfig, stageCfg, incCfg]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl

private theorem work_origin (b : List Bool) : work b 0 = none := by simp [work]

private theorem work_end (b : List Bool) : work b ((b.length : Int) + 1) = none := by
  simp [work, show ¬ ((b.length : Int) + 1 ≤ 0) by omega]

private theorem work_block (b : List Bool) : TapeArithmetic.block (work b) 1 b := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem work_below (b : List Bool) {j : Int} (hj : j < 1) : work b j = none := by
  simp [work, show j ≤ 0 by omega]

private theorem work_above (b : List Bool) {j : Int} (hj : (b.length : Int) + 1 ≤ j) :
    work b j = none := by
  simp [work, show ¬ (j ≤ 0) by omega]
  omega

private theorem work_exact {c : Int → Option Bool} (old new : List Bool)
    (lengths : old.length = new.length) (hb : TapeArithmetic.block c 1 new)
    (outside : ∀ j, j < 1 ∨ (old.length : Int) + 1 ≤ j → c j = work old j) :
    c = work new := by
  funext j
  by_cases hl : j < 1
  · rw [outside _ (.inl hl), work_below _ hl, work_below _ hl]
  · by_cases hr : (old.length : Int) + 1 ≤ j
    · rw [outside _ (.inr hr), work_above _ hr, work_above _ (by simpa [← lengths] using hr)]
    · let i := (j - 1).toNat
      have hj : 1 + (i : Int) = j := by omega
      have hi : i < new.length := by omega
      rw [← hj]
      exact (hb ⟨i, hi⟩).trans ((work_block new) ⟨i, hi⟩).symm


private theorem capCorrect (n : ℕ) (M : Mul (Fin n)) (row col : Fin n)
    (capture identity candidate out : List Bool) (widthEq : capture.length = TableIO.width n) :
    let word := @encodeCayley n M
    let w := TableIO.width n
    let a := TableIO.offset n row.val col.val
    let payload := encodeLabel w (M.mul row col).val
    ∃ k, (stages.component 0).BoundedSegment word (w + 1)
      (entry a capture identity candidate out) (stageCfg 0 9 (a + w) payload identity candidate out) k ∧
      (stages.component 0).step word (stageCfg 0 9 (a + w) payload identity candidate out) = none := by
  dsimp only
  obtain ⟨k, run, bound⟩ := InputPosition.capture_tableEntry n M row col capture out widthEq
  have nativeRun := reader_segment (segment_of_prefix run bound)
  have stageRun := liftSegment 0 (cells capture identity candidate) nativeRun
  rw [capLift, capLift] at stageRun
  exact ⟨k, stageRun, by
    rw [← capLift _ _ _ capture]
    apply liftStop
    change reader.step _ (readerConfig _) = _
    rw [reader_step]
    rfl⟩

private theorem cmpCorrect (word capture identity candidate out : List Bool) (a : ℕ)
    (ha : a ≤ word.length) (widthEq : capture.length = identity.length) :
    ∃ k, (stages.component 1).BoundedSegment word (capture.length + 1)
      (compareEntry a capture identity candidate out)
      (compared (decide (capture = identity)) a capture identity candidate out) k ∧
      (stages.component 1).step word
        (compared (decide (capture = identity)) a capture identity candidate out) = none := by
  let c := cmpCfg 0 a capture identity candidate out
  obtain ⟨d, equal, run, state, equals, heads, memory, input, output⟩ :=
    TapeRegisters.executeCompare word c capture identity widthEq rfl
      (by simpa [c, cmpCfg, cells] using work_origin identity)
      (by simpa [c, cmpCfg, cells] using work_end capture)
      (by simpa [c, cmpCfg, cells, widthEq] using work_end identity)
      (by simpa [c, cmpCfg, cells] using work_block capture)
      (by simpa [c, cmpCfg, cells] using work_block identity)
  have hEqual : equal = decide (capture = identity) := by
    cases equal <;> simp_all
  have dst : d = cmpCfg (TapeRegisters.done (decide (capture = identity)))
      a capture identity candidate out := by
    cases d
    simp_all only [c, cmpCfg]
  have run' := run.boundedSegment (B := capture.length + 1)
    (by change (-1 : Int) ≤ (a : Int) ∧ (a : Int) ≤ (word.length : Int); omega)
    (by
      intro t j lo hi
      change 0 ≤ j at lo
      have upper : j ≤ (capture.length : Int) + 1 := by
        unfold TapeRegisters.finish at hi
        split at hi
        · simpa [c, cmpCfg] using hi
        · simp [c, cmpCfg] at hi
          omega
      have hj := Int.natAbs_of_nonneg lo
      omega)
  rw [dst] at run'
  have liftedRun := liftSegment 1 (cells capture identity candidate) run'
  rw [cmpLift, cmpLift] at liftedRun
  refine ⟨2 * capture.length + 3, liftedRun, ?_⟩
  rw [show compared (decide (capture = identity)) a capture identity candidate out =
    lifted 1 (cmpCfg (TapeRegisters.done (decide (capture = identity))) a capture identity candidate out)
      (cells capture identity candidate) from (cmpLift ..).symm]
  apply liftStop
  exact TapeRegisters.step_done word _ _ rfl


private theorem incCorrect (word capture identity out : List Bool) (a w label : ℕ)
    (ha : a ≤ word.length) :
    let old := encodeLabel w label
    let result := encodeLabel w (label + 1)
    ∃ k, (stages.component 2).BoundedSegment word (w + 1)
      (incrementEntry a capture identity old out) (stageCfg 2 4 a capture identity result out) k ∧
      (stages.component 2).step word (stageCfg 2 4 a capture identity result out) = none := by
  dsimp only
  let old := encodeLabel w label
  let result := encodeLabel w (label + 1)
  let c := incCfg 0 a capture identity old out
  have oldWidth : old.length = w := by simp [old, encodeLabel]
  have resultWidth : result.length = w := by simp [result, encodeLabel]
  obtain ⟨d, run, state, head, bits, frame⟩ := TapeArithmetic.executeIncrement word c w label rfl
    (by simpa [c, incCfg, cells] using work_origin old)
    (by simpa [c, incCfg, cells, oldWidth] using work_end old)
    (by simpa [c, incCfg, cells] using work_block old)
  have heads : d.workHead = fun _ => 0 := by
    funext t
    by_cases ht : t = 2
    · subst t
      exact head
    · exact frame.heads t ht
  have memory : d.workCell = cells capture identity result := by
    funext t
    fin_cases t
    · funext j
      exact frame.cells 0 j (.inl (by decide))
    · funext j
      exact frame.cells 1 j (.inl (by decide))
    · change d.workCell 2 = work result
      apply work_exact old result (oldWidth.trans resultWidth.symm) bits
      intro j outside
      exact frame.cells 2 j (.inr (by simpa [c, incCfg, oldWidth] using outside))
  have input : d.inputHead = (a : Int) := frame.input
  have output : d.outputReversed = out := frame.output
  have dst : d = incCfg 4 a capture identity result out := by
    cases d
    simp_all only [incCfg]
  have run' := TapeRegisters.arithmeticBoundedSegment (B := w + 1) run
    (by change (-1 : Int) ≤ (a : Int) ∧ (a : Int) ≤ (word.length : Int); omega)
    (by
      intro j lo hi
      change 0 ≤ j at lo
      simp [c, incCfg] at hi
      have hj := Int.natAbs_of_nonneg lo
      omega)
    (by simp [c, incCfg])
  rw [dst] at run'
  have liftedRun := liftSegment 2 (cells capture identity old) run'
  rw [incLift] at liftedRun
  have liftedDst : lifted 2 (incCfg 4 a capture identity result out) (cells capture identity old) =
      stageCfg 2 4 a capture identity result out := by
    simp only [lifted, padConfig, bankConfig, stageCfg, incCfg]
    congr 1
    · funext t
      fin_cases t <;> rfl
    · funext t
      fin_cases t <;> rfl
  rw [liftedDst] at liftedRun
  exact ⟨2 * w + 3, liftedRun, by
    rw [← liftedDst]
    apply liftStop
    exact TapeArithmetic.step_done word _ rfl⟩


private theorem labelsEqual (n : ℕ) (a b : Fin n) :
    encodeLabel (TableIO.width n) a.val = encodeLabel (TableIO.width n) b.val ↔ a = b := by
  have cap : n < 2 ^ TableIO.width n := Nat.lt_log2_self
  constructor
  · intro h
    have hd := congrArg InputPosition.digits h
    rw [InputPosition.digits_encodeLabel _ _ (a.isLt.trans cap),
      InputPosition.digits_encodeLabel _ _ (b.isLt.trans cap)] at hd
    exact Fin.ext hd
  · rintro rfl
    rfl

private theorem offsetNext (n row col : ℕ) :
    TableIO.offset n row col + TableIO.width n = TableIO.offset n row (col + 1) := by
  simp [TableIO.offset, Nat.add_assoc, Nat.add_mul]

private theorem rowLoop (n : ℕ) (G : Group (Fin n)) (row want goal : Fin n)
    (mulGoal : G.toMul.mul row goal = want) (out : List Bool)
    (fuel start : ℕ) (atTarget : start + fuel = goal.val) (capture : List Bool)
    (captureWidth : capture.length = TableIO.width n) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    let identity := encodeLabel w want.val
    let target := goal.val
    ∃ (k : ℕ) (result : (stages.component 1).Config),
      stages.Routed word (w + 1) 0
        (entry (TableIO.offset n row.val start) capture identity (encodeLabel w start) out)
        1 result k ∧
      (stages.component 1).step word result = none ∧
      stages.next 1 result.state = none ∧
      result.workCell 2 = work (encodeLabel w target) ∧ result.outputReversed = out ∧
      result.workHead = (fun _ => 0) := by
  let _ : Group (Fin n) := G
  let _ : Mul (Fin n) := G.toMul
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let identity := encodeLabel w want.val
  let target := goal.val
  induction fuel generalizing start capture with
  | zero =>
    have he : start = target := by simpa [target] using atTarget
    let col : Fin n := ⟨start, by rw [he]; exact goal.isLt⟩
    let addr := TableIO.offset n row.val start
    let payload := encodeLabel w (G.toMul.mul row col).val
    have hcol : col = goal := Fin.ext he
    have hp : payload = identity := (labelsEqual n _ _).mpr
      ((congrArg (G.toMul.mul row) hcol).trans mulGoal)
    have payloadW : payload.length = w := by simp [payload, encodeLabel]
    have hAddr : addr + w ≤ word.length := by
      have hw : 0 < w := by simp [w, TableIO.width]
      have h := @TableIO.tableAddress_lt_inputLength n G.toMul row col (w - 1) (by omega)
      change addr + (w - 1) < word.length at h
      omega
    obtain ⟨k, run, halt⟩ := capCorrect n G.toMul row col capture identity (encodeLabel w start) out captureWidth
    obtain ⟨j, cmp, stop⟩ := cmpCorrect word payload identity (encodeLabel w start) out
      (addr + w) hAddr (by simp [payloadW, identity, encodeLabel])
    change (stages.component 1).BoundedSegment word (payload.length + 1)
      (compareEntry (addr + w) payload identity (encodeLabel w start) out)
      (compared (decide (payload = identity)) (addr + w) payload identity (encodeLabel w start) out) j at cmp
    rw [payloadW, decide_eq_true hp] at cmp
    rw [decide_eq_true hp] at stop
    refine ⟨k + 1 + j, compared true (addr + w) payload identity (encodeLabel w start) out,
      ?_, stop, rfl, ?_, rfl, rfl⟩
    · exact .call run halt rfl (.finish cmp)
    · change work (encodeLabel w start) = work (encodeLabel w target)
      rw [he]
  | succ fuel ih =>
    have hAt : start + (fuel + 1) = target := atTarget
    have hLess : start < target := by omega
    have ht : target < n := goal.isLt
    let col : Fin n := ⟨start, hLess.trans ht⟩
    let addr := TableIO.offset n row.val start
    let payload := encodeLabel w (G.toMul.mul row col).val
    have hp : payload ≠ identity := by
      intro h
      have product : G.toMul.mul row col = want := (labelsEqual n _ _).mp h
      have colGoal : col = goal :=
        mul_left_cancel (product.trans mulGoal.symm)
      have he : start = target := congrArg Fin.val colGoal
      omega
    have payloadW : payload.length = w := by simp [payload, encodeLabel]
    have hAddr : addr + w ≤ word.length := by
      have hw : 0 < w := by simp [w, TableIO.width]
      have h := @TableIO.tableAddress_lt_inputLength n G.toMul row col (w - 1) (by omega)
      change addr + (w - 1) < word.length at h
      omega
    obtain ⟨k, run, halt⟩ := capCorrect n G.toMul row col capture identity (encodeLabel w start) out captureWidth
    obtain ⟨j, cmp, stop⟩ := cmpCorrect word payload identity (encodeLabel w start) out
      (addr + w) hAddr (by simp [payloadW, identity, encodeLabel])
    rw [payloadW, decide_eq_false hp] at cmp
    rw [decide_eq_false hp] at stop
    obtain ⟨i, inc, incStop⟩ := incCorrect word payload identity out (addr + w) w start hAddr
    obtain ⟨steps, result, rest, hStop, hNext, hBits, hOut, hHeads⟩ :=
      ih (start + 1) (by change start + 1 + fuel = target; omega) payload payloadW
    have hAddrNext : addr + w = TableIO.offset n row.val (start + 1) := offsetNext n row.val start
    change stages.Routed word (w + 1) 0
      (entry (TableIO.offset n row.val (start + 1)) payload identity
        (encodeLabel w (start + 1)) out) 1 result steps at rest
    rw [← hAddrNext] at rest
    exact ⟨k + 1 + (j + 1 + (i + 1 + steps)), result,
      .call run halt rfl (.call cmp stop rfl (.call inc incStop rfl rest)),
      hStop, hNext, hBits, hOut, hHeads⟩


/-- From a prepared row cursor and target-product bank, run the common scan
and return the unique right solution of a row multiplication equation. -/
theorem physicalRightSolve_layout (n : ℕ) (G : Group (Fin n)) (row want goal : Fin n)
    (mulGoal : G.toMul.mul row goal = want) (out : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    let zeros := List.replicate w false
    let targetLabel := encodeLabel w want.val
    let start := stages.tag 0 (entry (TableIO.offset n row.val 0) zeros targetLabel (encodeLabel w 0) out)
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (w + 1) start result k ∧ machine.step word result = none ∧
      result.workCell 2 = work (encodeLabel w goal.val) ∧ result.outputReversed = out ∧
      result.workHead = (fun _ => 0) := by
  dsimp only
  obtain ⟨k, result, route, halt, nextStop, bits, outEq, hHeads⟩ :=
    rowLoop n G row want goal mulGoal out goal.val 0 (Nat.zero_add _)
      (List.replicate (TableIO.width n) false) List.length_replicate
  obtain ⟨run, stop⟩ := stages.routed_stop route halt nextStop
  exact ⟨k, stages.tag 1 result, run, stop, bits, outEq, hHeads⟩

theorem physicalRightSolve (n : ℕ) (G : Group (Fin n)) (row want goal : Fin n)
    (mulGoal : G.toMul.mul row goal = want) (out : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    let zeros := List.replicate w false
    let targetLabel := encodeLabel w want.val
    let start := stages.tag 0 (entry (TableIO.offset n row.val 0) zeros targetLabel (encodeLabel w 0) out)
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (w + 1) start result k ∧ machine.step word result = none ∧
      result.workCell 2 = work (encodeLabel w goal.val) ∧ result.outputReversed = out := by
  obtain ⟨k, result, run, stop, bits, outEq, _⟩ :=
    physicalRightSolve_layout n G row want goal mulGoal out
  exact ⟨k, result, run, stop, bits, outEq⟩
/-- A physical inverse-row scan from a prepared row cursor and an identity
label. The capture and candidate banks start zeroed at the input's native
label width. The transducer returns the exact inverse in the candidate bank. -/
theorem physicalInverse (n : ℕ) (G : Group (Fin n)) (row : Fin n) (out : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    let zeros := List.replicate w false
    let identity := encodeLabel w G.toOne.one.val
    let start := stages.tag 0 (entry (TableIO.offset n row.val 0) zeros identity (encodeLabel w 0) out)
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (w + 1) start result k ∧ machine.step word result = none ∧
      result.workCell 2 = work (encodeLabel w (G.toInv.inv row).val) ∧ result.outputReversed = out := by
  let _ : Group (Fin n) := G
  have h : G.toMul.mul row (G.toInv.inv row) = G.toOne.one := by
    exact mul_inv_cancel row
  exact physicalRightSolve n G row G.toOne.one (G.toInv.inv row) h out

/-- Start immediately after the unary header and read the first row. A group
element multiplied on the right by the identity has itself as the product,
so the target product has the first row's label, namely zero. -/
theorem physicalIdentity (n : ℕ) (G : Group (Fin n)) (out : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    let zeros := List.replicate w false
    let start := stages.tag 0 (entry (n + 1) zeros (encodeLabel w 0) (encodeLabel w 0) out)
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (w + 1) start result k ∧ machine.step word result = none ∧
      result.workCell 2 = work (encodeLabel w G.toOne.one.val) ∧ result.outputReversed = out := by
  have positive : 0 < n := (Nat.zero_le _).trans_lt G.toOne.one.isLt
  let row : Fin n := ⟨0, positive⟩
  have hOffset : TableIO.offset n row.val 0 = n + 1 := by simp [TableIO.offset, row]
  have h := physicalRightSolve n G row row G.toOne.one (G.mul_one row) out
  dsimp only at h ⊢
  simpa only [hOffset, row] using h

end Mathproof.MinimumGeneration.PhysicalInverse
