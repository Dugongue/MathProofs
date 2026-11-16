import Mathproof.MinimumGenerationConnectivity
import Mathproof.MinimumGenerationLiveInverse

namespace Mathproof.MinimumGeneration.ReingoldLiveInput

open Connectivity SimpleGraph
open SearchTransducer
open Mathproof.Multitape.Locality (moveOffset)
open InputPosition (work)

/-- An outer graph query can use the whole Cayley graph, a rank prefix, or an
edge-deleted Cayley graph. -/
inductive Query (n : Nat)
  | full
  | below (threshold : Nat)
  | delete (u v : Fin n)

def baseGraph (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool) :
    SimpleGraph (Fin n) :=
  @SimpleGraph.mulCayley (Fin n) {a | allowed a = true} G.toMul

def queryGraph (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool) :
    Query n → SimpleGraph (Fin n)
  | .full => baseGraph n G allowed
  | .below threshold => earlier (baseGraph n G allowed) (finRank n) threshold
  | .delete u v => (baseGraph n G allowed).deleteEdges {s(u, v)}

/-- The raw virtual adjacency polls the encoded group table for differences. -/
def rawAdj (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool) :
    Query n → AdjBits (Fin n)
  | .full => TableIO.cayleyAdjBit word n identity allowed
  | .below k => earlierBits (TableIO.cayleyAdjBit word n identity allowed) (finRank n) k
  | .delete u v => withoutBits (TableIO.cayleyAdjBit word n identity allowed) u v

theorem rawAdj_correct (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (x y : Fin n) :
    rawAdj (@encodeCayley n G.toMul) n G.toOne.one.val allowed query x y = true ↔
      (queryGraph n G allowed query).Adj x y := by
  have hc : ∀ a b, TableIO.cayleyAdjBit (@encodeCayley n G.toMul) n G.toOne.one.val allowed a b =
      true ↔ (baseGraph n G allowed).Adj a b := TableIO.cayleyAdjBit_correct n G allowed
  cases query with
  | full => exact hc x y
  | below k => exact earlierBits_spec _ _ hc _ k x y
  | delete u v => exact withoutBits_spec _ _ hc u v x y

def virtualWord (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) : List Bool :=
  ustconWord (rawAdj word n identity allowed query) s t

def virtualRead (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) (i : Nat) : Bool :=
  ustconRead (rawAdj word n identity allowed query) s t i

def virtualCell (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) (i : Int) : InputCell :=
  ustconCell (rawAdj word n identity allowed query) s t i

/-- The Boolean reader includes the backend's false convention beyond the word. -/
theorem virtualRead_spec (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) (i : Nat) :
    virtualRead word n identity allowed query s t i =
      ((virtualWord word n identity allowed query s t)[i]?).getD false :=
  ustconRead_spec _ _ _ _

theorem virtualCell_spec (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) (i : Int) :
    virtualCell word n identity allowed query s t i =
      readInput (virtualWord word n identity allowed query s t) i :=
  ustconCell_spec _ _ _ _

theorem virtualWord_length (word : List Bool) (n identity : Nat) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) :
    (virtualWord word n identity allowed query s t).length =
      n + s.val + t.val + 3 + n * n :=
  ustconWord_length _ _ _

/-- A matrix address reads the literal graph predicate from the raw group word. -/
theorem virtualRead_matrix (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t x y : Fin n) :
    virtualRead (@encodeCayley n G.toMul) n G.toOne.one.val allowed query s t
        (ustconHeaderLength s t + (x.val * n + y.val)) = true ↔
      (queryGraph n G allowed query).Adj x y := by
  rw [virtualRead, ustconRead_matrix]
  exact rawAdj_correct n G allowed query x y

theorem virtualWord_length_le (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) :
    (virtualWord (@encodeCayley n G.toMul) n G.toOne.one.val allowed query s t).length + 1 ≤
      4 * ((@encodeCayley n G.toMul).length + 1) := by
  rw [virtualWord_length, @length_encodeCayley n G.toMul]
  have h₀ : n * n ≤ n * n * (Nat.log2 n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hs := s.isLt
  have ht := t.isLt
  omega

/-- Every in-range virtual address, including the right endmarker, fits in at most
two extra bits over the raw input's own bit-address width. -/
theorem virtual_address_width (n : Nat) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) (i : Nat)
    (hi : i ≤ (virtualWord (@encodeCayley n G.toMul) n G.toOne.one.val allowed query s t).length) :
    i < 2 ^ (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1 + 2) := by
  have hl := virtualWord_length_le n G allowed query s t
  have hp := Nat.lt_log2_self (n := ((@encodeCayley n G.toMul).length + 1))
  rw [Nat.pow_add]
  have hfour : (2 : Nat) ^ 2 = 4 := by decide
  rw [hfour, Nat.mul_comm]
  exact (show i ≤ 4 * ((@encodeCayley n G.toMul).length + 1) by omega).trans_lt
    (Nat.mul_lt_mul_of_pos_left hp (by decide))

/-- Evaluate a local transition with a materialization-free cell reader. -/
def callbackStep (M : SearchTransducer) (cell : Int → InputCell) (c : M.Config) :
    Option M.Config :=
  (M.transition c.state (cell c.inputHead) (fun i => c.workCell i (c.workHead i))).map
    fun (state, inputMove, workAction, outputBit) =>
      ⟨state, c.inputHead + moveOffset inputMove,
        fun i => c.workHead i + moveOffset (workAction i).move,
        fun i j => if j = c.workHead i then (workAction i).write.getD (c.workCell i j)
          else c.workCell i j,
        outputBit.elim c.outputReversed (fun bit => bit :: c.outputReversed)⟩

def callbackRun (M : SearchTransducer) (cell : Int → InputCell) (initial : M.Config) :
    Nat → Option M.Config
  | 0 => some initial
  | k + 1 => (callbackRun M cell initial k).bind (callbackStep M cell)

theorem callbackStep_eq (M : SearchTransducer) (word : List Bool)
    (cell : Int → InputCell) (hc : ∀ j, cell j = readInput word j) (c : M.Config) :
    callbackStep M cell c = M.step word c := by
  unfold callbackStep step
  rw [hc]

theorem callbackRun_eq (M : SearchTransducer) (word : List Bool)
    (cell : Int → InputCell) (hc : ∀ j, cell j = readInput word j)
    (start : M.Config) (k : Nat) :
    callbackRun M cell start k = M.runFrom word start k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [callbackRun, runFrom, ih]
    apply congrArg
    funext c
    exact callbackStep_eq M word cell hc c

/-- The same compiled transition table has identical runs under virtual input
polling and a materialized input tape. Each finite prefix is included. -/
theorem cayley_callbackRun (M : SearchTransducer) (word : List Bool)
    (n identity : Nat) (allowed : Fin n → Bool) (query : Query n) (s t : Fin n)
    (start : M.Config) (k : Nat) :
    callbackRun M (virtualCell word n identity allowed query s t) start k =
      M.runFrom (virtualWord word n identity allowed query s t) start k :=
  callbackRun_eq M _ _ (virtualCell_spec word n identity allowed query s t) start k


/-- The right factor relating two labelled vertices of the raw Cayley table. -/
def difference {n : Nat} (G : Group (Fin n)) (x y : Fin n) : Fin n :=
  G.toMul.mul (G.toInv.inv x) y

theorem difference_solves {n : Nat} (G : Group (Fin n)) (x y : Fin n) :
    G.toMul.mul x (difference G x y) = y := by
  let _ : Group (Fin n) := G
  let _ : Mul (Fin n) := G.toMul
  let _ : Inv (Fin n) := G.toInv
  change x * (x⁻¹ * y) = y
  rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem rawDifference_eq_difference (n : Nat) (G : Group (Fin n)) (x y : Fin n) :
    TableIO.rawDifference (@encodeCayley n G.toMul) n G.toOne.one.val x y =
      some (difference G x y) :=
  TableIO.rawDifference_correct n G x y

/-- The physical callback computes x⁻¹y by finding the live column z where
x*z=y. The caller's prepared order and two endpoint labels suffice. -/
theorem liveDifference (n : Nat) (G : Group (Fin n)) (x y : Fin n) (prior : List Bool) :
    let word := @encodeCayley n G.toMul
    let M := LiveInverse.machine
    ∃ (k : Nat) (result : M.Config),
      M.BoundedSegment word (3 * (Nat.log2 (word.length + 1) + 1))
        (LiveInverse.start n x.val y.val prior) result k ∧
      M.step word result = none ∧
      result.workCell ⟨8, by decide⟩ = InputPosition.work
        (encodeLabel (TableIO.width n) (difference G x y).val) ∧
      result.outputReversed = prior ∧ result.workHead = (fun _ => 0) := by
  exact LiveInverse.executeRightSolve n G x y (difference G x y) (difference_solves G x y) prior

/-- The physical difference callback can be called in a larger fixed bank
layout. Every prefix preserves the head and all cells of each caller bank
outside the callback's image. -/
theorem liveDifference_framed (n : Nat) (G : Group (Fin n)) (x y : Fin n) (prior : List Bool)
    {W : Nat} (e : Fin LiveInverse.machine.workTapes ↪ Fin W)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool)
    (hframe : ∀ j ∉ Set.range e, (heads j).natAbs ≤
        3 * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1)) :
    let word := @encodeCayley n G.toMul
    let B := 3 * (Nat.log2 (word.length + 1) + 1)
    let M := LiveInverse.machine
    let entry := M.bankConfig e (LiveInverse.start n x.val y.val prior) heads cells
    ∃ (k : Nat) (result : (M.relocateBanks e).Config),
      (M.relocateBanks e).BoundedSegment word B entry result k ∧
      (M.relocateBanks e).step word result = none ∧
      result.workCell (e ⟨8, by decide⟩) = InputPosition.work
        (encodeLabel (TableIO.width n) (difference G x y).val) ∧
      result.workHead (e ⟨8, by decide⟩) = 0 ∧
      result.outputReversed = prior ∧
      ∀ j c, (M.relocateBanks e).runFrom word entry j = some c →
        ∀ i ∉ Set.range e, c.workHead i = heads i ∧ c.workCell i = cells i := by
  obtain ⟨k, result, run, halt, label, output, hHeads⟩ := liveDifference n G x y prior
  let M := LiveInverse.machine
  let d := M.bankConfig e result heads cells
  refine ⟨k, d, relocateBanks_segment M e run hframe, ?_, ?_, ?_, output, ?_⟩
  · dsimp only [d]
    rw [relocateBanks_step, halt]
    rfl
  · exact (bankConfig_cell_image M e result heads cells _).trans label
  · exact (bankConfig_head_image M e result heads cells _).trans (congrFun hHeads _)
  · intro j c hc i hi
    rw [relocateBanks_runFrom] at hc
    obtain ⟨native, _, hc'⟩ := Option.map_eq_some_iff.mp hc
    subst c
    exact bankConfig_frame M e native heads cells hi

private theorem work_end (b : List Bool) : work b ((b.length : Int) + 1) = none := by
  simp [work, show ¬ ((b.length : Int) + 1 ≤ 0) by omega]

private theorem work_block (b : List Bool) : TapeArithmetic.block (work b) 1 b := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem labels_eq_iff (n : Nat) (x y : Fin n) :
    encodeLabel (TableIO.width n) x.val = encodeLabel (TableIO.width n) y.val ↔ x = y := by
  constructor
  · intro he
    have h := congrArg InputPosition.digits he
    have hx : x.val < 2 ^ TableIO.width n := x.isLt.trans Nat.lt_log2_self
    have hy : y.val < 2 ^ TableIO.width n := y.isLt.trans Nat.lt_log2_self
    rw [InputPosition.digits_encodeLabel _ _ hx, InputPosition.digits_encodeLabel _ _ hy] at h
    exact Fin.ext h
  · rintro rfl
    rfl

private def solveBanks : Fin LiveInverse.machine.workTapes ↪ Fin 10 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun z : Fin 10 => z.val) h)⟩

private abbrev compareMachine : SearchTransducer :=
  TapeRegisters.machine (8 : Fin 10) (9 : Fin 10) .compare

private def compareBanks : Fin compareMachine.workTapes ↪ Fin 10 :=
  Function.Embedding.refl (Fin 10)

abbrev signedTrialMachine : SearchTransducer :=
  thenMachine LiveInverse.machine compareMachine solveBanks compareBanks

private def signedFrame (bits : List Bool) (_ : Fin 10) : Int → Option Bool :=
  work bits

def signedTrialStart (n x y signed : Nat) (prior : List Bool) : signedTrialMachine.Config :=
  thenLeft LiveInverse.machine compareMachine solveBanks compareBanks
    (LiveInverse.machine.bankConfig solveBanks (LiveInverse.start n x y prior)
      (fun _ => 0) (signedFrame (encodeLabel (TableIO.width n) signed)))

/-- The last native control state of the signed-label trial. -/
def signedTrialVerdict (c : signedTrialMachine.Config) : Bool :=
  decide (c.state.val = LiveInverse.machine.states + (TapeRegisters.done true).val)

/-- One actual live signed-label test. The saved signed label is read from a
spectator bank, the right quotient is computed on the physical Cayley input,
and the finite control records their equality. -/
theorem signedTrial_execute (n : Nat) (G : Group (Fin n)) (x y signed : Fin n)
    (prior : List Bool) :
    let word := @encodeCayley n G.toMul
    let B := 3 * (Nat.log2 (word.length + 1) + 1)
    ∃ (k : Nat) (result : signedTrialMachine.Config),
      signedTrialMachine.BoundedSegment word B (signedTrialStart n x.val y.val signed.val prior) result k ∧
      signedTrialMachine.step word result = none ∧
      (signedTrialVerdict result = true ↔ difference G x y = signed) ∧
      result.outputReversed = prior ∧ result.workHead = (fun _ => 0) ∧
      result.workCell (9 : Fin 10) = work (encodeLabel (TableIO.width n) signed.val) := by
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let B := 3 * (Nat.log2 (word.length + 1) + 1)
  let D := LiveInverse.machine
  let src := encodeLabel w (difference G x y).val
  let tgt := encodeLabel w signed.val
  let memory := signedFrame tgt
  let heads : Fin 10 → Int := fun _ => 0
  obtain ⟨a, rawEnd, rawRun, rawStop, rawLabel, rawOutput, rawHeads⟩ := liveDifference n G x y prior
  let mid := D.bankConfig solveBanks rawEnd heads memory
  have leftRun := relocateBanks_segment D solveBanks rawRun (heads := heads) (cells := memory)
    (by simp [heads])
  have leftStop : (D.relocateBanks solveBanks).step word mid = none := by
    unfold mid
    rw [relocateBanks_step, rawStop]
    rfl
  have h₈ : mid.workCell (8 : Fin 10) = work src := by
    exact (bankConfig_cell_image D solveBanks rawEnd heads memory ⟨8, by decide⟩).trans rawLabel
  have other : (9 : Fin 10) ∉ Set.range solveBanks := by
    rintro ⟨i, hi⟩
    have h := congrArg (fun p : Fin 10 => p.val) hi
    change i.val = 9 at h
    have hb : i.val < 9 := i.isLt
    omega
  have h₉ : mid.workCell (9 : Fin 10) = work tgt :=
    (bankConfig_frame D solveBanks rawEnd heads memory other).2
  have hheads : mid.workHead = heads := by
    funext i
    by_cases hi : i ∈ Set.range solveBanks
    · obtain ⟨j, rfl⟩ := hi
      exact (bankConfig_head_image D solveBanks rawEnd heads memory j).trans (congrFun rawHeads j)
    · exact (bankConfig_frame D solveBanks rawEnd heads memory hi).1
  have hin : (-1 : Int) ≤ mid.inputHead ∧ mid.inputHead ≤ word.length :=
    ⟨(rawRun.2 a le_rfl rawEnd rawRun.1).1, (rawRun.2 a le_rfl rawEnd rawRun.1).2.1⟩
  let c : compareMachine.Config := ⟨0, mid.inputHead, heads, mid.workCell, mid.outputReversed⟩
  have hwidth : src.length = tgt.length := by simp [src, tgt, encodeLabel]
  have hsrc : src.length = w := by simp [src, encodeLabel]
  obtain ⟨d, yes, hc, hstate, hv, hdHead, hdCell, _, hdOut⟩ :=
    TapeRegisters.executeCompare word c src tgt hwidth rfl
      (by simp [c, heads, h₉, work])
      (by simpa [c, heads, h₈] using work_end src)
      (by simpa [c, heads, h₉, hwidth] using work_end tgt)
      (by simpa [c, heads, h₈] using work_block src)
      (by simpa [c, heads, h₉] using work_block tgt)
  have hn : n ≤ word.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have hlog : n.log2 ≤ (word.length + 1).log2 :=
    (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by have := x.isLt; omega)).trans (by omega))
  have hw : w + 1 ≤ B := by dsimp [w, B, TableIO.width]; omega
  have nativeCompare := hc.boundedSegment (B := B) (by exact hin)
    (by
      intro i j hlo hhi
      change 0 ≤ j at hlo
      unfold TapeRegisters.finish at hhi
      have hu : j ≤ (w : Int) + 1 := by
        split at hhi
        · simpa [c, heads, hsrc] using hhi
        · simp [c, heads] at hhi
          omega
      have habs := Int.natAbs_of_nonneg hlo
      omega)
  have compareFrame : ∀ j ∉ Set.range compareBanks, (heads j).natAbs ≤ B := by simp [heads]
  have compareRun := relocateBanks_segment compareMachine compareBanks nativeCompare
    (heads := heads) (cells := mid.workCell) compareFrame
  let finish := compareMachine.bankConfig compareBanks d heads mid.workCell
  have hhand : thenEntry D compareMachine solveBanks compareBanks mid =
      compareMachine.bankConfig compareBanks c heads mid.workCell := by
    have hbHead : (compareMachine.bankConfig compareBanks c heads mid.workCell).workHead =
        heads := by
      funext i
      exact bankConfig_head_image compareMachine compareBanks c heads mid.workCell i
    have hbCell : (compareMachine.bankConfig compareBanks c heads mid.workCell).workCell =
        mid.workCell := by
      funext i
      exact bankConfig_cell_image compareMachine compareBanks c heads mid.workCell i
    change (⟨compareMachine.initialState, mid.inputHead, mid.workHead, mid.workCell, mid.outputReversed⟩ :
      (compareMachine.relocateBanks compareBanks).Config) = _
    rw [hheads]
    cases he : compareMachine.bankConfig compareBanks c heads mid.workCell
    simp_all only [c, SearchTransducer.bankConfig, compareBanks, SearchTransducer.relocateBanks]
  change (compareMachine.relocateBanks compareBanks).BoundedSegment word B _ finish
     (2 * src.length + 3) at compareRun
  rw [← hhand] at compareRun
  have rightStop : (compareMachine.relocateBanks compareBanks).step word finish = none := by
    unfold finish
    rw [relocateBanks_step, TapeRegisters.step_done word d yes hstate]
    rfl
  let exit := thenRight D compareMachine solveBanks compareBanks finish
  refine ⟨a + 1 + (2 * src.length + 3), exit,
    thenSegment D compareMachine solveBanks compareBanks leftRun leftStop compareRun, ?_, ?_, ?_, ?_, ?_⟩
  · change (thenMachine D compareMachine solveBanks compareBanks).step word exit = none
    unfold exit
    rw [thenStep_right, rightStop]
    rfl
  · have hs : exit.state.val = D.states + (TapeRegisters.done yes).val := by
      change D.states + d.state.val = _
      rw [hstate]
    change decide (exit.state.val = D.states + (TapeRegisters.done true).val) = true ↔ _
    rw [hs]
    have hflag : decide (D.states + (TapeRegisters.done yes).val =
        D.states + (TapeRegisters.done true).val) = true ↔ yes = true := by
      cases yes <;> simp [TapeRegisters.done]
    exact hflag.trans (hv.trans (labels_eq_iff n _ _))
  · exact hdOut.trans rawOutput
  · funext i
    change finish.workHead (compareBanks i) = _
    rw [bankConfig_head_image, hdHead]
  · change finish.workCell (compareBanks (9 : Fin 10)) = _
    rw [bankConfig_cell_image, hdCell]
    exact h₉

theorem cayley_generation_trials_spec {n m : Nat} (G : Group (Fin n))
    (gen : Fin m → Fin n) (x y : Fin n) :
    (@SimpleGraph.mulCayley (Fin n) (Set.range gen) G.toMul).Adj x y ↔
      x ≠ y ∧ ∃ l : Letter m,
        difference G x y = @letterValue (Fin n) G m gen l := by
  let _ : Group (Fin n) := G
  let _ : Mul (Fin n) := G.toMul
  let _ : Inv (Fin n) := G.toInv
  have solve (z : Fin n) (h : x * z = y) : difference G x y = z :=
    mul_left_cancel ((difference_solves G x y).trans h.symm)
  constructor
  · intro h
    obtain ⟨a, ⟨i, rfl⟩, he | he⟩ := cayley_adj_has_label (Set.range gen) h
    · exact ⟨h.ne, (i, false), by simpa [letterValue] using solve (gen i) he⟩
    · exact ⟨h.ne, (i, true), by simpa [letterValue] using solve ((gen i)⁻¹) he⟩
  · rintro ⟨hne, l, hl⟩
    have hmul : x * @letterValue (Fin n) G m gen l = y := by
      rw [← hl]
      exact difference_solves G x y
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, gen l.1, ⟨l.1, rfl⟩, ?_⟩
    cases hs : l.2
    · left
      simpa [letterValue, hs] using hmul
    · right
      have hh : x * (gen l.1)⁻¹ = y := by simpa [letterValue, hs] using hmul
      rw [← hh, inv_mul_cancel_right]
end Mathproof.MinimumGeneration.ReingoldLiveInput
