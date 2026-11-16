import Mathproof.MinimumGenerationInputPosition
import Mathproof.MinimumGenerationTapeCompose
import Mathlib.Tactic.FinCases

namespace Mathproof.MinimumGeneration.PhysicalEntry

open InputPosition
open SearchTransducer

def reader : SearchTransducer := { skip with initialState := (show Fin skip.states from ⟨6, by decide⟩) }

def readerConfig (c : skip.Config) : reader.Config :=
  ⟨c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

theorem reader_step (word : List Bool) (c : skip.Config) :
    reader.step word (readerConfig c) = (skip.step word c).map readerConfig := by
  unfold step
  change (Option.map _ (skip.transition c.state (readInput word c.inputHead)
    (fun i => c.workCell i (c.workHead i)))) =
    (Option.map _ (skip.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)))).map readerConfig
  cases h : skip.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => rfl
  | some t => rcases t with ⟨a,b,d,e⟩; rfl

private theorem reader_run (word : List Bool) (c : skip.Config) (k : ℕ) :
    reader.runFrom word (readerConfig c) k =
      (skip.runFrom word c k).map readerConfig := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runFrom, ih]
    cases h : skip.runFrom word c k with
    | none => simp [runFrom, h]
    | some x => simpa [runFrom, h] using reader_step word x

private theorem runFrom_eq_afterFrom (M : SearchTransducer) (word : List Bool)
    (c : M.Config) (k : ℕ) :
    M.runFrom word c k = TableIO.afterFrom M word c k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runFrom, TableIO.afterFrom, ih]

theorem reader_segment {word : List Bool} {B k : ℕ} {c d : skip.Config}
    (h : skip.BoundedSegment word B c d k) :
    reader.BoundedSegment word B (readerConfig c) (readerConfig d) k := by
  refine ⟨by rw [reader_run, h.1]; rfl, ?_⟩
  intro j hj x hx
  rw [reader_run] at hx
  cases ht : skip.runFrom word c j with
  | none => simp [ht] at hx
  | some y =>
    simp only [ht, Option.map_some, Option.some.injEq] at hx
    have he : readerConfig y = x := hx
    subst x
    exact h.2 j hj y ht

theorem segment_of_prefix {M : SearchTransducer} {word : List Bool} {B k : ℕ}
    {c d : M.Config} (he : TableIO.afterFrom M word c k = some d)
    (hb : ∀ j x, TableIO.afterFrom M word c j = some x → M.Bounded word B x) :
    M.BoundedSegment word B c d k := by
  refine ⟨by simpa [runFrom_eq_afterFrom] using he, ?_⟩
  intro j _ x hx
  exact hb j x (by simpa [runFrom_eq_afterFrom] using hx)

theorem segment_mono {M : SearchTransducer} {word : List Bool} {B C k : ℕ}
    {c d : M.Config} (h : M.BoundedSegment word B c d k) (hBC : B ≤ C) :
    M.BoundedSegment word C c d k := by
  refine ⟨h.1, ?_⟩
  intro j hj x hx
  obtain ⟨hi, hl, hw⟩ := h.2 j hj x hx
  exact ⟨hi, hl, fun i => (hw i).trans hBC⟩

private def addressBank : Fin skip.workTapes ↪ Fin 2 where
  toFun _ := 0
  inj' i j _ := by
    change Fin 1 at i j
    exact Subsingleton.elim i j

private def valueBank : Fin reader.workTapes ↪ Fin 2 where
  toFun _ := 1
  inj' i j _ := by
    change Fin 1 at i j
    exact Subsingleton.elim i j

def machine : SearchTransducer := thenMachine skip reader addressBank valueBank

/-- The input head starts at zero and both prepared work banks at their left
markers. The first bank holds the binary address and the second fixes the width
of the entry. -/
def entryConfig (address template out : List Bool) : machine.Config :=
  thenLeft skip reader addressBank valueBank
    (skip.bankConfig addressBank (cfg address 0 0 0 out)
      (fun _ => 0) (fun _ => work template))

private theorem transfer_ready (done template out : List Bool) (a : ℕ) :
    thenEntry skip reader addressBank valueBank
      (skip.bankConfig addressBank (cfg done 5 a 0 out) (fun _ => 0) (fun _ => work template)) =
    reader.bankConfig valueBank (readerConfig (cfg template 6 a 0 out))
      (fun _ => 0) (fun _ => work done) := by
  let L := skip.bankConfig addressBank (cfg done 5 a 0 out) (fun _ => 0) (fun _ => work template)
  let R := reader.bankConfig valueBank (readerConfig (cfg template 6 a 0 out))
    (fun _ => 0) (fun _ => work done)
  change thenEntry skip reader addressBank valueBank L = R
  have hhead : L.workHead = R.workHead := by
    funext i
    fin_cases i <;> rfl
  have hcell : L.workCell = R.workCell := by
    funext i
    fin_cases i <;> rfl
  exact congrArg₂ (fun h c => (⟨⟨6, by decide⟩, (a : Int), h, c, out⟩ :
    (reader.relocateBanks valueBank).Config)) hhead hcell

/-- Execute a real two-bank machine on the read-only input with a prepared
binary address and a destination bank. The one-step handoff uses the live
input head left by the address loop. -/
theorem physicalRead (word address template out : List Bool)
    (ha : digits address + template.length ≤ word.length) :
    ∃ (t : ℕ) (c : machine.Config),
      machine.BoundedSegment word (max address.length template.length + 1)
        (entryConfig address template out) c t ∧
      machine.step word c = none ∧
      c.workCell ⟨1, by decide⟩ = work (window word (digits address) template.length) ∧
      c.inputHead = (↑(digits address + template.length) : Int) ∧
      c.outputReversed = out ∧
      ∀ i, c.workHead i = 0 := by
  let a := digits address
  let result := window word a template.length
  let B := max address.length template.length + 1
  obtain ⟨k, done, _, he, hh, hp⟩ := skip_correct word address out 0 (by omega)
  simp only [Nat.zero_add] at he hh
  obtain ⟨j, hj, hhalt, hprefix⟩ := capture_correct word template out a ha
  have hA0 := segment_of_prefix he hp
  have hB0 := segment_of_prefix hj hprefix
  have hA := segment_mono hA0 (show address.length + 1 ≤ B from
    Nat.add_le_add_right (Nat.le_max_left _ _) _)
  have hB := segment_mono (reader_segment hB0) (show template.length + 1 ≤ B from
    Nat.add_le_add_right (Nat.le_max_right _ _) _)
  have hA' := relocateBanks_segment skip addressBank hA
    (heads := fun _ => 0) (cells := fun _ => work template) (by simp)
  have hB' := relocateBanks_segment reader valueBank hB
    (heads := fun _ => 0) (cells := fun _ => work done) (by simp)
  have hAh : (skip.relocateBanks addressBank).step word
      (skip.bankConfig addressBank (cfg done 5 a 0 out) (fun _ => 0) (fun _ => work template)) = none := by
    rw [relocateBanks_step, hh]
    rfl
  let cB := reader.bankConfig valueBank (readerConfig (cfg result 9 (a+template.length) 0 out))
    (fun _ => 0) (fun _ => work done)
  have hBh : (reader.relocateBanks valueBank).step word cB = none := by
    change (reader.relocateBanks valueBank).step word
      (reader.bankConfig valueBank (readerConfig (cfg result 9 (a+template.length) 0 out)) _ _) = none
    rw [relocateBanks_step, reader_step, hhalt]
    rfl
  rw [← transfer_ready done template out a] at hB'
  refine ⟨k + 1 + j, thenRight skip reader addressBank valueBank cB,
    thenSegment skip reader addressBank valueBank hA' hAh hB', ?_, ?_, rfl, rfl, ?_⟩
  · change (thenMachine skip reader addressBank valueBank).step word
      (thenRight skip reader addressBank valueBank cB) = none
    rw [thenStep_right, hBh]
    rfl
  · rfl
  · intro i
    fin_cases i <;> rfl

/-- Prepared-address entry reader at the actual encoded Cayley table. All
reachable work heads obey the logarithmic bound in the original input length. -/
theorem physicalCayleyEntry (n : ℕ) (M : Mul (Fin n)) (row col : Fin n)
    (out : List Bool) :
    let word := @encodeCayley n M
    let W := Nat.log2 (word.length + 1) + 1
    let address := encodeLabel W (TableIO.offset n row.val col.val)
    let template := List.replicate (TableIO.width n) false
    ∃ (t : ℕ) (c : machine.Config),
      machine.BoundedSegment word (2 * W) (entryConfig address template out) c t ∧
      machine.step word c = none ∧
      c.workCell ⟨1, by decide⟩ = work (encodeLabel (TableIO.width n) (M.mul row col).val) ∧
      c.outputReversed = out := by
  let word := @encodeCayley n M
  let W := Nat.log2 (word.length + 1) + 1
  let a := TableIO.offset n row.val col.val
  let w := TableIO.width n
  let address := encodeLabel W a
  let template := List.replicate w false
  have hw : 0 < w := by simp [w, TableIO.width]
  have hlast := @TableIO.tableAddress_lt_inputLength n M row col (w - 1) (by omega)
  change a + (w - 1) < word.length at hlast
  have haddr : a < 2 ^ W := by
    have h : word.length + 1 < 2 ^ W := Nat.lt_log2_self
    omega
  have hd : digits address = a := digits_encodeLabel _ _ haddr
  have ht : template.length = w := List.length_replicate
  have hl : address.length = W := length_encodeLabel _ _
  have hinput : digits address + template.length ≤ word.length := by omega
  obtain ⟨t, c, hr, hh, hc, _, hout, _⟩ := physicalRead word address template out hinput
  have hn : n ≤ word.length + 1 := by
    change n ≤ (@encodeCayley n M).length + 1
    rw [@length_encodeCayley n M]
    omega
  have hn0 : n ≠ 0 := by
    have hr := row.isLt
    omega
  have hlog : n.log2 ≤ (word.length + 1).log2 := (Nat.le_log2 (by omega)).mpr
    ((Nat.log2_self_le hn0).trans hn)
  have hwW : w ≤ W := Nat.add_le_add_right hlog 1
  rw [hl, ht, max_eq_left hwW] at hr
  have hW : 0 < W := by simp [W]
  rw [hd, ht, window_encodeCayley n M row col] at hc
  have hbound : W + 1 ≤ 2 * W := by omega
  exact ⟨t, c, segment_mono hr hbound, hh, hc, hout⟩

end Mathproof.MinimumGeneration.PhysicalEntry
