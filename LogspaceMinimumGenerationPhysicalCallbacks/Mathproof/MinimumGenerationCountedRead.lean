import Mathproof.MinimumGenerationPhysicalEntry
import Mathproof.MinimumGenerationStrideSkip

namespace Mathproof.MinimumGeneration.CountedRead

open SearchTransducer
open InputPosition (cfg digits window work)
open PhysicalEntry (reader readerConfig reader_step reader_segment segment_mono segment_of_prefix)
open StrideSkip (strideSkip liftedConfig)

private def strideBanks : Fin strideSkip.workTapes ↪ Fin 2 :=
  Function.Embedding.refl (Fin 2)

private def captureBank : Fin reader.workTapes ↪ Fin 2 where
  toFun _ := 1
  inj' i j _ := by
    change Fin 1 at i j
    exact Subsingleton.elim i j

def machine : SearchTransducer := thenMachine strideSkip reader strideBanks captureBank

private def liftStride (c : strideSkip.Config) : (strideSkip.relocateBanks strideBanks).Config :=
  strideSkip.bankConfig strideBanks c (fun _ => 0) (fun _ _ => none)

/-- Prepared count and width banks at a supplied live input position. -/
def start (a : ℕ) (count template prior : List Bool) : machine.Config :=
  thenLeft strideSkip reader strideBanks captureBank
    (liftStride (liftedConfig a template (cfg count 0 0 0 prior)))

/-- One bounded physical run skips whole entries and reads the requested
fixed-width block. Its count is a binary block number relative to the live
input position. -/
theorem run (word count template prior : List Bool) (a : ℕ)
    (ha : a + template.length * digits count + template.length ≤ word.length) :
    ∃ (t : ℕ) (c : machine.Config),
      machine.BoundedSegment word (max count.length template.length + 1)
        (start a count template prior) c t ∧ machine.step word c = none ∧
      c.workCell ⟨1, by decide⟩ = work (window word (a + template.length * digits count) template.length) ∧
      c.inputHead = (↑(a + template.length * digits count + template.length) : Int) ∧
      c.outputReversed = prior ∧ (∀ i, c.workHead i = 0) := by
  let atBit := a + template.length * digits count
  let B := max count.length template.length + 1
  obtain ⟨k, done, hlen, hstride, hhalt⟩ := StrideSkip.skipStride_bounded word count template prior a (by omega)
  let mid0 := StrideSkip.config (5 : Fin 13)
    ((a : Int) + (template.length : Int) * (digits count : Int))
    0 0 (work done) template prior
  change strideSkip.BoundedSegment word B _ mid0 k at hstride
  change strideSkip.step word mid0 = none at hhalt
  let midpoint := liftStride mid0
  have hSeg : (strideSkip.relocateBanks strideBanks).BoundedSegment word B
      (liftStride (liftedConfig a template (cfg count 0 0 0 prior))) midpoint k :=
    relocateBanks_segment strideSkip strideBanks hstride
      (heads := fun _ => 0) (cells := fun _ _ => none) (by simp)
  obtain ⟨u, he, hh, hp⟩ := InputPosition.capture_correct word template prior atBit ha
  let result := window word atBit template.length
  have hBody := reader_segment (segment_of_prefix he hp)
  have hwide := segment_mono hBody (show template.length+1 ≤ B from
    Nat.add_le_add_right (Nat.le_max_right _ _) _)
  have hRelocB := relocateBanks_segment reader captureBank hwide
    (heads := fun _ => 0) (cells := fun _ => work done) (by simp)
  let firstExit := thenEntry strideSkip reader strideBanks captureBank midpoint
  let readerStart := reader.bankConfig captureBank (readerConfig (cfg template 6 atBit 0 prior))
    (fun _ => 0) (fun _ => work done)
  have hw : firstExit = readerStart := by
    have hh : firstExit.workHead = readerStart.workHead := by
      funext i
      fin_cases i <;> rfl
    have hc : firstExit.workCell = readerStart.workCell := by
      funext i
      fin_cases i <;> rfl
    have hi : (a : Int) + (template.length : Int) * (digits count : Int) = (atBit : Int) := by
      simp [atBit]
    change (⟨reader.initialState, _, firstExit.workHead, firstExit.workCell, prior⟩ :
      (reader.relocateBanks captureBank).Config) = readerStart
    have hip : midpoint.inputHead = (atBit : Int) := hi
    rw [hip, hh, hc]
    rfl
  change (reader.relocateBanks captureBank).BoundedSegment word B readerStart _ u at hRelocB
  rw [← hw] at hRelocB
  have hHaltReloc : (strideSkip.relocateBanks strideBanks).step word midpoint = none := by
    change (strideSkip.relocateBanks strideBanks).step word (strideSkip.bankConfig strideBanks _ _ _) = none
    rw [relocateBanks_step, hhalt]
    rfl
  let after := reader.bankConfig captureBank
    (readerConfig (cfg result 9 (atBit+template.length) 0 prior)) (fun _ => 0) (fun _ => work done)
  have hAfter : (reader.relocateBanks captureBank).step word after = none := by
    unfold after
    rw [relocateBanks_step, reader_step, hh]
    rfl
  refine ⟨k+1+u, thenRight strideSkip reader strideBanks captureBank after,
    thenSegment strideSkip reader strideBanks captureBank hSeg hHaltReloc hRelocB,
    ?_, rfl, rfl, rfl, ?_⟩
  · change (thenMachine strideSkip reader strideBanks captureBank).step word
      (thenRight strideSkip reader strideBanks captureBank after) = none
    rw [thenStep_right, hAfter]
    rfl
  · intro i
    fin_cases i <;> rfl

theorem counted_cayley (n : ℕ) (M : Mul (Fin n)) (row col : Fin n) (prior : List Bool) :
    let word := @encodeCayley n M
    let w := TableIO.width n
    let index := encodeLabel (2*w) (row.val*n + col.val)
    let zero := List.replicate w false
    let cap := Nat.log2 (word.length + 1) + 1
    ∃ (t : ℕ) (c : machine.Config),
      machine.BoundedSegment word (3*cap) (start (n+1) index zero prior) c t ∧
      machine.step word c = none ∧ c.workCell ⟨1, by decide⟩ =
        work (encodeLabel w (M.mul row col).val) ∧ c.outputReversed = prior := by
  let word := @encodeCayley n M
  let w := TableIO.width n
  let index := encodeLabel (2*w) (row.val*n + col.val)
  let zero := List.replicate w false
  let cap := Nat.log2 (word.length + 1) + 1
  have hn : 0 < n := Nat.zero_lt_of_lt row.isLt
  have hw : 0 < w := by simp [w, TableIO.width]
  have hnPow : n < 2^w := Nat.lt_log2_self
  have hindex : row.val*n + col.val < n*n := by
    have hm := Nat.mul_le_mul_right n (show row.val+1 ≤ n by omega)
    rw [Nat.succ_mul] at hm
    omega
  have hpow : row.val*n + col.val < 2^(2*w) := by
    rw [Nat.mul_comm 2 w, Nat.pow_mul, Nat.pow_two]
    exact hindex.trans_le (Nat.mul_le_mul (Nat.le_of_lt hnPow) (Nat.le_of_lt hnPow))
  have hcode : digits index = row.val*n + col.val := InputPosition.digits_encodeLabel _ _ hpow
  have hzero : zero.length = w := List.length_replicate
  have hwidth : index.length = 2*w := length_encodeLabel _ _
  have ha : n+1 + zero.length * digits index = TableIO.offset n row.val col.val := by
    rw [hcode, hzero]
    simp [TableIO.offset, w, Nat.mul_comm]
  have hlast := @TableIO.tableAddress_lt_inputLength n M row col (w-1) (by omega)
  change TableIO.offset n row.val col.val + (w-1) < word.length at hlast
  have hreach : n+1 + zero.length * digits index + zero.length ≤ word.length := by
    rw [ha, hzero]
    omega
  obtain ⟨t,c,hr,hh,hc,_,hout,_⟩ := run word index zero prior (n+1) hreach
  have hlen : n ≤ word.length + 1 := by
    change n ≤ (@encodeCayley n M).length + 1
    rw [@length_encodeCayley n M]
    omega
  have hlog : n.log2 ≤ (word.length+1).log2 := (Nat.le_log2 (by omega)).mpr
    ((Nat.log2_self_le (by omega)).trans hlen)
  have hcap : w ≤ cap := Nat.add_le_add_right hlog 1
  have hmax : max index.length zero.length + 1 ≤ 3*cap := by
    rw [hwidth, hzero, max_eq_left (by omega : w ≤ 2*w)]
    omega
  rw [ha, hzero, InputPosition.window_encodeCayley n M row col] at hc
  exact ⟨t,c,segment_mono hr hmax,hh,hc,hout⟩

end Mathproof.MinimumGeneration.CountedRead
