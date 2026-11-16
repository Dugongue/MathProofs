import Mathproof.MinimumGenerationVirtualCallbackDriver

namespace Mathproof.MinimumGeneration.VirtualMarkerScan

open Mathproof.Multitape SearchTransducer
open TapeArithmetic (block)
open TapeRegisters (done)

variable {W K : ℕ} (address : Fin W) (marker : Fin K → Fin W)

/-- Compare the live address with each of a fixed tuple of marked positions.
The first successful equality exits in the corresponding stage. -/
abbrev stages (first : Fin K) : Stages K 7 W where
  first := first
  entry := fun _ => 0
  transition i := (TapeRegisters.machine address (marker i) .compare).transition
  next i control :=
    if control = done true then none
    else if h : i.val + 1 < K then some ⟨i.val + 1, h⟩ else none

abbrev machine (first : Fin K) : SearchTransducer := (stages address marker first).machine

def verdict (first : Fin K) (c : (machine address marker first).Config) : Option (Fin K) :=
  let (i, q) := finProdFinEquiv.symm c.state
  if q = done true then some i else none

private theorem compareFalse : done false ≠ done true := by decide

def entry (first i : Fin K) (real : Int) (heads : Fin W → Int)
    (cells : Fin W → Int → Option Bool) (output : List Bool) :
    ((stages address marker first).component i).Config :=
  ⟨0, real, heads, cells, output⟩

/-- The compared work tapes are live, fixed-width binary registers. The larger
frame is shared with the reader and remains available in the same layout. -/
structure Layout (raw : List Bool) (B w p : ℕ) (values : Fin K → ℕ)
    (real : Int) (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) : Prop where
  addressFit : p < 2 ^ w
  markerFit : ∀ i, values i < 2 ^ w
  realBounds : (-1 : Int) ≤ real ∧ real ≤ (raw.length : Int)
  windows : ∀ i j z, heads j ≤ z →
    z ≤ TapeRegisters.finish heads address (marker i) (w + 1) j →
    z.natAbs ≤ B
  addressWord : block (cells address) (heads address + 1) (encodeLabel w p)
  addressEnd : cells address (heads address + w + 1) = none
  markerWord : ∀ i, block (cells (marker i)) (heads (marker i) + 1) (encodeLabel w (values i))
  markerStart : ∀ i, cells (marker i) (heads (marker i)) = none
  markerEnd : ∀ i, cells (marker i) (heads (marker i) + w + 1) = none

private theorem encoded_length (w x : ℕ) : (encodeLabel w x).length = w := by simp [encodeLabel]

private theorem width_eq {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    encodeLabel w x = encodeLabel w y ↔ x = y := by
  constructor
  · intro h
    have e := congrArg InputPosition.digits h
    simpa only [InputPosition.digits_encodeLabel _ _ hx, InputPosition.digits_encodeLabel _ _ hy] using e
  · rintro rfl; rfl

/-- Execute all necessary bank comparisons in the same finite search
controller. A missing verdict certifies that the address is outside the
examined marked positions. -/
theorem execute {raw : List Bool} {B w p : ℕ} {values : Fin K → ℕ}
    {real : Int} {heads : Fin W → Int} {cells : Fin W → Int → Option Bool} (output : List Bool)
    (L : Layout address marker raw B w p values real heads cells) (first i : Fin K) :
    ∃ (len : ℕ) (result : (machine address marker first).Config),
      (machine address marker first).BoundedSegment raw B
        ((stages address marker first).tag i (entry address marker first i real heads cells output))
        result len ∧ (machine address marker first).step raw result = none ∧
      result.inputHead = real ∧ result.workHead = heads ∧ result.workCell = cells ∧
      result.outputReversed = output ∧
      (∀ hit, verdict address marker first result = some hit → p = values hit) ∧
      (verdict address marker first result = none → ∀ j, i.val ≤ j.val → p ≠ values j) := by
  let T := stages address marker first
  let A := fun k : Fin K => TapeRegisters.machine address (marker k) .compare
  let start := entry address marker first i real heads cells output
  obtain ⟨out, equal, run, state, verdictEq, outHeads, outCells, outInput, outOutput⟩ :=
    TapeRegisters.executeCompare (source := address) (target := marker i) raw start
      (encodeLabel w p) (encodeLabel w (values i))
      (by simp only [encoded_length]) rfl (L.markerStart i)
      (by simpa only [encoded_length, start, entry] using L.addressEnd)
      (by simpa only [encoded_length, start, entry] using L.markerEnd i) L.addressWord (L.markerWord i)
  have qr : (A i).BoundedSegment raw B start out (2 * w + 3) := by
    simpa only [encoded_length] using
      run.boundedSegment L.realBounds (by simpa only [encoded_length, start, entry] using L.windows i)
  have stops : (A i).step raw out = none := TapeRegisters.step_done raw out equal state
  have iffEq : equal = true ↔ p = values i :=
    verdictEq.trans (width_eq L.addressFit (L.markerFit i))
  have outFrame : ∀ j, T.enter j out = entry address marker first j real heads cells output := by
    intro j
    simp only [Stages.enter, entry, T, stages, outHeads, outInput, outCells, outOutput, start]
  cases equal with
  | true =>
    have hnext : T.next i out.state = none := by simp [T, state]
    have hstop : T.machine.step raw (T.tag i out) = none := by
      rw [T.step_halt i stops, hnext]
      rfl
    refine ⟨2 * w + 3, T.tag i out, T.segment_component i qr, hstop,
      outInput, outHeads, outCells, outOutput, ?_, ?_⟩
    · intro hit h
      have he : verdict address marker first (T.tag i out) = some i := by
        simp only [verdict, Stages.tag, Equiv.symm_apply_apply, state, if_true]
      have hitEq := Option.some.inj (he.symm.trans h)
      simpa only [hitEq] using iffEq.mp rfl
    · intro h
      simp only [verdict, Stages.tag, Equiv.symm_apply_apply, state, if_true] at h
      cases h
  | false =>
    have ne : p ≠ values i := fun h => Bool.false_ne_true (iffEq.mpr h)
    by_cases hasNext : i.val + 1 < K
    · let j : Fin K := ⟨i.val + 1, hasNext⟩
      have hnext : T.next i out.state = some j := by
        simp only [T, state, compareFalse, if_false, dif_pos hasNext, j]
      have hJump := T.segment_handoff stops hnext (qr.2 _ le_rfl _ qr.1)
      rw [outFrame] at hJump
      obtain ⟨len, result, rest, halt, realEq, headsEq, cellsEq, outEq, hits, misses⟩ :=
        execute output L first j
      refine ⟨2 * w + 3 + 1 + len, result, ?_, halt, realEq, headsEq, cellsEq, outEq, hits, ?_⟩
      · exact BoundedSegment.append _ (BoundedSegment.append _ (T.segment_component i qr) hJump) rest
      · intro none k hk
        by_cases he : k = i
        · subst k
          exact ne
        · have hjk : j.val ≤ k.val := by
            have hne : k.val ≠ i.val := fun h => he (Fin.ext h)
            dsimp only [j]
            omega
          exact misses none k hjk
    · have hnext : T.next i out.state = none := by
        simp only [T, state, compareFalse, if_false, dif_neg hasNext]
      have hstop : T.machine.step raw (T.tag i out) = none := by
        rw [T.step_halt i stops, hnext]
        rfl
      have hmiss : verdict address marker first (T.tag i out) = none := by
        simp only [verdict, Stages.tag, Equiv.symm_apply_apply, state, compareFalse, if_false]
      refine ⟨2 * w + 3, T.tag i out, T.segment_component i qr, hstop,
        outInput, outHeads, outCells, outOutput, ?_, ?_⟩
      · intro hit h
        rw [hmiss] at h
        cases h
      · intro _ j hj
        have he : j = i := Fin.ext (by have := j.isLt; omega)
        simpa only [he] using ne
termination_by K - i.val
decreasing_by
  have := i.isLt
  omega

section USTCON

open Connectivity (AdjBits ustconCell ustconRead ustconHeaderLength)

/-- The shifted virtual input addresses of the five marked symbols in the
standard unary USTCON encoding. -/
def boundaryAddresses {n : ℕ} (s t : Fin n) : Fin 5 → ℕ :=
  ![0, n + 1, n + s.val + 2, ustconHeaderLength s t, ustconHeaderLength s t + n * n + 1]

def boundarySymbol : Fin 5 → InputCell :=
  ![.leftEnd, .data false, .data false, .data false, .rightEnd]

private theorem unaryHeaderBit {n : ℕ} (bits : AdjBits (Fin n)) (s t : Fin n) (i : ℕ)
    (hi : i < ustconHeaderLength s t) :
    ustconRead bits s t i = decide (i ≠ n ∧ i ≠ n + s.val + 1 ∧
      i + 1 ≠ ustconHeaderLength s t) := by
  unfold ustconRead
  rw [if_pos hi]
  change (if i < n + 1 then decide (i < n)
    else if i - (n + 1) < s.val + 1 then decide (i - (n + 1) < s.val)
    else if i - (n + 1) - (s.val + 1) < t.val + 1 then
      decide (i - (n + 1) - (s.val + 1) < t.val) else false) = _
  unfold ustconHeaderLength at hi ⊢
  split
  · congr 1
    exact propext (by omega)
  · split
    · congr 1
      exact propext (by omega)
    · split
      · congr 1
        exact propext (by omega)
      · omega

private theorem boundarySymbol_spec {n : ℕ} (bits : AdjBits (Fin n)) (s t : Fin n)
    (k : Fin 5) : ustconCell bits s t ((boundaryAddresses s t k : ℕ) - (1 : Int)) =
      boundarySymbol k := by
  have hn := s.isLt
  have ht := t.isLt
  fin_cases k
  · simp [boundaryAddresses, boundarySymbol, ustconCell]
  · have h : n < ustconHeaderLength s t := by unfold ustconHeaderLength; omega
    have h' : n < ustconHeaderLength s t + n * n := Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    have raw := unaryHeaderBit bits s t n h
    simp [boundaryAddresses, boundarySymbol, ustconCell, h', raw]
  · have h : n + s.val + 1 < ustconHeaderLength s t := by unfold ustconHeaderLength; omega
    have h' : n + s.val + 1 < ustconHeaderLength s t + n * n := Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    have raw := unaryHeaderBit bits s t (n + s.val + 1) h
    change ustconCell bits s t (((n + s.val + 2 : ℕ) : Int) - 1) = .data false
    have eq : (((n + s.val + 2 : ℕ) : Int) - 1) = ((n + s.val + 1 : ℕ) : Int) := by
      push_cast
      omega
    rw [eq]
    unfold ustconCell
    rw [if_neg (show ¬ ((n + s.val + 1 : ℕ) : Int) < 0 by omega), Int.toNat_natCast, if_pos h', raw]
    simp
  · have h : ustconHeaderLength s t - 1 < ustconHeaderLength s t := by unfold ustconHeaderLength; omega
    have h' : ustconHeaderLength s t - 1 < ustconHeaderLength s t + n * n :=
      Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    have raw := unaryHeaderBit bits s t (ustconHeaderLength s t - 1) h
    have addback : ustconHeaderLength s t - 1 + 1 = ustconHeaderLength s t := by
      unfold ustconHeaderLength; omega
    have nz : ustconHeaderLength s t ≠ 0 := by unfold ustconHeaderLength; omega
    simp [boundaryAddresses, boundarySymbol, ustconCell, h', raw, addback, nz]
  · change ustconCell bits s t (((ustconHeaderLength s t + n * n + 1 : ℕ) : Int) - 1) = .rightEnd
    have eq : (((ustconHeaderLength s t + n * n + 1 : ℕ) : Int) - 1) =
        ((ustconHeaderLength s t + n * n : ℕ) : Int) := by push_cast; omega
    rw [eq]
    unfold ustconCell
    rw [if_neg (show ¬ ((ustconHeaderLength s t + n * n : ℕ) : Int) < 0 by omega),
      Int.toNat_natCast, if_neg (Nat.lt_irrefl _)]

def headerCallback (address : Fin W) (marker : Fin 5 → Fin W) :
    VirtualCallbackDriver.Callback where
  read := machine address marker 0
  returnCell q :=
    let (i, phase) := finProdFinEquiv.symm q
    if phase = done true then boundarySymbol i else .data true

/-- Fetch the exact virtual cell at an endmarker or any unary header position,
given the four boundary registers and the virtual right end. The evaluator
returns the cell in finite control and preserves every physical tape. -/
theorem executeHeader {n : ℕ} (bits : AdjBits (Fin n)) (s t : Fin n)
    (address : Fin W) (marker : Fin 5 → Fin W) {raw : List Bool} {B w p : ℕ}
    {real : Int} {heads : Fin W → Int} {cells : Fin W → Int → Option Bool}
    (out : List Bool) (L : Layout address marker raw B w p (boundaryAddresses s t) real heads cells)
    (headerOrRight : p ≤ ustconHeaderLength s t ∨ p = ustconHeaderLength s t + n * n + 1) :
    let C := headerCallback address marker
    ∃ (len : ℕ) (result : C.read.Config),
      C.read.BoundedSegment raw B
        ((stages address marker 0).tag 0 (entry address marker 0 0 real heads cells out)) result len ∧
      C.read.step raw result = none ∧
      C.returnCell result.state = ustconCell bits s t ((p : Int) - 1) ∧
      result.inputHead = real ∧ result.workHead = heads ∧ result.workCell = cells ∧
      result.outputReversed = out := by
  dsimp only [headerCallback]
  obtain ⟨len, result, run, stop, eqReal, eqHeads, eqCells, eqOutput, pos, neg⟩ :=
    execute address marker out L (0 : Fin 5) (0 : Fin 5)
  refine ⟨len, result, run, stop, ?_, eqReal, eqHeads, eqCells, eqOutput⟩
  generalize hcode : finProdFinEquiv.symm result.state = code
  obtain ⟨i,q⟩ := code
  change (if q = done true then boundarySymbol i else .data true) = _
  by_cases hg : q = done true
  · simp only [if_pos hg]
    have parsed : verdict address marker 0 result = some i := by
      simp only [verdict, hcode, hg, if_true]
    rw [pos i parsed]
    exact (boundarySymbol_spec bits s t i).symm
  · simp only [if_neg hg]
    have parsed : verdict address marker 0 result = none := by simp only [verdict, hcode, if_neg hg]
    have no (j : Fin 5) := neg parsed j (by omega)
    have noZero : p ≠ 0 := by simpa [boundaryAddresses] using no 0
    have noFirst : p ≠ n + 1 := by simpa [boundaryAddresses] using no 1
    have noSecond : p ≠ n + s.val + 2 := by simpa [boundaryAddresses] using no 2
    have noThird : p ≠ ustconHeaderLength s t := by simpa [boundaryAddresses] using no 3
    have inHeader : p ≤ ustconHeaderLength s t := headerOrRight.resolve_right
      (by simpa [boundaryAddresses] using no 4)
    have h : p - 1 < ustconHeaderLength s t := by omega
    have hu : p - 1 < ustconHeaderLength s t + n * n := Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    have eqDec : ustconRead bits s t (p - 1) = true := by
      rw [unaryHeaderBit bits s t (p - 1) h]
      exact decide_eq_true (by omega)
    simp [ustconCell, noZero, hu, eqDec]

end USTCON


end Mathproof.MinimumGeneration.VirtualMarkerScan
