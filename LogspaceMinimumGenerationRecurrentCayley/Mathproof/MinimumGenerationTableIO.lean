import Mathproof.MinimumGenerationProblem
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

namespace Mathproof.MinimumGeneration.TableIO

def width (n : ℕ) : ℕ := Nat.log2 n + 1

def offset (n row col : ℕ) : ℕ := n + 1 + (row * n + col) * width n

def inputBit (word : List Bool) (i : ℕ) : Bool :=
  (word[i]?).getD false

/-- Scan a unary header with one accumulating counter. -/
def scanOrder : List Bool → ℕ → ℕ
  | true :: tail, acc => scanOrder tail (acc + 1)
  | _, acc => acc

theorem scanOrder_header (n acc : ℕ) (body : List Bool) :
    scanOrder (List.replicate n true ++ false :: body) acc = acc + n := by
  induction n generalizing acc with
  | zero => simp [scanOrder]
  | succ n ih =>
    simpa [List.replicate_succ, scanOrder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (acc + 1)

@[simp] theorem scanOrder_encodeCayley (n : ℕ) [Mul (Fin n)] :
    scanOrder (encodeCayley n) 0 = n := by
  simp [encodeCayley, scanOrder_header, List.append_assoc]

/-- An indexed bit of a concatenation of fixed-width blocks. -/
private theorem getBlockBit {α β : Type*} (xs : List α) (f : α → List β) (w : ℕ)
    (hwidth : ∀ x, (f x).length = w) (i k : ℕ) (hi : i < xs.length) (hk : k < w) :
    (xs.flatMap f)[i * w + k]? = (f xs[i])[k]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa [hwidth] using hk)]
    | succ i =>
      have hh : (f x).length ≤ (i + 1) * w + k := by
        rw [hwidth, Nat.succ_mul]
        omega
      have ha : (i + 1) * w + k - (f x).length = i * w + k := by
        rw [hwidth, Nat.succ_mul]
        omega
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right hh, ha]
      exact ih i (by simpa using hi)

private theorem lengthFlatMap {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hwidth : ∀ x, (f x).length = w) :
    (xs.flatMap f).length = xs.length * w := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, hwidth, Nat.succ_mul, Nat.add_comm]

private theorem labelBit (w a k : ℕ) (hk : k < w) :
    (encodeLabel w a)[k]? = some (a.testBit k) := by
  simp [encodeLabel, List.getElem?_eq_getElem (by simpa using hk : k < (List.range w).length),
    List.getElem_range]

/-- The raw bit address really reads the requested multiplication-table entry. -/
theorem tableBit_correct (n : ℕ) [Mul (Fin n)] (row col : Fin n)
    (k : ℕ) (hk : k < width n) :
    (encodeCayley n)[offset n row.val col.val + k]? =
      some ((row * col).val.testBit k) := by
  let rowBits := fun r : Fin n =>
    (List.finRange n).flatMap (fun c => encodeLabel (width n) (r * c).val)
  have hrow (r : Fin n) : (rowBits r).length = n * width n := by
    change ((List.finRange n).flatMap (fun c => encodeLabel (width n) (r * c).val)).length = _
    rw [lengthFlatMap _ _ (width n) (by simp), List.length_finRange]
  have hcol (r : Fin n) (c : Fin n) : (encodeLabel (width n) (r * c).val).length = width n :=
    length_encodeLabel _ _
  have hkrow : col.val * width n + k < n * width n := by
    have h := Nat.mul_le_mul_right (width n) (show col.val + 1 ≤ n from col.isLt)
    rw [Nat.succ_mul] at h
    omega
  change (List.replicate n true ++ [false] ++ (List.finRange n).flatMap rowBits)[n + 1 + (row.val * n + col.val) * width n + k]? = _
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have haddr : n + 1 + (row.val * n + col.val) * width n + k - (n + 1) =
      row.val * (n * width n) + (col.val * width n + k) := by
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  rw [haddr, getBlockBit _ _ _ hrow row.val _ (by simpa using row.isLt) hkrow]
  simp only [List.getElem_finRange]
  change (rowBits row)[col.val * width n + k]? = _
  change ((List.finRange n).flatMap (fun c => encodeLabel (width n) (row * c).val))[col.val * width n + k]? = _
  rw [getBlockBit _ _ _ (hcol row) col.val k (by simpa using col.isLt) hk]
  simp only [List.getElem_finRange]
  exact labelBit _ _ _ hk

/-- High-to-low binary scan. Its recursion is tail-position and carries a
single value and a descending position. -/
def readBits (bitAt : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | fuel + 1, acc => readBits bitAt fuel (Nat.bit (bitAt fuel) acc)

theorem readBits_testBit (bitAt : ℕ → Bool) (w acc i : ℕ) :
    (readBits bitAt w acc).testBit i =
      if i < w then bitAt i else acc.testBit (i - w) := by
  induction w generalizing acc i with
  | zero => simp [readBits]
  | succ w ih =>
    rw [readBits, ih]
    by_cases h : i < w
    · simp [h, show i < w + 1 by omega]
    · by_cases he : i = w
      · subst i
        cases bitAt w <;> simp [Nat.testBit, Nat.bit]
      · have hi : w + 1 ≤ i := by omega
        have hs : i - w = (i - (w + 1)) + 1 := by omega
        rw [if_neg h, if_neg (by omega : ¬ i < w + 1), hs]
        exact Nat.testBit_bit_succ _ _ _

theorem readBits_correct (a w : ℕ) (h : a < 2 ^ w) :
    readBits a.testBit w 0 = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [readBits_testBit]
  split
  · rfl
  · have hh : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.testBit_eq_false_of_lt (h.trans_le hh)]

/-- Executable access to a raw table entry. The input list remains immutable. -/
def readEntry (word : List Bool) (n row col : ℕ) : ℕ :=
  readBits (fun k => inputBit word (offset n row col + k)) (width n) 0

theorem readEntry_correct (n : ℕ) [Mul (Fin n)] (row col : Fin n) :
    readEntry (encodeCayley n) n row.val col.val = (row * col).val := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [readEntry, readBits_testBit]
  split
  · simp [inputBit, tableBit_correct n row col k (by assumption)]
  · have hv : (row * col).val < 2 ^ width n :=
      (row * col).isLt.trans (Nat.lt_log2_self (n := n))
    have hp : 2 ^ width n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.testBit_eq_false_of_lt (hv.trans_le hp)]

/-- The address counter is bounded by the actual input length. -/
theorem tableAddress_lt_inputLength (n : ℕ) [Mul (Fin n)] (row col : Fin n)
    (k : ℕ) (hk : k < width n) :
    offset n row.val col.val + k < (encodeCayley n).length := by
  have h := tableBit_correct n row col k hk
  exact (List.getElem?_eq_some_iff.mp h).1

/-- Search candidates in order while retaining just the current label and fuel. -/
def firstLabel (accept : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, atLabel =>
    if accept atLabel then some atLabel else firstLabel accept fuel (atLabel + 1)

theorem firstLabel_correct {accept : ℕ → Bool} {start fuel target : ℕ}
    (h : ∀ i, start ≤ i → i < start + fuel → (accept i = true ↔ i = target))
    (hlo : start ≤ target) (hhi : target < start + fuel) :
    firstLabel accept fuel start = some target := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases he : start = target
    · subst start
      have hp := (h target hlo (by omega)).2 rfl
      simp [firstLabel, hp]
    · have hp : accept start = false := by
        cases hb : accept start
        · rfl
        · exact (he ((h start (by omega) (by omega)).1 hb)).elim
      simp only [firstLabel, hp, Bool.false_eq_true, ↓reduceIte]
      apply ih
      · intro i hil hih
        exact h i (by omega) (by omega)
      · omega
      · omega

def readIdentity (word : List Bool) (n : ℕ) : Option ℕ :=
  firstLabel (fun i => decide (readEntry word n i i = i)) n 0

theorem readIdentity_correct (n : ℕ) (G : Group (Fin n)) :
    readIdentity (@encodeCayley n G.toMul) n = some G.toOne.one.val := by
  letI := G
  letI : Mul (Fin n) := G.toMul
  letI : One (Fin n) := G.toOne
  apply firstLabel_correct
  · intro i _ hi
    let g : Fin n := ⟨i, by omega⟩
    change decide (readEntry (encodeCayley n) n g.val g.val = g.val) = true ↔ _
    rw [readEntry_correct, decide_eq_true_eq]
    constructor
    · intro hh
      have hg : g * g = g := Fin.ext hh
      have hg1 : g = 1 := mul_left_cancel (show g * g = g * 1 by simpa using hg)
      exact congrArg Fin.val hg1
    · intro hh
      have hg : g = 1 := Fin.ext hh
      simp [hg]
  · exact Nat.zero_le _
  · simpa using (1 : Fin n).isLt

def readInverse (word : List Bool) (n a identity : ℕ) : Option ℕ :=
  firstLabel (fun i => decide (readEntry word n a i = identity)) n 0

theorem readInverse_correct (n : ℕ) (G : Group (Fin n)) (a : Fin n) :
    readInverse (@encodeCayley n G.toMul) n a.val G.toOne.one.val = some (G.toInv.inv a).val := by
  letI := G
  letI : Mul (Fin n) := G.toMul
  letI : One (Fin n) := G.toOne
  letI : Inv (Fin n) := G.toInv
  apply firstLabel_correct
  · intro i _ hi
    let b : Fin n := ⟨i, by omega⟩
    change decide (readEntry (encodeCayley n) n a.val b.val = (1 : Fin n).val) = true ↔ _
    rw [readEntry_correct, decide_eq_true_eq]
    constructor
    · intro hh
      have hab : a * b = 1 := Fin.ext hh
      have hb : b = a⁻¹ := mul_left_cancel (hab.trans (mul_inv_cancel a).symm)
      exact congrArg Fin.val hb
    · intro hh
      have hb : b = a⁻¹ := Fin.ext hh
      simp [hb]
  · exact Nat.zero_le _
  · simpa using (a⁻¹ : Fin n).isLt



/-- The accumulating scan never requires more bits than its input width plus
the width of the incoming accumulator. -/
theorem readBits_width (bitAt : ℕ → Bool) (w acc cap : ℕ) (ha : acc < 2 ^ cap) :
    readBits bitAt w acc < 2 ^ (cap + w) := by
  induction w generalizing acc cap with
  | zero => simpa [readBits] using ha
  | succ w ih =>
    rw [readBits]
    have hb : Nat.bit (bitAt w) acc < 2 ^ (cap + 1) := by
      rw [Nat.pow_succ, Nat.bit_val]
      cases bitAt w <;> simp <;> omega
    exact (show cap + 1 + w = cap + (w + 1) by omega) ▸
      ih _ _ hb

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

/-- Copy one prepared label from a work tape to the write-only output. Each
transition reads one cell, advances one place, and emits precisely that bit. -/
def labelEmitter : SearchTransducer where
  states := 1
  workTapes := 1
  initialState := 0
  transition _ _ cells :=
    (cells 0).map (fun bit => (0, .stay, (fun _ => ⟨none, .right⟩), some bit))

private def emitterConfig (bits prior : List Bool) (inputHead : Int) (j : ℕ) :
    labelEmitter.Config :=
  ⟨labelEmitter.initialState, inputHead, fun _ => (j : Int), fun _ x => if x < 0 then none else bits[x.toNat]?,
    (bits.take j).reverse ++ prior.reverse⟩

private theorem labelEmitter_step (word bits prior : List Bool) (inputHead : Int) (j : ℕ)
    (hj : j < bits.length) :
    labelEmitter.step word (emitterConfig bits prior inputHead j) =
      some (emitterConfig bits prior inputHead (j + 1)) := by
  have hread : (if (j : Int) < 0 then none else bits[(j : Int).toNat]?) =
      some bits[j] := by
    simp [List.getElem?_eq_getElem hj]
  unfold SearchTransducer.step
  change (Option.map _ (Option.map _ (if (j : Int) < 0 then none else bits[(j : Int).toNat]?))) =
    some (emitterConfig bits prior inputHead (j + 1))
  rw [hread]
  simp only [Option.map, Option.some.injEq, emitterConfig, moveOffset, Int.add_zero,
    Option.getD_none, Int.natCast_succ, List.take_succ_eq_append_getElem hj,
    List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append, Option.elim]
  congr 1
  funext i x
  by_cases hx : x = (j : Int) <;> simp only [hx, if_true, if_false]

private theorem labelEmitter_halts (word bits prior : List Bool) (inputHead : Int) :
    labelEmitter.step word (emitterConfig bits prior inputHead bits.length) = none := by
  simp [SearchTransducer.step, labelEmitter, emitterConfig]

/-- Execute a prepared macro from an explicit caller configuration. -/
def afterFrom (M : SearchTransducer) (word : List Bool) (start : M.Config) :
    ℕ → Option M.Config
  | 0 => some start
  | k + 1 => (afterFrom M word start k).bind (M.step word)

theorem labelEmitter_prefix (word bits prior : List Bool) (inputHead : Int) (k : ℕ)
    (hk : k ≤ bits.length) :
    afterFrom labelEmitter word (emitterConfig bits prior inputHead 0) k =
      some (emitterConfig bits prior inputHead k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [afterFrom, ih (by omega)]
    exact labelEmitter_step word bits prior inputHead k (by omega)

/-- The finite-control emitter appends exactly the prepared label in order.
Every visited work position is bounded by the encoded label width. -/
theorem labelEmitter_correct (word prior : List Bool) (inputHead : Int) (w a : ℕ) :
    ∃ c : labelEmitter.Config,
      afterFrom labelEmitter word (emitterConfig (encodeLabel w a) prior inputHead 0) w = some c ∧
      labelEmitter.step word c = none ∧ c.outputReversed.reverse = prior ++ encodeLabel w a ∧
      ∀ (k : ℕ) (d : labelEmitter.Config),
        afterFrom labelEmitter word (emitterConfig (encodeLabel w a) prior inputHead 0) k = some d →
        ∀ i, (d.workHead i).natAbs ≤ w := by
  let bits := encodeLabel w a
  have hw : bits.length = w := length_encodeLabel _ _
  refine ⟨emitterConfig bits prior inputHead w, ?_, ?_, ?_, ?_⟩
  · exact labelEmitter_prefix _ _ _ _ _ hw.ge
  · simpa only [hw] using labelEmitter_halts word bits prior inputHead
  · change ((bits.take w).reverse ++ prior.reverse).reverse = prior ++ bits
    rw [← hw, List.take_length]
    simp
  · intro k d h i
    have hk : k ≤ w := by
      by_contra! hlt
      have hnone (j : ℕ) :
          afterFrom labelEmitter word (emitterConfig bits prior inputHead 0) (w + 1 + j) = none := by
        induction j with
        | zero =>
          simp only [afterFrom]
          rw [labelEmitter_prefix word bits prior inputHead w hw.ge]
          change labelEmitter.step word (emitterConfig bits prior inputHead w) = none
          simpa only [hw] using labelEmitter_halts word bits prior inputHead
        | succ j ih =>
          rw [Nat.add_succ, afterFrom, ih]
          rfl
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show w + 1 ≤ k by omega)
      have hn := hnone j
      rw [← hj] at hn
      change afterFrom labelEmitter word (emitterConfig bits prior inputHead 0) k = some d at h
      rw [h] at hn
      contradiction
    have hd := labelEmitter_prefix word bits prior inputHead k (by omega)
    have he : d = emitterConfig bits prior inputHead k := by
      apply Option.some.inj
      exact h.symm.trans hd
    simpa [he, emitterConfig] using hk



/-- Decode a group-element label with explicit range checking. -/
def boundedLabel (n value : ℕ) : Option (Fin n) :=
  if h : value < n then some ⟨value, h⟩ else none

def mulLabel (word : List Bool) (n : ℕ) (a b : Fin n) : Option (Fin n) :=
  boundedLabel n (readEntry word n a.val b.val)

theorem mulLabel_correct (n : ℕ) (M : Mul (Fin n)) (a b : Fin n) :
    mulLabel (@encodeCayley n M) n a b = some (M.mul a b) := by
  have hc : readEntry (@encodeCayley n M) n a.val b.val = (M.mul a b).val :=
    @readEntry_correct n M a b
  unfold mulLabel boundedLabel
  rw [hc, dif_pos (M.mul a b).isLt]

/-- All active address and accumulator labels in a raw entry query fit the
same input-dependent bit width. The accumulator represents a high-bit prefix,
while the next-position counter is charged separately. -/
theorem entryRegisterBounds (n : ℕ) (M : Mul (Fin n)) (row col : Fin n)
    (remaining : ℕ) (hr : remaining < width n) :
    let word := @encodeCayley n M
    let W := Nat.log2 (word.length + 1) + 1
    offset n row.val col.val + remaining < 2 ^ W ∧
      remaining < 2 ^ W ∧
      readBits (fun k => inputBit word (offset n row.val col.val + remaining + k))
        (width n - remaining) 0 < 2 ^ W := by
  dsimp only
  let word := @encodeCayley n M
  let W := Nat.log2 (word.length + 1) + 1
  change offset n row.val col.val + remaining < 2 ^ W ∧
      remaining < 2 ^ W ∧
      readBits (fun k => inputBit word (offset n row.val col.val + remaining + k))
        (width n - remaining) 0 < 2 ^ W
  have hn : n ≤ word.length := by
    change n ≤ (@encodeCayley n M).length
    rw [@length_encodeCayley n M]
    omega
  have hw : width n ≤ W := by
    have hn0 : n ≠ 0 := by
      have := row.isLt
      omega
    have hp : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).1 le_rfl
    have hlog := (Nat.le_log2 (by omega : word.length + 1 ≠ 0)).2
      (hp.trans (by omega : n ≤ word.length + 1))
    exact Nat.add_le_add_right hlog 1
  have haddr := @tableAddress_lt_inputLength n M row col remaining hr
  change offset n row.val col.val + remaining < word.length at haddr
  have hpow : word.length + 1 < 2 ^ W := Nat.lt_log2_self
  have hbit : readBits (fun k => inputBit word (offset n row.val col.val + remaining + k))
      (width n - remaining) 0 < 2 ^ (width n - remaining) := by
    simpa using readBits_width
      (fun k => inputBit word (offset n row.val col.val + remaining + k))
      (width n - remaining) 0 0 (by decide)
  have hW : W < 2 ^ W := Nat.lt_two_pow_self
  refine ⟨by omega, by omega, hbit.trans_le ?_⟩
  exact Nat.pow_le_pow_right (by decide) (by omega)



def rawDifference (word : List Bool) (n identity : ℕ) (x y : Fin n) : Option (Fin n) := do
  let inverse ← readInverse word n x.val identity
  let xInv ← boundedLabel n inverse
  mulLabel word n xInv y

theorem rawDifference_correct (n : ℕ) (G : Group (Fin n)) (x y : Fin n) :
    rawDifference (@encodeCayley n G.toMul) n G.toOne.one.val x y =
      some (G.toMul.mul (G.toInv.inv x) y) := by
  unfold rawDifference
  rw [readInverse_correct n G]
  change (boundedLabel n (G.toInv.inv x).val).bind _ = _
  rw [show boundedLabel n (G.toInv.inv x).val = some (G.toInv.inv x) by
    unfold boundedLabel
    rw [dif_pos (G.toInv.inv x).isLt]]
  exact mulLabel_correct n G.toMul (G.toInv.inv x) y

/-- Evaluate virtual Cayley adjacency directly by consulting the encoded table. -/
def cayleyAdjBit (word : List Bool) (n identity : ℕ) (allowed : Fin n → Bool)
    (x y : Fin n) : Bool :=
  if x = y then false
  else ((rawDifference word n identity x y).map allowed).getD false ||
    ((rawDifference word n identity y x).map allowed).getD false

theorem cayleyAdjBit_correct (n : ℕ) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (x y : Fin n) :
    cayleyAdjBit (@encodeCayley n G.toMul) n G.toOne.one.val allowed x y = true ↔
      (@SimpleGraph.mulCayley (Fin n) {a | allowed a = true} G.toMul).Adj x y := by
  letI := G
  letI : Mul (Fin n) := G.toMul
  letI : Inv (Fin n) := G.toInv
  rw [SimpleGraph.mulCayley_adj]
  unfold cayleyAdjBit
  rw [rawDifference_correct n G, rawDifference_correct n G]
  by_cases h : x = y <;> simp [h] <;> rfl

end Mathproof.MinimumGeneration.TableIO
