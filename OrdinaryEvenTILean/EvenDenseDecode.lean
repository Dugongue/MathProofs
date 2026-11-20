import EvenRootSpec
import Mathlib.Data.List.FinRange

namespace EvenTI.Contract

open Action

variable {K : Type} [Field K] [Fintype K]

theorem mem_coordinates (n d : Nat) (x : Coord d n) : x ∈ coordinates n d := by
  induction d with
  | zero =>
    simpa [coordinates] using (Subsingleton.elim x (Fin.elim0 : Coord 0 n))
  | succ d ih =>
    apply List.mem_flatMap.mpr
    refine ⟨x 0, List.mem_finRange _, List.mem_map.mpr ⟨fun j => x j.succ, ih _, ?_⟩⟩
    exact Fin.cons_self_tail x

theorem tensorWords_eq_map (F : FieldEncoding K) {d n : Nat} (T : Tensor K d n) :
    tensorWords F T = (coordinates n d).map (fun x => (F (T x)).val) := by
  unfold tensorWords fieldWords
  induction coordinates n d with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem findCode_of_mem {A : Type*} [DecidableEq A]
    (xs : List A) (f : A → Nat) (a : A) (ha : a ∈ xs) :
    (xs.zip (xs.map f)).findSome? (fun p => if p.1 = a then some p.2 else none) =
      some (f a) := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hb : b = a
    · simp [hb]
    · simp [hb, ih (List.mem_cons.mp ha |>.resolve_left (Ne.symm hb))]

/-- Decode valid field digits using a fixed digit table. Invalid digits are rejected
by the outer parser. -/
def decodeDigit (F : FieldEncoding K) (w : Nat) : K :=
  if hw : w < Fintype.card K then F.symm ⟨w, hw⟩ else 0

theorem decodeDigit_encode (F : FieldEncoding K) (x : K) :
    decodeDigit F (F x).val = x := by
  simp [decodeDigit, (F x).isLt]

/-- A fixed-size dense block. A list lookup suffices for polynomial cost in the
dense input length and avoids imposing a new flattening order. -/
def decodeTensor (F : FieldEncoding K) (n d : Nat) (words : List Nat) : Tensor K d n :=
  let rows := (coordinates n d).zip words
  fun x => decodeDigit F (Option.getD (rows.findSome? fun p => if p.1 = x then some p.2 else none) 0)

theorem decodeTensor_encode (F : FieldEncoding K) {n d : Nat} (T : Tensor K d n) :
    decodeTensor F n d (tensorWords F T) = T := by
  funext x
  rw [tensorWords_eq_map]
  unfold decodeTensor
  rw [findCode_of_mem _ _ _ (mem_coordinates n d x)]
  exact decodeDigit_encode F (T x)

structure ParsedSource (K : Type) where
  d : Nat
  n : Nat
  tensor : Tensor K d n

structure ParsedPair (K : Type) where
  d : Nat
  n : Nat
  source : Tensor K d n
  target : Tensor K d n

/-- Bound the header by the available length before computing the dense size. -/
def admissibleHeader (d n available : Nat) : Bool :=
  decide (4 ≤ d ∧ d % 2 = 0 ∧ 2 ≤ n ∧ d ≤ available ∧ n ≤ available)

def decodeSource (F : FieldEncoding K) : List Nat → Option (ParsedSource K)
  | d :: n :: words =>
    if admissibleHeader d n words.length &&
      decide (words.length = n ^ d) &&
      words.all (fun w => decide (w < Fintype.card K)) then
      some ⟨d, n, decodeTensor F n d words⟩
    else none
  | _ => none

def decodePair (F : FieldEncoding K) : List Nat → Option (ParsedPair K)
  | d :: n :: words =>
    if admissibleHeader d n words.length &&
      decide (words.length = 2 * n ^ d) &&
      words.all (fun w => decide (w < Fintype.card K)) then
      let width := n ^ d
      some ⟨d, n, decodeTensor F n d (words.take width),
        decodeTensor F n d (words.drop width)⟩
    else none
  | _ => none

private theorem header_le_width {n d : Nat} (hn : 2 ≤ n) (hd : 4 ≤ d) :
    n ≤ n ^ d ∧ d ≤ n ^ d := by
  constructor
  · simpa using Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ d)
  · exact (Nat.lt_two_pow_self (n := d)).le.trans (Nat.pow_le_pow_left hn _)

private theorem digits_valid (F : FieldEncoding K) {n d : Nat} (T : Tensor K d n) :
    (tensorWords F T).all (fun w => decide (w < Fintype.card K)) = true := by
  rw [tensorWords_eq_map]
  simp only [List.all_map, Function.comp_def, List.all_eq_true, decide_eq_true_eq]
  exact fun x _ => (F (T x)).isLt

theorem decodeSource_encode (F : FieldEncoding K) {n d : Nat} (T : Tensor K d n)
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) :
    decodeSource F (sourceInput F T) = some ⟨d, n, T⟩ := by
  have h := header_le_width hn hd
  have he' : d % 2 = 0 := Nat.even_iff.mp he
  simp [sourceInput, decodeSource, admissibleHeader, tensorWords_length, hd, hn, he',
    h.1, h.2, digits_valid, decodeTensor_encode]

theorem decodePair_encode (F : FieldEncoding K) {n d : Nat} (T S : Tensor K d n)
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) :
    decodePair F (comparisonInput F T S) = some ⟨d, n, T, S⟩ := by
  have h := header_le_width hn hd
  have hsum : n ^ d + n ^ d = 2 * n ^ d := by omega
  have hn' : n ≤ 2 * n ^ d := by omega
  have hd' : d ≤ 2 * n ^ d := by omega
  have he' : d % 2 = 0 := Nat.even_iff.mp he
  simp [comparisonInput, decodePair, admissibleHeader, tensorWords_length, hd, hn, he',
    hd', hn', hsum, digits_valid, decodeTensor_encode]
#print axioms decodeTensor_encode
#print axioms decodeSource_encode
#print axioms decodePair_encode

end EvenTI.Contract
