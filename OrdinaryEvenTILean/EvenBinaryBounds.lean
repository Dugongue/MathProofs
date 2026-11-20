import EvenWordDriver
import EvenBranchBound

namespace EvenTI.Contract

open Action
open Lax51.BinaryWordEncoding

variable {K : Type} [Field K] [Fintype K] {d n : Nat}

theorem words_le_bitSize (words : List Nat) : words.length ≤ bitSize words := by
  unfold bitSize encode
  induction words with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append, encodeNat,
      List.length_map]
    omega

theorem dense_le_comparison_bits (F : FieldEncoding K) (T S : Tensor K d n) :
    n ^ d ≤ bitSize (comparisonInput F T S) := by
  apply Nat.le_trans _ (words_le_bitSize _)
  simp [comparisonInput, tensorWords_length]
  omega

theorem transporterOutput_words (F : FieldEncoding K) (g : Changes K d n) (count : Nat) :
    (transporterOutput F g count).length = 2 + d * n ^ 2 := by
  simp [transporterOutput, fieldWords, List.length_flatMap, List.map_const',
    pow_two] <;> omega

theorem search_charge_le_square_input_bits (F : FieldEncoding K) (T S : Tensor K d n)
    (hn : 2 ≤ n) (hd : 2 ≤ d) {A B G : Type}
    (outer : List A) (inner : A → List B) (visit : B → Option G) (cost : B → Nat)
    (houter : outer.length ≤ n ^ 2) (hinner : ∀ a ∈ outer, (inner a).length ≤ n ^ d)
    (C : Nat) (hcost : ∀ b ∈ outer.flatMap inner, cost b ≤ C) :
    chargeScan visit cost (outer.flatMap inner) ≤
      bitSize (comparisonInput F T S) ^ 2 * C := by
  have hb := EvenTI.BranchBudget.kernel_primary_trials_le outer inner hn hd houter hinner
  have hi := Nat.pow_le_pow_left (dense_le_comparison_bits F T S) 2
  exact (chargeScan_le visit cost _ C hcost).trans (Nat.mul_le_mul_right C (hb.trans hi))

#print axioms words_le_bitSize
#print axioms transporterOutput_words
#print axioms search_charge_le_square_input_bits

end EvenTI.Contract
