import Mathproof.MinimumGenerationBipartiteCayley

namespace Mathproof.MinimumGeneration.BipartiteCayley

open Connectivity

variable {n : Nat}

/-- The virtual graph may have twice the vertex count, with a common
constant-factor bound in the raw Cayley input length, including endmarkers. -/
theorem virtualPrefixLength (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat)
    (s t : Fin n) :
    let raw := @encodeCayley n G.toMul
    let bits := rawBits raw G.toOne.one eligible cut
    (ustconWord bits (left s) (left t)).length + 1 ≤ 4 * (raw.length + 1) := by
  dsimp only
  rw [ustconWord_length, @length_encodeCayley n G.toMul]
  have htable : n * n ≤ n * n * (Nat.log2 n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hm : (n + n) * (n + n) = 4 * (n * n) := by ring
  have hs := s.isLt
  have ht := t.isLt
  simp only [ustconHeaderLength, left, hm]
  omega

/-- The shifted physical address is zero at the left endmarker, and its
right endmarker still fits with two extra bits. -/
theorem shiftedAddressFits (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat)
    (s t : Fin n) (position : Nat)
    (inRange : position ≤ (ustconWord (rawBits (@encodeCayley n G.toMul)
            G.toOne.one eligible cut) (left s) (left t)).length + 1) :
    position < 2 ^ (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1 + 2) := by
  have size := virtualPrefixLength G eligible cut s t
  have top := Nat.lt_log2_self (n := (@encodeCayley n G.toMul).length + 1)
  rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide, Nat.mul_comm]
  exact (inRange.trans size).trans_lt (Nat.mul_lt_mul_of_pos_left top (by decide))

/-- A native logarithmic workspace bound in the virtual input size is also
logarithmic in the original Cayley input size. -/
theorem nativeSpaceFromRaw (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat)
    (s t : Fin n) (C : Nat) :
    let raw := @encodeCayley n G.toMul
    let bits := rawBits raw G.toOne.one eligible cut
    C * (Nat.log2 ((ustconWord bits (left s) (left t)).length + 1) + 1)
      ≤ (3 * C) * (Nat.log2 (raw.length + 1) + 1) := by
  dsimp only
  have h := shiftedAddressFits G eligible cut s t _ le_rfl
  have log : ((ustconWord (rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut)
      (left s) (left t)).length + 1).log2 < ((@encodeCayley n G.toMul).length + 1).log2 + 1 + 2 :=
    (Nat.log2_lt (by omega)).2 h
  have size : ((ustconWord (rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut)
      (left s) (left t)).length + 1).log2 + 1
      ≤ 3 * ((@encodeCayley n G.toMul).length + 1).log2 + 3 := by omega
  exact (Nat.mul_le_mul_left C size).trans_eq (by ring)

end Mathproof.MinimumGeneration.BipartiteCayley
