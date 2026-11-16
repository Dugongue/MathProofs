/-
Copyright (c) the Lax51 authors.
Released under the Apache License, Version 2.0.
Lax submission 51 by Szymon Toruńczyk / Codex 5.6.
https://github.com/szymtor/RAM-TM/tree/6fe5a3d94f6c2da46cc2c5ab98cd36997b130737
Modified in 2026 by Dugongue for MathProofs Problem 1.8. The adaptation
changes module paths and options, ports to Lean 4.33 and splits the proof.
-/
import Mathproof.Meta.Problem18RAMLax51BinaryWordEncoding20261001
import Mathlib.Data.Nat.Size

set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false

namespace Lax51Proofs.Encoding

open Lax51.BinaryWordEncoding

@[simp] theorem encode_nil : encode [] = [] := rfl

@[simp] theorem encode_cons (a : ℕ) (x : List ℕ) :
    encode (a :: x) = encodeNat a ++ encode x := rfl

@[simp] theorem bitSize_nil : bitSize [] = 0 := rfl

theorem bitSize_cons (a : ℕ) (x : List ℕ) :
    bitSize (a :: x) = (Nat.bits a).length + 1 + bitSize x := by
  simp [bitSize, encode, encodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_le_bitSize (x : List ℕ) : x.length ≤ bitSize x := by
  induction x with
  | nil => simp
  | cons a x ih =>
      rw [bitSize_cons]
      simp only [List.length_cons]
      omega

theorem bits_length_add_one_le_bitSize_of_mem {a : ℕ} {x : List ℕ}
    (ha : a ∈ x) : a.bits.length + 1 ≤ bitSize x := by
  induction x with
  | nil => simp at ha
  | cons b x ih =>
      rw [bitSize_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · have := ih ha
        omega

theorem mem_lt_two_pow_bitSize_add_one {a : ℕ} {x : List ℕ} (ha : a ∈ x) :
    a < 2 ^ (bitSize x + 1) := by
  have haSize : a < 2 ^ a.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size_self a
  exact haSize.trans_le (Nat.pow_le_pow_right (by omega)
    (by have := bits_length_add_one_le_bitSize_of_mem ha; omega))

theorem length_lt_two_pow_bitSize_add_one (x : List ℕ) :
    x.length < 2 ^ (bitSize x + 1) := by
  have hlen := length_le_bitSize x
  have hpow := Nat.lt_two_pow_self (n := bitSize x)
  exact hlen.trans_lt (hpow.trans_le
    (Nat.pow_le_pow_right (by omega) (by omega)))

end Lax51Proofs.Encoding
