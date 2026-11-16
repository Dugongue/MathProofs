/-
Copyright (c) the Lax51 authors.
Released under the Apache License, Version 2.0.
Lax submission 51 by Szymon Toruńczyk / Codex 5.6.
https://github.com/szymtor/RAM-TM/tree/6fe5a3d94f6c2da46cc2c5ab98cd36997b130737
Modified in 2026 by Dugongue for MathProofs Problem 1.8. The adaptation
changes module paths and options, ports to Lean 4.33 and splits the proof.
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

set_option backward.isDefEq.respectTransparency false


/-!
---
title: Binary encoding of finite words
type: definition
---
A finite list of natural numbers is encoded over a three-symbol alphabet.
Each number begins with a separator and is followed by its canonical
least-significant-bit-first binary expansion. Thus zero is represented by a
separator with no following bits, and the next separator begins the next
number. The empty list is represented by the empty string.

This encoding is self-delimiting at the level of numbers: separators cannot
occur as binary digits. Its length is the common input-size measure used by
the Turing-machine and word-RAM polynomial-time definitions in this
submission.
-/

set_option autoImplicit false

namespace Lax51.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax51.BinaryWordEncoding
