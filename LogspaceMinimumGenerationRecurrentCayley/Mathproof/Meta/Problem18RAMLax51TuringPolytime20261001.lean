/-
Copyright (c) the Lax51 authors.
Released under the Apache License, Version 2.0.
Lax submission 51 by Szymon Toruńczyk / Codex 5.6.
https://github.com/szymtor/RAM-TM/tree/6fe5a3d94f6c2da46cc2c5ab98cd36997b130737
Modified in 2026 by Dugongue for MathProofs Problem 1.8. The adaptation
changes module paths and options, ports to Lean 4.33 and splits the proof.
-/
import Mathproof.Meta.Problem18RAMLax51BinaryWordEncoding20261001
import Mathlib.Computability.TuringMachine.Computable

set_option backward.isDefEq.respectTransparency false


/-!
---
title: Polynomial-time computation by a Turing machine
type: definition
---
A total function from finite lists of natural numbers to finite lists of
natural numbers is Turing-computable in polynomial time when a finite
multi-tape Turing machine transforms the canonical binary encoding of every
input into the canonical binary encoding of its value within a polynomial
number of steps in the encoded input length.

The underlying machine and time bound are mathlib's
`Turing.TM2ComputableInPolyTime`: a bundled finite multi-stack Turing machine
and a polynomial over the natural numbers. Taking `Nonempty` forgets the
computational content of the bundle and retains the proposition that such a
machine exists.
-/

set_option autoImplicit false

namespace Lax51.TuringPolytime

open Lax51.BinaryWordEncoding

/-- Polynomial-time computation, on the canonical binary word encoding, by
a finite multi-tape Turing machine. -/
def TuringPolytime (f : List ℕ → List ℕ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encode encode f)

end Lax51.TuringPolytime
