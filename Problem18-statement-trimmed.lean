/-
Copyright (c) 2026 <AUTHOR NAME>. All rights reserved.

NO LICENSE IS GRANTED for the original portions of this file (everything except the two
Formal Conjectures sections identified below). The author has not released the original
portions under the Apache License or any other license, and nothing in this file should be
read as doing so. The author may choose a license for them later.

Third-party material and credits
================================

THE APACHE LICENSE MENTIONED BELOW APPLIES ONLY TO THE THIRD-PARTY MATERIAL. It is stated here
because that license requires it of anyone redistributing the material. It is a compliance notice,
not a license of the original portions of this file.

1. Mathlib (https://github.com/leanprover-community/mathlib4), Apache License 2.0.
   Mathlib is imported via `import Mathlib`, not copied into this file. In particular this
   statement uses Mathlib's multi-stack Turing machines (`Turing.TM2`, `Turing.FinTM2`,
   `TM2ComputableInPolyTime`), from Mathlib/Computability/TuringMachine.lean
   (Copyright (c) 2018 Mario Carneiro) and Mathlib/Computability/TuringMachine/Computable.lean
   and Encoding.lean (Copyright (c) 2020 Pim Spelier, Daan van Gent).

2. Formal Conjectures (https://github.com/google-deepmind/formal-conjectures,
   commit 7d1a8c9912747679d0093f6d1216420c33ee5ffa), "Copyright 2026 The Formal Conjectures
   Authors", licensed by its authors under the Apache License 2.0
   (https://www.apache.org/licenses/LICENSE-2.0).
   The two sections marked FormalConjecturesForMathlib.Computability.BitstringEncoding and
   FormalConjecturesForMathlib.Computability.Complexity below are copied verbatim (unmodified)
   from that project. They remain under the Apache License 2.0 and keep their original copyright
   notices in place. They are provided "AS IS", without warranties or conditions of any kind.

No other third-party code is contained in this file. The full proof (Problem18.lean) carries
its own, longer credits section.
-/

import Mathlib

/-!
# Problem 1.8 (LLQTW, arXiv:2604.00591): the statement only

This file contains exactly the declarations needed to state
`Mathproof.Problem18AllFormatRoot20260930.AllFormatRoot`, copied verbatim (same names,
same namespaces) from the project sources, and nothing else. It imports only Mathlib,
has no `sorry`, and proves nothing about the main result. The proof is the theorem
`Mathproof.Problem18RootClosure20261004.allFormatRoot : AllFormatRoot` in `Problem18.lean`,
which contains these same declarations verbatim (checked by `check_trimmed.py`).

What `AllFormatRoot` says, in plain mathematics. Tensors are A ∈ K^{a×b×c}, stored as
c × (a·b) matrices, for a finite field K given explicitly by a prime p, a degree e and a
monic modulus (power-basis coordinates over F_p). The group O_I(n) × O_I(n') × O_I(n'')
acts by (P,Q,R)·A = R·A·(P⊗Q)ᵀ, where O_I(n) = {P : PᵀP = I}. In the unitary case,
with |K| = q², the group is U(n) = {P : (P^{(q)})ᵀP = I}, x ↦ x^q being the conjugation.
There exist ONE recognizer `recognize`, deterministic polynomial time on bitstrings,
ONE probabilistic (fair-coin) stack machine M, and constants c₀ > 0, C > 0, B₀ > 0,
T₀, k, such that for EVERY finite field K (which has a presentation), every presentation
of K, both groups, and all a, b, c ≥ 1, writing m = median(a,b,c), A uniform in K^{abc}:
 (i)   the recognizer's verdict on A is invariant under the group action;
 (ii)  Pr[A accepted] ≥ c₀/q;
 (iii) if a, b, c ≥ 2, then Pr[A rejected] ≤ min(1, C(1 + log m)/√m);
 (iv)  if m < B₀, every A is accepted;
 (v)   for ALL A, B: M never answers wrongly (it outputs [A ≅ B] when A is accepted
       and "fail" when it is rejected) and halts in expected time
       ≤ T₀·((abc + 1)(bitlength(q) + 1))^k.
So M is a zero-error (Las Vegas) average-case polynomial-time algorithm for 3-tensor
isomorphism under orthogonal and unitary group actions, over all finite fields and formats.

Scope. "Orthogonal" means the standard group O_I = {PᵀP = I} of the dot product (the
CGQTZ/TI convention), and "unitary" the Hermitian unitary group, which is unique up to
conjugacy. Not covered: for q odd and even dimension, the orthogonal group of the other
discriminant class (only one of O^±_{2m}(q) is O_I), and in characteristic 2 the
quadratic-form orthogonal groups O^±_{2m}(q), O_{2m+1}(q).

Layout: third-party code (Formal Conjectures, Apache-2.0, original copyright headers kept),
then the project's own definitions. The file ends with `def Claim : Prop := AllFormatRoot`,
the only declaration that is not copied from the sources. (The docstring "UNPROVED: ..." on
`AllFormatRoot` is kept verbatim from its 2026-09-30 source, written before the proof existed.)
-/

--------------------------------------------------------------------------------
-- Source: External/FormalConjectures/FormalConjecturesForMathlib/Computability/BitstringEncoding.lean  (third-party, Formal Conjectures, Apache-2.0)
--------------------------------------------------------------------------------
section
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

open Computability

section BitstringEncodings

/-- A canonical encoding of a type as bitstrings (`List Bool`).

This is a class version of Mathlib's `Computability.Encoding`, specialized to the
alphabet `Bool`. -/
class BitstringEncoding α extends Computability.Encoding α Bool

namespace BitstringEncoding

variable {α β : Type*}

/-- The encoding function of the canonical `BitstringEncoding` of `α`. -/
def bitEncode [BitstringEncoding α] (a : α) : List Bool := toEncoding.encode a

/-- The decoding function of the canonical `BitstringEncoding` of `α`. -/
def bitDecode [BitstringEncoding α] (l : List Bool) : Option α := toEncoding.decode l

/-- Decoding is a left inverse of encoding. -/
@[simp]
theorem bitDecode_bitEncode [BitstringEncoding α] (a : α) : bitDecode (bitEncode a) = some a :=
  toEncoding.decode_encode a

/-- `ℕ` is encoded by its (little-endian) binary representation, as in
`Computability.encodeNat`. -/
instance : BitstringEncoding ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits
`[true, b]`, and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the payload
and the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem length_delimit (l : List Bool) : (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; omega

/-- Parse a sequence of self-delimiting blocks, using `fuel` to bound the number of blocks.

This is the auxiliary, fuel-carrying implementation of `undelimitBlocks`; since every block
is nonempty, `input.length` is always enough fuel. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input =>
    -- `p.1` is the parsed block and `p.2` the remaining input; using projections rather than a
    -- pattern-matching lambda keeps the body free of matchers.
    (undelimit input).bind fun p => (undelimitBlocksAux fuel p.2).map (p.1 :: ·)

/-- Parse a sequence of self-delimiting blocks off the front of the input.

Since every block is nonempty, `input.length` bounds the number of blocks, so it always
suffices as fuel for `undelimitBlocksAux`. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      length_delimit]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) (fuel : ℕ)
    (hfuel : l.length ≤ fuel) : undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons b t ih =>
    rw [List.length_cons] at hfuel
    cases fuel <;> cases b <;> grind [delimit, undelimitBlocksAux, undelimit_delimit]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp]
theorem mapM_bitDecode_map_bitEncode [BitstringEncoding α] (l : List α) :
    (l.map bitEncode).mapM bitDecode = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map bitEncode).map delimit).flatten
  decode input := (undelimitBlocks input).bind (·.mapM bitDecode)
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map bitEncode)]
    exact mapM_bitDecode_map_bitEncode l

end BitstringEncoding

end BitstringEncodings

end

--------------------------------------------------------------------------------
-- Source: External/FormalConjectures/FormalConjecturesForMathlib/Computability/Complexity.lean  (third-party, Formal Conjectures, Apache-2.0)
--------------------------------------------------------------------------------
section
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

open Computability Turing

namespace ComplexityTheory

/--
`IsPolyTimeWithEncoding ea eb f` asserts that `f` is computable in polynomial time
when its input and output are encoded via the given `Encoding`s `ea` and `eb`.
-/
def IsPolyTimeWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea.encode eb.encode f)

/--
A function is polynomial-time computable when it is `IsPolyTimeWithEncoding`
for the canonical `Bool`-alphabet encodings of its domain and codomain
as given by the `BitstringEncoding` typeclass.
-/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toEncoding (α := α)) (BitstringEncoding.toEncoding (α := β)) f

end ComplexityTheory

end

--------------------------------------------------------------------------------
-- Source: Mathproof/Meta/Problem18OrthogonalAssembly20260929.lean
--------------------------------------------------------------------------------
namespace Problem18OrthogonalAssembly

open Matrix
variable {K : Type*} [Field K]
variable {a b c : ℕ}

def IsOrthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n K) : Prop := P.transpose * P = 1

abbrev RectTensor (a b c : ℕ) (K : Type*) :=
  Matrix (Fin c) (Fin a × Fin b) K

def rectAction (P : Matrix (Fin a) (Fin a) K)
    (Q : Matrix (Fin b) (Fin b) K)
    (R : Matrix (Fin c) (Fin c) K)
    (A : RectTensor a b c K) : RectTensor a b c K :=
  R * A * (Matrix.kronecker P Q).transpose

end Problem18OrthogonalAssembly

--------------------------------------------------------------------------------
-- Source: Mathproof/Meta/Problem18OperationalMachine20260930.lean
--------------------------------------------------------------------------------
namespace Mathproof.Problem18OperationalMachine20260930
open scoped BigOperators

structure CoinMachine extends Turing.TM2ComputableAux Bool Bool where
  program : Bool → tm.Λ → Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
  alphabetFinite : ∀ k, Fintype (tm.Γ k)

def run (M : CoinMachine) (input : List Bool) (coins : List Bool) : M.tm.Cfg :=
  coins.foldl (fun c bit => (Turing.TM2.step (M.program bit) c).getD c)
    (Turing.initList M.tm (input.map M.inputAlphabet.symm))

def halted (M : CoinMachine) (input coins : List Bool) : Bool :=
  (run M input coins).l.isNone

def output (M : CoinMachine) (input coins : List Bool) : List Bool :=
  ((run M input coins).stk M.tm.k₁).map M.outputAlphabet

def encodeAnswer : Option Bool → List Bool
  | none => []
  | some b => [b]

/-- Every finite halting computation gives the specified answer. -/
def ZeroError (M : CoinMachine) (input : List Bool) (answer : Option Bool) : Prop :=
  ∀ coins, halted M input coins = true → output M input coins = encodeAnswer answer

/-- The exact probability of still running after n independent fair coins. -/
noncomputable def survival (M : CoinMachine) (input : List Bool) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun coins : Fin n → Bool =>
    halted M input (List.ofFn coins) = false)).card : ℝ) / (2 : ℝ)^n

/-- Bounded finite partial sums of the survival series specify an expected
step bound, including almost-sure termination; no arbitrary time function occurs. -/
def ExpectedStepsLE (M : CoinMachine) (input : List Bool) (bound : ℝ) : Prop :=
  ∀ N : ℕ, (∑ n ∈ Finset.range N, survival M input n) ≤ bound

end Mathproof.Problem18OperationalMachine20260930

--------------------------------------------------------------------------------
-- Source: Mathproof/Meta/Problem18AllFormatRoot20260930.lean
--------------------------------------------------------------------------------
namespace Mathproof.Problem18AllFormatRoot20260930
open scoped BigOperators Matrix
open Mathproof.Problem18OperationalMachine20260930
open Problem18OrthogonalAssembly

/-- A power-basis finite-field representation. The input contains only the
prime, degree, monic modulus coefficients and tensor coordinates, never an
operation table. All equations here validate representation data. -/
structure FieldPresentation (K : Type) [Field K] where
  p : ℕ
  e : ℕ
  prime : p.Prime
  degree_pos : 0 < e
  characteristic : CharP K p
  generator : K
  modulus : Fin e → Fin p
  coordinate : K ≃ (Fin e → Fin p)
  coordinate_spec : ∀ x : K,
    x = ∑ i : Fin e, ((coordinate x i).val : K) * generator ^ i.val
  modulus_spec : generator ^ e +
    ∑ i : Fin e, ((modulus i).val : K) * generator ^ i.val = 0

def tensorCoordinates {K : Type} [Field K] (F : FieldPresentation K)
    {a b c : ℕ} (A : RectTensor a b c K) : List ℕ :=
  (List.finRange c).flatMap fun k =>
    (List.finRange a).flatMap fun i =>
      (List.finRange b).flatMap fun j =>
        (List.finRange F.e).map fun t => (F.coordinate (A k (i,j)) t).val

def header {K : Type} [Field K] (F : FieldPresentation K)
    (unitary : Bool) (q a b c : ℕ) : List ℕ :=
  [unitary.toNat, q, F.p, F.e, a, b, c] ++ (List.finRange F.e).map (fun i => (F.modulus i).val)

def sourceBits {K : Type} [Field K] (F : FieldPresentation K)
    (unitary : Bool) (q : ℕ) {a b c : ℕ} (A : RectTensor a b c K) : List Bool :=
  BitstringEncoding.bitEncode (0 :: (header F unitary q a b c ++ tensorCoordinates F A))

def queryBits {K : Type} [Field K] (F : FieldPresentation K)
    (unitary : Bool) (q : ℕ) {a b c : ℕ} (A B : RectTensor a b c K) : List Bool :=
  BitstringEncoding.bitEncode
    (1 :: (header F unitary q a b c ++ tensorCoordinates F A ++ tensorCoordinates F B))

def isometry {K : Type} [Field K] {n : ℕ} (unitary : Bool) (q : ℕ)
    (P : Matrix (Fin n) (Fin n) K) : Prop :=
  if unitary then (P.map (fun x => x^q)).transpose * P = 1 else IsOrthogonal P

/-- Exact standard O_I action or the standard q-Frobenius unitary action. -/
def equivalent {K : Type} [Field K] {a b c : ℕ} (unitary : Bool) (q : ℕ)
    (A B : RectTensor a b c K) : Prop :=
  ∃ (P : Matrix (Fin a) (Fin a) K) (Q : Matrix (Fin b) (Fin b) K)
    (R : Matrix (Fin c) (Fin c) K),
    isometry unitary q P ∧ isometry unitary q Q ∧ isometry unitary q R ∧
    rectAction P Q R A = B

def validSize (K : Type) [Fintype K] (unitary : Bool) (q : ℕ) : Prop :=
  if unitary then
    (∃ p k : ℕ, p.Prime ∧ 0 < k ∧ q = p^k) ∧ Fintype.card K = q*q
  else q = Fintype.card K

def median (a b c : ℕ) : ℕ := a+b+c - min a (min b c) - max a (max b c)

noncomputable def goodDensity {K : Type} [Field K] [Fintype K]
    (F : FieldPresentation K) (recognize : List Bool → Bool)
    (unitary : Bool) (q a b c : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun A : RectTensor a b c K =>
    recognize (sourceBits F unitary q A) = true)).card : ℝ) /
      Fintype.card (RectTensor a b c K)

noncomputable def requiredAnswer {K : Type} [Field K]
    (F : FieldPresentation K) (recognize : List Bool → Bool)
    (unitary : Bool) (q : ℕ) {a b c : ℕ} (A B : RectTensor a b c K) : Option Bool := by
  classical
  exact if recognize (sourceBits F unitary q A) then
    some (decide (equivalent unitary q A B)) else none

/-- The uniform root conclusion for one represented field and format. -/
def FormatConclusion {K : Type} [Field K] [Fintype K]
    (F : FieldPresentation K) (recognize : List Bool → Bool) (M : CoinMachine)
    (c₀ C : ℝ) (B₀ timeConstant timeExponent : ℕ)
    (unitary : Bool) (q a b c : ℕ) : Prop :=
  (∀ A B : RectTensor a b c K, equivalent unitary q A B →
    recognize (sourceBits F unitary q A) = recognize (sourceBits F unitary q B)) ∧
  c₀ / q ≤ goodDensity F recognize unitary q a b c ∧
  (2 ≤ a → 2 ≤ b → 2 ≤ c →
    1 - goodDensity F recognize unitary q a b c ≤
      min 1 (C * (1 + Real.log (median a b c)) / Real.sqrt (median a b c))) ∧
  (median a b c < B₀ → ∀ A : RectTensor a b c K,
    recognize (sourceBits F unitary q A) = true) ∧
  (∀ A B : RectTensor a b c K,
    ZeroError M (queryBits F unitary q A B) (requiredAnswer F recognize unitary q A B) ∧
    ExpectedStepsLE M (queryBits F unitary q A B)
      (timeConstant * (((a*b*c+1)*(q.size+1)) : ℝ)^timeExponent))

/-- UNPROVED: one machine and uniform constants, before quantifying over fields
or dimensions. All algorithms and runtime proofs are existential outputs. -/
def AllFormatRoot : Prop :=
  ∃ (recognize : List Bool → Bool) (M : CoinMachine) (c₀ C : ℝ)
    (B₀ timeConstant timeExponent : ℕ),
    0 < c₀ ∧ 0 < C ∧ 0 < B₀ ∧
    ComplexityTheory.IsPolyTime recognize ∧
    ∀ (K : Type) [Field K] [Fintype K],
      Nonempty (FieldPresentation K) ∧
      ∀ (F : FieldPresentation K) (unitary : Bool) (q a b c : ℕ),
        validSize K unitary q → 0 < a → 0 < b → 0 < c →
        FormatConclusion F recognize M c₀ C B₀ timeConstant timeExponent unitary q a b c

end Mathproof.Problem18AllFormatRoot20260930

/-- The statement proved in `Problem18.lean`, as
`theorem Mathproof.Problem18RootClosure20261004.allFormatRoot :
  Mathproof.Problem18AllFormatRoot20260930.AllFormatRoot`.
This is the only declaration of this file that is not copied from the sources. -/
def Claim : Prop := Mathproof.Problem18AllFormatRoot20260930.AllFormatRoot
