import EvenPhysicalAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathproof.Meta.Problem18RAMLax51TuringPolytime20261001

namespace EvenTI.Contract

open Action
open Lax51.TuringPolytime (TuringPolytime)

/-- Mixed-radix enumeration, with the first physical index outermost. -/
def coordinates (n : Nat) : (d : Nat) → List (Coord d n)
  | 0 => [Fin.elim0]
  | d + 1 => (List.finRange n).flatMap fun i => (coordinates n d).map (Fin.cons i)

theorem coordinates_length (n d : Nat) : (coordinates n d).length = n ^ d := by
  induction d with
  | zero => simp [coordinates]
  | succ d ih =>
    simp [coordinates, List.length_flatMap, List.map_const', List.sum_replicate_nat, ih, pow_succ, Nat.mul_comm]

variable {K : Type} [Field K] [Fintype K]

/-- A field is fixed before the algorithm, so each element may use one digit. -/
abbrev FieldEncoding (K : Type) [Fintype K] := K ≃ Fin (Fintype.card K)

def fieldWords (F : FieldEncoding K) (x : K) : List Nat :=
  [(F x).val]

def tensorWords (F : FieldEncoding K) {d n : Nat} (T : Tensor K d n) : List Nat :=
  (coordinates n d).flatMap fun a => fieldWords F (T a)

theorem tensorWords_length (F : FieldEncoding K) {d n : Nat} (T : Tensor K d n) :
    (tensorWords F T).length = n ^ d := by
  simp [tensorWords, fieldWords, List.length_flatMap, List.map_const', List.sum_replicate_nat,
    coordinates_length]
def sourceInput (F : FieldEncoding K) {d n : Nat} (T : Tensor K d n) : List Nat :=
  [d, n] ++ tensorWords F T

def comparisonInput (F : FieldEncoding K) {d n : Nat} (T S : Tensor K d n) : List Nat :=
  [d, n] ++ tensorWords F T ++ tensorWords F S

def transporterOutput (F : FieldEncoding K) {d n : Nat} (g : Changes K d n)
    (count : Nat) : List Nat :=
  [2, count] ++ (List.finRange d).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      (List.finRange n).flatMap fun k => fieldWords F ((g i).val j k)

def filterInput (F : FieldEncoding K) {n : Nat} (parameters : List Nat)
    (mode : Nat) (g : (Matrix (Fin n) (Fin n) K)ˣ) : List Nat :=
  [parameters.length] ++ parameters ++ [mode, n] ++
    (List.finRange n).flatMap fun j =>
      (List.finRange n).flatMap fun k => fieldWords F (g.val j k)

def filteredComparisonInput (F : FieldEncoding K) {d n : Nat}
    (parameters : List Nat) (T S : Tensor K d n) : List Nat :=
  [parameters.length] ++ parameters ++ comparisonInput F T S

noncomputable def rejectDensity (F : FieldEncoding K) (recognize : List Nat → List Nat)
    (d n : Nat) : Real := by
  classical
  exact ((Finset.univ.filter fun T : Tensor K d n => recognize (sourceInput F T) ≠ [1]).card :
    Real) / Fintype.card (Tensor K d n)

/-- Deterministic binary-machine target for a single fixed field presentation.
The routines and their polynomial time bounds are chosen before the order. -/
structure VerifiedSolver (F : FieldEncoding K) where
  recognize : List Nat → List Nat
  compare : List Nat → List Nat
  recognizesInTime : TuringPolytime recognize
  comparesInTime : TuringPolytime compare
  range : ∀ {d n : Nat} (T : Tensor K d n),
    recognize (sourceInput F T) = [0] ∨ recognize (sourceInput F T) = [1]
  invariant : ∀ {d n : Nat} (T : Tensor K d n) (g : Changes K d n),
    recognize (sourceInput F (act g T)) = recognize (sourceInput F T)
  uniformCoverage : ∀ ε : Real, 0 < ε → ∃ n₀ : Nat,
    ∀ d n : Nat, 4 ≤ d → Even d → n₀ ≤ n → rejectDensity F recognize d n ≤ ε
  higherOrderRate : ∃ C : Real, 0 < C ∧ ∃ n₀ : Nat, 2 ≤ n₀ ∧
    ∀ d n : Nat, 6 ≤ d → Even d → n₀ ≤ n →
      rejectDensity F recognize d n ≤ C / Real.log n
  exactAnswer : ∀ {d n : Nat}, 4 ≤ d → Even d → 2 ≤ n →
    ∀ T S : Tensor K d n,
      recognize (sourceInput F T) = [1] →
      (compare (comparisonInput F T S) = [0] ∧ ∀ g, act g T ≠ S) ∨
      ∃ g : Changes K d n, act g T = S ∧
        compare (comparisonInput F T S) =
          transporterOutput F g (Nat.card {a : Changes K d n // act a T = S})

  filteredCount : ∀ (test : List Nat → List Nat), TuringPolytime test →
    ∃ count : List Nat → List Nat, TuringPolytime count ∧
      ∀ {d n : Nat}, 4 ≤ d → Even d → 2 ≤ n →
        ∀ (parameters : List Nat) (T S : Tensor K d n),
          recognize (sourceInput F T) = [1] →
          count (filteredComparisonInput F parameters T S) =
            [Nat.card {g : Changes K d n // act g T = S ∧
              ∀ i, test (filterInput F parameters i.val (g i)) = [1]}]

def FixedFieldEvenOrderTI : Prop :=
  ∀ (K : Type) [Field K] [Fintype K], ∀ F : FieldEncoding K,
    Nonempty (VerifiedSolver F)

#print axioms coordinates_length
#print axioms tensorWords_length

end EvenTI.Contract
