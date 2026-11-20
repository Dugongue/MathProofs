import EvenP6AlignSharp
import Mathlib.Data.List.Pi

/-! Exhaustive finite repeated-block tuples with one aggregate gate. -/

namespace EvenTI.PrimaryAlignment

open scoped BigOperators
open Matrix Polynomial EvenTI.Contract

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r : ℕ}

abbrev SquareBlock (K : Type) (w : ℕ) := Matrix (Fin w) (Fin w) K

def familyDimension {w : Fin r → ℕ} (A B : ∀ i, SquareBlock K (w i)) : ℕ :=
  ∑ i, (intertwinerBasis (A i) (B i)).length

private def eachBlock (F : FieldEncoding K) {w : Fin r → ℕ}
    (A B : ∀ i, SquareBlock K (w i)) (i : Fin r) : List (SquareBlock K (w i)) :=
  boundedUnits F (Fintype.card K ^ (intertwinerBasis (A i) (B i)).length) (A i) (B i)

private theorem mem_eachBlock (F : FieldEncoding K) {w : Fin r → ℕ}
    (A B X : ∀ i, SquareBlock K (w i)) (i : Fin r) :
    X i ∈ eachBlock F A B i ↔ B i * X i = X i * A i ∧ IsUnit (X i) := by
  simp [eachBlock, mem_boundedUnits]

/-- Enumerate simultaneous invertible intertwiners. Each family consistently
assigns one matrix to every repeated primary block. -/
def boundedFamilies (F : FieldEncoding K) {w : Fin r → ℕ} (budget : ℕ)
    (A B : ∀ i, SquareBlock K (w i)) : List (∀ i, SquareBlock K (w i)) :=
  if Fintype.card K ^ familyDimension A B ≤ budget then
    ((List.finRange r).pi (eachBlock F A B)).map fun x i => x i (List.mem_finRange i)
  else []

theorem mem_boundedFamilies (F : FieldEncoding K) {w : Fin r → ℕ} (budget : ℕ)
    (A B X : ∀ i, SquareBlock K (w i)) :
    X ∈ boundedFamilies F budget A B ↔ Fintype.card K ^ familyDimension A B ≤ budget ∧
      ∀ i, B i * X i = X i * A i ∧ IsUnit (X i) := by
  by_cases hg : Fintype.card K ^ familyDimension A B ≤ budget
  · rw [boundedFamilies, if_pos hg, List.mem_map]
    simp only [hg, true_and]
    constructor
    · rintro ⟨f, hf, hfX⟩ i
      apply (mem_eachBlock F A B X i).mp
      rw [← congrFun hfX i]
      exact (List.mem_pi _ _).mp hf i (List.mem_finRange i)
    · intro h
      refine ⟨fun i _ => X i, (List.mem_pi _ _).mpr ?_, rfl⟩
      exact fun i _ => (mem_eachBlock F A B X i).mpr (h i)
  · simp [boundedFamilies, hg]

private theorem length_pi_le {ι : Type} [DecidableEq ι] {E : ι → Type}
    (g : ∀ i, List (E i)) (l : List ι) (q : ℕ) (e : ι → ℕ)
    (h : ∀ i, (g i).length ≤ q ^ e i) :
    (l.pi g).length ≤ q ^ (l.map e).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.pi_cons, List.length_flatMap, List.length_map, List.map_const',
      List.sum_replicate, List.map_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (h i) ih

theorem boundedFamilies_length_le (F : FieldEncoding K) {w : Fin r → ℕ} (budget : ℕ)
    (A B : ∀ i, SquareBlock K (w i)) :
    (boundedFamilies F budget A B).length ≤ budget := by
  unfold boundedFamilies
  split
  next hg =>
    rw [List.length_map]
    have hc := length_pi_le (eachBlock F A B) (List.finRange r) (Fintype.card K)
      (fun i => (intertwinerBasis (A i) (B i)).length)
      (fun i => boundedUnits_length_le F _ (A i) (B i))
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange] at hc
    exact hc.trans hg
  next _ => simp

/-- The aggregate cost of the raw kernels is charged to the sharp
degree-times-multiplicity-squared budget for the actual primary blocks. -/
theorem familyDimension_le_primary {w : Fin r → ℕ}
    (A B : ∀ i, SquareBlock K (w i)) (p : Fin r → K[X]) (e : Fin r → ℕ)
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hw : ∀ i, w i = (p i).natDegree * e i)
    (hA : ∀ i, aeval (A i) (p i ^ e i) = 0) (hB : ∀ i, aeval (B i) (p i ^ e i) = 0) :
    familyDimension A B ≤ ∑ i, (p i).natDegree * (e i)^2 := by
  unfold familyDimension
  apply Finset.sum_le_sum
  intro i _
  simpa only [pow_two] using
    intertwinerBasis_length_le_primary (A i) (B i) (p i) (hm i) (hi i)
      (e i) (e i) (e i) (hA i) (hB i) (hw i) (hw i)

theorem mem_boundedFamilies_of_primary {w : Fin r → ℕ} (F : FieldEncoding K) (budget : ℕ)
    (A B X : ∀ i, SquareBlock K (w i)) (p : Fin r → K[X]) (e : Fin r → ℕ)
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hw : ∀ i, w i = (p i).natDegree * e i)
    (hA : ∀ i, aeval (A i) (p i ^ e i) = 0) (hB : ∀ i, aeval (B i) (p i ^ e i) = 0)
    (hg : Fintype.card K ^ (∑ i, (p i).natDegree * (e i)^2) ≤ budget) :
    X ∈ boundedFamilies F budget A B ↔ ∀ i, B i * X i = X i * A i ∧ IsUnit (X i) := by
  rw [mem_boundedFamilies]
  have hc : Fintype.card K ^ familyDimension A B ≤ budget :=
    (Nat.pow_le_pow_right Fintype.card_pos (familyDimension_le_primary A B p e hm hi hw hA hB)).trans hg
  exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

#print axioms mem_boundedFamilies_of_primary
#print axioms boundedFamilies_length_le

end EvenTI.PrimaryAlignment
