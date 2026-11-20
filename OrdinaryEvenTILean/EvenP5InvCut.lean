import EvenDenseDecode
import EvenFlattening
import EvenP5KernelCore
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The raw balanced-cut inverse via the checked row-kernel algorithm.
Each column solves an augmented homogeneous system and is normalized by the
last coordinate. One matrix product checks the result before it leaves the routine. -/

namespace EvenTI.Contract

open EvenTI.Action Matrix
open Mathproof.P15RecogOps20261007 EvenTI.KernelDonor
open scoped BigOperators Matrix

variable {K ι : Type} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]

private def augIndices (idx : List ι) : List (Option ι) := none :: idx.map some

private theorem mem_augIndices {idx : List ι} (hidx : ∀ i, i ∈ idx) (c : Option ι) :
    c ∈ augIndices idx := by cases c <;> simp [augIndices, hidx]

private theorem nodup_augIndices {idx : List ι} (hnd : idx.Nodup) :
    (augIndices idx).Nodup := by
  exact List.nodup_cons.mpr ⟨by simp, hnd.map (fun a b h => Option.some_injective _ h)⟩

private def augRow (M : Matrix ι ι K) (j i : ι) : Option ι → K
  | some k => M i k
  | none => -(1 : Matrix ι ι K) i j

private def augBasis (idx : List ι) (M : Matrix ι ι K) (j : ι) : List (Option ι → K) :=
  kerBasis (Ops.ofField K) (augIndices idx) (idx.map (augRow M j))

private def findColumn (idx : List ι) (M : Matrix ι ι K) (j : ι) :=
  (augBasis idx M j).find? fun v => decide (v none ≠ 0)

private def candidateInverse (idx : List ι) (M : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => match findColumn idx M j with
    | none => 0
    | some v => v (some i) * (v none)⁻¹

private theorem augBasis_spec {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    (M : Matrix ι ι K) (j : ι) :
    (∀ v ∈ augBasis idx M j, v ∈ rowKer (idx.map (augRow M j))) ∧
    Submodule.span K {v | v ∈ augBasis idx M j} = rowKer (idx.map (augRow M j)) :=
  kerBasis_spec (mem_augIndices hidx) (nodup_augIndices hnd) _

private theorem findColumn_exists {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    {M : Matrix ι ι K} (hM : IsUnit M) (j : ι) :
    ∃ v, findColumn idx M j = some v := by
  by_contra! h
  have hnone : findColumn idx M j = none := Option.eq_none_iff_forall_ne_some.mpr h
  have hz (v : Option ι → K) (hv : v ∈ augBasis idx M j) : v none = 0 := by
    have hc := List.find?_eq_none.mp hnone v hv
    simpa using hc
  let v : Option ι → K := fun c => c.elim 1 (fun i => M⁻¹ i j)
  have hvr : v ∈ rowKer (idx.map (augRow M j)) := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    have h := congrArg (fun A : Matrix ι ι K => A i j)
      (M.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det M).mp hM))
    change (∑ k, M i k * M⁻¹ k j) = _ at h
    simp [Fintype.sum_option, augRow, v, h]
  have hvspan : v ∈ Submodule.span K {w | w ∈ augBasis idx M j} :=
    (augBasis_spec hidx hnd M j).2.symm ▸ hvr
  have hvz : v none = 0 :=
    (Submodule.span_le.mpr (fun w hw => hz w hw) hvspan : v ∈ (LinearMap.proj none).ker)
  exact one_ne_zero hvz

private theorem mul_candidateInverse {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    {M : Matrix ι ι K} (hM : IsUnit M) : M * candidateInverse idx M = 1 := by
  ext i j
  obtain ⟨v, hv⟩ := findColumn_exists hidx hnd hM j
  have hmem : v ∈ augBasis idx M j := List.mem_of_find?_eq_some hv
  have hne : v none ≠ 0 := by simpa using List.find?_some hv
  have hvker := (augBasis_spec hidx hnd M j).1 v hmem
  have hrow : augRow M j i ∈ idx.map (augRow M j) := List.mem_map_of_mem (hidx i)
  have hz : ∑ c, augRow M j i c * v c = 0 := hvker _ hrow
  rw [Fintype.sum_option] at hz
  simp only [augRow, neg_mul] at hz
  have heq : (∑ k, M i k * v (some k)) = (1 : Matrix ι ι K) i j * v none := by
    linear_combination hz
  simp only [Matrix.mul_apply, candidateInverse, hv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, heq, mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- Compute the balanced-cut inverse through verified RREF, or reject the cut. -/
def cutInverse (idx : List ι) (M : Matrix ι ι K) : Option (Matrix ι ι K) :=
  let B := candidateInverse idx M
  if idx.all (fun i => idx.all fun j => decide ((M * B) i j = (1 : Matrix ι ι K) i j))
    then some B else none

private theorem check_mul_iff {idx : List ι} (hidx : ∀ i, i ∈ idx) (M B : Matrix ι ι K) :
    idx.all (fun i => idx.all fun j => decide ((M * B) i j = (1 : Matrix ι ι K) i j)) =
      true ↔ M * B = 1 := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    ext i j
    exact h i (hidx i) j (hidx j)
  · intro h i _ j _
    rw [h]

theorem cutInverse_eq_some_iff {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    {M B : Matrix ι ι K} : cutInverse idx M = some B ↔ IsUnit M ∧ B = M⁻¹ := by
  let C := candidateInverse idx M
  by_cases hc : M * C = 1
  · have hdet : IsUnit M.det := by
      have hprod : M.det * C.det = 1 := by rw [← Matrix.det_mul, hc, Matrix.det_one]
      exact IsUnit.of_mul_eq_one _ hprod
    have hM := (Matrix.isUnit_iff_isUnit_det M).mpr hdet
    have hC : C = M⁻¹ := by rw [← M.nonsing_inv_mul_cancel_left C hdet, hc, Matrix.mul_one]
    have hcheck := (check_mul_iff hidx M C).mpr hc
    change (if _ then some C else none) = _ ↔ _
    rw [if_pos hcheck, Option.some.injEq]
    exact ⟨fun h => ⟨hM, h.symm.trans hC⟩, fun h => hC.trans h.2.symm⟩
  · have hM : ¬ IsUnit M := fun h => hc (mul_candidateInverse hidx hnd h)
    have hcheck := (check_mul_iff hidx M C).not.mpr hc
    change (if _ then some C else none) = _ ↔ _
    rw [if_neg hcheck]
    simp only [reduceCtorEq, hM, false_and]

theorem cutInverse_eq_none_iff {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    (M : Matrix ι ι K) : cutInverse idx M = none ↔ ¬ IsUnit M := by
  constructor
  · intro h hM
    have hs := (cutInverse_eq_some_iff hidx hnd (M := M) (B := M⁻¹)).mpr ⟨hM, rfl⟩
    rw [h] at hs
    cases hs
  · intro h
    cases he : cutInverse idx M with
    | none => rfl
    | some B => exact False.elim (h ((cutInverse_eq_some_iff hidx hnd).mp he).1)

/-- Matrix inverse on finite numeric indices. -/
def rawMatrixInverse {m : Nat} (M : Matrix (Fin m) (Fin m) K) : Option (Matrix (Fin m) (Fin m) K) :=
  cutInverse (List.finRange m) M

theorem rawMatrixInverse_eq_some_iff {m : Nat} (M B : Matrix (Fin m) (Fin m) K) :
    rawMatrixInverse M = some B ↔ IsUnit M ∧ B = M⁻¹ :=
  cutInverse_eq_some_iff (fun i => List.mem_finRange i) (List.nodup_finRange _)

theorem rawMatrixInverse_eq_none_iff {m : Nat} (M : Matrix (Fin m) (Fin m) K) :
    rawMatrixInverse M = none ↔ ¬ IsUnit M :=
  cutInverse_eq_none_iff (fun i => List.mem_finRange i) (List.nodup_finRange _) _

theorem rawMatrixInverse_mul {m : Nat} {M B : Matrix (Fin m) (Fin m) K}
    (h : rawMatrixInverse M = some B) :
    M * B = 1 ∧ B * M = 1 := by
  obtain ⟨hM, rfl⟩ := (rawMatrixInverse_eq_some_iff M B).mp h
  exact ⟨M.mul_nonsing_inv (Matrix.isUnit_iff_isUnit_det M |>.mp hM),
    M.nonsing_inv_mul (Matrix.isUnit_iff_isUnit_det M |>.mp hM)⟩

private theorem coordinates_nodup (n d : Nat) : (coordinates n d).Nodup := by
  induction d with
  | zero => simp [coordinates]
  | succ d ih =>
    rw [coordinates, List.nodup_flatMap]
    refine ⟨fun i _ => ih.map (fun a b h => funext fun k => congrFun h k.succ), ?_⟩
    exact (List.nodup_finRange n).pairwise_of_forall_ne (fun i _ j _ hij => by
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, h⟩ := List.mem_map.mp hx'
      exact hij (by simpa using (congrFun h (0 : Fin (d + 1))).symm))

/-- Physical inverse of the balanced flattening. -/
def rawCutInverse {s n : Nat} (T : Tensor K (s + s) n) :
    Option (Matrix (Coord s n) (Coord s n) K) :=
  cutInverse (coordinates n s) (flatten (l := s) (r := s) T)

theorem rawCutInverse_eq_some_iff {s n : Nat} (T : Tensor K (s + s) n)
    (B : Matrix (Coord s n) (Coord s n) K) :
    rawCutInverse T = some B ↔ IsUnit (flatten (l := s) (r := s) T) ∧
      B = (flatten (l := s) (r := s) T)⁻¹ :=
  cutInverse_eq_some_iff (mem_coordinates n s) (coordinates_nodup n s)

theorem rawCutInverse_eq_none_iff {s n : Nat} (T : Tensor K (s + s) n) :
    rawCutInverse T = none ↔ ¬ IsUnit (flatten (l := s) (r := s) T) :=
  cutInverse_eq_none_iff (mem_coordinates n s) (coordinates_nodup n s) _

#print axioms cutInverse_eq_some_iff
#print axioms rawMatrixInverse_mul
#print axioms rawCutInverse_eq_some_iff
#print axioms rawCutInverse_eq_none_iff

end EvenTI.Contract
