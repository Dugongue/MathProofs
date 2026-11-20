import EvenP5InvRref

/-! Coordinate arithmetic for the field corners of a finite reduced
algebra. A normalized pivot row basis turns field projections and
embeddings into ordinary slots in the represented algebra. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.CellProducer

open Module EvenTI.Contract
open Mathproof.P15RecogOps20261007 Mathproof.P15RecogLinAlg20261007
open scoped BigOperators

variable {K A : Type} [Field K] [DecidableEq K]
  [CommRing A] [Algebra K A] {d : ℕ}

private def mulCell (e : A) : A →ₗ[K] A where
  toFun x := e * x
  map_add' x y := mul_add e x y
  map_smul' c x := mul_smul_comm c e x

/-- Multiplication by an ambient element in the ambient basis. -/
def cornerCoordMap (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    (Fin d → K) →ₗ[K] (Fin d → K) :=
  C.toLinearMap.comp ((mulCell (K := K) e).comp C.symm.toLinearMap)

private def cornerGenerators (C : A ≃ₗ[K] (Fin d → K)) (e : A) : List (Fin d → K) :=
  List.ofFn (fun j : Fin d => cornerCoordMap C e (Pi.single j 1))

/-- RREF of the coordinate vectors of (e) times the ambient basis. Each row
records both the pivot coordinate and the corresponding corner basis vector. -/
def rawCellRows (C : A ≃ₗ[K] (Fin d → K)) (e : A) : List (Fin d × (Fin d → K)) :=
  rrefStored (Ops.ofField K) (List.finRange d) (cornerGenerators C e)

/-- Number of base-field coordinates in this corner. -/
def rawCellDegree (C : A ≃ₗ[K] (Fin d → K)) (e : A) : ℕ :=
  (rawCellRows C e).length

theorem rawCellRows_spec (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    Pivoted (rawCellRows C e) ∧ spanB (rawCellRows C e) = (cornerCoordMap C e).range := by
  have h := rref_spec (fun j : Fin d => List.mem_finRange j) (cornerGenerators C e)
  unfold rawCellRows
  rw [rrefStored_eq (Ops.ofField K) List.mem_finRange]
  refine ⟨h.1, h.2.trans ?_⟩
  let b := Pi.basisFun K (Fin d)
  let f := cornerCoordMap C e
  have hList : {v | v ∈ cornerGenerators C e} = f '' Set.range b := by
    ext v
    change (v ∈ List.ofFn (fun j : Fin d => f (Pi.single j 1))) ↔ _
    simp only [List.mem_ofFn, Set.mem_image, Set.mem_range, Pi.basisFun_apply, b]
    exact ⟨by rintro ⟨j, rfl⟩; exact ⟨_, ⟨j, rfl⟩, rfl⟩,
      by rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩⟩
  rw [spanL, hList, ← Submodule.map_span, b.span_eq, Submodule.map_top]

theorem rawCellDegree_eq (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    rawCellDegree C e = finrank K (cornerCoordMap C e).range := by
  obtain ⟨hPivot, hRange⟩ := rawCellRows_spec C e
  rw [← hRange, finrank_spanB hPivot]
  rfl

/-- Coordinates of the projection (e x), given by its entries at the
actual RREF pivots. -/
def cellCoefficients (C : A ≃ₗ[K] (Fin d → K)) (e x : A) :
    Fin (rawCellDegree C e) → K :=
  fun i => C (e * x) ((rawCellRows C e).get i).1

/-- Evaluate a packed corner vector in the represented ambient algebra. -/
def cellDecode (C : A ≃ₗ[K] (Fin d → K)) (e : A)
    (x : Fin (rawCellDegree C e) → K) : A :=
  C.symm (∑ i : Fin (rawCellDegree C e), (x i) • ((rawCellRows C e).get i).2)

private theorem pivot_sum {bs : List (Fin d × (Fin d → K))} (P : Pivoted bs)
    (x : Fin bs.length → K) (i : Fin bs.length) :
    (∑ j : Fin bs.length, x j • (bs.get j).2) (bs.get i).1 = x i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [P.2.1 _ (List.get_mem _ _), mul_one]
  · intro j _ hji
    have hne : (bs.get i).1 ≠ (bs.get j).1 := by
      intro h
      apply hji
      have := (List.Nodup.get_inj_iff P.1 (i := ⟨j, by simp⟩) (j := ⟨i, by simp⟩)).1
        (by simpa using h.symm)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    rw [P.2.2 _ (List.get_mem _ _) _ (List.get_mem _ _) hne, mul_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

theorem cellDecode_coefficients (C : A ≃ₗ[K] (Fin d → K)) (e x : A) :
    cellDecode C e (cellCoefficients C e x) = e * x := by
  let bs := rawCellRows C e
  let v := C (e * x)
  obtain ⟨P, hspan⟩ := rawCellRows_spec C e
  have hv : v ∈ spanB bs := by
    rw [show spanB bs = (cornerCoordMap C e).range from hspan]
    refine ⟨C x, ?_⟩
    change C (e * (C.symm (C x))) = C (e * x)
    rw [C.symm_apply_apply]
  rw [spanB_eq_range] at hv
  obtain ⟨ws, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hcoeff : cellCoefficients C e x = ws := by
    funext i
    change v (bs.get i).1 = ws i
    rw [← hw]
    exact pivot_sum P ws i
  rw [hcoeff]
  exact C.symm_apply_eq.mpr hw

/-- Field block coordinates of a mode embedding into a given live corner. -/
def cellEmbedding {B : Type} [Semiring B] [Algebra K B]
    (C : A ≃ₗ[K] (Fin d → K)) (e : A) (f : B →ₐ[K] A) (x : B) :
    Fin (rawCellDegree C e) → K :=
  cellCoefficients C e (f x)

theorem cellDecode_embedding {B : Type} [Semiring B] [Algebra K B]
    (C : A ≃ₗ[K] (Fin d → K)) (e : A) (f : B →ₐ[K] A) (x : B) :
    cellDecode C e (cellEmbedding C e f x) = e * f x :=
  cellDecode_coefficients C e (f x)

/-- Any unpacked corner word is in the image of multiplication by its
idempotent. -/
theorem cellDecode_fixed (C : A ≃ₗ[K] (Fin d → K)) {e : A} (he : e * e = e)
    (w : Fin (rawCellDegree C e) → K) : e * cellDecode C e w = cellDecode C e w := by
  let bs := rawCellRows C e
  let s := ∑ i : Fin bs.length, w i • (bs.get i).2
  have hm : s ∈ spanB bs := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (mem_spanB (List.get_mem _ _))
  rw [(rawCellRows_spec C e).2] at hm
  obtain ⟨y, hy⟩ := hm
  change C (e * C.symm y) = s at hy
  have hr : C.symm s = e * C.symm y := C.symm_apply_eq.mpr hy.symm
  change e * C.symm s = C.symm s
  rw [hr, ← mul_assoc, he]

theorem cellCoefficients_decode (C : A ≃ₗ[K] (Fin d → K)) {e : A} (he : e * e = e)
    (w : Fin (rawCellDegree C e) → K) : cellCoefficients C e (cellDecode C e w) = w := by
  funext i
  unfold cellCoefficients
  rw [cellDecode_fixed C he w]
  change C (C.symm (∑ j, w j • ((rawCellRows C e).get j).2))
      ((rawCellRows C e).get i).1 = w i
  rw [C.apply_symm_apply]
  exact pivot_sum (rawCellRows_spec C e).1 w i

theorem rawCellDegree_le (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    rawCellDegree C e ≤ d := by
  rw [rawCellDegree, ← finrank_spanB (rawCellRows_spec C e).1]
  simpa using Submodule.finrank_le (spanB (rawCellRows C e))

#print axioms cellDecode_coefficients
#print axioms cellDecode_embedding
#print axioms cellCoefficients_decode
#print axioms rawCellDegree_le

end EvenTI.CellProducer
