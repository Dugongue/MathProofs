import EvenP6PrimaryKernel
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace EvenTI.PrimaryProducer

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial Module EvenTI.Contract
open Mathproof.P15FactorRef20261007 Mathproof.P15RecogOps20261007
open Mathproof.P15LinAlgKer20261007 (freeCols kerVec_free_other mem_freeCols)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

def primaryRows (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    List (Fin n × (Fin n → K)) :=
  rrefStored (Ops.ofField K) (List.finRange n)
    ((List.finRange n).map (matrixPower (matrixHorner A p) e))

/-- The free coordinates of a primary subspace are obtained from the same
row reduction that constructs its basis vectors. -/
def primaryLabels (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    List (Fin n) :=
  freeCols (List.finRange n) (primaryRows A p e)

def primaryColumns (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ)
    (j : Fin (primaryLabels A p e).length) : Fin n → K :=
  kerVec (Ops.ofField K) (primaryRows A p e) ((primaryLabels A p e).get j)

theorem primaryColumns_read (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ)
    (i j : Fin (primaryLabels A p e).length) :
    primaryColumns A p e j ((primaryLabels A p e).get i) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [primaryColumns, kerVec, Ops.ofField]
  · have hnodup : (primaryLabels A p e).Nodup := (List.nodup_finRange _).filter _
    have hne : (primaryLabels A p e).get i ≠ (primaryLabels A p e).get j :=
      fun h => hij (hnodup.injective_get h)
    have hFree := (mem_freeCols.mp (List.get_mem (primaryLabels A p e) i)).2
    rw [if_neg hij]
    exact kerVec_free_other hFree hne

theorem primaryColumns_independent (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    LinearIndependent K (primaryColumns A p e) := by
  let read : (Fin n → K) →ₗ[K] (Fin (primaryLabels A p e).length → K) :=
    LinearMap.pi fun i => LinearMap.proj ((primaryLabels A p e).get i)
  apply LinearIndependent.of_comp read
  have h : read ∘ primaryColumns A p e = Pi.basisFun K (Fin (primaryLabels A p e).length) := by
    funext j i
    change primaryColumns A p e j ((primaryLabels A p e).get i) = _
    rw [primaryColumns_read, Pi.basisFun_apply, Pi.single_apply]
  rw [h]
  exact (Pi.basisFun K _).linearIndependent

theorem primaryColumns_span (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Submodule.span K (Set.range (primaryColumns A p e)) =
      ((aeval A ((toPoly p) ^ e)).mulVecLin).ker := by
  rw [← primaryBasis_span A p e]
  apply congrArg (Submodule.span K)
  ext y
  have he : primaryBasis A p e = (primaryLabels A p e).map
      (kerVec (Ops.ofField K) (primaryRows A p e)) := rfl
  change (∃ j, primaryColumns A p e j = y) ↔ ∃ j, (primaryBasis A p e).get j = y
  rw [← List.mem_iff_get, he, List.mem_map]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨_, List.get_mem _ _, rfl⟩
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hc
    exact ⟨j, congrArg _ hj⟩

def inclusion (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Matrix (Fin n) (Fin (primaryLabels A p e).length) K :=
  fun i j => primaryColumns A p e j i

/-- Convert the restriction of the anchor to the actual primary basis.
The inverse coordinate read is just the row indexed by the free coordinate. -/
def restrictedAnchor (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Matrix (Fin (primaryLabels A p e).length) (Fin (primaryLabels A p e).length) K :=
  fun i j => (A.mulVec (primaryColumns A p e j)) ((primaryLabels A p e).get i)

theorem assemble_read (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ)
    (x : Fin n → K) (hx : x ∈ ((aeval A ((toPoly p)^e)).mulVecLin).ker) :
    (inclusion A p e).mulVec (fun j => x ((primaryLabels A p e).get j)) = x := by
  let L := frameFromVectors ((aeval A ((toPoly p)^e)).mulVecLin)
    (primaryColumns A p e) (primaryColumns_independent A p e) (primaryColumns_span A p e)
  obtain ⟨v,hv⟩ := L.surjective ⟨x,hx⟩
  have he : x = ∑ j, v j • primaryColumns A p e j := by
    have hval : (L v).val = x := congrArg Subtype.val hv
    exact hval.symm.trans (frameFromVectors_apply ((aeval A ((toPoly p)^e)).mulVecLin)
      (primaryColumns A p e) (primaryColumns_independent A p e) (primaryColumns_span A p e) v)
  have hread (i : Fin (primaryLabels A p e).length) :
      x ((primaryLabels A p e).get i) = v i := by
    rw [he, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, primaryColumns_read, mul_ite, mul_zero, mul_one]
    simp
  ext i
  simp only [Matrix.mulVec, dotProduct, hread, inclusion]
  rw [he, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem restrictedAnchor_spec (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    inclusion A p e * restrictedAnchor A p e = A * inclusion A p e := by
  let M := aeval A ((toPoly p)^e)
  have hc : Commute M A := by
    have h : Commute (aeval A ((toPoly p)^e)) (aeval A (X : K[X])) :=
      (Commute.all _ _).map (aeval A)
    rw [aeval_X] at h
    exact h
  ext i j
  let col := primaryColumns A p e j
  have hk : col ∈ M.mulVecLin.ker := by
    rw [← primaryColumns_span A p e]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hk' : A.mulVec col ∈ M.mulVecLin.ker := by
    have hz : M.mulVec col = 0 := LinearMap.mem_ker.mp hk
    apply LinearMap.mem_ker.mpr
    change M.mulVec (A.mulVec col) = 0
    rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  exact congrFun (assemble_read A p e (A.mulVec col) hk') i

#print axioms primaryColumns_span
#print axioms primaryColumns_independent
#print axioms restrictedAnchor_spec

end EvenTI.PrimaryProducer
