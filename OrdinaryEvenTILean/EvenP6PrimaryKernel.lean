import EvenP5InvRref
import EvenP5KernelBasis
import Mathproof.Meta.P15FactorRefPoly20261007

namespace EvenTI.PrimaryProducer

open scoped Polynomial Matrix
open Polynomial Matrix EvenTI.Contract
open Mathproof.P15FactorRef20261007 Mathproof.P15RecogOps20261007

variable {K : Type} [Field K] {n : ℕ}

/-- Store the entries of a square matrix in a shared dense table. -/
def storeMatrix (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  let table := Vector.ofFn (fun i : Fin n => Vector.ofFn (A i))
  Matrix.of fun i j => table[i.val][j.val]

@[simp] theorem storeMatrix_eq (A : Matrix (Fin n) (Fin n) K) : storeMatrix A = A := by
  ext i j
  simp [storeMatrix]

/-- Horner evaluation of an ascending coefficient list at an actual matrix. -/
def matrixHorner (A : Matrix (Fin n) (Fin n) K) : List K → Matrix (Fin n) (Fin n) K
  | [] => 0
  | a :: p => storeMatrix (a • (1 : Matrix (Fin n) (Fin n) K) + A * matrixHorner A p)

theorem matrixHorner_spec (A : Matrix (Fin n) (Fin n) K) (p : List K) :
    matrixHorner A p = aeval A (toPoly p) := by
  induction p with
  | nil => simp [matrixHorner, toPoly]
  | cons a p ih =>
    rw [matrixHorner, storeMatrix_eq, toPoly, map_add, map_mul, aeval_X, aeval_C, ih,
      Algebra.algebraMap_eq_smul_one]

/-- A materialized matrix power. The caller uses at most the multiplicity of
one characteristic factor. -/
def matrixPower (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 1
  | e+1 => storeMatrix (matrixPower A e * A)

@[simp] theorem matrixPower_spec (A : Matrix (Fin n) (Fin n) K) (e : ℕ) :
    matrixPower A e = A ^ e := by
  induction e with
  | zero => simp [matrixPower]
  | succ e ih => rw [matrixPower, storeMatrix_eq, ih, pow_succ]

section Kernel

variable [DecidableEq K]

/-- Compute the live primary basis using the stored-row elimination routine. -/
def primaryBasis (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    List (Fin n → K) :=
  let M := matrixPower (matrixHorner A p) e
  kerBasisStored (Ops.ofField K) (List.finRange n) ((List.finRange n).map M)

private theorem primaryBasis_eq_raw (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    primaryBasis A p e =
      rawKernelVectors (matrixPower (matrixHorner A p) e) (Equiv.refl _) (Equiv.refl _) := by
  simp [primaryBasis, kerBasisStored_eq _ (fun i => List.mem_finRange i),
    rawKernelVectors, orderedIndices]

theorem primaryBasis_independent (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    LinearIndependent K (primaryBasis A p e).get := by
  rw [primaryBasis_eq_raw]
  apply rawKernelVectors_independent

theorem primaryBasis_span (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Submodule.span K (Set.range (primaryBasis A p e).get) =
      ((aeval A ((toPoly p) ^ e)).mulVecLin).ker := by
  rw [primaryBasis_eq_raw, rawKernelVectors_span, matrixPower_spec, matrixHorner_spec, map_pow]

#print axioms primaryBasis_independent
#print axioms primaryBasis_span

end Kernel
end EvenTI.PrimaryProducer
