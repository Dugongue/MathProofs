import EvenP6PrimaryBlocks
import Comparator46PrimaryTransport

/-! Restrict an ambient change in the actual free-column coordinates,
and reconstruct it from the direct-sum frame projections. -/

namespace EvenTI.PrimaryAlignment

open scoped BigOperators Polynomial
open Matrix Module Polynomial EvenTI.PrimaryProducer
open Mathproof.P15FactorRef20261007
open Mathproof.Problem17Comparator46Primary

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

abbrev blockWidth (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :=
  (primaryLabels A p e).length

/-- Read the designated free rows of the image of each source basis vector. -/
def restrictTransport (A B P : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Matrix (Fin (blockWidth B p e)) (Fin (blockWidth A p e)) K :=
  fun i j => (P.mulVec (primaryColumns A p e j)) ((primaryLabels B p e).get i)

private theorem eval_to_mulVecLin (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    (aeval A f).mulVecLin = aeval A.mulVecLin f := by
  have h := aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _) A f
  have convert (M : Matrix (Fin n) (Fin n) K) :
      Matrix.toLinAlgEquiv' M = M.mulVecLin := by
    apply LinearMap.ext
    intro v
    exact Matrix.toLinAlgEquiv'_apply M v
  simpa only [convert] using h.symm

theorem transport_primary_mem (A B P : Matrix (Fin n) (Fin n) K)
    (h : B * P = P * A) (f : K[X]) (v : Fin n → K)
    (hv : v ∈ ((aeval A f).mulVecLin).ker) :
    P.mulVec v ∈ ((aeval B f).mulVecLin).ker := by
  have hp (x : Fin n → K) : P.mulVecLin (A.mulVecLin x) = B.mulVecLin (P.mulVecLin x) := by
    change P.mulVec (A.mulVec x) = B.mulVec (P.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  rw [eval_to_mulVecLin] at hv ⊢
  apply LinearMap.mem_ker.mpr
  change aeval B.mulVecLin f (P.mulVecLin v) = 0
  rw [← Mathproof.Problem17Comparator46Primary.map_eval A.mulVecLin B.mulVecLin
    P.mulVecLin hp f v, LinearMap.mem_ker.mp hv, map_zero]

theorem inclusion_restrictTransport
    (A B P : Matrix (Fin n) (Fin n) K) (h : B * P = P * A) (p : List K) (e : ℕ) :
    inclusion B p e * restrictTransport A B P p e = P * inclusion A p e := by
  ext i j
  let v := primaryColumns A p e j
  have hv : v ∈ ((aeval A ((toPoly p)^e)).mulVecLin).ker := by
    rw [← primaryColumns_span A p e]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hw := transport_primary_mem A B P h ((toPoly p)^e) v hv
  exact congrFun (assemble_read B p e (P.mulVec v) hw) i

/-- Matrix reading of the free coordinates left-inverts the actual primary basis. -/
def readPrimary (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    Matrix (Fin (blockWidth A p e)) (Fin n) K :=
  fun i j => if j = (primaryLabels A p e).get i then 1 else 0

theorem readPrimary_inclusion (A : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ) :
    readPrimary A p e * inclusion A p e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, readPrimary, inclusion, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [primaryColumns_read, Matrix.one_apply]

theorem inclusion_left_injective {b : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (p : List K) (e : ℕ) :
    Function.Injective (fun X : Matrix (Fin (blockWidth A p e)) (Fin b) K =>
      inclusion A p e * X) := by
  intro X Y h
  have hx := congrArg (fun D : Matrix (Fin n) (Fin b) K => readPrimary A p e * D) h
  simpa only [← Matrix.mul_assoc, readPrimary_inclusion, Matrix.one_mul] using hx

theorem restrictTransport_intertwines (A B P : Matrix (Fin n) (Fin n) K)
    (h : B * P = P * A) (p : List K) (e : ℕ) :
    restrictedAnchor B p e * restrictTransport A B P p e =
      restrictTransport A B P p e * restrictedAnchor A p e := by
  apply inclusion_left_injective B p e
  calc
    inclusion B p e * (restrictedAnchor B p e * restrictTransport A B P p e) =
        B * (inclusion B p e * restrictTransport A B P p e) := by
      rw [← Matrix.mul_assoc, restrictedAnchor_spec, Matrix.mul_assoc]
    _ = P * (A * inclusion A p e) := by
      rw [inclusion_restrictTransport A B P h, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
    _ = inclusion B p e * (restrictTransport A B P p e * restrictedAnchor A p e) := by
      rw [← restrictedAnchor_spec, ← Matrix.mul_assoc, ← inclusion_restrictTransport A B P h,
        Matrix.mul_assoc]

theorem restrictTransport_inverses (A B : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) K)ˣ) (h : B * P.val = P.val * A)
    (p : List K) (e : ℕ) :
    restrictTransport A B P.val p e * restrictTransport B A P.inv p e = 1 ∧
      restrictTransport B A P.inv p e * restrictTransport A B P.val p e = 1 := by
  have hi : A * P.inv = P.inv * B := by
    calc
      A * P.inv = (P.inv * P.val) * A * P.inv := by rw [Units.inv_val, Matrix.one_mul]
      _ = P.inv * (P.val * A) * P.inv := by rw [Matrix.mul_assoc P.inv P.val A]
      _ = P.inv * B := by rw [← h, ← Matrix.mul_assoc P.inv B P.val,
          Matrix.mul_assoc (P.inv * B) P.val P.inv, Units.val_inv, Matrix.mul_one]
  constructor
  · apply inclusion_left_injective B p e
    change inclusion B p e * (_ * _) = inclusion B p e * 1
    rw [← Matrix.mul_assoc, inclusion_restrictTransport A B P.val h,
      Matrix.mul_assoc, inclusion_restrictTransport B A P.inv hi, ← Matrix.mul_assoc,
      Units.val_inv, Matrix.one_mul, Matrix.mul_one]
  · apply inclusion_left_injective A p e
    change inclusion A p e * (_ * _) = inclusion A p e * 1
    rw [← Matrix.mul_assoc, inclusion_restrictTransport B A P.inv hi,
      Matrix.mul_assoc, inclusion_restrictTransport A B P.val h, ← Matrix.mul_assoc,
      Units.inv_val, Matrix.one_mul, Matrix.mul_one]

theorem blockWidth_eq_of_transport (A B : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) K)ˣ) (h : B * P.val = P.val * A)
    (p : List K) (e : ℕ) :
    blockWidth B p e = blockWidth A p e := by
  let X := restrictTransport A B P.val p e
  let Y := restrictTransport B A P.inv p e
  obtain ⟨hXY, hYX⟩ := restrictTransport_inverses A B P h p e
  have hX : Function.Injective X.mulVecLin :=
    (show Function.LeftInverse Y.mulVec X.mulVec from fun x => by
      rw [Matrix.mulVec_mulVec, show Y * X = 1 from hYX, Matrix.one_mulVec]).injective
  have hY : Function.Injective Y.mulVecLin :=
    (show Function.LeftInverse X.mulVec Y.mulVec from fun y => by
      rw [Matrix.mulVec_mulVec, show X * Y = 1 from hXY, Matrix.one_mulVec]).injective
  have hx : blockWidth A p e ≤ blockWidth B p e := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_injective hX
  have hy : blockWidth B p e ≤ blockWidth A p e := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_injective hY
  exact le_antisymm hy hx

/-- Reindex target coordinates into the actual source block width. -/
def alignedTargetAnchor (A B : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ)
    (hw : blockWidth B p e = blockWidth A p e) :
    Matrix (Fin (blockWidth A p e)) (Fin (blockWidth A p e)) K :=
  (restrictedAnchor B p e).submatrix (finCongr hw).symm (finCongr hw).symm

def alignedTargetColumns (A B : Matrix (Fin n) (Fin n) K) (p : List K) (e : ℕ)
    (hw : blockWidth B p e = blockWidth A p e) :
    Matrix (Fin n) (Fin (blockWidth A p e)) K :=
  (inclusion B p e).submatrix id (finCongr hw).symm

/-- An ambient unit intertwining the two matrices supplies a unit in the
matching executable primary blocks, with the correct column equation. -/
theorem alignedRestriction_exists (A B : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) K)ˣ) (h : B * P.val = P.val * A)
    (p : List K) (e : ℕ) (hw : blockWidth B p e = blockWidth A p e) :
    ∃ X : Matrix (Fin (blockWidth A p e)) (Fin (blockWidth A p e)) K, IsUnit X ∧
      alignedTargetAnchor A B p e hw * X = X * restrictedAnchor A p e ∧
      alignedTargetColumns A B p e hw * X = P.val * inclusion A p e := by
  let E := (finCongr hw).symm
  let U := restrictTransport A B P.val p e
  let V := restrictTransport B A P.inv p e
  let X := U.submatrix E id
  let Y := V.submatrix id E
  obtain ⟨hUV,hVU⟩ := restrictTransport_inverses A B P h p e
  have hXY : X * Y = 1 := by
    change U.submatrix E (Equiv.refl _) * V.submatrix (Equiv.refl _) E = 1
    rw [Matrix.submatrix_mul_equiv, show U * V = 1 from hUV, Matrix.submatrix_one_equiv]
  have hYX : Y * X = 1 := by
    change V.submatrix id E * U.submatrix E id = 1
    rw [Matrix.submatrix_mul_equiv, show V * U = 1 from hVU, Matrix.submatrix_id_id]
  refine ⟨X, ⟨⟨X, Y, hXY, hYX⟩, rfl⟩, ?_, ?_⟩
  · change (restrictedAnchor B p e).submatrix E E * U.submatrix E (Equiv.refl _) =
      U.submatrix E (Equiv.refl _) * (restrictedAnchor A p e).submatrix (Equiv.refl _) (Equiv.refl _)
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, restrictTransport_intertwines A B P.val h]
  · change (inclusion B p e).submatrix id E * U.submatrix E id = _
    rw [Matrix.submatrix_mul_equiv, inclusion_restrictTransport A B P.val h, Matrix.submatrix_id_id]

section Reconstruct

variable {I : Type} [Fintype I] {w v : I → ℕ}

/-- Place the individual maps into the physical matrix using the rows of
the source frame inverse and the columns of the target frame. -/
def assembleTransport (D : ∀ i, Matrix (Fin n) (Fin (v i)) K)
    (X : ∀ i, Matrix (Fin (v i)) (Fin (w i)) K)
    (R : ∀ i, Matrix (Fin (w i)) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  ∑ i, D i * X i * R i

theorem assembleTransport_eq (P : Matrix (Fin n) (Fin n) K)
    (C : ∀ i, Matrix (Fin n) (Fin (w i)) K) (D : ∀ i, Matrix (Fin n) (Fin (v i)) K)
    (X : ∀ i, Matrix (Fin (v i)) (Fin (w i)) K)
    (R : ∀ i, Matrix (Fin (w i)) (Fin n) K)
    (hmatch : ∀ i, D i * X i = P * C i) (hframe : (∑ i, C i * R i) = 1) :
    assembleTransport D X R = P := by
  unfold assembleTransport
  simp only [hmatch, Matrix.mul_assoc]
  rw [← Matrix.mul_sum, hframe, Matrix.mul_one]

end Reconstruct

#print axioms inclusion_restrictTransport
#print axioms restrictTransport_intertwines
#print axioms restrictTransport_inverses
#print axioms blockWidth_eq_of_transport
#print axioms alignedRestriction_exists
#print axioms assembleTransport_eq

end EvenTI.PrimaryAlignment
