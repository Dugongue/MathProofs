import EvenP5InvCut
import ComparatorPrimaryAlign

/-! A deterministic intertwiner for simple primary blocks. Existing
Problem 1.7 root actions supply the algebraic field meaning. -/

namespace EvenTI.PrimaryAlignment

open Matrix Module Polynomial EvenTI.Contract
open Mathproof.Problem17ComparatorPrimaryAlign

variable {K : Type} [Field K] {m : ℕ}

/-- The first standard vector of the installed primary coordinates. -/
def firstVector (m : ℕ) : Fin m → K := fun i => if i.val = 0 then 1 else 0

theorem firstVector_ne_zero (hm : 0 < m) : firstVector (K := K) m ≠ 0 := by
  intro h
  simpa [firstVector] using congrFun h ⟨0, hm⟩

/-- A deterministic Krylov basis from the literal anchor matrix. -/
def krylovMatrix (A : Matrix (Fin m) (Fin m) K) : Matrix (Fin m) (Fin m) K :=
  fun i j => ((A ^ j.val).mulVec (firstVector m)) i

noncomputable def fieldVector (p : K[X]) (A : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) : AdjoinRoot p →ₗ[K] (Fin m → K) where
  toFun c := (matrixRootAction p A hA c).mulVec (firstVector m)
  map_add' c d := by rw [map_add, Matrix.add_mulVec]
  map_smul' c d := by simp [map_smul, Matrix.smul_mulVec]

theorem fieldVector_mul (p : K[X]) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0)
    (x y : AdjoinRoot p) :
    fieldVector p A hA (x * y) =
      (matrixRootAction p A hA x).mulVec (fieldVector p A hA y) := by
  simp only [fieldVector, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Matrix.mulVec_mulVec]

@[simp] theorem fieldVector_one (p : K[X]) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) :
    fieldVector p A hA 1 = firstVector m := by
  simp [fieldVector]

theorem fieldVector_injective (p : K[X]) [Fact (Irreducible p)]
    (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) (hm : 0 < m) :
    Function.Injective (fieldVector p A hA) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra h
  have hu : IsUnit (matrixRootAction p A hA x) :=
    (isUnit_iff_ne_zero.mpr h).map (matrixRootAction p A hA)
  exact firstVector_ne_zero (K := K) hm
    (Matrix.mulVec_injective_iff_isUnit.mpr hu (hx.trans (Matrix.mulVec_zero _).symm))

noncomputable def fieldBasis (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m) :
    Basis (Fin m) K (AdjoinRoot p) :=
  (AdjoinRoot.powerBasis' hp).basis.reindex (finCongr hd)

theorem fieldBasis_apply (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m) (j : Fin m) :
    fieldBasis p hp hd j = AdjoinRoot.root p ^ j.val := by
  unfold fieldBasis
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem krylovMatrix_mulVec (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m)
    (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) (c : Fin m → K) :
    (krylovMatrix A).mulVec c = fieldVector p A hA ((fieldBasis p hp hd).equivFun.symm c) := by
  rw [Basis.equivFun_symm_apply, map_sum]
  ext i
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, fieldBasis_apply, fieldVector, map_pow,
    matrixRootAction_root, LinearMap.coe_mk, AddHom.coe_mk]
  unfold Matrix.mulVec dotProduct krylovMatrix
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem krylovMatrix_isUnit (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) :
    IsUnit (krylovMatrix A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro c d h
  rw [krylovMatrix_mulVec p hp hd A hA, krylovMatrix_mulVec p hp hd A hA] at h
  have hm : 0 < m := hd ▸ (Fact.out : Irreducible p).natDegree_pos
  exact (fieldBasis p hp hd).equivFun.symm.injective (fieldVector_injective p A hA hm h)

variable [DecidableEq K]

/-- Compute the common-factor gauge using the checked executable inverse. -/
def simpleGauge (A B : Matrix (Fin m) (Fin m) K) : Option (Matrix (Fin m) (Fin m) K) :=
  (rawMatrixInverse (krylovMatrix A)).map fun Ainv => krylovMatrix B * Ainv

theorem simpleGauge_eq_some (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) :
    simpleGauge A B = some (krylovMatrix B * (krylovMatrix A)⁻¹) := by
  unfold simpleGauge
  rw [(rawMatrixInverse_eq_some_iff _ _).mpr ⟨krylovMatrix_isUnit p hp hd A hA, rfl⟩]
  rfl

theorem fieldVector_surjective (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) :
    Function.Surjective (fieldVector p A hA) := by
  intro x
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr (krylovMatrix_isUnit p hp hd A hA) x
  exact ⟨(fieldBasis p hp hd).equivFun.symm v,
    (krylovMatrix_mulVec p hp hd A hA v).symm.trans hv⟩

/-- The computed gauge sends every field-vector coordinate to the same
coordinate in the other primary block. -/
theorem simpleGauge_mulVec (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0)
    (G : Matrix (Fin m) (Fin m) K) (hG : simpleGauge A B = some G) (c : AdjoinRoot p) :
    G.mulVec (fieldVector p A hA c) = fieldVector p B hB c := by
  rw [simpleGauge_eq_some p hp hd A hA] at hG
  obtain rfl := Option.some.inj hG
  let v := (fieldBasis p hp hd).equivFun c
  have eqA := krylovMatrix_mulVec p hp hd A hA v
  have eqB := krylovMatrix_mulVec p hp hd B hB v
  rw [LinearEquiv.symm_apply_apply] at eqA eqB
  rw [← eqA, ← eqB, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul]
  · rw [Matrix.mul_one]
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (krylovMatrix_isUnit p hp hd A hA)

theorem simpleGauge_spec (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0)
    (G : Matrix (Fin m) (Fin m) K) (hG : simpleGauge A B = some G) :
    IsUnit G ∧ B * G = G * A := by
  constructor
  · apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro y
    obtain ⟨c, rfl⟩ := fieldVector_surjective p hp hd B hB y
    exact ⟨_, simpleGauge_mulVec p hp hd A B hA hB G hG c⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := fieldVector_surjective p hp hd A hA x
    change (B * G).mulVec (fieldVector p A hA c) = (G * A).mulVec (fieldVector p A hA c)
    have hmove (M : Matrix (Fin m) (Fin m) K) (hM : aeval M p = 0) :
        fieldVector p M hM (AdjoinRoot.root p * c) =
        M.mulVec (fieldVector p M hM c) := by
      rw [fieldVector_mul, matrixRootAction_root]
    simp only [← Matrix.mulVec_mulVec, simpleGauge_mulVec p hp hd A B hA hB G hG,
      ← hmove]

#print axioms simpleGauge_eq_some
#print axioms simpleGauge_spec

end EvenTI.PrimaryAlignment
