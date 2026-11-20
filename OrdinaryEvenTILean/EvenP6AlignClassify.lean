import EvenP6AlignGauge
import EvenP6AlignIntertwiners

namespace EvenTI.PrimaryAlignment

open Matrix Module Polynomial EvenTI.Contract
open Mathproof.Problem17ComparatorPrimaryAlign

variable {K : Type} [Field K] [DecidableEq K] {m a b : ℕ}

/-- The actual linear-system kernel never uses more coordinates than
the space of all rectangular maps. -/
theorem intertwinerBasis_length_le
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    (intertwinerBasis A B).length ≤ b * a := by
  have hi := rawKernelVectors_independent (intertwiningMatrix A B)
    finProdFinEquiv finProdFinEquiv
  simpa [intertwinerBasis, Fintype.card_prod] using hi.fintype_card_le_finrank

theorem intertwine_fieldAction (p : K[X]) (A B : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0) (X : Matrix (Fin m) (Fin m) K)
    (hX : B * X = X * A) (c : AdjoinRoot p) :
    X * matrixRootAction p A hA c = matrixRootAction p B hB c * X := by
  have hc : c ∈ Algebra.adjoin K ({AdjoinRoot.root p} : Set (AdjoinRoot p)) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem d hd =>
    obtain rfl : d = AdjoinRoot.root p := hd
    simpa only [matrixRootAction_root] using hX.symm
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Algebra.commutes r X).symm
  | add x y hx hy ihx ihy =>
    rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, map_mul, ← Matrix.mul_assoc X, ihx, Matrix.mul_assoc, ihy, ← Matrix.mul_assoc]

/-- The output gauge turns an arbitrary simple-block intertwiner into a
unique scalar over the common factor field. -/
theorem simpleGauge_classify (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0)
    (G : Matrix (Fin m) (Fin m) K) (hG : simpleGauge A B = some G)
    (X : Matrix (Fin m) (Fin m) K) :
    B * X = X * A ↔ ∃! c : AdjoinRoot p, X = G * matrixRootAction p A hA c := by
  have move : ∀ c, (G * matrixRootAction p A hA c).mulVec (firstVector m) =
      fieldVector p B hB c := by
    intro c
    rw [← Matrix.mulVec_mulVec]
    exact simpleGauge_mulVec p hp hd A B hA hB G hG c
  constructor
  · intro hX
    obtain ⟨c, hc⟩ := fieldVector_surjective p hp hd B hB (X.mulVec (firstVector m))
    have hformula : X = G * matrixRootAction p A hA c := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨d, rfl⟩ := fieldVector_surjective p hp hd A hA v
      change X.mulVec (fieldVector p A hA d) =
        (G * matrixRootAction p A hA c).mulVec (fieldVector p A hA d)
      have hL : X.mulVec (fieldVector p A hA d) =
          (matrixRootAction p B hB d).mulVec (fieldVector p B hB c) := by
        change X.mulVec ((matrixRootAction p A hA d).mulVec (firstVector m)) = _
        rw [Matrix.mulVec_mulVec, intertwine_fieldAction p A B hA hB X hX d,
          ← Matrix.mulVec_mulVec, ← hc]
      rw [hL, ← fieldVector_mul, mul_comm d c, ← Matrix.mulVec_mulVec, ← fieldVector_mul,
        simpleGauge_mulVec p hp hd A B hA hB G hG]
    refine ⟨c, hformula, fun d hd' => ?_⟩
    have hm : 0 < m := hd ▸ (Fact.out : Irreducible p).natDegree_pos
    apply fieldVector_injective p B hB hm
    rw [← move, ← move, ← hd', ← hformula]
  · rintro ⟨c, rfl, _⟩
    have h := (simpleGauge_spec p hp hd A B hA hB G hG).2
    calc
      B * (G * matrixRootAction p A hA c) =
          G * (A * matrixRootAction p A hA c) := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
      _ = (G * matrixRootAction p A hA c) * A := by
        rw [intertwine_fieldAction p A A hA hA A rfl c, ← Matrix.mul_assoc]

theorem simpleGauge_unitScalar (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A B : Matrix (Fin m) (Fin m) K)
    (hA : aeval A p = 0) (hB : aeval B p = 0)
    (G : Matrix (Fin m) (Fin m) K) (hG : simpleGauge A B = some G)
    (c : AdjoinRoot p) : IsUnit (G * matrixRootAction p A hA c) ↔ c ≠ 0 := by
  constructor
  · intro hu hz
    have hm : 0 < m := hd ▸ (Fact.out : Irreducible p).natDegree_pos
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hzero : IsUnit (0 : Matrix (Fin m) (Fin m) K) := by simpa [hz] using hu
    exact not_isUnit_zero hzero
  · intro hc
    exact (simpleGauge_spec p hp hd A B hA hB G hG).1.mul
      ((isUnit_iff_ne_zero.mpr hc).map (matrixRootAction p A hA))

#print axioms intertwinerBasis_length_le
#print axioms simpleGauge_classify
#print axioms simpleGauge_unitScalar

end EvenTI.PrimaryAlignment
