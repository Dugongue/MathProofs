import EvenP6AlignCoordinates
import EvenP5KernelScan
import ComparatorPrimaryPower
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! Use the explicit Problem 1.7 primary power to count a compact
intertwining kernel over the common coefficient field. -/

namespace EvenTI.PrimaryAlignment

open Matrix Module Polynomial EvenTI.Contract
open Mathproof.Problem17ComparatorPrimaryAlign
open Mathproof.Problem17ComparatorPrimaryPower

variable {K : Type} [Field K] [DecidableEq K] {a b : ℕ}

private theorem intertwines_powers {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (S : End K V) (T : End K W) (L : V →ₗ[K] W)
    (h : ∀ x, L (S x) = T (L x)) (r : ℕ) :
    ∀ x : V, L ((S ^ r) x) = (T ^ r) (L x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    intro x
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem intertwinerBasis_length_le_field
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (p : K[X]) (hp : p.Monic) [Fact (Irreducible p)] (r c d : ℕ)
    (hA : aeval (A ^ r) p = 0) (hB : aeval (B ^ r) p = 0)
    (ha : a = p.natDegree * c) (hb : b = p.natDegree * d) :
    (intertwinerBasis A B).length ≤ p.natDegree * (c * d) := by
  let V := Fin a → K
  let W := Fin b → K
  let S : End K V := Matrix.toLinAlgEquiv' A
  let T : End K W := Matrix.toLinAlgEquiv' B
  let E := AdjoinRoot p
  let M := intertwiningMatrix A B
  let N := M.mulVecLin.ker
  have hS : aeval (S ^ r) p = 0 := by
    change aeval (Matrix.toLinAlgEquiv' A ^ r) p = 0
    rw [← map_pow, aeval_algHom_apply, hA, map_zero]
  have hT : aeval (T ^ r) p = 0 := by
    change aeval (Matrix.toLinAlgEquiv' B ^ r) p = 0
    rw [← map_pow, aeval_algHom_apply, hB, map_zero]
  let φ := rootAction p (S ^ r) hS
  let ψ := rootAction p (T ^ r) hT
  letI : Module E V := Module.compHom V φ.toRingHom
  letI : Module E W := Module.compHom W ψ.toRingHom
  haveI : IsScalarTower K E V := ⟨fun k e x => by
    change φ (k • e) x = k • φ e x
    rw [map_smul]
    rfl⟩
  haveI : IsScalarTower K E W := ⟨fun k e x => by
    change ψ (k • e) x = k • ψ e x
    rw [map_smul]
    rfl⟩
  haveI : Module.Finite E V := Module.Finite.of_restrictScalars_finite K E V
  haveI : Module.Finite E W := Module.Finite.of_restrictScalars_finite K E W
  let base (x : N) : V →ₗ[K] W := Matrix.toLin' (unflattenMap x.val)
  have hbase (x : N) (z : V) : base x (S z) = T (base x z) := by
    have hx := (intertwiningKernel_iff A B (unflattenMap x.val)).mp (by
      rw [flattenMap_unflattenMap]
      exact x.property)
    change (unflattenMap x.val).mulVec (A.mulVec z) =
      B.mulVec ((unflattenMap x.val).mulVec z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx]
  let transport (x : N) : V →ₗ[E] W :=
    { toFun := base x
      map_add' := (base x).map_add
      map_smul' := root_intertwining φ ψ (base x) (by
        simpa only [φ, ψ, rootAction_root] using
          intertwines_powers S T (base x) (hbase x) r) }
  let J : N →ₗ[K] (V →ₗ[E] W) :=
    { toFun := transport
      map_add' := by
        intro x y
        ext z i
        change Matrix.mulVec (unflattenMap (x.val + y.val)) z i =
          (Matrix.mulVec (unflattenMap x.val) z + Matrix.mulVec (unflattenMap y.val) z) i
        rw [show unflattenMap (x.val + y.val) = unflattenMap x.val + unflattenMap y.val from rfl,
          Matrix.add_mulVec]
      map_smul' := by
        intro k x
        ext z i
        change Matrix.mulVec (unflattenMap (k • x.val)) z i =
          (k • Matrix.mulVec (unflattenMap x.val) z) i
        rw [show unflattenMap (k • x.val) = k • unflattenMap x.val from rfl, Matrix.smul_mulVec] }
  have hJ : Function.Injective J := by
    intro x y h
    have hxy : base x = base y := by
      apply LinearMap.ext
      intro z
      exact LinearMap.congr_fun h z
    apply Subtype.ext
    exact congrArg flattenMap (Matrix.toLin'.injective hxy)
  have hE : finrank K E = p.natDegree := (AdjoinRoot.powerBasis' hp).finrank
  have hV : finrank K V = a := by simp [V]
  have hW : finrank K W = b := by simp [W]
  have hpos := (Fact.out : Irreducible p).natDegree_pos
  have hv : finrank E V = c := Nat.eq_of_mul_eq_mul_left hpos
    (((hE ▸ Module.finrank_mul_finrank K E V).trans hV).trans ha)
  have hw : finrank E W = d := Nat.eq_of_mul_eq_mul_left hpos
    (((hE ▸ Module.finrank_mul_finrank K E W).trans hW).trans hb)
  calc
    (intertwinerBasis A B).length = finrank K N :=
      rawKernelVectors_length M finProdFinEquiv finProdFinEquiv
    _ ≤ finrank K (V →ₗ[E] W) := LinearMap.finrank_le_finrank_of_injective hJ
    _ = p.natDegree * (c * d) := by
      rw [← Module.finrank_mul_finrank K E (V →ₗ[E] W), hE, Module.finrank_linearMap, hv, hw]

theorem intertwinerBasis_length_le_primary [Fintype K]
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (p : K[X]) (hp : p.Monic) (hi : Irreducible p) (e c d : ℕ)
    (hA : aeval A (p ^ e) = 0) (hB : aeval B (p ^ e) = 0)
    (ha : a = p.natDegree * c) (hb : b = p.natDegree * d) :
    (intertwinerBasis A B).length ≤ p.natDegree * (c * d) := by
  by_cases hapos : 0 < a
  · by_cases hbpos : 0 < b
    · letI : Nonempty (Fin a) := ⟨⟨0, hapos⟩⟩
      letI : Nonempty (Fin b) := ⟨⟨0, hbpos⟩⟩
      letI : Fact (Irreducible p) := ⟨hi⟩
      have hpA := (minpoly_explicit_primary_power A hp hi
        (minpoly.dvd K A hA) (le_refl e)).2
      have hpB := (minpoly_explicit_primary_power B hp hi
        (minpoly.dvd K B hB) (le_refl e)).2
      exact intertwinerBasis_length_le_field A B p hp _ c d
        (hpA ▸ minpoly.aeval K _) (hpB ▸ minpoly.aeval K _) ha hb
    · have hbzero : b = 0 := Nat.eq_zero_of_not_pos hbpos
      exact (intertwinerBasis_length_le A B).trans (by simp [hbzero])
  · have hazero : a = 0 := Nat.eq_zero_of_not_pos hapos
    exact (intertwinerBasis_length_le A B).trans (by simp [hazero])

#print axioms intertwinerBasis_length_le_field
#print axioms intertwinerBasis_length_le_primary

end EvenTI.PrimaryAlignment
