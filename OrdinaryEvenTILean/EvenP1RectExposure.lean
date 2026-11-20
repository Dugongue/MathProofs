import Anticommutator
import EvenLiveSingularBlock
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Bilinear

namespace Mathproof.EvenTI.Reciprocal.Part1

open Matrix Module
open scoped Matrix

variable {K I B L : Type*} [Field K]

/-- Apply one functional separately to each column. -/
def rowProjection (v : Module.Dual K (I → K)) : Matrix I B K →ₗ[K] (B → K) where
  toFun A b := v (fun i => A i b)
  map_add' A C := by
    ext b
    change v ((fun i => A i b) + fun i => C i b) = _
    exact map_add v _ _
  map_smul' a A := by
    ext b
    change v (a • fun i => A i b) = _
    exact map_smul v _ _

variable [Fintype I] [DecidableEq I]

theorem exists_escape_functional (Z : Matrix I I K)
    (hZ : ∀ a : K, Z ≠ a • 1) :
    ∃ (u : I → K) (v : Module.Dual K (I → K)), v u = 0 ∧ v (Z *ᵥ u) = 1 := by
  let E : Matrix I I K ≃ₐ[K] Module.End K (I → K) := Matrix.toLinAlgEquiv'
  have hP (a : K) : E Z ≠ a • LinearMap.id := by
    intro h
    apply hZ a
    apply E.injective
    have h1 : E (1 : Matrix I I K) = LinearMap.id := map_one E
    simpa only [map_smul, h1] using h
  obtain ⟨u, hu⟩ := Mathproof.Problem17Anticommutator.exists_outside_line (E Z) hP
  obtain ⟨v, hv, hvZ⟩ :=
    LinearMap.exists_extend_of_notMem (0 : (K ∙ u) →ₗ[K] K) hu 1
  exact ⟨u, v, LinearMap.congr_fun hv ⟨u, Submodule.mem_span_singleton_self u⟩, hvZ⟩

theorem rowProjection_vecMulVec (v : Module.Dual K (I → K)) (u : I → K)
    (z : B → K) :
    rowProjection v (vecMulVec u z) = v u • z := by
  ext b
  change v (fun i => u i * z b) = v u * z b
  have h : (fun i => u i * z b) = z b • u := by ext i; exact mul_comm _ _
  rw [h, map_smul, smul_eq_mul, mul_comm]

def rowSpan (v : Module.Dual K (I → K)) (U : L → Matrix I B K) : Submodule K (B → K) :=
  Submodule.span K (Set.range fun j => rowProjection v (U j))

/-- The projected row rank permits any label with a separating functional. -/
noncomputable def projectedRank (v : Module.Dual K (I → K)) (Z : Matrix I I K)
    (U : L → Matrix I B K) : Nat :=
  finrank K (Submodule.span K (Set.range fun j => (rowSpan v U).mkQ (rowProjection v (Z * U j))))

noncomputable def coefficientRank (Z : Matrix I I K) (U : L → Matrix I B K) : Nat :=
  let S := Submodule.span K (Set.range U)
  finrank K (Submodule.span K (Set.range fun j => S.mkQ (Z * U j)))

variable [Fintype B]

theorem projectedRank_le_coefficientRank (v : Module.Dual K (I → K))
    (Z : Matrix I I K) (U : L → Matrix I B K) :
    projectedRank v Z U ≤ coefficientRank Z U := by
  let S := Submodule.span K (Set.range U)
  let T := rowSpan v U
  have hST : S ≤ ((T.mkQ).comp (rowProjection v)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change T.mkQ (rowProjection v (U j)) = 0
    exact (Submodule.Quotient.mk_eq_zero T).mpr (Submodule.subset_span ⟨j, rfl⟩)
  let f := S.liftQ (T.mkQ.comp (rowProjection v)) hST
  let M := Submodule.span K (Set.range fun j => S.mkQ (Z * U j))
  have hM : M.map f =
      Submodule.span K (Set.range fun j => T.mkQ (rowProjection v (Z * U j))) := by
    change (Submodule.span K _).map f = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  change _ ≤ finrank K M
  unfold projectedRank
  rw [← hM]
  exact Submodule.finrank_map_le _ _

def perturb (U : L → Matrix I B K) (u : I → K) (z : L → B → K) :
    L → Matrix I B K :=
  fun j => U j + vecMulVec u (z j)

/-- With a fresh uniform input z, perturbation leaves the full matrix law unchanged. -/
def perturbEquiv (u : I → K) :
    ((L → Matrix I B K) × (L → B → K)) ≃ ((L → Matrix I B K) × (L → B → K)) where
  toFun x := (perturb x.1 u x.2, x.2)
  invFun x := (fun j => x.1 j - vecMulVec u (x.2 j), x.2)
  left_inv x := by
    apply Prod.ext
    · funext j
      exact add_sub_cancel_right _ _
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext j
      exact sub_add_cancel _ _
    · rfl

theorem rowSpan_perturb (U : L → Matrix I B K) (u : I → K)
    (v : Module.Dual K (I → K)) (z : L → B → K) (hv : v u = 0) :
    rowSpan v (perturb U u z) = rowSpan v U := by
  have h (j : L) : rowProjection v ((perturb U u z) j) = rowProjection v (U j) := by
    rw [perturb, map_add, rowProjection_vecMulVec, hv, zero_smul, add_zero]
  have he : (fun j => rowProjection v ((perturb U u z) j)) = fun j => rowProjection v (U j) :=
    funext h
  unfold rowSpan
  rw [he]

theorem projected_perturb (Z : Matrix I I K) (U : L → Matrix I B K)
    (u : I → K) (v : Module.Dual K (I → K)) (z : L → B → K)
    (hvZ : v (Z *ᵥ u) = 1) (j : L) :
    rowProjection v (Z * (perturb U u z) j) = rowProjection v (Z * U j) + z j := by
  rw [perturb, Matrix.mul_add, map_add, Matrix.mul_vecMulVec, rowProjection_vecMulVec,
    hvZ, one_smul]

#print axioms exists_escape_functional
#print axioms projectedRank_le_coefficientRank
#print axioms perturbEquiv
#print axioms rowSpan_perturb
#print axioms projected_perturb

end Mathproof.EvenTI.Reciprocal.Part1
