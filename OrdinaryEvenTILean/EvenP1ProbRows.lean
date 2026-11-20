import EvenNextRecipLabels

namespace Mathproof.EvenTI.Reciprocal.PartOne

open Matrix Module LinearMap
open scoped Matrix BigOperators
open Mathproof.EvenTI.Reciprocal.Next (traceKernel)

noncomputable section

variable {K I B L J : Type*} [Field K]
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

def rectDualLin : Matrix B I K →ₗ[K] Dual K (Matrix I B K) where
  toFun V :=
    { toFun := fun U => (U * V).trace
      map_add' U U' := by rw [Matrix.add_mul, Matrix.trace_add]
      map_smul' c U := by simp [Matrix.smul_mul, Matrix.trace_smul] }
  map_add' V V' := by ext U; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c V := by ext U; simp [Matrix.mul_smul, Matrix.trace_smul]

theorem rectDualLin_apply (V : Matrix B I K) (U : Matrix I B K) :
    rectDualLin V U = (U * V).trace := rfl

/-- The shape transposition identifies the rectangular dual pairing with
the ordinary linear dual. -/
def rectDual : Matrix B I K ≃ₗ[K] Dual K (Matrix I B K) := by
  have hi : Function.Injective (rectDualLin (K := K) (I := I) (B := B)) := by
    intro A C he
    ext b i
    have h := congrArg (fun f : Dual K (Matrix I B K) => f (Matrix.single i b 1)) he
    simpa only [rectDualLin_apply, Matrix.trace_single_mul, one_smul] using h
  have hd : finrank K (Matrix B I K) = finrank K (Dual K (Matrix I B K)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_matrix, Module.finrank_matrix]; ac_rfl
  exact LinearEquiv.ofBijective rectDualLin
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

theorem rectDual_apply (V : Matrix B I K) (U : Matrix I B K) :
    rectDual V U = (U * V).trace := rfl

def primalSpan (U : L → Matrix I B K) : Submodule K (Matrix I B K) :=
  Submodule.span K (Set.range U)

abbrev Ann (U : L → Matrix I B K) := (primalSpan U).dualAnnihilator

theorem ann_mul_trace (U : L → Matrix I B K) (v : Ann U) (j : L) :
    (U j * rectDual.symm v.val).trace = 0 := by
  rw [← rectDual_apply, LinearEquiv.apply_symm_apply]
  exact (Submodule.mem_dualAnnihilator v.val).mp v.property (U j) (Submodule.subset_span ⟨j, rfl⟩)

variable [Fintype L]

def selectedRowsMatrix {a : ℕ} (U : L → Matrix I B K)
    (V : Fin a → J → Ann U) (t : J) : (Fin a → L → K) →ₗ[K] Matrix I I K where
  toFun x := ∑ i : Fin a, ∑ j : L, x i j • (U j * rectDual.symm (V i t).val)
  map_add' x y := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem selectedRowsMatrix_trace {a : ℕ} (U : L → Matrix I B K)
    (V : Fin a → J → Ann U) (t : J) (x : Fin a → L → K) :
    (selectedRowsMatrix U V t x).trace = 0 := by
  simp [selectedRowsMatrix, Matrix.trace_sum, Matrix.trace_smul, ann_mul_trace]

/-- The selected shear row map on the joint sample of primal rows and
the dual rows in their annihilator. -/
def selectedRows {a : ℕ} (U : L → Matrix I B K)
    (V : Fin a → J → Ann U) : (Fin a → L → K) →ₗ[K] (J → traceKernel (K := K) (I := I)) :=
  LinearMap.pi fun t => (selectedRowsMatrix U V t).codRestrict traceKernel
    (selectedRowsMatrix_trace U V t)

theorem selectedRows_apply {a : ℕ} (U : L → Matrix I B K)
    (V : Fin a → J → Ann U) (x : Fin a → L → K) (t : J) :
    (selectedRows U V x t).val =
      ∑ i : Fin a, ∑ j : L, x i j • (U j * rectDual.symm (V i t).val) := rfl

#print axioms rectDual_apply
#print axioms selectedRowsMatrix_trace
#print axioms selectedRows_apply

end
end Mathproof.EvenTI.Reciprocal.PartOne
