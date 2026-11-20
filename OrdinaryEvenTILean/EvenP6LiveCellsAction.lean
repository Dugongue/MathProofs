import EvenP6LiveCells

/-! The raw field-cell caller and the dense tensor action use the same
local multiplication matrices in the gauges' coefficient coordinates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellPreparation

open scoped BigOperators TensorProduct
open EvenTI.CellProducer Module

variable {K : Type} [Field K] {d : ℕ} {width : Fin d → ℕ}
  {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (t : ∀ i v, WordTable K (D i v)) [WordTable.Laws (liveJointTable t)]
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)

def liveActionMatrix (i : Fin d) (a : ∀ v, X i v) :
    Matrix (LiveModeIndex D i) (LiveModeIndex D i) K :=
  fun p q => (blockTable (t i)).multiply
    (fun z => (P i z.1).symm (a z.1) z.2) (Pi.single q 1) p

include hOne hMul in
theorem liveActionMatrix_eq (i : Fin d) (a : ∀ v, X i v) (p q : LiveModeIndex D i) :
    liveActionMatrix t P i a p q =
      (liveModeBasis P i).repr (a * liveModeBasis P i q) p := by
  let E := blockDecode (P i)
  have h := (blockTable_model (t i) (P i) (hOne i) (hMul i)).2
  change _ = (Pi.basisFun K _).repr (E.symm (a * E ((Pi.basisFun K _) q))) p
  conv_rhs => rw [← E.apply_symm_apply a]
  rw [Pi.basisFun_apply, ← h, E.symm_apply_apply, Pi.basisFun_repr]
  rfl

private theorem livePure_eq_prod (a : ∀ i v, X i v) :
    PiTensorProduct.tprod K a =
      ∏ i : Fin d, PiTensorProduct.singleAlgHom (R := K) i (a i) := by
  have h : (∏ i : Fin d, MonoidHom.mulSingle (fun i => ∀ v, X i v) i (a i)) = a := by
    funext j
    rw [Fintype.prod_apply]
    simp only [MonoidHom.mulSingle_apply]
    exact Fintype.prod_pi_mulSingle ..
  conv_lhs => rw [← h]
  exact map_prod (PiTensorProduct.tprodMonoidHom K)
    (fun i => MonoidHom.mulSingle (fun i => ∀ v, X i v) i (a i)) Finset.univ

theorem liveMode_decode (i : Fin d) (a : ∀ v, X i v) :
    denseDecode (liveModeBasis P) (liveMode t P hOne hMul i a).val =
      PiTensorProduct.singleAlgHom (R := K) i a := by
  rw [liveMode_apply, modeWord_decode _ _ _ (liveUnitCoeff_eq t P hOne hMul),
    liveModeBasis_decode]
  congr 1
  exact (blockDecode (P i)).apply_symm_apply a

/-- Acting by the computed local multiplication matrices agrees exactly
with multiplying by the corresponding product in the real joint table. -/
theorem liveTableAction_eq (a : ∀ i v, X i v) (w : LiveJointIndex D → K) :
    (∏ i : Fin d, liveMode t P hOne hMul i (a i)) * (⟨w⟩ : LiveJoint t) =
      (⟨wordAction (fun i => liveActionMatrix t P i (a i)) w⟩ : LiveJoint t) := by
  let E := tensorTable_decode (liveModeBasis P) (liveUnitCoeff t) (liveMulCoeff t)
    (liveUnitCoeff_eq t P hOne hMul) (liveMulCoeff_eq t P hOne hMul)
  apply E.injective
  rw [map_mul, map_prod]
  have h (i : Fin d) : E (liveMode t P hOne hMul i (a i)) =
      PiTensorProduct.singleAlgHom (R := K) i (a i) :=
    liveMode_decode t P hOne hMul i (a i)
  simp_rw [h]
  rw [← livePure_eq_prod]
  exact (denseDecode_wordAction (liveModeBasis P) a _
    (fun i => liveActionMatrix_eq t P hOne hMul i (a i)) w).symm

#print axioms liveActionMatrix_eq
#print axioms liveTableAction_eq

end EvenTI.CellPreparation
