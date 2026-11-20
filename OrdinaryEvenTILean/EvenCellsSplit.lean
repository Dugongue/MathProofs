import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Artinian.Module

/-! Existence of field cells for a tensor product of a variable number of finite fields. -/

open scoped TensorProduct BigOperators
open Module

namespace EvenOrdinaryTI.CellSplit

section Frobenius

variable {K I : Type*} [Field K] [Fintype K] [Fintype I]
    {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]

-- The Frobenius induction from P15DecideRefKronMath20261007 with narrow imports.
private theorem add_pow_field_card (x y : ⨂[K] i, A i) (b : ℕ) :
    (x + y) ^ (Fintype.card K ^ b) =
      x ^ (Fintype.card K ^ b) + y ^ (Fintype.card K ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    simpa only [FiniteField.coe_frobeniusAlgHom] using
      map_add (FiniteField.frobeniusAlgHom K (⨂[K] i, A i))
        (x ^ Fintype.card K ^ b) (y ^ Fintype.card K ^ b)

theorem pow_eq_of_factors (b : ℕ)
    (h : ∀ i (x : A i), x ^ (Fintype.card K ^ b) = x)
    (x : ⨂[K] i, A i) : x ^ (Fintype.card K ^ b) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [smul_pow, FiniteField.pow_card_pow]
    congr 1
    change ((PiTensorProduct.tprodMonoidHom K) v) ^ _ = (PiTensorProduct.tprodMonoidHom K) v
    rw [← map_pow]
    apply congrArg (PiTensorProduct.tprodMonoidHom K)
    funext i
    exact h i (v i)
  | add x y hx hy =>
    rw [add_pow_field_card, hx, hy]

theorem isReduced_of_factors (b : ℕ) (hb : 0 < b)
    (h : ∀ i (x : A i), x ^ (Fintype.card K ^ b) = x) :
    IsReduced (⨂[K] i, A i) := by
  constructor
  intro x ⟨k, hk⟩
  have hQ : 1 < Fintype.card K ^ b := Nat.one_lt_pow hb.ne' Fintype.one_lt_card
  have hpow (t : ℕ) : x ^ ((Fintype.card K ^ b) ^ t) = x := by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, pow_mul, ih, pow_eq_of_factors b h]
  have hk' : k ≤ (Fintype.card K ^ b) ^ k := (Nat.lt_pow_self hQ).le
  rw [← hpow k, ← Nat.sub_add_cancel hk', pow_add, hk, mul_zero]

end Frobenius

section Fields

variable {K I : Type*} [Field K] [Fintype K] [Fintype I]
    {A : I → Type*} [∀ i, Field (A i)] [∀ i, Algebra K (A i)] [∀ i, Fintype (A i)]

theorem isReduced_tensor_of_finite_fields : IsReduced (⨂[K] i, A i) := by
  classical
  let b := ∏ i, Module.finrank K (A i)
  have hb : 0 < b := Finset.prod_pos fun i _ => Module.finrank_pos
  apply isReduced_of_factors b hb
  intro i x
  obtain ⟨c, hc⟩ : Module.finrank K (A i) ∣ b :=
    Finset.dvd_prod_of_mem (fun j => Module.finrank K (A j)) (Finset.mem_univ i)
  rw [hc, pow_mul, ← Module.card_eq_pow_finrank]
  exact FiniteField.pow_card_pow c x

theorem finite_tensor_of_finite_fields : Module.Finite K (⨂[K] i, A i) := by
  classical
  exact Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.finBasis K (A i)))

/-- The cell decomposition exists for any number of finite-field factors.
This equivalence uses maximal ideals and is a semantic specification for a splitter. -/
noncomputable def finiteFieldCells :
    (⨂[K] i, A i) ≃ₐ[K]
      (∀ M : MaximalSpectrum (⨂[K] i, A i), (⨂[K] i, A i) ⧸ M.asIdeal) := by
  letI := finite_tensor_of_finite_fields (K := K) (A := A)
  letI := isReduced_tensor_of_finite_fields (K := K) (A := A)
  letI : IsArtinianRing (⨂[K] i, A i) := IsArtinianRing.of_finite K _
  exact (IsArtinianRing.equivPi (⨂[K] i, A i)).restrictScalars K

end Fields


section Products

variable {K I : Type*} [Field K] [Fintype K] [Fintype I]
    {L : I → Type*} [∀ i, Fintype (L i)]
    {C : ∀ i, L i → Type*} [∀ i j, Field (C i j)] [∀ i j, Algebra K (C i j)]
    [∀ i j, Fintype (C i j)]

theorem isReduced_tensor_of_products :
    IsReduced (⨂[K] i, (∀ j, C i j)) := by
  classical
  let b := ∏ a : Sigma L, Module.finrank K (C a.1 a.2)
  have hb : 0 < b := Finset.prod_pos fun a _ => Module.finrank_pos
  apply isReduced_of_factors b hb
  intro i x
  funext j
  rw [Pi.pow_apply]
  obtain ⟨c, hc⟩ : Module.finrank K (C i j) ∣ b :=
    Finset.dvd_prod_of_mem (fun a : Sigma L => Module.finrank K (C a.1 a.2))
      (Finset.mem_univ ⟨i, j⟩)
  rw [hc, pow_mul, ← Module.card_eq_pow_finrank]
  exact FiniteField.pow_card_pow c (x j)

end Products
end EvenOrdinaryTI.CellSplit

#print axioms EvenOrdinaryTI.CellSplit.isReduced_tensor_of_finite_fields
#print axioms EvenOrdinaryTI.CellSplit.finiteFieldCells
#print axioms EvenOrdinaryTI.CellSplit.isReduced_tensor_of_products
