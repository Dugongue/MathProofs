import EvenWordDriver
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange

/-! Exact bounded enumeration for the kernel forms and repeated-primary
coefficient variables used by the even-order comparison driver. -/
namespace EvenTI.Contract
open Action

variable {K : Type} [Field K] [Fintype K]

/-- Binary arithmetical ranks index a complete list of coefficient choices.
The caller supplies the digit bijection of the fixed field. -/
def coefficients (F : FieldEncoding K) (c : Nat)
    (r : Fin (Fintype.card K ^ c)) : Fin c → K :=
  fun i => F.symm (finFunctionFinEquiv.symm r i)

/-- Inverse to the executable enumeration. -/
def coefficientIndex (F : FieldEncoding K) {c : Nat} (x : Fin c → K) :
    Fin (Fintype.card K ^ c) :=
  finFunctionFinEquiv (F ∘ x)

@[simp] theorem coefficients_index (F : FieldEncoding K) {c : Nat} (x : Fin c → K) :
    coefficients F c (coefficientIndex F x) = x := by
  funext i
  simp [coefficients, coefficientIndex]

theorem coefficients_injective (F : FieldEncoding K) (c : Nat) :
    Function.Injective (coefficients F c) := by
  intro r s h
  apply finFunctionFinEquiv.symm.injective
  funext i
  apply F.symm.injective
  exact congrFun h i

def coefficientChoices (F : FieldEncoding K) (c budget : Nat) : List (Fin c → K) :=
  if Fintype.card K ^ c ≤ budget then
    (List.finRange (Fintype.card K ^ c)).map (coefficients F c)
  else []

theorem coefficientChoices_length (F : FieldEncoding K) (c budget : Nat) :
    (coefficientChoices F c budget).length =
      if Fintype.card K ^ c ≤ budget then Fintype.card K ^ c else 0 := by
  unfold coefficientChoices
  split <;> simp

theorem coefficientChoices_length_le (F : FieldEncoding K) (c budget : Nat) :
    (coefficientChoices F c budget).length ≤ budget := by
  rw [coefficientChoices_length]
  split <;> omega

theorem mem_coefficientChoices (F : FieldEncoding K) {c budget : Nat} (x : Fin c → K) :
    x ∈ coefficientChoices F c budget ↔ Fintype.card K ^ c ≤ budget := by
  by_cases h : Fintype.card K ^ c ≤ budget
  · simp only [coefficientChoices, h, if_true, iff_true, List.mem_map]
    exact ⟨coefficientIndex F x, List.mem_finRange _, coefficients_index F x⟩
  · simp [coefficientChoices, h]

/-- Materialize the kernel vectors from a verified coefficient basis.
The zero vector is retained so the same enumerator also applies to
linear spaces of maps used in the repeated-primary steps. -/
def kernelChoices {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) : List V :=
  (coefficientChoices F c budget).map fun x => (frame x).val

theorem mem_kernelChoices {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) (v : V) :
    v ∈ kernelChoices F f frame budget ↔ f v = 0 ∧ Fintype.card K ^ c ≤ budget := by
  unfold kernelChoices
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(frame x).property, (mem_coefficientChoices F x).mp hx⟩
  · rintro ⟨hv, hg⟩
    refine ⟨frame.symm ⟨v, hv⟩, (mem_coefficientChoices F _).mpr hg, ?_⟩
    rw [LinearEquiv.apply_symm_apply]

theorem kernelChoices_length_le {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) :
    (kernelChoices F f frame budget).length ≤ budget := by
  unfold kernelChoices
  rw [List.length_map]
  exact coefficientChoices_length_le F c budget

/-- The exact test used by the singular form scan, with arbitrary
additional rank checks on the form. -/
def kernelForms {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [DecidableEq V] (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) (suitable : V → Bool) : List V :=
  (kernelChoices F f frame budget).filter fun v => decide (v ≠ 0) && suitable v

theorem mem_kernelForms {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [DecidableEq V] (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) (suitable : V → Bool) (v : V) :
    v ∈ kernelForms F f frame budget suitable ↔
      (f v = 0 ∧ Fintype.card K ^ c ≤ budget) ∧ (v ≠ 0 ∧ suitable v = true) := by
  simp [kernelForms, List.mem_filter, mem_kernelChoices]

theorem kernelForms_length_le {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [DecidableEq V] (F : FieldEncoding K) {c : Nat} (f : V →ₗ[K] W)
    (frame : (Fin c → K) ≃ₗ[K] f.ker) (budget : Nat) (suitable : V → Bool) :
    (kernelForms F f frame budget suitable).length ≤ budget :=
  (List.length_filter_le _ _).trans (kernelChoices_length_le F f frame budget)

#print axioms mem_coefficientChoices
#print axioms mem_kernelForms
#print axioms kernelForms_length_le

end EvenTI.Contract
