import EvenP1ProbKernel

namespace Mathproof.EvenTI.Reciprocal.Four

open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)

noncomputable section

/-- Independent finite batches fail jointly with the product of their event
fractions. The exponent is the literal number of independently sampled batches. -/
theorem independent_batch_fraction {V : Type*} [Fintype V] (P : V → Prop) (s : ℕ) :
    uniformFraction (Fin s → V) (fun x => ∀ i, P (x i)) = uniformFraction V P ^ s := by
  classical
  let e : {x : Fin s → V // ∀ i, P (x i)} ≃ (Fin s → {v : V // P v}) :=
    { toFun := fun x i => ⟨x.val i, x.property i⟩
      invFun := fun x => ⟨fun i => (x i).val, fun i => (x i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold uniformFraction
  rw [Nat.card_congr e, div_pow]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- A single successful batch suffices for the full coefficient family, so
failure of the assembled family pays the entire independently repeated cost. -/
theorem repeated_batch_bound {V : Type*} [Fintype V] (P : V → Prop) (s : ℕ)
    (F : (Fin s → V) → Prop) (ε : ℝ)
    (h : ∀ x, F x → ∀ i, P (x i))
    (hp : uniformFraction V P ≤ ε) :
    uniformFraction (Fin s → V) F ≤ ε ^ s := by
  have hP : 0 ≤ uniformFraction V P := by unfold uniformFraction; positivity
  apply (uniformFraction_le_of_imp h).trans
  rw [independent_batch_fraction]
  exact pow_le_pow_left₀ hP hp _

/-- A full rectangular coefficient pool has span at least the width of one
independent subbatch. -/
theorem deficient_span_repeated_bound {K V M A : Type*} [Field K]
    [Fintype V] [Fintype A] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (P : V → A → M) (s : ℕ) (ε : ℝ)
    (hp : uniformFraction V (fun v => ¬ LinearIndependent K (P v)) ≤ ε) :
    uniformFraction (Fin s → V) (fun x =>
      Module.finrank K (Submodule.span K (Set.range (fun j : Fin s × A => P (x j.1) j.2)))
        < Fintype.card A) ≤ ε ^ s := by
  apply repeated_batch_bound (fun v => ¬ LinearIndependent K (P v)) _ _ _ _ hp
  intro x hx i hi
  have hsub : Set.range (P (x i)) ⊆ Set.range (fun j : Fin s × A => P (x j.1) j.2) := by
    rintro _ ⟨j,rfl⟩
    exact ⟨(i,j),rfl⟩
  have h := Submodule.finrank_mono (Submodule.span_mono (R := K) hsub)
  have he := linearIndependent_iff_card_eq_finrank_span.mp hi
  change Fintype.card A = Module.finrank K (Submodule.span K (Set.range (P (x i)))) at he
  omega

#print axioms independent_batch_fraction
#print axioms repeated_batch_bound
#print axioms deficient_span_repeated_bound

end
end Mathproof.EvenTI.Reciprocal.Four