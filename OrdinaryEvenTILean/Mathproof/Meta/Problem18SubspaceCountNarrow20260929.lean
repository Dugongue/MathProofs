import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic

/-! Exact proof lift from FiniteFieldOrthogonalUnitaryTI.lean lines 6717–6787,
with only import and namespace changes. -/

namespace Mathproof.Problem18SubspaceCountNarrow20260929

variable {K : Type*} [Field K]
/-- Independent tuples are partitioned by their spans. -/
def independentSpan {V : Type*} [AddCommGroup V] [Module K V] (k : ℕ) :
    {v : Fin k → V // LinearIndependent K v} →
      {W : Submodule K V // Module.finrank K W = k} :=
  fun v => ⟨Submodule.span K (Set.range v.val), by
    rw [finrank_span_eq_card v.property, Fintype.card_fin]⟩

/-- A span fiber is exactly the independent tuples in that subspace. -/
noncomputable def independentSpanFiberEquiv {V : Type*} [AddCommGroup V]
    [Module K V] [Module.Finite K V] (k : ℕ)
    (W : {W : Submodule K V // Module.finrank K W = k}) :
    {v : {v : Fin k → V // LinearIndependent K v} // independentSpan k v = W} ≃
      {v : Fin k → W.val // LinearIndependent K v} := by
  let e : {v : Fin k → W.val // LinearIndependent K (Subtype.val ∘ v)} ≃
      {v : Fin k → W.val // LinearIndependent K v} :=
    Equiv.subtypeEquivRight fun v => ⟨fun h => LinearIndependent.of_comp W.val.subtype h,
      fun h => h.map' W.val.subtype (Submodule.ker_subtype W.val)⟩
  refine (Equiv.ofBijective ?_ ⟨?_, ?_⟩).trans e
  · rintro ⟨⟨v, hv⟩, hvW⟩
    have heq : Submodule.span K (Set.range v) = W.val := congrArg Subtype.val hvW
    refine ⟨fun i => ⟨v i, ?_⟩, hv⟩
    rw [← heq]
    exact Submodule.subset_span (Set.mem_range_self i)
  · rintro ⟨⟨v, hv⟩, hvW⟩ ⟨⟨w, hw⟩, hwW⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    funext i
    exact congrArg Subtype.val (congrFun heq i)
  · rintro ⟨w, hw⟩
    let v : Fin k → V := Subtype.val ∘ w
    have hv : LinearIndependent K v := hw
    have hs : Submodule.span K (Set.range v) = W.val := by
      have hl : Submodule.span K (Set.range v) ≤ W.val := by
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        exact (w i).property
      apply Submodule.eq_of_le_of_finrank_eq hl
      rw [finrank_span_eq_card hv, Fintype.card_fin, W.property]
    refine ⟨⟨⟨v, hv⟩, Subtype.ext hs⟩, ?_⟩
    apply Subtype.ext
    funext i
    rfl

/-- Exact basis multiplicity in every span fiber. -/
theorem independentSpan_fiber_card {V : Type*} [AddCommGroup V]
    [Module K V] [Module.Finite K V] [Fintype K] (k : ℕ)
    (W : {W : Submodule K V // Module.finrank K W = k}) :
    Nat.card {v : {v : Fin k → V // LinearIndependent K v} // independentSpan k v = W} =
      ∏ a : Fin k, (Fintype.card K ^ k - Fintype.card K ^ a.val) := by
  have : Finite V := Module.finite_of_finite (R := K) (M := V)
  rw [Nat.card_congr (independentSpanFiberEquiv k W)]
  simpa only [W.property] using
    (card_linearIndependent (K := K) (V := W.val) (by rw [W.property]))

/-- Exact finite Grassmannian count, without introducing q-binomial notation. -/
theorem subspace_card_mul_bases [Fintype K] {n k : ℕ} (hk : k ≤ n) :
    Nat.card {W : Submodule K (Fin n → K) // Module.finrank K W = k} *
      (∏ a : Fin k, (Fintype.card K ^ k - Fintype.card K ^ a.val)) =
      ∏ a : Fin k, (Fintype.card K ^ n - Fintype.card K ^ a.val) := by
  classical
  let f := independentSpan (K := K) (V := Fin n → K) k
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  have hf (W : {W : Submodule K (Fin n → K) // Module.finrank K W = k}) :=
    independentSpan_fiber_card k W
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma] at he hf
  dsimp only [f] at he
  simp_rw [hf] at he
  have hc := card_linearIndependent (K := K) (V := Fin n → K)
    (show k ≤ Module.finrank K (Fin n → K) by simpa using hk)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Nat.card_eq_fintype_card] at hc
  simpa [f, Finset.sum_const] using he.trans hc

end Mathproof.Problem18SubspaceCountNarrow20260929