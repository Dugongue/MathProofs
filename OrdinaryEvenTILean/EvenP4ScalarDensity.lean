import EvenNextScalarDensity
import EvenPrimaryEnvelope
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped BigOperators Classical

namespace EvenTI.Action

open EvenTI.Primary

noncomputable section

variable {K : Type*} [Field K] {d n : ℕ}

/-- The stabilizer gate on a raw source tensor. -/
def scalarAccepted (T : Tensor K d n) : Prop :=
  T ≠ 0 ∧ ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u

private theorem exists_nonscalar_unit (hn : 2 ≤ n) :
    ∃ m : (Matrix (Fin n) (Fin n) K)ˣ, ∀ u : Kˣ, m ≠ scalar u := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let s := Equiv.swap i j
  let m : (Matrix (Fin n) (Fin n) K)ˣ :=
    ⟨s.permMatrix K, (s⁻¹).permMatrix K,
      by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
      by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩
  refine ⟨m, fun u h => ?_⟩
  have he := congrArg (fun a : (Matrix (Fin n) (Fin n) K)ˣ => a.val i j) h
  simp [m, s, Equiv.Perm.permMatrix, PEquiv.toMatrix, scalar_val, Matrix.one_apply, hij] at he

/-- A zero tensor already lies in the nonscalar exception for this range. -/
theorem scalar_only_ne_zero (hn : 2 ≤ n) (hd : 0 < d) {T : Tensor K d n}
    (h : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u) : T ≠ 0 := by
  rintro rfl
  obtain ⟨m, hm⟩ := exists_nonscalar_unit (K := K) hn
  let a : Changes K d n := fun _ => m
  obtain ⟨u, hu⟩ := h a (by simp [act])
  let i : Fin d := ⟨0, hd⟩
  exact hm (u i) (congrFun hu i)

/-- The raw scalar gate loses at most one exponentially small event,
uniformly over the tensor order. -/
theorem scalar_bad_le [Fintype K] (hn : 5 ≤ n) (hd : 4 ≤ d) :
    event (fun T : Tensor K d n => ¬ scalarAccepted T) ≤
      ((Fintype.card K : ℝ)^(n^2))⁻¹ := by
  cases d with
  | zero => omega
  | succ l =>
    have he : (fun T : Tensor K (l+1) n => ¬ scalarAccepted T) =
        fun T => ¬ (∀ a : Changes K (l+1) n, act a T = T → ∃ u, a = scalars u) := by
      funext T
      apply propext
      constructor
      · intro h hc
        exact h ⟨scalar_only_ne_zero (by omega) (by omega) hc, hc⟩
      · exact fun h hc => h hc.2
    have hb := scalar_only_failure_card (K := K) n l hn (by omega)
    simp only [he, event_eq_card, Nat.card_eq_fintype_card, Fintype.card_subtype, ← one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simp only [one_mul]
    exact_mod_cast hb

/-- The gate certifies the same product-one scalar stabilizer used for counting. -/
theorem scalarAccepted_iff_product_one_stabilizer (T : Tensor K d n) :
    scalarAccepted T ↔ T ≠ 0 ∧ ∀ a : Changes K d n,
      (act a T = T ↔ ∃ u : Fin d → Kˣ, a = scalars u ∧ (∏ i, u i) = 1) := by
  constructor
  · rintro ⟨hT, h⟩
    refine ⟨hT, fun a => ⟨?_, ?_⟩⟩
    · intro ha
      obtain ⟨u, rfl⟩ := h a ha
      exact ⟨u, rfl, (scalars_fix_iff hT u).1 ha⟩
    · rintro ⟨u, rfl, hp⟩
      exact (scalars_fix_iff hT u).2 hp
  · rintro ⟨hT, h⟩
    refine ⟨hT, fun a ha => ?_⟩
    obtain ⟨u, hu, _⟩ := (h a).1 ha
    exact ⟨u, hu⟩

#print axioms scalar_only_ne_zero
#print axioms scalar_bad_le
#print axioms scalarAccepted_iff_product_one_stabilizer

end
end EvenTI.Action
