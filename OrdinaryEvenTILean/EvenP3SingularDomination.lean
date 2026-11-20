import EvenLiveSingularEstimate
import Mathproof.Meta.Problem18RankDensity20260929

namespace Mathproof.EvenOrdinaryTISingular
open Module
open Mathproof.Problem18RankDensity20260929

noncomputable section

/-- Conditioning on a finite event of probability at least a quarter
increases the probability of every observation by a factor of at most four. -/
theorem uniformFraction_condition_le_four {A : Type*} [Fintype A] [Nonempty A]
    (P G : A → Prop)
    (hG : (Nat.card A : ℝ) / 4 ≤ Nat.card {x : A // G x}) :
    uniformFraction {x : A // G x} (fun x => P x.val) ≤ 4 * uniformFraction A P := by
  classical
  have hA : 0 < (Nat.card A : ℝ) := by exact_mod_cast (Nat.card_pos (α := A))
  have hG' : 0 < (Nat.card {x : A // G x} : ℝ) := by linarith
  let e : {x : {x : A // G x} // P x.val} ↪ {x : A // P x} :=
    ⟨fun x => ⟨x.val.val, x.property⟩, fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun y : {y : A // P y} => y.val) h))⟩
  have hP : (Nat.card {x : {x : A // G x} // P x.val} : ℝ) ≤
      Nat.card {x : A // P x} := by
    exact_mod_cast Nat.card_le_card_of_injective e e.injective
  unfold uniformFraction
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hG' hA).2
  calc
    _ ≤ (Nat.card {x : A // P x} : ℝ) * Nat.card A :=
      mul_le_mul_of_nonneg_right hP hA.le
    _ ≤ (Nat.card {x : A // P x} : ℝ) * (4 * Nat.card {x : A // G x}) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

variable {K V W : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W]

theorem independent_fraction_ge_quarter {b : ℕ} (hb : b ≤ finrank K V) :
    (Nat.card (Fin b → V) : ℝ) / 4 ≤ Nat.card (Independent K V b) := by
  have hi := card_linearIndependent (K := K) (V := V) hb
  have hj := fullRowRank_card (K := K) hb
  have he : Nat.card (Independent K V b) =
      Nat.card {M : Matrix (Fin b) (Fin (finrank K V)) K // M.rank = b} := hi.trans hj.symm
  let e : (Fin b → V) ≃ Matrix (Fin b) (Fin (finrank K V)) K :=
    Equiv.piCongrRight (fun _ => (Module.finBasis K V).equivFun.toEquiv)
  have hc := Nat.card_congr e
  rw [hc, he]
  have hPos : 0 < (Nat.card (Matrix (Fin b) (Fin (finrank K V)) K) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := Matrix (Fin b) (Fin (finrank K V)) K))
  have h := (le_div_iff₀ hPos).mp (fullRowRank_density_ge_quarter (K := K) hb)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

theorem uniformFraction_independent_observation_le_four {b : ℕ}
    (hb : b ≤ finrank K V) (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (P : (Fin b → W) → Prop) :
    uniformFraction (Independent K V b) (fun x => P (fun i => f (x.val i))) ≤
      4 * uniformFraction (Fin b → W) P := by
  let g : (Fin b → V) →ₗ[K] (Fin b → W) := LinearMap.pi fun i => f.comp (LinearMap.proj i)
  have hg : Function.Surjective g := by
    intro x
    exact ⟨fun i => Function.surjInv hf (x i), funext fun i => Function.surjInv_eq hf (x i)⟩
  rw [← uniformFraction_linear_surjective g hg P]
  exact uniformFraction_condition_le_four (fun x => P (g x))
    (fun x : Fin b → V => LinearIndependent K x) (independent_fraction_ge_quarter (K := K) hb)

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_independent_observation_le_four
