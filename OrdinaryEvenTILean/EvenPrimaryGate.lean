import EvenPrimaryEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Classical

namespace EvenTI.Primary

noncomputable section

theorem event_pow_gate_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℕ) (B : ℝ) (hB : ∀ i, mean (fun x => (X i x : ℝ)) ≤ B)
    (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    event (fun x => n^(Fintype.card ι) < q^(∑ i, X i x)) ≤
      (B * Real.log q) / Real.log n := by
  have hq' : (1:ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hqlog := Real.log_pos hq'
  have hnlog := Real.log_pos hn'
  let t := Real.log n / Real.log q
  have ht : 0 < t := div_pos hnlog hqlog
  have heq (x : Ω) :
      n^(Fintype.card ι) < q^(∑ i, X i x) ↔
        (Fintype.card ι : ℝ) * t < ∑ i, (X i x : ℝ) := by
    have hreal :
        n^(Fintype.card ι) < q^(∑ i, X i x) ↔
          (n:ℝ)^(Fintype.card ι) < (q:ℝ)^(∑ i, X i x) := by exact_mod_cast Iff.rfl
    rw [hreal, ← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [Nat.cast_sum, show (Fintype.card ι : ℝ) * t =
        ((Fintype.card ι : ℝ) * Real.log n) / Real.log q by rw [mul_div_assoc]]
    exact (div_lt_iff₀ hqlog).symm
  rw [show (fun x => n^(Fintype.card ι) < q^(∑ i, X i x)) =
      (fun x => (Fintype.card ι : ℝ)*t < ∑ i, (X i x : ℝ)) from funext (fun x => propext (heq x))]
  have h := event_sum_budget_le (fun i x => (X i x : ℝ)) (fun _ _ => by positivity) B t ht hB
  rwa [show B / t = (B * Real.log q) / Real.log n by
    dsimp [t]
    rw [div_div_eq_mul_div]] at h

#print axioms event_pow_gate_le

end
end EvenTI.Primary
