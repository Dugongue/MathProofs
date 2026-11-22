import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

namespace BlindReturn

open Polynomial.Chebyshev Real

theorem extremal_iff_dvd {d n : ℕ} (hd : d ≠ 0) :
    |(T ℝ n).eval (cos (π / d))| = 1 ↔ d ∣ n := by
  rw [T_real_cos, Int.cast_natCast, abs_cos_eq_one_iff]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  constructor
  · rintro ⟨k, hk⟩
    have eqn : (k : ℝ) * d = n := by
      field_simp [hd'] at hk
      exact hk
    apply Int.natCast_dvd_natCast.mp
    refine ⟨k, ?_⟩
    exact_mod_cast (show (n : ℝ) = d * k by linarith only [eqn])
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp [hd'] <;> ring⟩

theorem return_times {X : Type*} (f : X → X) (x : X)
    (hx : Function.minimalPeriod f x ≠ 0) (n : ℕ) :
    Function.IsPeriodicPt f n x ↔
      |(T ℝ n).eval (cos (π / Function.minimalPeriod f x))| = 1 := by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, extremal_iff_dvd hx]

end BlindReturn
