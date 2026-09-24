/- For every 0 <= lam <= 1/2, constructs five normalized two-qubit states
forming an equiangular tight frame, all with reduced-state eigenvalues lam and
1-lam (certified by the exact characteristic polynomial). -/
import Mathlib
open scoped ComplexConjugate
open Complex

namespace FiveFrame

theorem primitive_star (w : ℂ) (hw : IsPrimitiveRoot w 5) : star w = w^4 := by
  have hnorm : ‖w‖ = 1 := hw.norm'_eq_one (by norm_num)
  change (starRingEnd ℂ) w = w^4
  rw [← Complex.inv_eq_conj hnorm]
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using hw.pow_eq_one

theorem primitive_inner_pow (w : ℂ) (hw : IsPrimitiveRoot w 5) (r s : ℕ) :
    star (w^r) * w^s = w^((4*r+s)%5) := by
  rw [star_pow, primitive_star w hw, ← pow_mul, ← pow_add]
  simpa only [hw.eq_orderOf] using (pow_mod_orderOf w (4*r+s)).symm

theorem fifth_sum (w : ℂ) (hw : IsPrimitiveRoot w 5) :
    1+w+w^2+w^3+w^4 = 0 := by
  have h := hw.geom_sum_eq_zero (by norm_num : 1 < 5)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] using h

theorem fourier_orthogonal (w : ℂ) (hw : IsPrimitiveRoot w 5) (r s : Fin 5) :
    (∑ j : Fin 5, star (w^(r.val*j.val)) * w^(s.val*j.val)) =
      if r = s then 5 else 0 := by
  simp only [primitive_inner_pow w hw]
  have h := fifth_sum w hw
  fin_cases r <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ] <;> linear_combination h

theorem fifth_root_exists : ∃ w : ℂ, IsPrimitiveRoot w 5 := by
  exact ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩

theorem fourier_truncated_gram (w : ℂ) (hw : IsPrimitiveRoot w 5) (j k : Fin 5)
    (hjk : j ≠ k) :
    (∑ r : Fin 4, star (w^(r.val*j.val)) * w^(r.val*k.val)) =
      -(star (w^(4*j.val)) * w^(4*k.val)) := by
  have h := fourier_orthogonal w hw j k
  rw [if_neg hjk, Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last] at h
  simp_rw [Nat.mul_comm j.val, Nat.mul_comm k.val] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fifth_unit (w : ℂ) (hw : IsPrimitiveRoot w 5) (n : ℕ) :
    star (w^n) * w^n = 1 := by
  rw [primitive_inner_pow w hw]
  have : (4*n+n)%5 = 0 := by omega
  rw [this, pow_zero]

theorem fourier_truncated_gram_norm (w : ℂ) (hw : IsPrimitiveRoot w 5)
    (j k : Fin 5) (hjk : j ≠ k) :
    Complex.normSq ((∑ r : Fin 4, star (w^(r.val*j.val)) * w^(r.val*k.val))/4) = 1/16 := by
  rw [fourier_truncated_gram w hw j k hjk]
  have hn := hw.norm'_eq_one (by norm_num)
  norm_num [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_conj, Complex.star_def, map_pow, Complex.normSq_eq_norm_sq, norm_pow, hn]

theorem scaled_inner_factor (a b x y : ℂ) :
    star (a*x/2) * (b*y/2) = (star a*b)/4 * (star x*y) := by
  simp only [star_div₀, star_mul, star_ofNat]
  ring

theorem weighted_fourier_tight (w : ℂ) (hw : IsPrimitiveRoot w 5)
    (d : Fin 4 → ℂ) (hd : ∀ i, star (d i)*d i = 1) (r s : Fin 4) :
    (∑ j : Fin 5, star (d r*w^(r.val*j.val)/2) * (d s*w^(s.val*j.val)/2)) =
      if r = s then (5:ℂ)/4 else 0 := by
  simp_rw [scaled_inner_factor]
  rw [← Finset.mul_sum]
  have ho := fourier_orthogonal w hw (r.castLE (by decide : 4 ≤ 5))
    (s.castLE (by decide : 4 ≤ 5))
  simp only [Fin.val_castLE, Fin.castLE_inj] at ho
  rw [ho]
  by_cases h : r = s
  · subst s
    simp only [if_pos rfl, hd]
    norm_num
  · simp [h]

theorem weighted_fourier_gram (w : ℂ) (d : Fin 4 → ℂ)
    (hd : ∀ i, star (d i)*d i = 1) (j k : Fin 5) :
    (∑ i : Fin 4, star (d i*w^(i.val*j.val)/2) * (d i*w^(i.val*k.val)/2)) =
      (∑ i : Fin 4, star (w^(i.val*j.val)) * w^(i.val*k.val))/4 := by
  simp_rw [scaled_inner_factor, hd]
  rw [← Finset.mul_sum]
  ring

theorem weighted_fourier_norm (w : ℂ) (hw : IsPrimitiveRoot w 5)
    (d : Fin 4 → ℂ) (hd : ∀ i, star (d i)*d i = 1) (j : Fin 5) :
    (∑ i : Fin 4, star (d i*w^(i.val*j.val)/2) * (d i*w^(i.val*j.val)/2)) = 1 := by
  rw [weighted_fourier_gram w d hd j j]
  simp_rw [fifth_unit w hw]
  norm_num

theorem weighted_fourier_equiangular (w : ℂ) (hw : IsPrimitiveRoot w 5)
    (d : Fin 4 → ℂ) (hd : ∀ i, star (d i)*d i = 1) (j k : Fin 5) (hjk : j ≠ k) :
    Complex.normSq (∑ i : Fin 4,
      star (d i*w^(i.val*j.val)/2) * (d i*w^(i.val*k.val)/2)) = 1/16 := by
  rw [weighted_fourier_gram w d hd j k]
  exact fourier_truncated_gram_norm w hw j k hjk

end FiveFrame


theorem isoentangled_phase_certificate (t s : ℝ) (h : t^2 + s^2 = 1) : Complex.normSq (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ)) = 1 ∧ Complex.normSq (1 + (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ))) = 4*t^2 := by
  exact (by
    have phase_unit_norm (t s : ℝ) (h : t^2 + s^2 = 1) : Complex.normSq (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ)) = 1 := by
      exact (by
        rw [mul_comm Complex.I, Complex.normSq_add_mul_I]
        calc
          (2 * t ^ 2 - 1) ^ 2 + (2 * t * s) ^ 2 = 4 * t ^ 2 * (t ^ 2 + s ^ 2 - 1) + 1 := by ring
          _ = 1 := by rw [h]; ring
      )
    have phase_plus_norm (t s : ℝ) (h : t^2 + s^2 = 1) : Complex.normSq (1 + (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ))) = 4*t^2 := by
      exact (by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
        calc
          _ = 4 * t ^ 2 * (t ^ 2 + s ^ 2) := by ring
          _ = 4 * t ^ 2 := by rw [h]; ring
      )
    exact ⟨phase_unit_norm t s h, phase_plus_norm t s h⟩
  )

theorem phase_for_schmidt
    (phase_identities : ∀ (t s : ℝ), t^2 + s^2 = 1 →
      Complex.normSq (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ)) = 1 ∧
      Complex.normSq (1 + (((2*t^2-1 : ℝ) : ℂ) + Complex.I * ((2*t*s : ℝ) : ℂ))) = 4*t^2)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1/2) :
    ∃ z : ℂ, Complex.normSq z = 1 ∧
      Complex.normSq (1 + z) = 4 * (1 - 2*lam)^2 := by
  let t : ℝ := 1 - 2*lam
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have ht : 0 ≤ 1 - t^2 := by nlinarith
  have hs : t^2 + (Real.sqrt (1-t^2))^2 = 1 := by
    rw [Real.sq_sqrt ht]
    ring
  exact ⟨_, phase_identities t (Real.sqrt (1-t^2)) hs⟩

namespace IsoentangledFrame

theorem mul_star_eq_one_of_normSq {z : ℂ} (hz : Complex.normSq z = 1) :
    z * star z = 1 := by
  simpa only [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]

theorem sum_star_of_normSq (z : ℂ) (lam : ℝ)
    (hz : Complex.normSq z = 1)
    (hs : Complex.normSq (1 + z) = 4 * (1 - 2 * lam)^2) :
    z + star z = 2 - 16 * (lam : ℂ) * (1 - (lam : ℂ)) := by
  have hu := mul_star_eq_one_of_normSq hz
  have hn := congrArg (fun x : ℝ => (x : ℂ)) hs
  push_cast at hn
  rw [Complex.normSq_eq_conj_mul_self] at hn
  simp only [map_add, map_one] at hn
  change (1 + star z) * (1 + z) = 4 * (1 - 2 * (lam : ℂ))^2 at hn
  linear_combination hn - hu

#print axioms sum_star_of_normSq

end IsoentangledFrame

open scoped BigOperators

noncomputable def isoentangledSeed (z a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2,a/2; b/2,z*a*b/2]

namespace FiveFrame

def pairIndex (a b : Fin 2) : Fin 4 := ⟨2*a.val+b.val, by omega⟩

theorem sum_pairIndex (f : Fin 4 → ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, f (pairIndex a b)) = ∑ i : Fin 4, f i := by
  simp [pairIndex, Fin.sum_univ_succ]
  ring

noncomputable def weights (z : ℂ) : Fin 4 → ℂ := ![1,1,1,z]

theorem weights_unit (z : ℂ) (hz : Complex.normSq z = 1) :
    ∀ i, star (weights z i) * weights z i = 1 := by
  intro i
  fin_cases i <;> simp [weights]
  simpa [mul_comm] using IsoentangledFrame.mul_star_eq_one_of_normSq hz

noncomputable def matrixFrame (w z : ℂ) (j : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => weights z (pairIndex a b) * w^((pairIndex a b).val*j.val)/2

theorem matrixFrame_eq_seed (w z : ℂ) (j : Fin 5) :
    matrixFrame w z j = isoentangledSeed z (w^j.val) (w^(2*j.val)) := by
  have hp : w^(3*j.val) = w^j.val * w^(2*j.val) := by
    rw [← pow_add]
    congr 1
    omega
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrixFrame, isoentangledSeed, weights, pairIndex, hp, mul_assoc]

theorem matrixFrame_norm (w z : ℂ) (hw : IsPrimitiveRoot w 5)
    (hz : Complex.normSq z = 1) (j : Fin 5) :
    (∑ a, ∑ b, star (matrixFrame w z j a b) * matrixFrame w z j a b) = 1 := by
  unfold matrixFrame
  rw [sum_pairIndex (fun i => star (weights z i * w^(i.val*j.val)/2) *
    (weights z i * w^(i.val*j.val)/2))]
  exact weighted_fourier_norm w hw (weights z) (weights_unit z hz) j

theorem matrixFrame_equiangular (w z : ℂ) (hw : IsPrimitiveRoot w 5)
    (hz : Complex.normSq z = 1) (j k : Fin 5) (hjk : j ≠ k) :
    Complex.normSq (∑ a, ∑ b,
      star (matrixFrame w z j a b) * matrixFrame w z k a b) = 1/16 := by
  unfold matrixFrame
  rw [sum_pairIndex (fun i => star (weights z i * w^(i.val*j.val)/2) *
    (weights z i * w^(i.val*k.val)/2))]
  exact weighted_fourier_equiangular w hw (weights z) (weights_unit z hz) j k hjk

theorem matrixFrame_tight (w z : ℂ) (hw : IsPrimitiveRoot w 5)
    (hz : Complex.normSq z = 1) (a b c d : Fin 2) :
    (∑ j, matrixFrame w z j a b * star (matrixFrame w z j c d)) =
      if a = c ∧ b = d then (5:ℂ)/4 else 0 := by
  have h := weighted_fourier_tight w hw (weights z) (weights_unit z hz)
    (pairIndex c d) (pairIndex a b)
  have hi : pairIndex c d = pairIndex a b ↔ a = c ∧ b = d := by
    simp only [pairIndex, Fin.mk.injEq]
    constructor
    · intro h
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl,rfl⟩
      rfl
  simpa only [matrixFrame, mul_comm, hi] using h

end FiveFrame

theorem five_isoentangled_equiangular_tight_frame_of_spectrum
    (spectrum_leaf : ∀ (z a b : ℂ) (lam : ℝ),
      a * star a = 1 → b * star b = 1 → z * star z = 1 →
      z + star z = 2 - 16 * (lam : ℂ) * (1 - (lam : ℂ)) →
      (isoentangledSeed z a b * (isoentangledSeed z a b).conjTranspose).charpoly =
        (Polynomial.X - Polynomial.C (lam : ℂ)) *
        (Polynomial.X - Polynomial.C (1 - (lam : ℂ))))
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1/2) :
    ∃ v : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ j, (∑ a, ∑ b, star (v j a b) * v j a b) = 1) ∧
      (∀ j k, j ≠ k → Complex.normSq (∑ a, ∑ b,
        star (v j a b) * v k a b) = 1/16) ∧
      (∀ a b c d, (∑ j, v j a b * star (v j c d)) =
        if a = c ∧ b = d then (5:ℂ)/4 else 0) ∧
      (∀ j, ((v j) * (v j).conjTranspose).charpoly =
        (Polynomial.X - Polynomial.C (lam : ℂ)) *
        (Polynomial.X - Polynomial.C (1 - (lam : ℂ)))) := by
  obtain ⟨z,hz,hs⟩ := phase_for_schmidt isoentangled_phase_certificate lam h0 h1
  obtain ⟨w,hw⟩ := FiveFrame.fifth_root_exists
  refine ⟨FiveFrame.matrixFrame w z, FiveFrame.matrixFrame_norm w z hw hz,
    FiveFrame.matrixFrame_equiangular w z hw hz, FiveFrame.matrixFrame_tight w z hw hz, ?_⟩
  intro j
  rw [FiveFrame.matrixFrame_eq_seed]
  apply spectrum_leaf
  · simpa [mul_comm] using FiveFrame.fifth_unit w hw j.val
  · simpa [mul_comm] using FiveFrame.fifth_unit w hw (2*j.val)
  · exact IsoentangledFrame.mul_star_eq_one_of_normSq hz
  · exact IsoentangledFrame.sum_star_of_normSq z lam hz hs

#print axioms five_isoentangled_equiangular_tight_frame_of_spectrum

open Polynomial

theorem isoentangled_seed_reduced_charpoly (z a b : ℂ) (lam : ℝ) (ha : a * star a = 1) (hb : b * star b = 1) (hz : z * star z = 1) (hs : z + star z = 2 - 16 * (lam : ℂ) * (1 - (lam : ℂ))) : let A := isoentangledSeed z a b; (A * A.conjTranspose).charpoly = (X - C (lam : ℂ)) * (X - C (1 - (lam : ℂ))) := by
  exact (by
    change (isoentangledSeed z a b * (isoentangledSeed z a b).conjTranspose).charpoly = _
    have htr : (isoentangledSeed z a b * (isoentangledSeed z a b).conjTranspose).trace = 1 := by
      calc
        _ = (1 + a * star a + b * star b + (z * star z) * (a * star a) * (b * star b)) / 4 := by
          simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
          simp [isoentangledSeed, star_mul, star_div₀] <;> ring
        _ = 1 := by rw [ha, hb, hz]; norm_num
    have hdet : (isoentangledSeed z a b * (isoentangledSeed z a b).conjTranspose).det = (lam : ℂ) * (1 - (lam : ℂ)) := by
      calc
        _ = (a * star a) * (b * star b) * (z * star z - (z + star z) + 1) / 16 := by
          rw [Matrix.det_mul, Matrix.det_conjTranspose]
          simp [isoentangledSeed, Matrix.det_fin_two, star_mul, star_sub, star_div₀] <;> ring
        _ = (lam : ℂ) * (1 - (lam : ℂ)) := by
          rw [ha, hb, hz, hs]
          ring
    rw [Matrix.charpoly_fin_two, htr, hdet]
    simp only [map_mul, map_sub, map_one]
    ring
  )

theorem five_isoentangled_equiangular_tight_frame (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1/2) : ∃ v : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ, (∀ j, (∑ a, ∑ b, star (v j a b) * v j a b) = 1) ∧ (∀ j k, j ≠ k → Complex.normSq (∑ a, ∑ b, star (v j a b) * v k a b) = 1/16) ∧ (∀ a b c d, (∑ j, v j a b * star (v j c d)) = if a = c ∧ b = d then (5:ℂ)/4 else 0) ∧ (∀ j, ((v j) * (v j).conjTranspose).charpoly = (Polynomial.X - Polynomial.C (lam : ℂ)) * (Polynomial.X - Polynomial.C (1 - (lam : ℂ)))) := by
  exact five_isoentangled_equiangular_tight_frame_of_spectrum
    isoentangled_seed_reduced_charpoly lam h0 h1

#print axioms five_isoentangled_equiangular_tight_frame
