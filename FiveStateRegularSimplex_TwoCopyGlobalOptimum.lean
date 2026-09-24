import Mathlib

/-!
# Exact global discrimination optimum for two copies of a five-state regular simplex

For five complex unit vectors X_j in any finite-dimensional ambient space,
assume their pairwise inner products are -1/4 for distinct labels. For two
identical copies X_j tensor X_j with uniform prior, the optimal success over
all global POVMs is exactly

  (13 + 4 sqrt(3))/20 = 13/20 + sqrt(3)/5.

The theorem constructs a positive complete POVM attaining this value and
proves a matching upper bound for every positive complete POVM. Its hypotheses
specify a regular simplex in a fixed phase convention, not arbitrary five states.
The doubled Gram matrix is (15 I + J)/16; an explicit square-root factorization
supplies both the attaining measurement and a positive-semidefinite dual witness.

Relation to the literature: Section VII of Amanda Wei, Gabriele Cobucci and
Armin Tavakoli, "Nonprojective Bell-state measurements", Physical Review A 110,
042206 (2024), DOI: 10.1103/PhysRevA.110.042206, reports a numerical two-copy
GLOBAL optimum of approximately 0.9964 from a semidefinite program. The formula
above gives the corresponding exact value in the regular-simplex formulation.
This is an exact certification, not an increase in that numerical optimum.
It does not determine the separate local, one-way LOCC, or PPT optimum.

A normalized five-state tight frame spanning dimension four can be rephased
into this Gram convention: I-(4/5)G is a rank-one projection uu*, with
|u_j|^2=1/5; phases sqrt(5)u_j make off-diagonal entries -1/4. Individual state
phases leave discrimination probabilities unchanged. This paragraph explains
the application to the paper; the general rephasing bridge is not formalized
here. The formal theorem below assumes the stated Gram entries directly.

This is an elementary matrix certificate of established square-root-measurement
reasoning, not a claim of novelty for the general theory.
Main theorem: doubled_five_simplex_global_optimum.
-/

open scoped BigOperators ComplexOrder
namespace GramFactor

def ones (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun _ _ => 1
noncomputable def hMatrix (N : ℕ) (s t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (s : ℂ) • 1 + (t : ℂ) • ones N

theorem hMatrix_mul (N : ℕ) (s t u v : ℝ) :
    hMatrix N s t * hMatrix N u v = hMatrix N (s*u) (s*v+t*u+N*t*v) := by
  ext i j
  simp only [hMatrix, ones, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, mul_one, add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  simp
  split_ifs <;> push_cast <;> ring

theorem hMatrix_zero (N : ℕ) : hMatrix N 1 0 = 1 := by
  simp [hMatrix]

theorem hMatrix_hermitian (N : ℕ) (s t : ℝ) :
    (hMatrix N s t).conjTranspose = hMatrix N s t := by
  ext i j
  simp [hMatrix, ones, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  split_ifs <;> simp

theorem hMatrix_inverse (N : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    hMatrix N s t * hMatrix N (1/s) (-t/(s*(s+N*t))) = 1 ∧
    hMatrix N (1/s) (-t/(s*(s+N*t))) * hMatrix N s t = 1 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hd0 : s + N*t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs (mul_nonneg (Nat.cast_nonneg N) ht))
  constructor <;> rw [hMatrix_mul]
  · have h1 : s*(1/s)=1 := by field_simp
    have h2 : s*(-t/(s*(s+N*t)))+t*(1/s)+N*t*(-t/(s*(s+N*t)))=0 := by
      field_simp
      <;> ring
    rw [h1,h2,hMatrix_zero]
  · have h1 : (1/s)*s=1 := by field_simp
    have h2 : (1/s)*t+(-t/(s*(s+N*t)))*s+N*(-t/(s*(s+N*t)))*t=0 := by
      field_simp
      <;> ring
    rw [h1,h2,hMatrix_zero]

theorem factor_of_inverse {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}
    (Ψ : Matrix α (Fin N) ℂ) (H K : Matrix (Fin N) (Fin N) ℂ)
    (hGram : Ψ.conjTranspose * Ψ = H * H)
    (hK : K.conjTranspose = K) (hHK : H*K=1) (hKH : K*H=1) :
    ∃ Q : Matrix α (Fin N) ℂ, Q.conjTranspose * Q = 1 ∧ Q*H=Ψ := by
  refine ⟨Ψ*K, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hK]
    calc
      K * Ψ.conjTranspose * (Ψ*K) = K*(Ψ.conjTranspose*Ψ)*K := by simp [Matrix.mul_assoc]
      _ = K*(H*H)*K := by rw [hGram]
      _ = (K*H)*(H*K) := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hKH,hHK]; simp
  · rw [Matrix.mul_assoc,hKH,Matrix.mul_one]

theorem factor_hMatrix {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}
    (Ψ : Matrix α (Fin N) ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t)
    (hGram : Ψ.conjTranspose * Ψ = hMatrix N s t * hMatrix N s t) :
    ∃ Q : Matrix α (Fin N) ℂ, Q.conjTranspose * Q = 1 ∧ Q*hMatrix N s t=Ψ := by
  have hi := hMatrix_inverse N s t hs ht
  exact factor_of_inverse Ψ _ _ hGram (hMatrix_hermitian N _ _) hi.1 hi.2

end GramFactor

open scoped BigOperators ComplexOrder
open Matrix
namespace GlobalPrimal

variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}

noncomputable def complement (Q : Matrix α (Fin N) ℂ) : Matrix α α ℂ :=
  1 - Q * Q.conjTranspose

noncomputable def measurement (Q : Matrix α (Fin N) ℂ) (j : Fin N) : Matrix α α ℂ :=
  Matrix.vecMulVec (fun a => Q a j) (star (fun a => Q a j)) +
    ((N : ℝ)⁻¹) • complement Q

theorem complement_psd (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1) :
    (complement Q).PosSemidef := by
  have hh : (complement Q).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self Q)
  have hp : complement Q * complement Q = complement Q := by
    have hP : (Q * Q.conjTranspose) * (Q * Q.conjTranspose) = Q * Q.conjTranspose := by
      calc
        _ = Q * (Q.conjTranspose * Q) * Q.conjTranspose := by simp [Matrix.mul_assoc]
        _ = _ := by rw [hQ]; simp
    simp only [complement, sub_mul, mul_sub, one_mul, mul_one, hP]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self (complement Q)
  rwa [hh.eq, hp] at h

theorem measurement_psd (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (j : Fin N) : (measurement Q j).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (fun a => Q a j)).add
    ((complement_psd Q hQ).smul (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹))

theorem measurement_complete (Q : Matrix α (Fin N) ℂ) (hN : 0 < N) :
    (∑ j, measurement Q j) = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext a b
  simp only [Matrix.sum_apply, measurement, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.smul_apply, Complex.real_smul, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (Q * Q.conjTranspose) a b + (N : ℂ) *
    ((((N : ℝ)⁻¹ : ℝ) : ℂ) * (complement Q) a b) = _
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, ← mul_assoc,
    mul_inv_cancel₀ hN0, one_mul]
  simp [complement]

theorem complement_mul (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (H : Matrix (Fin N) (Fin N) ℂ) : complement Q * (Q * H) = 0 := by
  have he : Q.conjTranspose * (Q * H) = H := by
    rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  simp [complement, Matrix.sub_mul, Matrix.mul_assoc, he]

theorem column_inner (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    star (fun a => Q a j) ⬝ᵥ (fun a => (Q * H) a j) = H j j := by
  have he := congrFun (congrFun (show Q.conjTranspose * (Q*H) = H by
    rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]) j) j
  exact he

theorem measurement_success (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (H : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (hdiag : ∀ j, H j j = (c : ℂ))
    (j : Fin N) :
    star (fun a => (Q*H) a j) ⬝ᵥ
      ((measurement Q j).mulVec (fun a => (Q*H) a j)) = ((c^2 : ℝ) : ℂ) := by
  have hinner := column_inner Q hQ H j
  rw [hdiag] at hinner
  have hinner' : star (fun a => (Q*H) a j) ⬝ᵥ (fun a => Q a j) = (c : ℂ) := by
    have he : (Q * H).conjTranspose * Q = H.conjTranspose := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]
    change ((Q * H).conjTranspose * Q) j j = (c : ℂ)
    rw [he]
    simp [Matrix.conjTranspose_apply, hdiag]
  have hz : (complement Q).mulVec (fun a => (Q*H) a j) = 0 := by
    ext a
    exact congrFun (congrFun (complement_mul Q hQ H) a) j
  simp only [measurement, Matrix.add_mulVec, Matrix.smul_mulVec, hz, smul_zero, add_zero,
    Matrix.vecMulVec_mulVec, hinner, dotProduct_smul, hinner']
  simp [pow_two]

theorem measurement_average (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (hN : 0 < N) (H : Matrix (Fin N) (Fin N) ℂ) (c : ℝ)
    (hdiag : ∀ j, H j j = (c : ℂ)) :
    (∑ j, star (fun a => (Q*H) a j) ⬝ᵥ
      ((measurement Q j).mulVec (fun a => (Q*H) a j))).re / (N : ℝ) = c^2 := by
  simp_rw [measurement_success Q hQ H c hdiag]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

end GlobalPrimal

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace GlobalOptimality

noncomputable def hMatrix (N : ℕ) (s t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then (s + t : ℝ) else (t : ℂ)

noncomputable def outer {α : Type*} (v : α → ℂ) : Matrix α α ℂ :=
  fun i j => v i * star (v j)

theorem trace_mul_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hC]
  have h := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  have he : (C * A * C.conjTranspose).trace = (A * (star C * C)).trace := by
    simp only [star_eq_conjTranspose]
    rw [mul_assoc, Matrix.trace_mul_comm C, mul_assoc]
  rw [he] at h
  exact (Complex.nonneg_iff.mp h).1

theorem canonical_gap (N : ℕ) (s t : ℝ) (j : Fin N) :
    (s + t : ℂ) • hMatrix N s t - outer (fun i => hMatrix N s t i j) =
      ((s * (s + t) : ℝ) : ℂ) • Matrix.diagonal (fun i => if i = j then 0 else 1) +
      ((s * t : ℝ) : ℂ) • outer (fun i => if i = j then 0 else 1) := by
  ext a b
  by_cases ha : a = j <;> by_cases hb : b = j <;> by_cases hab : a = b <;>
    simp_all [hMatrix, outer, Matrix.diagonal_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.conj_ofReal, Complex.ofReal_add, Complex.ofReal_mul] <;> ring

theorem canonical_gap_posSemidef (N : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (j : Fin N) :
    ((s + t : ℂ) • hMatrix N s t - outer (fun i => hMatrix N s t i j)).PosSemidef := by
  rw [canonical_gap]
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.smul
    · apply Matrix.PosSemidef.diagonal
      intro i
      change 0 ≤ (if i = j then (0 : ℂ) else 1)
      split_ifs <;> norm_num
    · exact_mod_cast (mul_nonneg hs (add_nonneg hs ht))
  · apply Matrix.PosSemidef.smul
    · exact Matrix.posSemidef_vecMulVec_self_star _
    · exact_mod_cast (mul_nonneg hs ht)

theorem outer_mulVec {α β : Type*} [Fintype β]
    (Q : Matrix α β ℂ) (v : β → ℂ) :
    outer (Q.mulVec v) = Q * outer v * Q.conjTranspose := by
  change Matrix.vecMulVec (Q.mulVec v) (star (Q.mulVec v)) =
    Q * Matrix.vecMulVec v (star v) * Q.conjTranspose
  simp [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem trace_outer {α : Type*} [Fintype α]
    (M : Matrix α α ℂ) (v : α → ℂ) :
    (M * outer v).trace = star v ⬝ᵥ M.mulVec v := by
  change (M * Matrix.vecMulVec v (star v)).trace = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem transported_gap {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (Q : Matrix α (Fin N) ℂ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (j : Fin N) :
    (((s+t : ℂ) • (Q * hMatrix N s t * Q.conjTranspose)) -
      outer (fun x => (Q * hMatrix N s t) x j)).PosSemidef := by
  have h := (canonical_gap_posSemidef N s t hs ht j).mul_mul_conjTranspose_same Q
  have he : outer (fun x => (Q * hMatrix N s t) x j) =
      Q * outer (fun i => hMatrix N s t i j) * Q.conjTranspose :=
    outer_mulVec Q (fun i => hMatrix N s t i j)
  rw [he]
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using h

theorem dual_trace {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1) (s t : ℝ) :
    (((s+t : ℂ) • (Q * hMatrix N s t * Q.conjTranspose)).trace).re =
      (N : ℝ) * (s+t)^2 := by
  rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hQ, one_mul]
  simp [Matrix.trace, hMatrix, smul_eq_mul, Complex.mul_re, pow_two]
  ring

theorem success_upper_bound {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (hN : 0 < N) (Q : Matrix α (Fin N) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (M : Fin N → Matrix α α ℂ) (hM : ∀ j, (M j).PosSemidef)
    (hsum : ∑ j, M j = 1) :
    ((∑ j, star (fun x => (Q * hMatrix N s t) x j) ⬝ᵥ
      (M j).mulVec (fun x => (Q * hMatrix N s t) x j)).re) / (N : ℝ) ≤ (s+t)^2 := by
  let Y := (s+t : ℂ) • (Q * hMatrix N s t * Q.conjTranspose)
  have hp (j : Fin N) :
      (star (fun x => (Q * hMatrix N s t) x j) ⬝ᵥ
        (M j).mulVec (fun x => (Q * hMatrix N s t) x j)).re ≤ (M j * Y).trace.re := by
    have h := trace_mul_nonneg (M j) (Y - outer (fun x => (Q * hMatrix N s t) x j))
      (hM j) (transported_gap N Q s t hs ht j)
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re, trace_outer] at h
    linarith
  have hall := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp j)
  have hy : (∑ j, (M j * Y).trace.re) = (N : ℝ) * (s+t)^2 := by
    calc
      _ = ((∑ j, M j) * Y).trace.re := by simp [Matrix.sum_mul, Matrix.trace_sum]
      _ = Y.trace.re := by rw [hsum, one_mul]
      _ = _ := dual_trace N Q hQ s t
  rw [hy] at hall
  rw [div_le_iff₀ (show 0 < (N : ℝ) by exact_mod_cast hN)]
  simpa [mul_comm] using hall

end GlobalOptimality

noncomputable section

namespace TwoCopyParameters

def s : ℝ := Real.sqrt 15 / 4

def t : ℝ := (2 * Real.sqrt 5 - Real.sqrt 15) / 20

theorem s_pos : 0 < s := by
  unfold s
  positivity

theorem t_nonneg : 0 ≤ t := by
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h15 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  unfold t
  nlinarith [Real.sqrt_nonneg (15 : ℝ)]

theorem s_sq : s ^ 2 = 15 / 16 := by
  have h15 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  unfold s
  nlinarith

theorem mixed : 2 * s * t + 5 * t ^ 2 = 1 / 16 := by
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h15 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  unfold s t
  nlinarith

theorem radical_value : ((Real.sqrt 5 / 2 + Real.sqrt 15) / 5)^2 =
    13 / 20 + Real.sqrt 3 / 5 := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [h15]
  calc
    ((Real.sqrt 5 / 2 + Real.sqrt 3 * Real.sqrt 5) / 5) ^ 2 =
        ((Real.sqrt 5) ^ 2 / 4 + Real.sqrt 3 * (Real.sqrt 5) ^ 2 +
          (Real.sqrt 3) ^ 2 * (Real.sqrt 5) ^ 2) / 25 := by ring
    _ = 13 / 20 + Real.sqrt 3 / 5 := by rw [h5, h3]; ring

theorem value : (s + t) ^ 2 = 13 / 20 + Real.sqrt 3 / 5 := by
  have h : s + t = (Real.sqrt 5 / 2 + Real.sqrt 15) / 5 := by
    unfold s t
    ring
  rw [h]
  exact radical_value

end TwoCopyParameters

end

open scoped BigOperators ComplexOrder
namespace TensorSimplex

theorem tensor_inner (n m : ℕ) (v u : Fin n → ℂ) (w z : Fin m → ℂ) :
    (∑ x : Fin n × Fin m, star (v x.1 * w x.2) * (u x.1 * z x.2)) =
      (∑ a, star (v a) * u a) * (∑ b, star (w b) * z b) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [star_mul]
  ring

noncomputable def doubled {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) :
    Matrix (Fin m × Fin m) (Fin N) ℂ := fun a j => X a.1 j * X a.2 j

theorem gram_doubled {m : ℕ} (X : Matrix (Fin m) (Fin 5) ℂ)
    (hX : ∀ j k, (∑ a, star (X a j) * X a k) =
      if j=k then 1 else (-1/4 : ℂ)) :
    (doubled X).conjTranspose * doubled X = GramFactor.hMatrix 5 (15/16) (1/16) := by
  ext j k
  change (∑ a : Fin m × Fin m, star (X a.1 j * X a.2 j) * (X a.1 k * X a.2 k)) = _
  rw [tensor_inner m m (fun a => X a j) (fun a => X a k)
    (fun a => X a j) (fun a => X a k), hX]
  by_cases h : j=k <;>
    norm_num [GramFactor.hMatrix, GramFactor.ones, Matrix.one_apply, h]

end TensorSimplex

theorem doubled_five_simplex_global_optimum {m : ℕ}
    (X : Matrix (Fin m) (Fin 5) ℂ)
    (hX : ∀ j k, (∑ a, star (X a j) * X a k) =
      if j = k then 1 else -(1 : ℂ)/4) :
    let W : Matrix (Fin m × Fin m) (Fin 5) ℂ := fun a j => X a.1 j * X a.2 j
    let p : ℝ := 13/20 + Real.sqrt 3/5
    (∃ M : Fin 5 → Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
      (∀ j, (M j).PosSemidef) ∧ (∑ j, M j) = 1 ∧
      (∑ j, star (fun a => W a j) ⬝ᵥ ((M j).mulVec (fun a => W a j))).re / 5 = p) ∧
    (∀ M : Fin 5 → Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
      (∀ j, (M j).PosSemidef) → (∑ j, M j) = 1 →
      (∑ j, star (fun a => W a j) ⬝ᵥ ((M j).mulVec (fun a => W a j))).re / 5 ≤ p) := by
  let W : Matrix (Fin m × Fin m) (Fin 5) ℂ := TensorSimplex.doubled X
  let s := TwoCopyParameters.s
  let t := TwoCopyParameters.t
  have hGram : W.conjTranspose * W =
      GramFactor.hMatrix 5 s t * GramFactor.hMatrix 5 s t := by
    rw [GramFactor.hMatrix_mul]
    have hs : s * s = 15 / 16 := by
      nlinarith [TwoCopyParameters.s_sq]
    have ht : s*t+t*s+(5 : ℝ)*t*t = 1/16 := by
      nlinarith [TwoCopyParameters.mixed]
    norm_num only [Nat.cast_ofNat]
    rw [hs, ht]
    exact TensorSimplex.gram_doubled X hX
  obtain ⟨Q, hQ, hW⟩ := GramFactor.factor_hMatrix W s t
    TwoCopyParameters.s_pos TwoCopyParameters.t_nonneg hGram
  have hdiag (j : Fin 5) : GramFactor.hMatrix 5 s t j j = ((s+t : ℝ) : ℂ) := by
    simp [GramFactor.hMatrix, GramFactor.ones]
  have hH : GramFactor.hMatrix 5 s t = GlobalOptimality.hMatrix 5 s t := by
    ext i j
    by_cases h : i=j <;>
      simp [GramFactor.hMatrix, GramFactor.ones, GlobalOptimality.hMatrix,
        Matrix.one_apply, h, Complex.ofReal_add]
  change (∃ M : Fin 5 → Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
      (∀ j, (M j).PosSemidef) ∧ (∑ j, M j) = 1 ∧
      (∑ j, star (fun a => W a j) ⬝ᵥ ((M j).mulVec (fun a => W a j))).re / 5 =
        13/20 + Real.sqrt 3/5) ∧ _
  constructor
  · refine ⟨GlobalPrimal.measurement Q, GlobalPrimal.measurement_psd Q hQ,
      GlobalPrimal.measurement_complete Q (by norm_num), ?_⟩
    have h := GlobalPrimal.measurement_average Q hQ (by norm_num)
      (GramFactor.hMatrix 5 s t) (s+t) hdiag
    rw [hW, TwoCopyParameters.value] at h
    simpa using h
  · intro M hM hsum
    have h := GlobalOptimality.success_upper_bound 5 (by norm_num) Q hQ s t
      (le_of_lt TwoCopyParameters.s_pos) TwoCopyParameters.t_nonneg M hM hsum
    rw [← hH, hW, TwoCopyParameters.value] at h
    simpa [W, TensorSimplex.doubled] using h

