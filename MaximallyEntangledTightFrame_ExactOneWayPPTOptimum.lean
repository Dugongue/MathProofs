import Mathlib

/-!
# Exact one-way and PPT discrimination optimum for maximally entangled tight frames

For every local dimension d >= 2 and number of states N > 0, a normalized
maximally entangled tight frame in C^d tensor C^d admits an explicit one-way
Alice-to-Bob discrimination protocol with uniform-prior, single-copy success d/N.
Every positive-partial-transpose (PPT) POVM has success at most d/N.
Equiangularity is not required; tightness and maximal entanglement are required.
The theorem applies whenever such a frame exists, and does not assert existence
for every pair (d, N).

Alice measures the computational basis. Given outcome a, Bob uses effects
B[a,j](b,e) = (d^2/N) V_j(a,b) conjugate(V_j(a,e)). We prove conditional
positivity and completeness, exact success, and positivity, completeness and
PPT of the induced joint measurement, together with the universal PPT bound.

Relation to the literature: Section VII of Amanda Wei, Gabriele Cobucci and
Armin Tavakoli, "Nonprojective Bell-state measurements", Physical Review A 110,
042206 (2024), DOI: 10.1103/PhysRevA.110.042206, reports numerical local success
approximately 0.3936 for its five-state qubit frame, no increase found by its
one-way LOCC search, and PPT success 2/5. The present theorem gives an explicit
one-way protocol attaining exactly 2/5 for that frame, and generalizes the
attainment and upper bound to every maximally entangled tight frame.
This resolves a numerical shortfall, not a theorem asserting a lower optimum
or an explicitly named open problem. The no-communication LO optimum is not
settled here. No claim of literature priority is made.

Main theorem: maximally_entangled_tight_frame_one_way_ppt_optimal.
Born-rule bridge: maximally_entangled_tight_frame_joint_success.
-/

open scoped BigOperators ComplexOrder

namespace EntangledReduction

/-- For a square coefficient matrix, one maximally mixed reduction implies the other. -/
theorem columnGram_of_rowGram {d : ℕ} (hd : d ≠ 0)
    (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V * V.conjTranspose = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    V.conjTranspose * V = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hleft : ((d : ℂ) • V) * V.conjTranspose = 1 := by
    rw [Matrix.smul_mul, hV, smul_smul]
    simp [hd']
  have hright : V.conjTranspose * ((d : ℂ) • V) = 1 :=
    mul_eq_one_comm.mp hleft
  rw [Matrix.mul_smul] at hright
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (d : ℂ)⁻¹ • A) hright
  simpa [smul_smul, hd'] using h

end EntangledReduction


open scoped BigOperators ComplexOrder
noncomputable section
namespace BellLOCCProtocol

def bobEffect (d N : ℕ) (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d) (j : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  fun b e => ((d : ℂ)^2 / (N : ℂ)) * V j a b * star (V j a e)

def protocolSuccess (d N : ℕ) (V : Fin N → Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j, ∑ a, ∑ b, ∑ e,
    star (V j a b) * bobEffect d N V a j b e * V j a e

theorem bobEffect_posSemidef (d N : ℕ)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ) (a : Fin d) (j : Fin N) :
    (bobEffect d N V a j).PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star (V j a)).smul
    (show 0 ≤ (d : ℝ)^2 / (N : ℝ) by positivity)
  convert h using 1
  ext b e
  simp [bobEffect, Matrix.vecMulVec, Complex.real_smul, mul_assoc]

theorem bobEffect_complete (d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (htight : ∀ a b c e, (∑ j, V j a b * star (V j c e)) =
      if a = c ∧ b = e then (N : ℂ)/(d : ℂ)^2 else 0) (a : Fin d) :
    (∑ j, bobEffect d N V a j) = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext b e
  simp only [Matrix.sum_apply, bobEffect]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, htight]
  by_cases hbe : b = e
  · subst e
    simp only [and_self, if_true, Matrix.one_apply_eq]
    field_simp
  · simp [hbe, Matrix.one_apply]

theorem row_norm (d N : ℕ)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hrow : ∀ j, (V j) * (V j).conjTranspose = (d : ℂ)⁻¹ • 1)
    (j : Fin N) (a : Fin d) :
    (∑ b, star (V j a b) * V j a b) = (d : ℂ)⁻¹ := by
  have h := congrFun (congrFun (hrow j) a) a
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h

theorem branch_success (d N : ℕ) (hd : 0 < d)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hrow : ∀ j, (V j) * (V j).conjTranspose = (d : ℂ)⁻¹ • 1)
    (j : Fin N) (a : Fin d) :
    (∑ b, ∑ e, star (V j a b) * bobEffect d N V a j b e * V j a e) =
      (N : ℂ)⁻¹ := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  calc
    _ = ((d : ℂ)^2/(N : ℂ)) *
        (∑ b, star (V j a b)*V j a b) * (∑ e, star (V j a e)*V j a e) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro e he
      unfold bobEffect
      ring
    _ = (N : ℂ)⁻¹ := by
      rw [row_norm d N V hrow j a]
      field_simp

theorem success_value (d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hrow : ∀ j, (V j) * (V j).conjTranspose = (d : ℂ)⁻¹ • 1) :
    protocolSuccess d N V = (d : ℂ)/(N : ℂ) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold protocolSuccess
  simp_rw [branch_success d N hd V hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end BellLOCCProtocol

end

open scoped BigOperators ComplexOrder

namespace BellJoint

noncomputable def effect {d : ℕ} (B : Fin d → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => if x.1 = y.1 then B x.1 x.2 y.2 else 0

theorem effect_hermitian {d : ℕ} (B : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hB : ∀ a, (B a).IsHermitian) : (effect B).IsHermitian := by
  ext x y
  change star (if y.1 = x.1 then B y.1 y.2 x.2 else 0) =
    if x.1 = y.1 then B x.1 x.2 y.2 else 0
  by_cases h : x.1 = y.1
  · simp only [h, if_pos rfl]
    exact congrFun (congrFun (hB y.1) x.2) y.2
  · simp [h, Ne.symm h]

theorem effect_quadratic {d : ℕ} (B : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (z : (Fin d × Fin d) → ℂ) :
    star z ⬝ᵥ ((effect B).mulVec z) =
      ∑ a, star (fun b => z (a,b)) ⬝ᵥ ((B a).mulVec (fun b => z (a,b))) := by
  simp [dotProduct, Matrix.mulVec, effect, Fintype.sum_prod_type, Finset.mul_sum]

theorem effect_posSemidef {d : ℕ} (B : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hB : ∀ a, (B a).PosSemidef) : (effect B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact effect_hermitian B (fun a => (hB a).isHermitian)
  · intro z
    rw [effect_quadratic]
    exact Finset.sum_nonneg fun a _ => (hB a).dotProduct_mulVec_nonneg _

theorem effect_partialTranspose_posSemidef {d : ℕ}
    (B : Fin d → Matrix (Fin d) (Fin d) ℂ) (hB : ∀ a, (B a).PosSemidef) :
    Matrix.PosSemidef (fun x y : Fin d × Fin d => (effect B) (x.1,y.2) (y.1,x.2)) := by
  exact effect_posSemidef (fun a => (B a).transpose) (fun a => (hB a).transpose)

theorem effect_complete {d N : ℕ} (B : Fin d → Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hB : ∀ a, (∑ j, B a j) = 1) : (∑ j, effect (fun a => B a j)) = 1 := by
  ext x y
  simp only [Matrix.sum_apply, effect]
  by_cases h : x.1 = y.1
  · simp only [h, if_pos rfl]
    have he := congrFun (congrFun (hB y.1) x.2) y.2
    simpa [Matrix.sum_apply, Matrix.one_apply, Prod.ext_iff, h] using he
  · simp [h, Matrix.one_apply, Prod.ext_iff]

theorem effect_expectation {d : ℕ} (B : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin d) (Fin d) ℂ) :
    (∑ x : Fin d × Fin d, ∑ y : Fin d × Fin d,
      star (V x.1 x.2) * effect B x y * V y.1 y.2) =
      ∑ a, ∑ b, ∑ e, star (V a b) * B a b e * V a e := by
  simp [effect, Fintype.sum_prod_type, Finset.mul_sum]

theorem success_real (d N : ℕ) (z : ℂ)
    (h : (N : ℂ)⁻¹ * z = (d : ℂ)/(N : ℂ)) :
    z.re/(N : ℝ) = (d : ℝ)/(N : ℝ) := by
  have he : (((N : ℝ)⁻¹ : ℝ) : ℂ) * z = (((d : ℝ)/(N : ℝ) : ℝ) : ℂ) := by
    simpa using h
  have hre := congrArg Complex.re he
  simpa [Complex.mul_re, div_eq_mul_inv, mul_comm] using hre

end BellJoint

open scoped BigOperators ComplexOrder
open Matrix

namespace BellPPT

def partialTranspose {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => A (x.1, y.2) (y.1, x.2)

def density {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => V x.1 x.2 * star (V y.1 y.2)

theorem pt_density_hermitian {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :
    (partialTranspose (density V)).IsHermitian := by
  ext x y
  simp [partialTranspose, density, Matrix.conjTranspose_apply, mul_comm]

theorem pt_density_sq {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) (r : ℂ)
    (hr : V * V.conjTranspose = r • 1)
    (hc : V.conjTranspose * V = r • 1) :
    partialTranspose (density V) * partialTranspose (density V) = r^2 • 1 := by
  ext ⟨a,b⟩ ⟨c,e⟩
  change (∑ x : Fin d × Fin d,
    (V a x.2 * star (V x.1 b)) * (V x.1 e * star (V c x.2))) = _
  rw [Fintype.sum_prod_type]
  have hfactor : (∑ x, ∑ y, (V a y * star (V x b)) *
      (V x e * star (V c y))) =
      (∑ y, V a y * star (V c y)) * (∑ x, star (V x b) * V x e) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hfactor]
  have hr' := congrFun (congrFun hr a) c
  have hc' := congrFun (congrFun hc b) e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul] at hr' hc'
  rw [hr', hc']
  by_cases hac : a = c <;> by_cases hbe : b = e <;>
    simp [hac, hbe, Matrix.one_apply, Matrix.smul_apply, pow_two]

theorem involution_trace_le {n : Type*} [Fintype n] [DecidableEq n]
    (F E : Matrix n n ℂ) (r : ℝ) (hr : 0 < r)
    (hF : F.IsHermitian) (hsq : F * F = (r : ℂ)^2 • 1)
    (hE : E.PosSemidef) :
    (E * F).trace.re ≤ r * E.trace.re := by
  let A : Matrix n n ℂ := (r : ℂ) • 1 - F
  have hA : A.IsHermitian := by
    dsimp [A]
    exact (Matrix.isHermitian_one.smul (show IsSelfAdjoint (r : ℂ) from by
      exact Complex.conj_ofReal r)).sub hF
  have hAsq : A * A = (2 * (r : ℂ)) • A := by
    dsimp [A]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, smul_smul]
    rw [hsq]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  have hp := (hE.conjTranspose_mul_mul_same A).trace_nonneg
  rw [hA.eq, Matrix.trace_mul_cycle, hAsq,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm A E] at hp
  have hp' := (Complex.nonneg_iff.mp hp).1
  have heq : (E * A).trace = (r : ℂ) * E.trace - (E * F).trace := by
    simp [A, mul_sub, Matrix.trace_sub, Matrix.trace_smul]
  rw [heq] at hp'
  simp [smul_eq_mul, Complex.mul_re, Complex.mul_im] at hp'
  nlinarith

theorem pt_trace {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (partialTranspose A).trace = A.trace := rfl

theorem pt_trace_duality {d : ℕ}
    (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (partialTranspose A * partialTranspose B).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    partialTranspose, Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, ∑ c, ∑ e, A (a,e) (c,b) * B (c,b) (a,e)) =
        ∑ a, ∑ e, ∑ c, ∑ b, A (a,e) (c,b) * B (c,b) (a,e) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b, ∑ c, ∑ e, A (a,e) (c,b) * B (c,b) (a,e)) =
            ∑ c, ∑ b, ∑ e, A (a,e) (c,b) * B (c,b) (a,e) := Finset.sum_comm
        _ = ∑ c, ∑ e, ∑ b, A (a,e) (c,b) * B (c,b) (a,e) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := rfl

theorem trace_density {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (E : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (E * density V).trace =
      ∑ x, ∑ y, star (V x.1 x.2) * E x y * V y.1 y.2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, density]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem ppt_effect_bound {d : ℕ} (hd : 0 < d)
    (V : Matrix (Fin d) (Fin d) ℂ)
    (hr : V * V.conjTranspose = (d : ℂ)⁻¹ • 1)
    (hc : V.conjTranspose * V = (d : ℂ)⁻¹ • 1)
    (E : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hPT : (partialTranspose E).PosSemidef) :
    (∑ x, ∑ y, star (V x.1 x.2) * E x y * V y.1 y.2).re ≤
      E.trace.re / (d : ℝ) := by
  have hsq : partialTranspose (density V) * partialTranspose (density V) =
      (((d : ℝ)⁻¹ : ℝ) : ℂ)^2 • 1 := by
    simpa using pt_density_sq V (d : ℂ)⁻¹ hr hc
  have h := involution_trace_le (partialTranspose (density V)) (partialTranspose E)
    (d : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr hd)) (pt_density_hermitian V) hsq hPT
  rw [pt_trace_duality, pt_trace, trace_density] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem ppt_uniform_success_bound {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hr : ∀ j, V j * (V j).conjTranspose = (d : ℂ)⁻¹ • 1)
    (hc : ∀ j, (V j).conjTranspose * V j = (d : ℂ)⁻¹ • 1)
    (M : Fin N → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hPT : ∀ j, (partialTranspose (M j)).PosSemidef)
    (hsum : ∑ j, M j = 1) :
    (∑ j, ∑ x, ∑ y, star (V j x.1 x.2) * M j x y * V j y.1 y.2).re /
      (N : ℝ) ≤ (d : ℝ) / (N : ℝ) := by
  have hpoint (j : Fin N) := ppt_effect_bound hd (V j) (hr j) (hc j) (M j) (hPT j)
  have ht : (∑ j, (M j).trace.re) = (d : ℝ)^2 := by
    calc
      (∑ j, (M j).trace.re) = (∑ j, M j).trace.re := by
        simp [Matrix.trace_sum]
      _ = (d : ℝ)^2 := by simp [hsum, Matrix.trace_one, pow_two]
  have hbound := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  rw [← Finset.sum_div, ht] at hbound
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hddiv : (d : ℝ)^2 / (d : ℝ) = d := by field_simp
  rw [hddiv] at hbound
  have hsumre : (∑ j, ∑ x, ∑ y,
      star (V j x.1 x.2) * M j x y * V j y.1 y.2).re ≤ (d : ℝ) := by
    simpa using hbound
  exact div_le_div_of_nonneg_right hsumre (by positivity)

end BellPPT

theorem maximally_entangled_tight_frame_one_way_ppt_optimal (d N : ℕ)
    (hd : 2 ≤ d) (hN : 0 < N) (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hmax : ∀ j, V j * (V j).conjTranspose = (d : ℂ)⁻¹ • 1)
    (hframe : ∀ a b c e, (∑ j, V j a b * star (V j c e)) =
      if a = c ∧ b = e then (N : ℂ)/(d : ℂ)^2 else 0) :
    ∃ B : Fin d → Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ a j, (B a j).PosSemidef) ∧
      (∀ a, (∑ j, B a j) = 1) ∧
      ((N : ℂ)⁻¹ * (∑ j, ∑ a, ∑ b, ∑ e,
        star (V j a b) * B a j b e * V j a e) = (d : ℂ)/(N : ℂ)) ∧
      (∀ j, Matrix.PosSemidef (fun x y : Fin d × Fin d =>
        if x.1 = y.1 then B x.1 j x.2 y.2 else 0)) ∧
      (∀ j, Matrix.PosSemidef (fun x y : Fin d × Fin d =>
        if x.1 = y.1 then B x.1 j y.2 x.2 else 0)) ∧
      ((∑ j, (fun x y : Fin d × Fin d =>
        if x.1 = y.1 then B x.1 j x.2 y.2 else 0)) =
          (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ∧
      (∀ M : Fin N → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
        (∀ j, (M j).PosSemidef) →
        (∀ j, Matrix.PosSemidef (fun x y : Fin d × Fin d => M j (x.1,y.2) (y.1,x.2))) →
        (∑ j, M j) = 1 →
        (∑ j, ∑ x : Fin d × Fin d, ∑ y : Fin d × Fin d,
          star (V j x.1 x.2) * M j x y * V j y.1 y.2).re / (N : ℝ)
          ≤ (d : ℝ)/(N : ℝ)) := by
  have hdpos : 0 < d := by omega
  let B := BellLOCCProtocol.bobEffect d N V
  have hB : ∀ a j, (B a j).PosSemidef := BellLOCCProtocol.bobEffect_posSemidef d N V
  have hsum : ∀ a, (∑ j, B a j) = 1 :=
    BellLOCCProtocol.bobEffect_complete d N hdpos hN V hframe
  refine ⟨B, hB, hsum, BellLOCCProtocol.success_value d N hdpos hN V hmax, ?_, ?_, ?_, ?_⟩
  · intro j
    exact BellJoint.effect_posSemidef (fun a => B a j) (fun a => hB a j)
  · intro j
    exact BellJoint.effect_partialTranspose_posSemidef (fun a => B a j) (fun a => hB a j)
  · exact BellJoint.effect_complete B hsum
  · intro M hM hPT hMsum
    have hcol : ∀ j, (V j).conjTranspose * V j = (d : ℂ)⁻¹ • 1 :=
      fun j => EntangledReduction.columnGram_of_rowGram (Nat.ne_of_gt hdpos) (V j) (hmax j)
    exact BellPPT.ppt_uniform_success_bound hdpos hN V hmax hcol M hPT hMsum

/-- The joint POVM has the same real success probability as the sequential protocol. -/
theorem maximally_entangled_tight_frame_joint_success (d N : ℕ)
    (hd : 0 < d) (hN : 0 < N) (V : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hmax : ∀ j, V j * (V j).conjTranspose = (d : ℂ)⁻¹ • 1) :
    (∑ j, ∑ x : Fin d × Fin d, ∑ y : Fin d × Fin d,
      star (V j x.1 x.2) *
        BellJoint.effect (fun a => BellLOCCProtocol.bobEffect d N V a j) x y *
        V j y.1 y.2).re / (N : ℝ) = (d : ℝ)/(N : ℝ) := by
  simp_rw [BellJoint.effect_expectation]
  exact BellJoint.success_real d N _ (BellLOCCProtocol.success_value d N hd hN V hmax)

