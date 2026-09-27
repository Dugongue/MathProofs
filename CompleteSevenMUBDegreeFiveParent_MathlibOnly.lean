/-
A complete family of seven mutually unbiased orthonormal bases in complex
dimension six admits an explicit degree-five parent POVM. The construction
has depolarizing visibility 4415/14497 and generalized visibility 18286/43491.

This file is self-contained apart from Mathlib: it proves the dephasing-frame,
exact conditional moments, positivity, normalization, and every marginal.
-/
import Mathlib


open scoped BigOperators Matrix ComplexConjugate ComplexOrder
namespace MUBCP

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def IsMUBFamily {d k : ℕ} (B : Fin k → Mat d) : Prop :=
  (∀ a, (B a)ᴴ * B a = 1) ∧
  ∀ a b, a ≠ b → ∀ i j, Complex.normSq (((B a)ᴴ * B b) i j) = 1 / (d : ℝ)

def projector {d : ℕ} (U : Mat d) (j : Fin d) : Mat d :=
  Matrix.vecMulVec (fun i => U i j) (fun i => star (U i j))

noncomputable def dephase {d : ℕ} (U : Mat d) (X : Mat d) : Mat d :=
  ∑ j, Matrix.trace (projector U j * X) • projector U j

noncomputable def depolarize (d : ℕ) (X : Mat d) : Mat d :=
  (Matrix.trace X / (d : ℂ)) • (1 : Mat d)

noncomputable def residual {d k : ℕ} (B : Fin k → Mat d) (X : Mat d) : Mat d :=
  X - ∑ a, dephase (B a) X + (k : ℂ) • depolarize d X

noncomputable def noise {d k : ℕ} (B : Fin k → Mat d) (t : ℝ) (X : Mat d) : Mat d :=
  (1 - (t : ℂ)) • depolarize d X + (t : ℂ) • residual B X

/-- Genuine matrix amplification, applying Phi to every d-by-d block. -/
def amplify {d : ℕ} (Phi : Mat d → Mat d) (n : ℕ)
    (X : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ) :
    Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ :=
  fun p q => Phi (fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- Complete positivity quantifies over every matrix amplification, not a scalar test. -/
def CompletelyPositive {d : ℕ} (Phi : Mat d → Mat d) : Prop :=
  ∀ n (X : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ),
    X.PosSemidef → (amplify Phi n X).PosSemidef

def TracePreserving {d : ℕ} (Phi : Mat d → Mat d) : Prop :=
  ∀ X, Matrix.trace (Phi X) = Matrix.trace X

def Feasible {d k : ℕ} (B : Fin k → Mat d) (X : Mat d) : Prop :=
  X.PosSemidef ∧ Matrix.trace X = 1 ∧
    ∀ a j, Matrix.trace (projector (B a) j * X) = 1 / (d : ℂ)

/-- The unchanged CP/TP threshold and density-output theorem to be proved.
This is a proposition definition, not a proof, axiom, or weakened CP criterion. -/
def ExactThreshold : Prop :=
  ∀ (d k : ℕ), 2 ≤ d → 1 ≤ k → k ≤ d →
  ∀ B : Fin k → Mat d, IsMUBFamily B →
  ∀ t : ℝ, 0 ≤ t →
    ((CompletelyPositive (noise B t) ∧ TracePreserving (noise B t)) ↔
      t ≤ 1 / ((d : ℝ) + 1 - (k : ℝ))) ∧
    (t ≤ 1 / ((d : ℝ) + 1 - (k : ℝ)) →
      ∀ X : Mat d, X.PosSemidef → Matrix.trace X = 1 → Feasible B (noise B t X))

def choi {d : ℕ} (Phi : Mat d → Mat d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => Phi (Matrix.single p.1 q.1 1) p.2 q.2

/-- Actual rank-one dephasing Choi matrix as a sum of Gram outer products. -/
theorem choi_dephase {d : ℕ} (U : Mat d) :
    choi (dephase U) =
      ∑ j, Matrix.vecMulVec
        (fun p : Fin d × Fin d => star (U p.1 j) * U p.2 j)
        (fun p : Fin d × Fin d => star (star (U p.1 j) * U p.2 j)) := by
  classical
  ext p q
  simp [choi, dephase, projector, Matrix.trace_mul_single,
    Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact Choi decomposition before the orthogonal-projector spectral argument. -/
theorem choi_noise {d k : ℕ} (B : Fin k → Mat d) (t : ℝ) :
    choi (noise B t) =
      (t : ℂ) • choi (fun X : Mat d => X) -
      (t : ℂ) • (∑ a, choi (dephase (B a))) +
      (1 + (t : ℂ) * ((k : ℂ) - 1)) • choi (depolarize d) := by
  classical
  ext p q
  simp only [choi, noise, residual, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  ring

/-- Complete positivity is stable under addition at every amplification. -/
theorem completelyPositive_add {d : ℕ} (Phi Psi : Mat d → Mat d)
    (hPhi : CompletelyPositive Phi) (hPsi : CompletelyPositive Psi) :
    CompletelyPositive (fun X => Phi X + Psi X) := by
  intro n X hX
  exact (hPhi n X hX).add (hPsi n X hX)

/-- Every matrix congruence is positive at every amplification size. -/
theorem completelyPositive_conjugation {d : ℕ} (K : Mat d) :
    CompletelyPositive (fun X => K * X * Kᴴ) := by
  classical
  intro n X hX
  let A : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ :=
    fun p q => if p.1 = q.1 then K p.2 q.2 else 0
  have heq : amplify (fun Y => K * Y * Kᴴ) n X = A * X * Aᴴ := by
    ext p q
    change (∑ i, (∑ j, K p.2 j * X (p.1, j) (q.1, i)) * star (K q.2 i)) =
      ∑ r : Fin n × Fin d, (∑ s : Fin n × Fin d, A p s * X s r) * star (A q r)
    simp [A, Fintype.sum_prod_type, Finset.sum_mul, apply_ite, ite_mul, mul_ite]
  rw [heq]
  exact hX.mul_mul_conjTranspose_same A

/-- A concrete finite Kraus representation suffices for genuine complete positivity. -/
theorem completelyPositive_kraus {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → Mat d) :
    CompletelyPositive (fun X => ∑ i, K i * X * (K i)ᴴ) := by
  classical
  intro n X hX
  have heq : amplify (fun Y => ∑ i, K i * Y * (K i)ᴴ) n X =
      ∑ i, amplify (fun Y => K i * Y * (K i)ᴴ) n X := by
    ext p q
    simp [amplify, Matrix.sum_apply]
  rw [heq]
  exact Matrix.posSemidef_sum Finset.univ
    (fun i _ => completelyPositive_conjugation (K i) n X hX)

end MUBCP

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix
namespace MUBCP

theorem projector_trace_general {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) (j : Fin d) :
    Matrix.trace (projector U j) = 1 := by
  have h := congrArg (fun A : Mat d => A j j) hU
  simpa [projector, Matrix.trace_vecMulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm] using h

theorem projector_sum_general {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    ∑ j, projector U j = 1 := by
  have hh : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  rw [← hh]
  ext a b
  simp [projector, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem projector_overlap_general {d : ℕ} (U V : Mat d) (i j : Fin d) :
    Matrix.trace (projector U i * projector V j) =
      (Complex.normSq ((Uᴴ * V) i j) : ℂ) := by
  simp only [projector, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

def lifted {d : ℕ} (U : Mat d) : Matrix (Fin d × Fin d) (Fin d) ℂ :=
  fun p j => star (U p.1 j) * U p.2 j

def omega (d : ℕ) : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0

def omegaGram (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (omega d) (star (omega d))

theorem lifted_gram {d : ℕ} (U V : Mat d) (i j : Fin d) :
    ((lifted U)ᴴ * lifted V) i j = (Complex.normSq ((Uᴴ * V) i j) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, lifted,
    Fintype.sum_prod_type, star_mul, star_star]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem lifted_isometry {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    (lifted U)ᴴ * lifted U = 1 := by
  ext i j
  rw [lifted_gram, hU]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem lifted_sum {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) (p : Fin d × Fin d) :
    (∑ j, lifted U p j) = omega d p := by
  have hh : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h := congrArg (fun A : Mat d => A p.2 p.1) hh
  simpa [lifted, omega, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_comm, eq_comm] using h

theorem choi_dephase_factor {d : ℕ} (U : Mat d) :
    choi (dephase U) = lifted U * (lifted U)ᴴ := by
  rw [choi_dephase]
  ext p q
  simp [lifted, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply]

theorem choi_dephase_idempotent {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    choi (dephase U) * choi (dephase U) = choi (dephase U) := by
  rw [choi_dephase_factor]
  calc
    (lifted U * (lifted U)ᴴ) * (lifted U * (lifted U)ᴴ) =
      lifted U * ((lifted U)ᴴ * lifted U) * (lifted U)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [lifted_isometry U hU, Matrix.mul_one]

theorem choi_identity {d : ℕ} : choi (fun X : Mat d => X) = omegaGram d := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [choi, omegaGram, omega, Matrix.vecMulVec_apply, Matrix.single,
      Pi.star_apply, hp, hq]

theorem choi_depolarize {d : ℕ} : choi (depolarize d) =
    (1 / (d : ℂ)) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  ext p q
  have ht : Matrix.trace (Matrix.single p.1 q.1 (1 : ℂ)) =
      if p.1 = q.1 then 1 else 0 := by
    by_cases h : p.1 = q.1
    · simp [h, Matrix.trace_single_eq_same]
    · simp [h]
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;>
    simp [choi, depolarize, ht, Matrix.smul_apply, Matrix.one_apply,
      Prod.ext_iff, smul_eq_mul, h₁, h₂]

theorem lifted_star_omega {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    (lifted U)ᴴ *ᵥ omega d = fun _ => 1 := by
  ext j
  have h := congrArg (fun A : Mat d => A j j) hU
  simpa [Matrix.mulVec, dotProduct, lifted, omega, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, mul_comm] using h

theorem choi_dephase_omega {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    choi (dephase U) * omegaGram d = omegaGram d := by
  rw [omegaGram, Matrix.mul_vecMulVec]
  congr 1
  rw [choi_dephase_factor, ← Matrix.mulVec_mulVec, lifted_star_omega U hU]
  ext p
  simpa [Matrix.mulVec, dotProduct] using lifted_sum U hU p

theorem choi_dephase_cross {d : ℕ} (U V : Mat d)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hUV : ∀ i j, Complex.normSq ((Uᴴ * V) i j) = 1 / (d : ℝ)) :
    choi (dephase U) * choi (dephase V) = (1 / (d : ℂ)) • omegaGram d := by
  have hg : (lifted U)ᴴ * lifted V = fun _ _ => (1 / (d : ℂ)) := by
    ext i j
    rw [lifted_gram, hUV]
    simp
  rw [choi_dephase_factor, choi_dephase_factor]
  calc
    (lifted U * (lifted U)ᴴ) * (lifted V * (lifted V)ᴴ) =
      lifted U * ((lifted U)ᴴ * lifted V) * (lifted V)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hg]
      ext p q
      change (∑ j, (∑ i, lifted U p i * (1 / (d : ℂ))) * star (lifted V q j)) =
        (1 / (d : ℂ)) * (omega d p * star (omega d q))
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← star_sum,
        lifted_sum U hU, lifted_sum V hV]
      ring

theorem omegaGram_sq {d : ℕ} : omegaGram d * omegaGram d = (d : ℂ) • omegaGram d := by
  have hdot : star (omega d) ⬝ᵥ omega d = (d : ℂ) := by
    simp [omega, dotProduct, Fintype.sum_prod_type]
  simp only [omegaGram, Matrix.vecMulVec_mul_vecMulVec, hdot]
  exact Matrix.vecMulVec_smul _ _ _

end MUBCP

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder
namespace MUBCP

theorem completelyPositive_posSemidef {d : ℕ} {Phi : Mat d → Mat d}
    (hPhi : CompletelyPositive Phi) {X : Mat d} (hX : X.PosSemidef) :
    (Phi X).PosSemidef := by
  have h := hPhi 1 (X.submatrix Prod.snd Prod.snd) (hX.submatrix Prod.snd)
  exact h.submatrix (fun i => ((0 : Fin 1), i))

theorem completelyPositive_choi {d : ℕ} {Phi : Mat d → Mat d}
    (hPhi : CompletelyPositive Phi) : (choi Phi).PosSemidef := by
  classical
  let v : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have h := hPhi d (Matrix.vecMulVec v (star v))
    (Matrix.posSemidef_vecMulVec_self_star v)
  have heq : amplify Phi d (Matrix.vecMulVec v (star v)) = choi Phi := by
    ext p q
    unfold amplify choi
    congr 1
    ext i j
    by_cases hp : p.1 = i <;> by_cases hq : q.1 = j <;>
      simp [v, Matrix.vecMulVec_apply, Matrix.single, hp, hq]
  rwa [heq] at h

theorem linear_eq_of_choi_eq {d : ℕ} (Phi Psi : Mat d →ₗ[ℂ] Mat d)
    (h : choi Phi = choi Psi) : Phi = Psi := by
  classical
  have hu (i j : Fin d) : Phi (Matrix.single i j 1) = Psi (Matrix.single i j 1) := by
    ext a b
    exact congrArg (fun C => C (i,a) (j,b)) h
  ext X a b
  have hx : Phi X = Psi X := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hs : Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [hs, map_smul, map_smul, hu]
  exact congrArg (fun Y => Y a b) hx

noncomputable def krausLinear {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun X := ∑ r, K r * X * (K r)ᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem choi_krausLinear {d : ℕ}
    (R : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    choi (krausLinear (fun r a i => star (R r (i,a)))) = Rᴴ * R := by
  classical
  ext p q
  simp only [choi, krausLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  change (∑ r, ∑ j, (∑ i, star (R r (i,p.2)) *
    Matrix.single p.1 q.1 (1 : ℂ) i j) * star (star (R r (j,q.2)))) =
    ∑ r, star (R r p) * R r q
  simp [Matrix.single, ite_and, mul_ite, ite_mul]

theorem choi_posSemidef_iff_completelyPositive {d : ℕ}
    (Phi : Mat d →ₗ[ℂ] Mat d) :
    (choi Phi).PosSemidef ↔ CompletelyPositive Phi := by
  constructor
  · intro h
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
    have heq : Phi = krausLinear (fun r a i => star (R r (i,a))) := by
      apply linear_eq_of_choi_eq
      rw [choi_krausLinear]
      exact hR
    rw [heq]
    exact completelyPositive_kraus _
  · exact completelyPositive_choi

end MUBCP

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
namespace MUBCP

noncomputable def dephaseLinear {d : ℕ} (U : Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun := dephase U
  map_add' X Y := by
    simp [dephase, Matrix.mul_add, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [dephase, Matrix.mul_smul, Matrix.trace_smul, mul_smul, Finset.smul_sum]

noncomputable def depolarizeLinear (d : ℕ) : Mat d →ₗ[ℂ] Mat d where
  toFun := depolarize d
  map_add' X Y := by simp [depolarize, Matrix.trace_add, add_div, add_smul]
  map_smul' c X := by
    simp [depolarize, Matrix.trace_smul, div_eq_mul_inv, mul_smul, mul_assoc]

noncomputable def noiseLinear {d k : ℕ} (B : Fin k → Mat d) (t : ℝ) :
    Mat d →ₗ[ℂ] Mat d :=
  (1 - (t : ℂ)) • depolarizeLinear d + (t : ℂ) •
    (LinearMap.id - ∑ a, dephaseLinear (B a) + (k : ℂ) • depolarizeLinear d)

theorem noiseLinear_apply {d k : ℕ} (B : Fin k → Mat d) (t : ℝ) (X : Mat d) :
    noiseLinear B t X = noise B t X := by
  simp only [noiseLinear, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.id_apply]
  rfl

theorem noise_cp_iff_choi {d k : ℕ} (B : Fin k → Mat d) (t : ℝ) :
    CompletelyPositive (noise B t) ↔ (choi (noise B t)).PosSemidef := by
  have heq : (noiseLinear B t : Mat d → Mat d) = noise B t :=
    funext (noiseLinear_apply B t)
  rw [← heq]
  exact (choi_posSemidef_iff_completelyPositive (noiseLinear B t)).symm

theorem trace_dephase {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) (X : Mat d) :
    Matrix.trace (dephase U X) = Matrix.trace X := by
  simp only [dephase, Matrix.trace_sum, Matrix.trace_smul,
    projector_trace_general U hU, smul_eq_mul, mul_one]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, projector_sum_general U hU, Matrix.one_mul]

theorem trace_depolarize {d : ℕ} (hd : d ≠ 0) (X : Mat d) :
    Matrix.trace (depolarize d X) = Matrix.trace X := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp [depolarize, Matrix.trace_smul, Matrix.trace_one, hdC]

theorem noise_tracePreserving {d k : ℕ} (hd : d ≠ 0)
    (B : Fin k → Mat d) (hB : IsMUBFamily B) (t : ℝ) :
    TracePreserving (noise B t) := by
  intro X
  simp only [noise, residual, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_sum, trace_depolarize hd, trace_dephase _ (hB.1 _), smul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem measurement_dephase {d k : ℕ} (B : Fin k → Mat d) (hB : IsMUBFamily B)
    (a b : Fin k) (i : Fin d) (X : Mat d) :
    Matrix.trace (projector (B a) i * dephase (B b) X) =
      if a = b then Matrix.trace (projector (B a) i * X)
      else Matrix.trace X / (d : ℂ) := by
  classical
  simp only [dephase, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, projector_overlap_general]
  by_cases hab : a = b
  · subst b
    simp [hB.1 a, Matrix.one_apply, apply_ite]
  · simp only [hB.2 a b hab, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, if_neg hab]
    rw [← Finset.sum_mul]
    have hs : (∑ j, Matrix.trace (projector (B b) j * X)) = Matrix.trace X := by
      rw [← Matrix.trace_sum, ← Matrix.sum_mul, projector_sum_general _ (hB.1 b),
        Matrix.one_mul]
    rw [hs]
    ring

theorem measurement_depolarize {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1)
    (i : Fin d) (X : Mat d) :
    Matrix.trace (projector U i * depolarize d X) = Matrix.trace X / (d : ℂ) := by
  simp [depolarize, Matrix.mul_smul, Matrix.trace_smul, projector_trace_general U hU]

theorem noise_measurement {d k : ℕ} (B : Fin k → Mat d) (hB : IsMUBFamily B)
    (t : ℝ) (a : Fin k) (i : Fin d) (X : Mat d) :
    Matrix.trace (projector (B a) i * noise B t X) = Matrix.trace X / (d : ℂ) := by
  classical
  have hs : (∑ b, Matrix.trace (projector (B a) i * dephase (B b) X)) =
      (k : ℂ) * (Matrix.trace X / (d : ℂ)) +
        (Matrix.trace (projector (B a) i * X) - Matrix.trace X / (d : ℂ)) := by
    calc
      _ = ∑ b, (Matrix.trace X / (d : ℂ) +
          if b = a then Matrix.trace (projector (B a) i * X) - Matrix.trace X / (d : ℂ)
          else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [measurement_dephase B hB]
        by_cases hab : a = b
        · subst b; simp
        · simp [hab, Ne.symm hab]
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [noise, residual, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul, measurement_depolarize _ (hB.1 a), hs]
  ring

theorem noise_feasible_of_cp {d k : ℕ} (hd : d ≠ 0)
    (B : Fin k → Mat d) (hB : IsMUBFamily B) (t : ℝ)
    (hcp : CompletelyPositive (noise B t)) (X : Mat d)
    (hX : X.PosSemidef) (htr : Matrix.trace X = 1) : Feasible B (noise B t X) := by
  refine ⟨completelyPositive_posSemidef hcp hX, ?_, ?_⟩
  · rw [noise_tracePreserving hd B hB t X, htr]
  · intro a i
    rw [noise_measurement B hB, htr]

end MUBCP

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix
namespace MUBCP

noncomputable def totalChoi {d k : ℕ} (B : Fin k → Mat d) :=
  ∑ a, choi (dephase (B a))

noncomputable def combinedProjection {d k : ℕ} (B : Fin k → Mat d) :=
  totalChoi B - (((k : ℂ) - 1) / (d : ℂ)) • omegaGram d

theorem choi_dephase_hermitian {d : ℕ} (U : Mat d) :
    (choi (dephase U)).IsHermitian := by
  rw [choi_dephase_factor]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).isHermitian

theorem omegaGram_hermitian {d : ℕ} : (omegaGram d).IsHermitian :=
  (Matrix.posSemidef_vecMulVec_self_star (omega d)).isHermitian

theorem omega_choi_dephase {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) :
    omegaGram d * choi (dephase U) = omegaGram d := by
  have h := congrArg Matrix.conjTranspose (choi_dephase_omega U hU)
  simpa only [Matrix.conjTranspose_mul, (choi_dephase_hermitian U).eq,
    omegaGram_hermitian.eq] using h

theorem totalChoi_omega {d k : ℕ} (B : Fin k → Mat d) (hB : IsMUBFamily B) :
    totalChoi B * omegaGram d = (k : ℂ) • omegaGram d := by
  simp only [totalChoi, Matrix.sum_mul, choi_dephase_omega _ (hB.1 _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul ℂ]

theorem omega_totalChoi {d k : ℕ} (B : Fin k → Mat d) (hB : IsMUBFamily B) :
    omegaGram d * totalChoi B = (k : ℂ) • omegaGram d := by
  simp only [totalChoi, Matrix.mul_sum, omega_choi_dephase _ (hB.1 _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul ℂ]

theorem totalChoi_sq {d k : ℕ} (B : Fin k → Mat d) (hB : IsMUBFamily B) :
    totalChoi B * totalChoi B = totalChoi B +
      ((k : ℂ) * ((k : ℂ) - 1) / (d : ℂ)) • omegaGram d := by
  have hprod (a b : Fin k) :
      choi (dephase (B a)) * choi (dephase (B b)) =
        if a = b then choi (dephase (B a)) else (1 / (d : ℂ)) • omegaGram d := by
    by_cases h : a = b
    · subst b
      simp [choi_dephase_idempotent _ (hB.1 _)]
    · rw [if_neg h]
      exact choi_dephase_cross _ _ (hB.1 _) (hB.1 _) (hB.2 a b h)
  have hs (a : Fin k) :
      (∑ b, choi (dephase (B a)) * choi (dephase (B b))) =
      choi (dephase (B a)) + ((k : ℂ) - 1) • ((1 / (d : ℂ)) • omegaGram d) := by
    simp_rw [hprod]
    calc
      _ = ∑ b : Fin k, ((if a = b then
          choi (dephase (B a)) - (1 / (d : ℂ)) • omegaGram d else 0) +
          (1 / (d : ℂ)) • omegaGram d) := by
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> abel
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [sub_smul, one_smul, Nat.cast_smul_eq_nsmul ℂ]
        abel
  simp only [totalChoi, Matrix.sum_mul, Matrix.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  ext p q
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem combinedProjection_hermitian {d k : ℕ} (B : Fin k → Mat d) :
    (combinedProjection B).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · exact isSelfAdjoint_sum _ (fun a _ => choi_dephase_hermitian (B a))
  · exact omegaGram_hermitian.smul (by simp [IsSelfAdjoint])

theorem combinedProjection_idempotent {d k : ℕ} (hd : (d : ℂ) ≠ 0)
    (B : Fin k → Mat d) (hB : IsMUBFamily B) :
    combinedProjection B * combinedProjection B = combinedProjection B := by
  simp only [combinedProjection, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, totalChoi_sq B hB,
    totalChoi_omega B hB, omega_totalChoi B hB, omegaGram_sq]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  <;> ring

theorem complement_combinedProjection_posSemidef {d k : ℕ} (hd : (d : ℂ) ≠ 0)
    (B : Fin k → Mat d) (hB : IsMUBFamily B) :
    (1 - combinedProjection B).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (1 - combinedProjection B)
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    (combinedProjection_hermitian B).eq, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, combinedProjection_idempotent hd B hB,
    sub_self, sub_zero] using h

theorem choi_noise_positive_decomposition {d k : ℕ} (hd : (d : ℂ) ≠ 0)
    (B : Fin k → Mat d) (t : ℝ) :
    choi (noise B t) =
      ((1 + t * ((k : ℝ) - 1)) / (d : ℝ) - t) •
        (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
      t • (1 - combinedProjection B) +
      (t * ((d : ℝ) + 1 - (k : ℝ)) / (d : ℝ)) • omegaGram d := by
  rw [choi_noise, choi_identity, choi_depolarize]
  ext p q
  simp only [combinedProjection, totalChoi, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, Matrix.sum_apply]
  field_simp
  <;> ring

theorem noise_completelyPositive_of_bound {d k : ℕ} (hd : 0 < d)
    (hkd : k ≤ d) (B : Fin k → Mat d) (hB : IsMUBFamily B)
    (t : ℝ) (ht : 0 ≤ t) (hbound : t ≤ 1 / ((d : ℝ) + 1 - (k : ℝ))) :
    CompletelyPositive (noise B t) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hkdR : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkd
  have hden : 0 < (d : ℝ) + 1 - (k : ℝ) := by linarith
  have hc : 0 ≤ (1 + t * ((k : ℝ) - 1)) / (d : ℝ) - t := by
    rw [sub_nonneg, le_div_iff₀ hdR]
    have hb := (le_div_iff₀ hden).mp hbound
    nlinarith
  have hz : 0 ≤ t * ((d : ℝ) + 1 - (k : ℝ)) / (d : ℝ) :=
    div_nonneg (mul_nonneg ht hden.le) hdR.le
  apply (noise_cp_iff_choi B t).mpr
  rw [choi_noise_positive_decomposition hdC]
  exact ((Matrix.PosSemidef.one.smul hc).add
    ((complement_combinedProjection_posSemidef hdC B hB).smul ht)).add
    ((Matrix.posSemidef_vecMulVec_self_star (omega d)).smul hz)

end MUBCP

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix MUBCP

namespace CompleteMUBFiveMoment

/-- Seven pairwise mutually unbiased orthonormal bases in dimension six fill
the whole traceless operator space.  This is the Choi-matrix form of the
complete-MUB dephasing-frame identity. -/
theorem complete_mub_totalChoi
    (B : Fin 7 → Mat 6) (hB : IsMUBFamily B) :
    totalChoi B = 1 + omegaGram 6 := by
  have htrD (a : Fin 7) :
      Matrix.trace (choi (dephase (B a))) = (6 : ℂ) := by
    rw [choi_dephase_factor, Matrix.trace_mul_comm,
      lifted_isometry _ (hB.1 a)]
    simp
  have htrK : Matrix.trace (omegaGram 6) = (6 : ℂ) := by
    simp [omegaGram, omega, Matrix.trace, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type]
  have htrP : Matrix.trace (combinedProjection B) = (36 : ℂ) := by
    simp only [combinedProjection, Matrix.trace_sub, totalChoi,
      Matrix.trace_sum, Matrix.trace_smul]
    simp_rw [htrD]
    rw [htrK]
    norm_num
  have htrC : Matrix.trace (1 - combinedProjection B) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_one, htrP]
    norm_num
  have hpos : (1 - combinedProjection B).PosSemidef :=
    complement_combinedProjection_posSemidef (by norm_num) B hB
  have hzero : 1 - combinedProjection B = 0 :=
    (hpos.trace_eq_zero_iff).mp htrC
  have hP : combinedProjection B = 1 := (sub_eq_zero.mp hzero).symm
  rw [combinedProjection] at hP
  norm_num at hP
  exact (sub_eq_iff_eq_add.mp hP)

/-- Construction-independent complete-MUB dephasing identity in dimension six:
the seven basis dephasings are the identity channel plus the trace channel. -/
theorem complete_mub_dephasing_frame
    (B : Fin 7 → Mat 6) (hB : IsMUBFamily B) (X : Mat 6) :
    (∑ a, dephase (B a) X) = X + Matrix.trace X • (1 : Mat 6) := by
  let L : Mat 6 →ₗ[ℂ] Mat 6 := ∑ a, dephaseLinear (B a)
  let R : Mat 6 →ₗ[ℂ] Mat 6 :=
    LinearMap.id + (6 : ℂ) • depolarizeLinear 6
  have hchoiL : choi L = totalChoi B := by
    ext p q
    change (∑ a, dephase (B a) (Matrix.single p.1 q.1 1) p.2 q.2) =
      (∑ a, choi (dephase (B a))) p q
    simp only [Matrix.sum_apply, choi]
  have hchoiR : choi R = 1 + omegaGram 6 := by
    calc
      choi R =
          choi (fun Y : Mat 6 => Y) +
            (6 : ℂ) • choi (depolarize 6) := by
        ext p q
        change
          ((Matrix.single p.1 q.1 1 : Mat 6) +
            (6 : ℂ) • depolarize 6 (Matrix.single p.1 q.1 1)) p.2 q.2 =
          (choi (fun Y : Mat 6 => Y) +
            (6 : ℂ) • choi (depolarize 6)) p q
        rfl
      _ = omegaGram 6 +
          (6 : ℂ) • ((1 / (6 : ℂ)) •
            (1 : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℂ)) := by
        rw [choi_identity, choi_depolarize]
        norm_num
      _ = 1 + omegaGram 6 := by
        rw [show (6 : ℂ) • ((1 / (6 : ℂ)) •
            (1 : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℂ)) = 1 by
          rw [smul_smul]
          norm_num]
        abel
  have hLR : L = R := linear_eq_of_choi_eq L R <|
    hchoiL.trans ((complete_mub_totalChoi B hB).trans hchoiR.symm)
  have happ := congrArg (fun T : Mat 6 →ₗ[ℂ] Mat 6 => T X) hLR
  have hs : (6 : ℂ) * (Matrix.trace X / ((6 : ℕ) : ℂ)) = Matrix.trace X := by
    field_simp
    <;> ring
  change (∑ a, dephase (B a) X) =
    X + (6 : ℂ) • depolarize 6 X at happ
  simp only [depolarize, smul_smul, hs] at happ
  exact happ

/-- Projectors onto two columns of one unitary basis are orthogonal idempotents. -/
theorem projector_mul_same_basis {d : ℕ} (V : Mat d)
    (hV : Vᴴ * V = 1) (i j : Fin d) :
    projector V i * projector V j =
      if i = j then projector V i else 0 := by
  unfold projector
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd :
      (fun x => star (V x i)) ⬝ᵥ (fun x => V x j) =
        if i = j then 1 else 0 := by
    have h := congrArg (fun A : Mat d => A i j) hV
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, dotProduct] using h
  rw [hd]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- A rank-one dephasing keeps only the diagonal block selected by a
rightmost projector from its own basis. -/
theorem dephase_mul_right_projector {d : ℕ} (V : Mat d)
    (hV : Vᴴ * V = 1) (j : Fin d) (X : Mat d) :
    dephase V (X * projector V j) =
      Matrix.trace (projector V j * X) • projector V j := by
  classical
  unfold dephase
  have hdiag :
      Matrix.trace (projector V j * (X * projector V j)) =
        Matrix.trace (projector V j * X) := by
    have hm : projector V j * projector V j = projector V j := by
      simpa using projector_mul_same_basis V hV j j
    rw [show projector V j * (X * projector V j) =
      projector V j * X * projector V j by noncomm_ring,
      Matrix.trace_mul_cycle]
    rw [hm]
  rw [← hdiag]
  apply Finset.sum_eq_single j
  · intro i hi hij
    have hm : projector V j * projector V i = 0 := by
      rw [projector_mul_same_basis V hV]
      simp [Ne.symm hij]
    have ht :
        Matrix.trace (projector V i * (X * projector V j)) = 0 := by
      rw [show projector V i * (X * projector V j) =
        projector V i * X * projector V j by noncomm_ring,
        Matrix.trace_mul_cycle]
      rw [hm]
      simp
    rw [ht]
    simp
  · simp

/-- The analogous left-projector form. -/
theorem dephase_mul_left_projector {d : ℕ} (V : Mat d)
    (hV : Vᴴ * V = 1) (j : Fin d) (X : Mat d) :
    dephase V (projector V j * X) =
      Matrix.trace (projector V j * X) • projector V j := by
  classical
  unfold dephase
  have hdiag :
      Matrix.trace (projector V j * (projector V j * X)) =
        Matrix.trace (projector V j * X) := by
    have hm : projector V j * projector V j = projector V j := by
      simpa using projector_mul_same_basis V hV j j
    rw [show projector V j * (projector V j * X) =
      (projector V j * projector V j) * X by noncomm_ring, hm]
  rw [← hdiag]
  apply Finset.sum_eq_single j
  · intro i hi hij
    have hm : projector V i * projector V j = 0 := by
      rw [projector_mul_same_basis V hV]
      simp [hij]
    rw [show projector V i * (projector V j * X) =
      (projector V i * projector V j) * X by noncomm_ring, hm]
    simp
  · simp

/-- Sandwiching any matrix by a column projector extracts its corresponding
rank-one coefficient. -/
theorem projector_sandwich {d : ℕ} (V : Mat d) (j : Fin d) (X : Mat d) :
    projector V j * X * projector V j =
      Matrix.trace (projector V j * X) • projector V j := by
  unfold projector
  change
    (Matrix.vecMulVec (fun i => V i j) (fun i => star (V i j)) * X) *
        Matrix.vecMulVec (fun i => V i j) (fun i => star (V i j)) =
      Matrix.trace
          (Matrix.vecMulVec (fun i => V i j) (fun i => star (V i j)) * X) •
        Matrix.vecMulVec (fun i => V i j) (fun i => star (V i j))
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  rw [dotProduct_comm]
  simp
/-- Rank-one dephasing is equivalently the sum of projector sandwiches. -/
theorem dephase_eq_sum_sandwich {d : ℕ} (V : Mat d)
    (X : Mat d) :
    dephase V X = ∑ j, projector V j * X * projector V j := by
  classical
  unfold dephase
  apply Finset.sum_congr rfl
  intro j hj
  exact (projector_sandwich V j X).symm

/-- The local noncommutative reduction used by the crossed fifth-word class.
The matrix `U` is the sum of the dephasings over all bases except the two
bases containing `P` and `R`. -/
theorem crossed_local_of_excluded_dephasing
    (P R U : Mat 6)
    (hR2 : R * R = R)
    (hRPR : R * P * R = (1 / 6 : ℂ) • R)
    (hU : U = R * P + (1 / 6 : ℂ) • 1 -
      (1 / 6 : ℂ) • P - (1 / 6 : ℂ) • R) :
    U * R = (1 / 6 : ℂ) • (R - P * R) := by
  rw [hU]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hR2]
  rw [show (R * P) * R = R * P * R by simp only [Matrix.mul_assoc], hRPR]
  module

/-- Summing the local crossed reduction over one complete six-outcome basis
collapses it to `1 - P`. -/
theorem sum_crossed_local_dimension_six
    (P : Mat 6) (R : Fin 6 → Fin 6 → Mat 6)
    (hR : ∀ z, ∑ c, R z c = 1) :
    (∑ z, ∑ c, (1 / 6 : ℂ) • (R z c - P * R z c)) = 1 - P := by
  calc
    _ = ∑ z : Fin 6, (1 / 6 : ℂ) •
        ((∑ c, R z c) - P * (∑ c, R z c)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← Matrix.mul_sum]
    _ = ∑ _z : Fin 6, (1 / 6 : ℂ) • (1 - P) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hR, Matrix.mul_one]
    _ = 1 - P := by
      simp only [Finset.sum_const, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      rw [smul_smul]
      norm_num

/-- The exact ordered aggregate of the residual fifth-word orbit.
The outer order is z then y distinct from z. -/
theorem complete_mub_crossed_sum_ordered
    (U : Mat 6) (B : Fin 6 → Mat 6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ z, ∑ c, ∑ y ∈ Finset.univ.erase z, ∑ b,
      projector (B y) b * projector (B z) c * projector U a *
      projector (B y) b * projector (B z) c) =
      1 - projector U a := by
  classical
  let P : Mat 6 := projector U a
  let R : Fin 6 → Fin 6 → Mat 6 := fun z c => projector (B z) c
  have hU : Uᴴ * U = 1 := by
    simpa using hMUB.1 (0 : Fin 7)
  have hB (z : Fin 6) : (B z)ᴴ * B z = 1 := by
    simpa using hMUB.1 (Fin.succ z)
  have hRP (z c : Fin 6) :
      Matrix.trace (R z c * P) = (1 / 6 : ℂ) := by
    dsimp [R, P]
    rw [projector_overlap_general]
    have hne : (Fin.succ z : Fin 7) ≠ 0 := Fin.succ_ne_zero z
    have hm := hMUB.2 (Fin.succ z) 0 hne c a
    have hm' := congrArg (fun r : ℝ => (r : ℂ)) hm
    norm_num at hm' ⊢
    simpa only [Fin.cons_succ, Fin.cons_zero] using hm'
  have hDA (z c : Fin 6) :
      dephase U (R z c * P) = (1 / 6 : ℂ) • P := by
    dsimp [P]
    rw [dephase_mul_right_projector U hU a (R z c),
      Matrix.trace_mul_comm, hRP]
  have hDR (z c : Fin 6) :
      dephase (B z) (R z c * P) = (1 / 6 : ℂ) • R z c := by
    dsimp [R]
    rw [dephase_mul_left_projector (B z) (hB z) c P, hRP]
  have hlocal (z c : Fin 6) :
      (∑ y ∈ Finset.univ.erase z, dephase (B y) (R z c * P)) * R z c =
        (1 / 6 : ℂ) • (R z c - P * R z c) := by
    have hall := complete_mub_dephasing_frame (Fin.cons U B) hMUB (R z c * P)
    rw [Fin.sum_univ_succ] at hall
    simp only [Fin.cons_zero, Fin.cons_succ] at hall
    rw [hDA, hRP] at hall
    have hrest :
        (∑ y, dephase (B y) (R z c * P)) =
          R z c * P + (1 / 6 : ℂ) • 1 - (1 / 6 : ℂ) • P := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hall
    have herase :
        (∑ y ∈ Finset.univ.erase z, dephase (B y) (R z c * P)) =
          R z c * P + (1 / 6 : ℂ) • 1 -
            (1 / 6 : ℂ) • P - (1 / 6 : ℂ) • R z c := by
      have he := Finset.sum_erase_add
        (Finset.univ : Finset (Fin 6))
        (fun y : Fin 6 => dephase (B y) (R z c * P))
        (Finset.mem_univ z)
      rw [hDR, hrest] at he
      rw [eq_sub_iff_add_eq]
      exact he
    have hR2 : R z c * R z c = R z c := by
      dsimp [R]
      simpa using projector_mul_same_basis (B z) (hB z) c c
    have hRPR :
        R z c * P * R z c = (1 / 6 : ℂ) • R z c := by
      rw [projector_sandwich]
      exact congrArg (fun t : ℂ => t • R z c) (hRP z c)
    exact crossed_local_of_excluded_dephasing
      P (R z c)
        (∑ y ∈ Finset.univ.erase z, dephase (B y) (R z c * P))
      hR2 hRPR herase
  change
    (∑ z, ∑ c, ∑ y ∈ Finset.univ.erase z, ∑ b,
      projector (B y) b * R z c * P *
      projector (B y) b * R z c) = 1 - P
  calc
    _ = ∑ z, ∑ c,
        (∑ y ∈ Finset.univ.erase z, dephase (B y) (R z c * P)) * R z c := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      rw [dephase_eq_sum_sandwich, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      noncomm_ring
    _ = ∑ z, ∑ c, (1 / 6 : ℂ) • (R z c - P * R z c) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro c hc
      exact hlocal z c
    _ = 1 - P := by
      apply sum_crossed_local_dimension_six
      intro z
      dsimp [R]
      exact projector_sum_general (B z) (hB z)

end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment

open Matrix

abbrev ReducerSymbol := Option (Fin 6)
abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℂ

def reducerStepD : List ReducerSymbol → Option (List ReducerSymbol)
  | a :: b :: t => if a = b then some (a :: t)
      else (reducerStepD (b :: t)).map (List.cons a)
  | _ => none

def reducerStepSAt (whole : List ReducerSymbol) :
    List ReducerSymbol → Option (List ReducerSymbol)
  | [] => none
  | none :: t => (reducerStepSAt whole t).map (List.cons none)
  | some y :: t => if whole.count (some y) = 1 then some t
      else (reducerStepSAt whole t).map (List.cons (some y))

def reducerStepS (w : List ReducerSymbol) := reducerStepSAt w w

def reducerStepX : List ReducerSymbol → Option (List ReducerSymbol)
  | a :: b :: c :: t => if a = c ∧ a ≠ b then some (a :: t)
      else (reducerStepX (b :: c :: t)).map (List.cons a)
  | _ => none

/-- First component counts the `1/6` factors introduced by S and X. -/
def reduceProjectorWord : Nat → List ReducerSymbol → Nat × List ReducerSymbol
  | 0, w => (0, w)
  | fuel + 1, w =>
      match reducerStepD w with
      | some w' => reduceProjectorWord fuel w'
      | none => match reducerStepS w with
        | some w' => let r := reduceProjectorWord fuel w'; (r.1 + 1, r.2)
        | none => match reducerStepX w with
          | some w' => let r := reduceProjectorWord fuel w'; (r.1 + 1, r.2)
          | none => (0, w)

def evalReducerWord (V : ReducerSymbol → Mat6) : List ReducerSymbol → Mat6
  | [] => 1
  | s :: w => V s * evalReducerWord V w

def completeFamilySymbolValue (P : Mat6) (Q : Fin 6 → Mat6) :
    ReducerSymbol → Mat6
  | none => P
  | some y => Q y

lemma completeFamilySymbolValue_idem (P : Mat6) (Q : Fin 6 → Mat6)
    (hP : P * P = P) (hQ : ∀ y, Q y * Q y = Q y) :
    ∀ s, completeFamilySymbolValue P Q s *
      completeFamilySymbolValue P Q s = completeFamilySymbolValue P Q s := by
  intro s
  cases s with
  | none => exact hP
  | some y => exact hQ y

lemma completeFamilySymbolValue_sandwich (P : Mat6) (Q : Fin 6 → Mat6)
    (hPQ : ∀ y, P * Q y * P = (1 / 6 : ℂ) • P)
    (hQP : ∀ y, Q y * P * Q y = (1 / 6 : ℂ) • Q y)
    (hQQ : ∀ y z, y ≠ z → Q y * Q z * Q y = (1 / 6 : ℂ) • Q y) :
    ∀ s t, s ≠ t →
      completeFamilySymbolValue P Q s * completeFamilySymbolValue P Q t *
        completeFamilySymbolValue P Q s =
      (1 / 6 : ℂ) • completeFamilySymbolValue P Q s := by
  intro s t hst
  cases s with
  | none =>
      cases t with
      | none => exact (hst rfl).elim
      | some y => exact hPQ y
  | some y =>
      cases t with
      | none => exact hQP y
      | some z => exact hQQ y z (fun hyz => hst (congrArg some hyz))

lemma reducerStepD_sound (V : ReducerSymbol → Mat6)
    (hidem : ∀ s, V s * V s = V s) {w w'}
    (h : reducerStepD w = some w') :
    evalReducerWord V w = evalReducerWord V w' := by
  induction w generalizing w' with
  | nil => simp [reducerStepD] at h
  | cons a w ih =>
      cases w with
      | nil => simp [reducerStepD] at h
      | cons b t =>
          by_cases hab : a = b
          · subst b
            simp only [reducerStepD, ↓reduceIte] at h
            injection h with hw
            subst w'
            simp only [evalReducerWord]
            rw [← Matrix.mul_assoc, hidem]
          · rw [reducerStepD, if_neg hab] at h
            cases hs : reducerStepD (b :: t) with
            | none => simp [hs] at h
            | some u =>
                have hu := ih (w' := u) hs
                simp only [hs, Option.map_some, Option.some.injEq] at h
                subst w'
                simpa only [evalReducerWord] using
                  congrArg (fun X : Mat6 => V a * X) hu

lemma reducerStepX_sound (V : ReducerSymbol → Mat6)
    (hcross : ∀ s t, s ≠ t →
      V s * V t * V s = (1 / 6 : ℂ) • V s) {w w'}
    (h : reducerStepX w = some w') :
    evalReducerWord V w = (1 / 6 : ℂ) • evalReducerWord V w' := by
  induction w generalizing w' with
  | nil => simp [reducerStepX] at h
  | cons a w ih =>
      cases w with
      | nil => simp [reducerStepX] at h
      | cons b t =>
          cases t with
          | nil => simp [reducerStepX] at h
          | cons c t =>
              by_cases hacb : a = c ∧ a ≠ b
              · rcases hacb with ⟨rfl, hab⟩
                rw [reducerStepX, if_pos ⟨rfl, hab⟩] at h
                injection h with hw
                subst w'
                simp only [evalReducerWord]
                calc
                  V a * (V b * (V a * evalReducerWord V t)) =
                      (V a * V b * V a) * evalReducerWord V t := by
                        simp only [Matrix.mul_assoc]
                  _ = ((1 / 6 : ℂ) • V a) * evalReducerWord V t := by
                        rw [hcross a b hab]
                  _ = (1 / 6 : ℂ) • (V a * evalReducerWord V t) := by
                        rw [Matrix.smul_mul]
              · rw [reducerStepX, if_neg hacb] at h
                cases hs : reducerStepX (b :: c :: t) with
                | none => simp [hs] at h
                | some u =>
                    have hu := ih (w' := u) hs
                    simp only [hs, Option.map_some, Option.some.injEq] at h
                    subst w'
                    simpa only [evalReducerWord, Matrix.mul_smul] using
                      congrArg (fun X : Mat6 => V a * X) hu

private lemma reducerStepSAt_spec (whole xs out : List ReducerSymbol)
    (h : reducerStepSAt whole xs = some out) :
    ∃ pre y post, xs = pre ++ some y :: post ∧ out = pre ++ post ∧
      whole.count (some y) = 1 := by
  induction xs generalizing out with
  | nil => simp [reducerStepSAt] at h
  | cons s xs ih =>
      cases s with
      | none =>
          rw [reducerStepSAt] at h
          cases hs : reducerStepSAt whole xs with
          | none => simp [hs] at h
          | some u =>
              obtain ⟨pre, y, post, hxs, hu, hc⟩ := ih u hs
              simp only [hs, Option.map_some, Option.some.injEq] at h
              subst out
              refine ⟨none :: pre, y, post, ?_, ?_, hc⟩
              · simp [hxs]
              · simp [hu]
      | some x =>
          by_cases hc : whole.count (some x) = 1
          · rw [reducerStepSAt, if_pos hc] at h
            injection h with hout
            subst out
            exact ⟨[], x, xs, by simp, by simp, hc⟩
          · rw [reducerStepSAt, if_neg hc] at h
            cases hs : reducerStepSAt whole xs with
            | none => simp [hs] at h
            | some u =>
                obtain ⟨pre, y, post, hxs, hu, hy⟩ := ih u hs
                simp only [hs, Option.map_some, Option.some.injEq] at h
                subst out
                refine ⟨some x :: pre, y, post, ?_, ?_, hy⟩
                · simp [hxs]
                · simp [hu]

lemma reducerStepS_spec {w w' : List ReducerSymbol}
    (h : reducerStepS w = some w') :
    ∃ pre y post, w = pre ++ some y :: post ∧ w' = pre ++ post ∧
      some y ∉ pre ∧ some y ∉ post := by
  have hs : reducerStepSAt w w = some w' := by
    simpa [reducerStepS] using h
  obtain ⟨pre, y, post, hw, hw', hc⟩ := reducerStepSAt_spec w w w' hs
  have hc' := hc
  rw [hw] at hc'
  simp [List.count_append] at hc'
  have hp : some y ∉ pre := by
    intro hm
    have hpos : 0 < pre.count (some y) := List.count_pos_iff.mpr hm
    omega
  have hpost : some y ∉ post := by
    intro hm
    have hpos : 0 < post.count (some y) := List.count_pos_iff.mpr hm
    omega
  exact ⟨pre, y, post, hw, hw', hp, hpost⟩

/- Finite histogram certificates are being split into bounded files; this
temporary comment isolates the semantic reducer core for kernel checking.
def zeroAnchorWord (v : Fin 5 → Fin 6) : List ReducerSymbol :=
  List.ofFn (fun i => some (v i))

def zeroAnchorHeadWord (h : Fin 6) (v : Fin 4 → Fin 6) : List ReducerSymbol :=
  some h :: List.ofFn (fun i => some (v i))

def zeroAnchorHeadExponentCount (h : Fin 6) (e : Nat) : Nat :=
  ((Finset.univ : Finset (Fin 4 → Fin 6)).filter
    (fun v => reduceProjectorWord 5 (zeroAnchorHeadWord h v) = (e, []))).card

set_option maxRecDepth 100000 in
theorem zero_anchor_head0_counts :
    zeroAnchorHeadExponentCount 0 1 = 1 ∧
    zeroAnchorHeadExponentCount 0 2 = 50 ∧
    zeroAnchorHeadExponentCount 0 3 = 425 ∧
    zeroAnchorHeadExponentCount 0 4 = 700 ∧
    zeroAnchorHeadExponentCount 0 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 0 v)).2 = []) := by decide

set_option maxRecDepth 100000 in
theorem zero_anchor_head1_counts :
    zeroAnchorHeadExponentCount 1 1 = 1 ∧
    zeroAnchorHeadExponentCount 1 2 = 50 ∧
    zeroAnchorHeadExponentCount 1 3 = 425 ∧
    zeroAnchorHeadExponentCount 1 4 = 700 ∧
    zeroAnchorHeadExponentCount 1 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 1 v)).2 = []) := by decide

set_option maxRecDepth 100000 in
theorem zero_anchor_head2_counts :
    zeroAnchorHeadExponentCount 2 1 = 1 ∧
    zeroAnchorHeadExponentCount 2 2 = 50 ∧
    zeroAnchorHeadExponentCount 2 3 = 425 ∧
    zeroAnchorHeadExponentCount 2 4 = 700 ∧
    zeroAnchorHeadExponentCount 2 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 2 v)).2 = []) := by decide

set_option maxRecDepth 100000 in
theorem zero_anchor_head3_counts :
    zeroAnchorHeadExponentCount 3 1 = 1 ∧
    zeroAnchorHeadExponentCount 3 2 = 50 ∧
    zeroAnchorHeadExponentCount 3 3 = 425 ∧
    zeroAnchorHeadExponentCount 3 4 = 700 ∧
    zeroAnchorHeadExponentCount 3 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 3 v)).2 = []) := by decide

set_option maxRecDepth 100000 in
theorem zero_anchor_head4_counts :
    zeroAnchorHeadExponentCount 4 1 = 1 ∧
    zeroAnchorHeadExponentCount 4 2 = 50 ∧
    zeroAnchorHeadExponentCount 4 3 = 425 ∧
    zeroAnchorHeadExponentCount 4 4 = 700 ∧
    zeroAnchorHeadExponentCount 4 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 4 v)).2 = []) := by decide

set_option maxRecDepth 100000 in
theorem zero_anchor_head5_counts :
    zeroAnchorHeadExponentCount 5 1 = 1 ∧
    zeroAnchorHeadExponentCount 5 2 = 50 ∧
    zeroAnchorHeadExponentCount 5 3 = 425 ∧
    zeroAnchorHeadExponentCount 5 4 = 700 ∧
    zeroAnchorHeadExponentCount 5 5 = 120 ∧
    (∀ v : Fin 4 → Fin 6,
      (reduceProjectorWord 5 (zeroAnchorHeadWord 5 v)).2 = []) := by decide

def oneAnchorWord (p : Fin 5) (v : Fin 4 → Fin 6) : List ReducerSymbol :=
  List.ofFn (fun i => if i = p then none else some (v (p.predAbove i)))

def oneAnchorResidueCount (p : Fin 5) (e : Nat) (r : List ReducerSymbol) : Nat :=
  ((Finset.univ : Finset (Fin 4 → Fin 6)).filter
    (fun v => reduceProjectorWord 5 (oneAnchorWord p v) = (e, r))).card

def centralCrossed (v : Fin 4 → Fin 6) : Prop :=
  v 0 = v 2 ∧ v 1 = v 3 ∧ v 0 ≠ v 1

set_option maxRecDepth 100000 in
theorem central_crossed_count :
    ((Finset.univ : Finset (Fin 4 → Fin 6)).filter centralCrossed).card = 30 := by decide
set_option maxRecDepth 100000 in
theorem anchor_pos0_counts :
    oneAnchorResidueCount 0 1 [none] = 6 ∧ oneAnchorResidueCount 0 2 [none] = 180 ∧
    oneAnchorResidueCount 0 3 [none] = 750 ∧ oneAnchorResidueCount 0 4 [none] = 360 := by decide
set_option maxRecDepth 100000 in
theorem anchor_pos4_counts :
    oneAnchorResidueCount 4 1 [none] = 6 ∧ oneAnchorResidueCount 4 2 [none] = 180 ∧
    oneAnchorResidueCount 4 3 [none] = 750 ∧ oneAnchorResidueCount 4 4 [none] = 360 := by decide
set_option maxRecDepth 100000 in
theorem anchor_pos1_counts :
    oneAnchorResidueCount 1 2 [none] = 30 ∧ oneAnchorResidueCount 1 3 [none] = 390 ∧
    oneAnchorResidueCount 1 4 [none] = 360 ∧ oneAnchorResidueCount 1 2 [] = 6 ∧
    oneAnchorResidueCount 1 3 [] = 150 ∧ oneAnchorResidueCount 1 4 [] = 360 := by decide
set_option maxRecDepth 100000 in
theorem anchor_pos3_counts :
    oneAnchorResidueCount 3 2 [none] = 30 ∧ oneAnchorResidueCount 3 3 [none] = 390 ∧
    oneAnchorResidueCount 3 4 [none] = 360 ∧ oneAnchorResidueCount 3 2 [] = 6 ∧
    oneAnchorResidueCount 3 3 [] = 150 ∧ oneAnchorResidueCount 3 4 [] = 360 := by decide
set_option maxRecDepth 100000 in
theorem anchor_pos2_ordinary_counts :
    oneAnchorResidueCount 2 2 [none] = 30 ∧ oneAnchorResidueCount 2 3 [none] = 240 ∧
    oneAnchorResidueCount 2 4 [none] = 360 ∧ oneAnchorResidueCount 2 2 [] = 6 ∧
    oneAnchorResidueCount 2 3 [] = 150 ∧ oneAnchorResidueCount 2 4 [] = 480 := by decide

-/

end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment

def allWord {n : Nat} (v : Fin n → ReducerSymbol) : List ReducerSymbol :=
  List.ofFn v

def allWordCount (n e : Nat) (r : List ReducerSymbol) : Nat :=
  ((Finset.univ : Finset (Fin n → ReducerSymbol)).filter
    (fun v => reduceProjectorWord n (allWord v) = (e, r))).card

def isCrossedResidue : List ReducerSymbol → Bool
  | [some y, some z, none, some y', some z'] =>
      decide (y = y' ∧ z = z' ∧ y ≠ z)
  | _ => false

def allWordCrossedCount (n e : Nat) : Nat :=
  ((Finset.univ : Finset (Fin n → ReducerSymbol)).filter
    (fun v => let out := reduceProjectorWord n (allWord v)
      out.1 = e ∧ isCrossedResidue out.2)).card

end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
theorem all_word_1_counts : allWordCount 1 0 [none] = 1 ∧ allWordCount 1 1 [] = 6 := by decide
theorem all_word_1_exhaustive : ∀ v : Fin 1 → ReducerSymbol, let r := (reduceProjectorWord 1 (allWord v)).2; r=[] ∨ r=[none] := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in theorem all_word_2_counts : allWordCount 2 0 [none]=1 ∧ allWordCount 2 1 [none]=12 ∧ allWordCount 2 1 []=6 ∧ allWordCount 2 2 []=30 := by decide
set_option maxRecDepth 100000 in theorem all_word_2_exhaustive : ∀ v : Fin 2 → ReducerSymbol, let r := (reduceProjectorWord 2 (allWord v)).2; r=[] ∨ r=[none] := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in theorem all_word_3_counts : allWordCount 3 0 [none]=1 ∧ allWordCount 3 1 [none]=30 ∧ allWordCount 3 2 [none]=90 ∧ allWordCount 3 1 []=6 ∧ allWordCount 3 2 []=96 ∧ allWordCount 3 3 []=120 := by decide
set_option maxRecDepth 100000 in theorem all_word_3_exhaustive : ∀ v : Fin 3 → ReducerSymbol, let r := (reduceProjectorWord 3 (allWord v)).2; r=[] ∨ r=[none] := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 1000000 in theorem all_word_4_counts : allWordCount 4 0 [none]=1 ∧ allWordCount 4 1 [none]=54 ∧ allWordCount 4 2 [none]=432 ∧ allWordCount 4 3 [none]=480 ∧ allWordCount 4 1 []=6 ∧ allWordCount 4 2 []=198 ∧ allWordCount 4 3 []=870 ∧ allWordCount 4 4 []=360 := by decide
set_option maxRecDepth 100000 in set_option maxHeartbeats 1000000 in theorem all_word_4_exhaustive : ∀ v : Fin 4 → ReducerSymbol, let r := (reduceProjectorWord 4 (allWord v)).2; r=[] ∨ r=[none] := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p0 : allWordCount 5 0 [none] = 1 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p1 : allWordCount 5 1 [none] = 84 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p2 : allWordCount 5 2 [none] = 1254 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p3 : allWordCount 5 3 [none] = 4020 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p4 : allWordCount 5 4 [none] = 1800 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_p5 : allWordCount 5 5 [none] = 0 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i0 : allWordCount 5 0 [] = 0 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i1 : allWordCount 5 1 [] = 6 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i2 : allWordCount 5 2 [] = 336 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i3 : allWordCount 5 3 [] = 3156 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i4 : allWordCount 5 4 [] = 5400 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_i5 : allWordCount 5 5 [] = 720 := by decide
end CompleteMUBFiveMoment

namespace CompleteMUBFiveMoment
set_option maxRecDepth 100000 in set_option maxHeartbeats 2000000 in theorem all_word_5_exhaustive :
    ∀ v : Fin 5 → ReducerSymbol,
      let out := reduceProjectorWord 5 (allWord v)
      out.2 = [] ∨ out.2 = [none] ∨
        (out = (0, allWord v) ∧ isCrossedResidue (allWord v)) := by decide
end CompleteMUBFiveMoment

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix MUBCP
open CompleteMUBFiveMoment

namespace CompleteMUBDegreeFiveCount

set_option maxHeartbeats 2000000

abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℂ

abbrev Assignment6 := Fin 6 → Fin 6

def anchoredSelectedSum
    (U : Mat6) (B : Fin 6 → Mat6) (a : Fin 6) (j : Assignment6) : Mat6 :=
  projector U a + ∑ y, projector (B y) (j y)

/-- Five adjacent copies of a projector collapse. -/
theorem idempotent_fifth_word (A : Mat6) (hA : A * A = A) :
    A * A * A * A * A = A := by
  rw [hA, hA, hA, hA]

/-- Sum out one projector in an arbitrary left/right word context. -/
theorem sum_insert_projector
    (Q : Fin 6 → Mat6) (hQ : ∑ b, Q b = 1) (L R : Mat6) :
    (∑ b, L * Q b * R) = L * R := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, hQ, mul_one]

/-- Normalized form of `sum_insert_projector`. -/
theorem normalized_sum_insert_projector
    (Q : Fin 6 → Mat6) (hQ : ∑ b, Q b = 1) (L R : Mat6) :
    (∑ b, (1 / 6 : ℂ) • (L * Q b * R)) =
      (1 / 6 : ℂ) • (L * R) := by
  rw [← Finset.smul_sum, sum_insert_projector Q hQ]

/-- The rank-one projectors of an orthonormal basis resolve the identity. -/
theorem mubcp_projector_sum (U : Mat6) (hU : Uᴴ * U = 1) :
    ∑ b, projector U b = 1 := by
  have hh : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  rw [← hh]
  ext i j
  simp [projector, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Every MUBCP rank-one projector is idempotent. -/
theorem mubcp_projector_idempotent (U : Mat6) (hU : Uᴴ * U = 1) (a : Fin 6) :
    projector U a * projector U a = projector U a := by
  ext i j
  have hd : (∑ k : Fin 6, star (U k a) * U k a) = 1 := by
    have h := congrArg (fun X : Mat6 => X a a) hU
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  simp only [projector, Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc
    (∑ k, (U i a * star (U k a)) * (U k a * star (U j a))) =
        U i a * (∑ k, star (U k a) * U k a) * star (U j a) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = U i a * star (U j a) := by rw [hd]; ring

/-- Compress an arbitrary matrix between two copies of a rank-one projector. -/
theorem mubcp_projector_compress (U : Mat6) (a : Fin 6) (X : Mat6) :
    projector U a * X * projector U a =
      Matrix.trace (projector U a * X) • projector U a := by
  unfold projector
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, Matrix.vecMulVec_smul, dotProduct_comm]

/-- Projector trace overlap is the squared transition-matrix entry. -/
theorem mubcp_projector_overlap (U V : Mat6) (a b : Fin 6) :
    Matrix.trace (projector U a * projector V b) =
      (Complex.normSq ((Uᴴ * V) a b) : ℂ) := by
  simp only [projector, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    map_mul, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Mutual unbiasedness turns every rank-one projector sandwich into scalar compression. -/
theorem mubcp_projector_sandwich (U V : Mat6) (a b : Fin 6)
    (hUV : Complex.normSq ((Uᴴ * V) a b) = 1 / 6) :
    projector U a * projector V b * projector U a =
      (1 / 6 : ℂ) • projector U a := by
  rw [mubcp_projector_compress, mubcp_projector_overlap, hUV]
  norm_num

/-- The concrete projector rules exported by a complete seven-basis MUB family. -/
lemma complete_family_projector_rules
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) :
    (Uᴴ * U = 1) ∧
    (∀ y, (B y)ᴴ * B y = 1) ∧
    (∀ a y b, projector U a * projector (B y) b * projector U a =
      (1 / 6 : ℂ) • projector U a) ∧
    (∀ a y b, projector (B y) b * projector U a * projector (B y) b =
      (1 / 6 : ℂ) • projector (B y) b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hMUB.1 (0 : Fin 7)
  · intro y
    simpa using hMUB.1 y.succ
  · intro a y b
    apply mubcp_projector_sandwich
    simpa using hMUB.2 (0 : Fin 7) y.succ (by
      intro h
      have hv := congrArg Fin.val h
      simp at hv) a b
  · intro a y b
    apply mubcp_projector_sandwich
    simpa using hMUB.2 y.succ (0 : Fin 7) (by simp) b a

/-- A selected projector occurring once can be summed out on the left. -/
theorem normalized_singleton_left
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ y, ∑ b, (1 / 6 : ℂ) • (Q y b * A * A * A * A)) = A := by
  calc
    _ = ∑ y, (1 / 6 : ℂ) • ((∑ b, Q y b) * A * A * A * A) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.smul_sum]
      congr 1
      simp only [Matrix.sum_mul]
    _ = ∑ _y : Fin 6, (1 / 6 : ℂ) • (A * A * A * A) := by simp [hQ]
    _ = A := by
      rw [show A * A * A * A = A by rw [hA, hA, hA]]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      rw [smul_smul]
      norm_num

/-- Split an assignment into its value at one basis and the five remaining values. -/
def splitAssignment (y : Fin 6) : Assignment6 ≃ (Fin 6 × (Fin 5 → Fin 6)) :=
  (Equiv.piCongrLeft' (fun _ : Fin 6 => Fin 6) (finSuccEquiv' y)).trans
    Equiv.piOptionEquivProd

@[simp] theorem splitAssignment_fst (y : Fin 6) (j : Assignment6) :
    (splitAssignment y j).1 = j y := by
  simp [splitAssignment, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

@[simp] theorem splitAssignment_snd (y : Fin 6) (j : Assignment6) (z : Fin 5) :
    (splitAssignment y j).2 z = j (y.succAbove z) := by
  simp [splitAssignment, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

theorem splitAssignment_symm_apply_ne (y z : Fin 6) (h : z ≠ y)
    (b b' : Fin 6) (r : Fin 5 → Fin 6) :
    (splitAssignment y).symm (b, r) z =
      (splitAssignment y).symm (b', r) z := by
  simp only [splitAssignment, Equiv.piCongrLeft',
    Equiv.piOptionEquivProd]
  have hn : (finSuccEquiv' y) z ≠ none := by
    intro hz
    apply h
    exact (finSuccEquiv'_eq_none.mp hz).symm
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
  simp [hq]

def evalAssignmentWord (P : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (j : Assignment6) : List ReducerSymbol → Mat6 :=
  evalReducerWord (fun s => match s with
    | none => P
    | some y => Q y (j y))

theorem evalAssignmentWord_split_independent
    (P : Mat6) (Q : Fin 6 → Fin 6 → Mat6) (y : Fin 6)
    (w : List ReducerSymbol) (hy : some y ∉ w)
    (b b' : Fin 6) (r : Fin 5 → Fin 6) :
    evalAssignmentWord P Q ((splitAssignment y).symm (b, r)) w =
      evalAssignmentWord P Q ((splitAssignment y).symm (b', r)) w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp only [List.mem_cons, not_or] at hy
      rcases hy with ⟨hsy, hyw⟩
      cases s with
      | none =>
          change P * evalAssignmentWord P Q ((splitAssignment y).symm (b, r)) w =
            P * evalAssignmentWord P Q ((splitAssignment y).symm (b', r)) w
          rw [ih hyw]
      | some z =>
          have hzy : z ≠ y := by
            intro h
            subst z
            exact hsy rfl
          change Q z ((splitAssignment y).symm (b, r) z) *
              evalAssignmentWord P Q ((splitAssignment y).symm (b, r)) w =
            Q z ((splitAssignment y).symm (b', r) z) *
              evalAssignmentWord P Q ((splitAssignment y).symm (b', r)) w
          rw [splitAssignment_symm_apply_ne y z hzy b b' r, ih hyw]

/-- Sum over assignments by the value at one chosen basis. -/
theorem sum_assignment_eval (y : Fin 6) (f : Fin 6 → Mat6) :
    (∑ j : Assignment6, f (j y)) =
      (6 ^ 5 : ℕ) • (∑ b : Fin 6, f b) := by
  calc
    (∑ j : Assignment6, f (j y)) =
        ∑ j : Assignment6, f ((splitAssignment y j).1) := by simp
    _ = ∑ p : Fin 6 × (Fin 5 → Fin 6), f p.1 :=
      (splitAssignment y).sum_comp (fun p => f p.1)
    _ = ∑ b : Fin 6, ∑ _r : (Fin 5 → Fin 6), f b := by
      rw [Fintype.sum_prod_type]
    _ = ∑ b : Fin 6, (6 ^ 5 : ℕ) • f b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
      norm_num [Fintype.card_fin]
    _ = (6 ^ 5 : ℕ) • (∑ b : Fin 6, f b) := by
      rw [Finset.smul_sum]

/-- If one basis label occurs in a word only once, summing its selected outcome
deletes that letter and contributes the normalized factor `1/6`. -/
theorem sum_assignment_singleton_delete
    (y : Fin 6) (Q : Fin 6 → Fin 6 → Mat6)
    (hQ : ∀ z, ∑ b, Q z b = 1)
    (L R : Assignment6 → Mat6)
    (hL : ∀ b b' r, L ((splitAssignment y).symm (b, r)) =
      L ((splitAssignment y).symm (b', r)))
    (hR : ∀ b b' r, R ((splitAssignment y).symm (b, r)) =
      R ((splitAssignment y).symm (b', r))) :
    (∑ j, L j * Q y (j y) * R j) =
      (1 / 6 : ℂ) • (∑ j, L j * R j) := by
  classical
  let E := splitAssignment y
  have heval (b : Fin 6) (r : Fin 5 → Fin 6) : E.symm (b, r) y = b := by
    simpa [E] using (splitAssignment_fst y (E.symm (b, r))).symm
  have horig :
      (∑ j, L j * Q y (j y) * R j) =
        ∑ r : Fin 5 → Fin 6, L (E.symm (0, r)) * R (E.symm (0, r)) := by
    calc
      _ = ∑ p : Fin 6 × (Fin 5 → Fin 6),
          L (E.symm p) * Q y (E.symm p y) * R (E.symm p) :=
            (E.symm.sum_comp _).symm
      _ = ∑ b : Fin 6, ∑ r : Fin 5 → Fin 6,
          L (E.symm (b, r)) * Q y b * R (E.symm (b, r)) := by
            rw [Fintype.sum_prod_type]
            simp_rw [heval]
      _ = ∑ b : Fin 6, ∑ r : Fin 5 → Fin 6,
          L (E.symm (0, r)) * Q y b * R (E.symm (0, r)) := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro r _
            rw [hL b 0 r, hR b 0 r]
      _ = ∑ r : Fin 5 → Fin 6, ∑ b : Fin 6,
          L (E.symm (0, r)) * Q y b * R (E.symm (0, r)) := by
            rw [Finset.sum_comm]
      _ = ∑ r : Fin 5 → Fin 6,
          L (E.symm (0, r)) * (∑ b : Fin 6, Q y b) * R (E.symm (0, r)) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by simp [hQ]
  have hdel :
      (∑ j, L j * R j) = (6 : ℂ) •
        (∑ r : Fin 5 → Fin 6, L (E.symm (0, r)) * R (E.symm (0, r))) := by
    calc
      _ = ∑ p : Fin 6 × (Fin 5 → Fin 6),
          L (E.symm p) * R (E.symm p) := (E.symm.sum_comp _).symm
      _ = ∑ b : Fin 6, ∑ r : Fin 5 → Fin 6,
          L (E.symm (b, r)) * R (E.symm (b, r)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ b : Fin 6, ∑ r : Fin 5 → Fin 6,
          L (E.symm (0, r)) * R (E.symm (0, r)) := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro r _
            rw [hL b 0 r, hR b 0 r]
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simpa using (Nat.cast_smul_eq_nsmul ℂ 6
          (∑ r : Fin 5 → Fin 6, L (E.symm (0, r)) * R (E.symm (0, r)))).symm
  rw [horig, hdel, smul_smul]
  norm_num

theorem evalReducerWord_append (V : ReducerSymbol → Mat6)
    (u v : List ReducerSymbol) :
    evalReducerWord V (u ++ v) = evalReducerWord V u * evalReducerWord V v := by
  induction u with
  | nil => simp [evalReducerWord]
  | cons s u ih => simp [evalReducerWord, ih, mul_assoc]

/-- Semantic soundness of deleting a basis label which occurs exactly once. -/
theorem reducerStepS_sound
    (P : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hQ : ∀ y, ∑ b, Q y b = 1) {w w' : List ReducerSymbol}
    (h : reducerStepS w = some w') :
    (∑ j, evalAssignmentWord P Q j w) =
      (1 / 6 : ℂ) • (∑ j, evalAssignmentWord P Q j w') := by
  obtain ⟨pre, y, post, hw, hw', hpre, hpost⟩ := reducerStepS_spec h
  subst w
  subst w'
  have hdelete := sum_assignment_singleton_delete y Q hQ
    (fun j => evalAssignmentWord P Q j pre)
    (fun j => evalAssignmentWord P Q j post)
    (fun b b' r => evalAssignmentWord_split_independent
      P Q y pre hpre b b' r)
    (fun b b' r => evalAssignmentWord_split_independent
      P Q y post hpost b b' r)
  simpa [evalAssignmentWord, evalReducerWord_append, evalReducerWord,
    mul_assoc] using hdelete

/-- Recursive semantic soundness of the deterministic word reducer.  This
statement is abstract in the aggregate evaluator, so the D/S/X rules can be
proved independently and then assembled without any further case table. -/
theorem reduceProjectorWord_sound
    (F : List ReducerSymbol → Mat6)
    (hD : ∀ {w w'}, reducerStepD w = some w' → F w = F w')
    (hS : ∀ {w w'}, reducerStepS w = some w' →
      F w = (1 / 6 : ℂ) • F w')
    (hX : ∀ {w w'}, reducerStepX w = some w' →
      F w = (1 / 6 : ℂ) • F w') :
    ∀ fuel w, F w =
      ((1 / 6 : ℂ) ^ (reduceProjectorWord fuel w).1) •
        F (reduceProjectorWord fuel w).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro w
      simp [reduceProjectorWord]
  | succ fuel ih =>
      intro w
      rw [reduceProjectorWord]
      cases hd : reducerStepD w with
      | some wd =>
          simp only [hd]
          rw [hD hd]
          exact ih wd
      | none =>
          simp only [hd]
          cases hs : reducerStepS w with
          | some ws =>
              simp only [hs]
              rw [hS hs, ih ws, smul_smul]
              simp only [pow_succ]
              congr 1
              ring
          | none =>
              simp only [hs]
              cases hx : reducerStepX w with
              | some wx =>
                  simp only [hx]
                  rw [hX hx, ih wx, smul_smul]
                  simp only [pow_succ]
                  congr 1
                  ring
              | none => simp [hx]

/-- Split out two distinct coordinates, parameterizing the second inside the
complement of the first. -/
def splitAssignmentTwo (y : Fin 6) (z : Fin 5) :
    Assignment6 ≃ (Fin 6 × (Fin 6 × (Fin 4 → Fin 6))) :=
  (Fin.insertNthEquiv (fun _ : Fin 6 => Fin 6) y).symm |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin 6))
      (Fin.insertNthEquiv (fun _ : Fin 5 => Fin 6) z).symm)

@[simp] theorem splitAssignmentTwo_fst (y : Fin 6) (z : Fin 5)
    (j : Assignment6) : (splitAssignmentTwo y z j).1 = j y := by
  simp [splitAssignmentTwo]

@[simp] theorem splitAssignmentTwo_snd_fst (y : Fin 6) (z : Fin 5)
    (j : Assignment6) : (splitAssignmentTwo y z j).2.1 = j (y.succAbove z) := by
  simpa [splitAssignmentTwo] using Fin.removeNth_apply y j z

/-- Two-coordinate assignment sum for an ordered pair of distinct bases. -/
theorem sum_assignment_eval_two_succAbove
    (y : Fin 6) (z : Fin 5) (f : Fin 6 → Fin 6 → Mat6) :
    (∑ j : Assignment6, f (j y) (j (y.succAbove z))) =
      (6 ^ 4 : ℕ) • (∑ b : Fin 6, ∑ c : Fin 6, f b c) := by
  calc
    _ = ∑ j : Assignment6,
        f (splitAssignmentTwo y z j).1 (splitAssignmentTwo y z j).2.1 := by simp
    _ = ∑ p : Fin 6 × (Fin 6 × (Fin 4 → Fin 6)), f p.1 p.2.1 :=
      (splitAssignmentTwo y z).sum_comp (fun p => f p.1 p.2.1)
    _ = ∑ b : Fin 6, ∑ c : Fin 6, ∑ _r : (Fin 4 → Fin 6), f b c := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Fintype.sum_prod_type]
    _ = ∑ b : Fin 6, ∑ c : Fin 6, (6 ^ 4 : ℕ) • f b c := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
    _ = (6 ^ 4 : ℕ) • (∑ b : Fin 6, ∑ c : Fin 6, f b c) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.smul_sum]

/-- The all-anchor mask contributes one copy of the anchor for every assignment. -/
theorem assignment_mask_11111 (A : Mat6) (hA : A * A = A) :
    (∑ _j : Assignment6, A * A * A * A * A) =
      (46656 : ℂ) • A := by
  simp_rw [idempotent_fifth_word A hA]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

/-- Sum an arbitrary one-selected-projector word over all assignments and bases. -/
theorem assignment_singleton_word
    (Q : Fin 6 → Fin 6 → Mat6) (hQ : ∀ y, ∑ b, Q y b = 1)
    (L R : Mat6) :
    (∑ j : Assignment6, ∑ y, L * Q y (j y) * R) =
      (46656 : ℂ) • (L * R) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ y, (6 ^ 5 : ℕ) • (∑ b, L * Q y b * R) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact sum_assignment_eval y (fun b => L * Q y b * R)
    _ = ∑ _y : Fin 6, (6 ^ 5 : ℕ) • (L * R) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [sum_insert_projector (Q y) (hQ y)]
    _ = (46656 : ℂ) • (L * R) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      norm_num

/-- Actual certificate row `01111`. -/
theorem assignment_mask_01111
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ j : Assignment6, A * A * A * A * (∑ y, Q y (j y))) =
      (46656 : ℂ) • A := by
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one, Matrix.one_mul,
    mul_assoc, hA] using
    assignment_singleton_word Q hQ (A * A * A * A) 1

/-- Actual certificate row `10111`. -/
theorem assignment_mask_10111
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ j : Assignment6, A * A * A * (∑ y, Q y (j y)) * A) =
      (46656 : ℂ) • A := by
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one, Matrix.one_mul,
    mul_assoc, hA] using
    assignment_singleton_word Q hQ (A * A * A) A

/-- Actual certificate row `11011`. -/
theorem assignment_mask_11011
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ j : Assignment6, A * A * (∑ y, Q y (j y)) * A * A) =
      (46656 : ℂ) • A := by
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one, Matrix.one_mul,
    mul_assoc, hA] using
    assignment_singleton_word Q hQ (A * A) (A * A)

/-- Actual certificate row `11101`. -/
theorem assignment_mask_11101
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ j : Assignment6, A * (∑ y, Q y (j y)) * A * A * A) =
      (46656 : ℂ) • A := by
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one, Matrix.one_mul,
    mul_assoc, hA] using
    assignment_singleton_word Q hQ A (A * A * A)

/-- Actual certificate row `11110`. -/
theorem assignment_mask_11110
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hA : A * A = A) (hQ : ∀ y, ∑ b, Q y b = 1) :
    (∑ j : Assignment6, (∑ y, Q y (j y)) * A * A * A * A) =
      (46656 : ℂ) • A := by
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_one, Matrix.one_mul,
    mul_assoc, hA] using
    assignment_singleton_word Q hQ 1 (A * A * A * A)

/- The following direct two-coordinate aggregate route is retained as source
documentation only.  The final proof uses the strictly more general all-word
reducer, so elaborating these expensive specialized lemmas would duplicate work.

/-- Exact second moment of the selected projector sum over all assignments. -/
theorem assignment_R_sq
    (Q : Fin 6 → Fin 6 → Mat6)
    (hQ : ∀ y, ∑ b, Q y b = 1)
    (hIdem : ∀ y b, Q y b * Q y b = Q y b) :
    (∑ j : Assignment6,
      (∑ y, Q y (j y)) * (∑ y, Q y (j y))) =
      (85536 : ℂ) • (1 : Mat6) := by
  classical
  calc
    _ = ∑ j : Assignment6, ∑ y : Fin 6, ∑ z : Fin 6,
          Q y (j y) * Q z (j z) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
    _ = ∑ y : Fin 6, ∑ z : Fin 6, ∑ j : Assignment6,
          Q y (j y) * Q z (j z) := by
      rw [Finset.sum_comm]
      congr 1 with y
      rw [Finset.sum_comm]
    _ = ∑ y : Fin 6,
          ((∑ j : Assignment6, Q y (j y) * Q y (j y)) +
           ∑ z : Fin 5, ∑ j : Assignment6,
             Q y (j y) * Q (y.succAbove z) (j (y.succAbove z))) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Fin.sum_univ_succAbove
        (fun z => ∑ j : Assignment6, Q y (j y) * Q z (j z)) y
    _ = ∑ y : Fin 6,
          ((6^5 : ℕ) • (∑ b : Fin 6, Q y b * Q y b) +
           ∑ z : Fin 5, (6^4 : ℕ) •
             (∑ b : Fin 6, ∑ c : Fin 6,
               Q y b * Q (y.succAbove z) c)) := by
      apply Finset.sum_congr rfl
      intro y _
      apply congrArg₂ (· + ·)
      · exact sum_assignment_eval y (fun b => Q y b * Q y b)
      · apply Finset.sum_congr rfl
        intro z _
        exact sum_assignment_eval_two_succAbove y z
          (fun b c => Q y b * Q (y.succAbove z) c)
    _ = (85536 : ℂ) • (1 : Mat6) := by
      simp_rw [hIdem]
      simp_rw [← Finset.mul_sum]
      simp [hQ]
      simp only [Algebra.smul_def]
      noncomm_ring

/-- Exact `R A R` aggregate over all assignments. -/
theorem assignment_R_A_R
    (A : Mat6) (Q : Fin 6 → Fin 6 → Mat6)
    (hQ : ∀ y, ∑ b, Q y b = 1)
    (hSandwich : ∀ y b, Q y b * A * Q y b = (1 / 6 : ℂ) • Q y b) :
    (∑ j : Assignment6,
      (∑ y, Q y (j y)) * A * (∑ y, Q y (j y))) =
      (38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6) := by
  classical
  calc
    _ = ∑ j : Assignment6, ∑ z : Fin 6, ∑ y : Fin 6,
          Q y (j y) * A * Q z (j z) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.sum_mul]
    _ = ∑ z : Fin 6, ∑ y : Fin 6, ∑ j : Assignment6,
          Q y (j y) * A * Q z (j z) := by
      rw [Finset.sum_comm]
      congr 1 with z
      rw [Finset.sum_comm]
    _ = ∑ y : Fin 6, ∑ z : Fin 6, ∑ j : Assignment6,
          Q y (j y) * A * Q z (j z) := by
      rw [Finset.sum_comm]
    _ = ∑ y : Fin 6,
          ((∑ j : Assignment6, Q y (j y) * A * Q y (j y)) +
           ∑ z : Fin 5, ∑ j : Assignment6,
             Q y (j y) * A * Q (y.succAbove z) (j (y.succAbove z))) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Fin.sum_univ_succAbove
        (fun z => ∑ j : Assignment6, Q y (j y) * A * Q z (j z)) y
    _ = ∑ y : Fin 6,
          ((6^5 : ℕ) • (∑ b : Fin 6, Q y b * A * Q y b) +
           ∑ z : Fin 5, (6^4 : ℕ) •
             (∑ b : Fin 6, ∑ c : Fin 6,
               Q y b * A * Q (y.succAbove z) c)) := by
      apply Finset.sum_congr rfl
      intro y _
      apply congrArg₂ (· + ·)
      · exact sum_assignment_eval y (fun b => Q y b * A * Q y b)
      · apply Finset.sum_congr rfl
        intro z _
        exact sum_assignment_eval_two_succAbove y z
          (fun b c => Q y b * A * Q (y.succAbove z) c)
    _ = (38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6) := by
      simp_rw [hSandwich]
      simp_rw [← Finset.smul_sum]
      simp_rw [← Finset.mul_sum]
      simp [hQ]
      simp_rw [← Finset.sum_mul]
      simp [hQ]
      simp only [Algebra.smul_def]
      noncomm_ring

/-- The ten words with exactly two selected projectors, reduced from the two
aggregate identities.  The conjunct order follows multiplication order. -/
theorem assignment_two_R_mask_certificate
    (A : Mat6) (R : Assignment6 → Mat6) (hA : A * A = A)
    (hR2 : (∑ j, R j * R j) = (85536 : ℂ) • (1 : Mat6))
    (hRAR : (∑ j, R j * A * R j) =
      (38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) :
    ((∑ j, R j * R j * A * A * A) = (85536 : ℂ) • A) ∧
    ((∑ j, R j * A * R j * A * A) = (46656 : ℂ) • A) ∧
    ((∑ j, R j * A * A * R j * A) = (46656 : ℂ) • A) ∧
    ((∑ j, R j * A * A * A * R j) =
      (38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) ∧
    ((∑ j, A * R j * R j * A * A) = (85536 : ℂ) • A) ∧
    ((∑ j, A * R j * A * R j * A) = (46656 : ℂ) • A) ∧
    ((∑ j, A * R j * A * A * R j) = (46656 : ℂ) • A) ∧
    ((∑ j, A * A * R j * R j * A) = (85536 : ℂ) • A) ∧
    ((∑ j, A * A * R j * A * R j) = (46656 : ℂ) • A) ∧
    ((∑ j, A * A * A * R j * R j) = (85536 : ℂ) • A) := by
  have rr_right := congrArg (fun X : Mat6 => X * A) hR2
  have rr_both := congrArg (fun X : Mat6 => A * X * A) hR2
  have rr_left := congrArg (fun X : Mat6 => A * X) hR2
  have rar_right := congrArg (fun X : Mat6 => X * A) hRAR
  have rar_both := congrArg (fun X : Mat6 => A * X * A) hRAR
  have rar_left := congrArg (fun X : Mat6 => A * X) hRAR
  have hA3 : A * A * A = A := by rw [hA, hA]
  constructor
  · simpa [Finset.sum_mul, hA, mul_assoc] using rr_right
  constructor
  · calc
      _ = ((38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) * A := by
        simpa [Finset.sum_mul, hA, mul_assoc] using rar_right
      _ = (46656 : ℂ) • A := by
        simp only [add_mul, smul_mul, one_mul, hA, ← add_smul]
        norm_num
  constructor
  · calc
      _ = ((38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) * A := by
        simpa [Finset.sum_mul, hA, mul_assoc] using rar_right
      _ = (46656 : ℂ) • A := by
        simp only [add_mul, smul_mul, one_mul, hA, ← add_smul]
        norm_num
  constructor
  · simpa [hA, mul_assoc] using hRAR
  constructor
  · simpa [Finset.mul_sum, Finset.sum_mul, hA, mul_assoc] using rr_both
  constructor
  · calc
      _ = A * ((38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) * A := by
        simpa [Finset.mul_sum, Finset.sum_mul, hA, mul_assoc] using rar_both
      _ = (38880 : ℂ) • (A * A * A) + (7776 : ℂ) • (A * A) := by
        simp only [mul_add, add_mul, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, mul_one, one_mul]
      _ = (46656 : ℂ) • A := by
        rw [hA3, hA, ← add_smul]
        norm_num
  constructor
  · calc
      _ = A * ((38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) := by
        simpa [Finset.mul_sum, hA, mul_assoc] using rar_left
      _ = (38880 : ℂ) • (A * A) + (7776 : ℂ) • A := by
        simp only [mul_add, Algebra.mul_smul_comm, mul_one]
      _ = (46656 : ℂ) • A := by
        rw [hA, ← add_smul]
        norm_num
  constructor
  · simpa [Finset.mul_sum, Finset.sum_mul, hA, mul_assoc] using rr_both
  constructor
  · calc
      _ = A * ((38880 : ℂ) • A + (7776 : ℂ) • (1 : Mat6)) := by
        simpa [Finset.mul_sum, hA, mul_assoc] using rar_left
      _ = (38880 : ℂ) • (A * A) + (7776 : ℂ) • A := by
        simp only [mul_add, Algebra.mul_smul_comm, mul_one]
      _ = (46656 : ℂ) • A := by
        rw [hA, ← add_smul]
        norm_num
  · simpa [Finset.mul_sum, hA, mul_assoc] using rr_left
-/

/-- Reindex the complement of one coordinate by `Fin.succAbove`. -/
theorem sum_succAbove_eq_sum_erase {M : Type*} [AddCancelCommMonoid M]
    (z : Fin 6) (f : Fin 6 → M) :
    (∑ w : Fin 5, f (z.succAbove w)) = ∑ y ∈ Finset.univ.erase z, f y := by
  have hall := Fin.sum_univ_succAbove f z
  have herase := Finset.sum_erase_add
    (Finset.univ : Finset (Fin 6)) f (Finset.mem_univ z)
  rw [hall] at herase
  have h : f z + (∑ y ∈ Finset.univ.erase z, f y) =
      f z + ∑ w : Fin 5, f (z.succAbove w) := by
    simpa [add_comm, add_left_comm, add_assoc] using herase
  exact (add_left_cancel h).symm

/-- The phase-sensitive crossed equality orbit, lifted from outcome sums to
assignment sums. -/
theorem assignment_crossed_orbit
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, ∑ z, ∑ y ∈ Finset.univ.erase z,
      projector (B y) (j y) * projector (B z) (j z) * projector U a *
      projector (B y) (j y) * projector (B z) (j z)) =
      (1296 : ℂ) • ((1 : Mat6) - projector U a) := by
  classical
  calc
    _ = ∑ z, ∑ w : Fin 5, ∑ j : Assignment6,
        projector (B (z.succAbove w)) (j (z.succAbove w)) *
        projector (B z) (j z) * projector U a *
        projector (B (z.succAbove w)) (j (z.succAbove w)) *
        projector (B z) (j z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_comm]
      rw [← sum_succAbove_eq_sum_erase z]
    _ = ∑ z, ∑ w : Fin 5, (6 ^ 4 : ℕ) •
        (∑ c : Fin 6, ∑ b : Fin 6,
          projector (B (z.succAbove w)) b * projector (B z) c *
          projector U a * projector (B (z.succAbove w)) b *
          projector (B z) c) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      exact sum_assignment_eval_two_succAbove z w
        (fun c b => projector (B (z.succAbove w)) b * projector (B z) c *
          projector U a * projector (B (z.succAbove w)) b * projector (B z) c)
    _ = (6 ^ 4 : ℕ) •
        (∑ z, ∑ w : Fin 5, ∑ c : Fin 6, ∑ b : Fin 6,
          projector (B (z.succAbove w)) b * projector (B z) c *
          projector U a * projector (B (z.succAbove w)) b *
          projector (B z) c) := by
      symm
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.smul_sum]
    _ = (6 ^ 4 : ℕ) •
        (∑ z, ∑ c, ∑ y ∈ Finset.univ.erase z, ∑ b,
          projector (B y) b * projector (B z) c * projector U a *
          projector (B y) b * projector (B z) c) := by
      apply congrArg ((6 ^ 4 : ℕ) • ·)
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_succAbove_eq_sum_erase z (fun y => ∑ b,
        projector (B y) b * projector (B z) c * projector U a *
          projector (B y) b * projector (B z) c)
    _ = (1296 : ℂ) • ((1 : Mat6) - projector U a) := by
      rw [CompleteMUBFiveMoment.complete_mub_crossed_sum_ordered U B hMUB a]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      norm_num

end CompleteMUBDegreeFiveCount

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix

namespace CompleteMUBFiveMoment

set_option maxHeartbeats 2000000

/-- Split a word into its first letter and its remaining letters. -/
def splitAllWord (n : Nat) :
    (Fin (n + 1) → ReducerSymbol) ≃
      (ReducerSymbol × (Fin n → ReducerSymbol)) :=
  (Equiv.piCongrLeft' (fun _ : Fin (n + 1) => ReducerSymbol)
    (finSuccEquiv n)).trans Equiv.piOptionEquivProd

@[simp] lemma splitAllWord_symm_zero (n : Nat) (s : ReducerSymbol)
    (v : Fin n → ReducerSymbol) :
    (splitAllWord n).symm (s, v) 0 = s := by
  simp [splitAllWord, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

@[simp] lemma splitAllWord_symm_succ (n : Nat) (s : ReducerSymbol)
    (v : Fin n → ReducerSymbol) (i : Fin n) :
    (splitAllWord n).symm (s, v) i.succ = v i := by
  simp [splitAllWord, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

lemma allWord_split (n : Nat) (s : ReducerSymbol)
    (v : Fin n → ReducerSymbol) :
    allWord ((splitAllWord n).symm (s, v)) = s :: allWord v := by
  simp [allWord, List.ofFn_succ]

/-- Noncommutative multinomial expansion indexed by all words. -/
theorem sum_allWord_eval (V : ReducerSymbol → Mat6) :
    ∀ n : Nat, (∑ s, V s) ^ n =
      ∑ v : Fin n → ReducerSymbol, evalReducerWord V (allWord v) := by
  intro n
  induction n with
  | zero => simp [allWord, evalReducerWord]
  | succ n ih =>
      rw [pow_succ', ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      calc
        (∑ s, ∑ v : Fin n → ReducerSymbol,
            V s * evalReducerWord V (allWord v)) =
            ∑ p : ReducerSymbol × (Fin n → ReducerSymbol),
              V p.1 * evalReducerWord V (allWord p.2) := by
                rw [Fintype.sum_prod_type]
        _ = ∑ v : Fin (n + 1) → ReducerSymbol,
              evalReducerWord V (allWord v) := by
                rw [← (splitAllWord n).symm.sum_comp]
                apply Finset.sum_congr rfl
                intro p hp
                rw [allWord_split]
                rfl

theorem sum_allWord_succ_reindex {M : Type*} [AddCommMonoid M]
    (n : Nat) (H : List ReducerSymbol → M) :
    (∑ v : Fin (n + 1) → ReducerSymbol, H (allWord v)) =
      ∑ s : ReducerSymbol, ∑ v : Fin n → ReducerSymbol,
        H (s :: allWord v) := by
  calc
    (∑ v : Fin (n + 1) → ReducerSymbol, H (allWord v)) =
        ∑ p : ReducerSymbol × (Fin n → ReducerSymbol),
          H (allWord ((splitAllWord n).symm p)) := by
            rw [← (splitAllWord n).symm.sum_comp]
    _ = ∑ p : ReducerSymbol × (Fin n → ReducerSymbol),
          H (p.1 :: allWord p.2) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [allWord_split]
    _ = _ := by rw [Fintype.sum_prod_type]

/-- The reducer introduces at most one scalar factor per unit of fuel. -/
theorem reduceProjectorWord_exponent_le :
    ∀ fuel w, (reduceProjectorWord fuel w).1 ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro w; simp [reduceProjectorWord]
  | succ fuel ih =>
      intro w
      rw [reduceProjectorWord]
      cases hd : reducerStepD w with
      | some wd =>
          simp only [hd]
          exact Nat.le_trans (ih wd) (Nat.le_succ fuel)
      | none =>
          simp only [hd]
          cases hs : reducerStepS w with
          | some ws =>
              simp only [hs]
              exact Nat.succ_le_succ (ih ws)
          | none =>
              simp only [hs]
              cases hx : reducerStepX w with
              | some wx =>
                  simp only [hx]
                  exact Nat.succ_le_succ (ih wx)
              | none => simp [hx]

/-- A reducer-residue fiber is exactly the finite histogram certified by
`allWordCount`; this is the bridge from finite counting to scalar weights. -/
theorem weighted_residue_eq_counts (n : Nat) (hn : n ≤ 5)
    (r : List ReducerSymbol) :
    (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
        (fun v => (reduceProjectorWord n (allWord v)).2 = r),
        (1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1) =
      ∑ e ∈ Finset.range 6,
        (allWordCount n e r : ℂ) * (1 / 6 : ℂ) ^ e := by
  classical
  let S := (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
    (fun v => (reduceProjectorWord n (allWord v)).2 = r)
  let g : (Fin n → ReducerSymbol) → Nat := fun v =>
    (reduceProjectorWord n (allWord v)).1
  have hmaps : ∀ v ∈ S, g v ∈ Finset.range 6 := by
    intro v hv
    simp only [Finset.mem_range]
    exact lt_of_le_of_lt (reduceProjectorWord_exponent_le n (allWord v))
      (Nat.lt_succ_iff.mpr hn)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.range 6) hmaps
    (fun v => (1 / 6 : ℂ) ^ g v)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ v ∈ S with g v = e, (1 / 6 : ℂ) ^ g v) =
        ∑ v ∈ S with g v = e, (1 / 6 : ℂ) ^ e := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [(Finset.mem_filter.1 hv).2]
    _ = ((S.filter fun v => g v = e).card : ℂ) *
        (1 / 6 : ℂ) ^ e := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (allWordCount n e r : ℂ) * (1 / 6 : ℂ) ^ e := by
          congr 2
          congr 1
          have hset : S.filter (fun v => g v = e) =
              (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
                (fun v => reduceProjectorWord n (allWord v) = (e, r)) := by
            ext v
            simp [S, g, Prod.ext_iff, and_left_comm, and_comm]
          rw [hset]

theorem allWordCount_eq_zero_of_fuel_lt (n e : Nat) (r : List ReducerSymbol)
    (h : n < e) : allWordCount n e r = 0 := by
  classical
  rw [allWordCount, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro v hv
  intro hout
  have he : (reduceProjectorWord n (allWord v)).1 = e :=
    congrArg Prod.fst hout
  have hle := reduceProjectorWord_exponent_le n (allWord v)
  omega

end CompleteMUBFiveMoment

namespace CompleteMUBDegreeFiveCount

open CompleteMUBFiveMoment
open MUBCP

private def assignmentSymbolValue (U : Mat6) (B : Fin 6 → Mat6)
    (a : Fin 6) (j : Assignment6) : ReducerSymbol → Mat6
  | none => projector U a
  | some y => projector (B y) (j y)

private lemma sum_assignmentSymbolValue (U : Mat6) (B : Fin 6 → Mat6)
    (a : Fin 6) (j : Assignment6) :
    (∑ s, assignmentSymbolValue U B a j s) =
      anchoredSelectedSum U B a j := by
  simp [assignmentSymbolValue, anchoredSelectedSum]

private lemma complete_family_projector_cross
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B))
    (y z : Fin 6) (hyz : y ≠ z) (b c : Fin 6) :
    projector (B y) b * projector (B z) c * projector (B y) b =
      (1 / 6 : ℂ) • projector (B y) b := by
  apply mubcp_projector_sandwich
  apply hMUB.2 y.succ z.succ
    (fun h => hyz (Fin.succ_inj.mp h)) b c

/-- Expand an assignment moment into all words and normalize every word by
the deterministic projector reducer. -/
theorem assignment_moment_eq_reduced_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) (n : Nat) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ n) =
      ∑ v : Fin n → ReducerSymbol,
        ((1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1) •
          (∑ j : Assignment6,
            evalAssignmentWord (projector U a)
              (fun y b => projector (B y) b) j
              (reduceProjectorWord n (allWord v)).2) := by
  classical
  obtain ⟨hU, hB, hPQ, hQP⟩ := complete_family_projector_rules U B hMUB
  have hsum : ∀ y, ∑ b, projector (B y) b = (1 : Mat6) := by
    intro y
    exact mubcp_projector_sum (B y) (hB y)
  have hidem (j : Assignment6) :
      ∀ s, assignmentSymbolValue U B a j s *
        assignmentSymbolValue U B a j s = assignmentSymbolValue U B a j s := by
    intro s
    cases s with
    | none => exact mubcp_projector_idempotent U hU a
    | some y => exact mubcp_projector_idempotent (B y) (hB y) (j y)
  have hcross (j : Assignment6) : ∀ s t, s ≠ t →
      assignmentSymbolValue U B a j s * assignmentSymbolValue U B a j t *
          assignmentSymbolValue U B a j s =
        (1 / 6 : ℂ) • assignmentSymbolValue U B a j s := by
    intro s t hst
    cases s with
    | none =>
        cases t with
        | none => exact (hst rfl).elim
        | some y => exact hPQ a y (j y)
    | some y =>
        cases t with
        | none => exact hQP a y (j y)
        | some z =>
            exact complete_family_projector_cross U B hMUB y z
              (fun hyz => hst (congrArg some hyz)) (j y) (j z)
  let F : List ReducerSymbol → Mat6 := fun w =>
    ∑ j : Assignment6, evalAssignmentWord (projector U a)
      (fun y b => projector (B y) b) j w
  have hD : ∀ {w w'}, reducerStepD w = some w' → F w = F w' := by
    intro w w' h
    apply Finset.sum_congr rfl
    intro j hj
    exact reducerStepD_sound (assignmentSymbolValue U B a j) (hidem j) h
  have hS : ∀ {w w'}, reducerStepS w = some w' →
      F w = (1 / 6 : ℂ) • F w' := by
    intro w w' h
    exact reducerStepS_sound (projector U a)
      (fun y b => projector (B y) b) hsum h
  have hX : ∀ {w w'}, reducerStepX w = some w' →
      F w = (1 / 6 : ℂ) • F w' := by
    intro w w' h
    change (∑ j : Assignment6, evalAssignmentWord (projector U a)
      (fun y b => projector (B y) b) j w) =
      (1 / 6 : ℂ) • (∑ j : Assignment6,
        evalAssignmentWord (projector U a)
          (fun y b => projector (B y) b) j w')
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact reducerStepX_sound (assignmentSymbolValue U B a j) (hcross j) h
  calc
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ n) =
        ∑ j : Assignment6, ∑ v : Fin n → ReducerSymbol,
          evalAssignmentWord (projector U a)
            (fun y b => projector (B y) b) j (allWord v) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← sum_assignmentSymbolValue U B a j,
            CompleteMUBFiveMoment.sum_allWord_eval]
          rfl
    _ = ∑ v : Fin n → ReducerSymbol, F (allWord v) := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro v hv
          exact reduceProjectorWord_sound F hD hS hX n (allWord v)

private theorem assignment_eval_nil (U : Mat6) (B : Fin 6 → Mat6)
    (a : Fin 6) :
    (∑ j : Assignment6, evalAssignmentWord (projector U a)
      (fun y b => projector (B y) b) j []) = (46656 : ℂ) • (1 : Mat6) := by
  change (∑ _j : Assignment6, (1 : Mat6)) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

private theorem assignment_eval_anchor (U : Mat6) (B : Fin 6 → Mat6)
    (a : Fin 6) :
    (∑ j : Assignment6, evalAssignmentWord (projector U a)
      (fun y b => projector (B y) b) j [none]) =
      (46656 : ℂ) • projector U a := by
  simp only [evalAssignmentWord, evalReducerWord, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

/-- If every reduced word has either the empty residue or the distinguished
anchor residue, its matrix sum is controlled by the two scalar histograms. -/
private theorem reduced_sum_two_residues (n : Nat)
    (F : List ReducerSymbol → Mat6)
    (hexhaustive : ∀ v : Fin n → ReducerSymbol,
      (reduceProjectorWord n (allWord v)).2 = [] ∨
      (reduceProjectorWord n (allWord v)).2 = [none]) :
    (∑ v : Fin n → ReducerSymbol,
      ((1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1) •
        F (reduceProjectorWord n (allWord v)).2) =
      (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
          (fun v => (reduceProjectorWord n (allWord v)).2 = [none]),
          (1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1) • F [none] +
      (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
          (fun v => (reduceProjectorWord n (allWord v)).2 = []),
          (1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1) • F [] := by
  classical
  let residue : (Fin n → ReducerSymbol) → List ReducerSymbol := fun v =>
    (reduceProjectorWord n (allWord v)).2
  let coeff : (Fin n → ReducerSymbol) → ℂ := fun v =>
    (1 / 6 : ℂ) ^ (reduceProjectorWord n (allWord v)).1
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n → ReducerSymbol))
    (fun v => residue v = [none]) (fun v => coeff v • F (residue v))]
  congr 1
  · calc
      (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
          (fun v => residue v = [none]), coeff v • F (residue v)) =
          ∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
            (fun v => residue v = [none]), coeff v • F [none] := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [(Finset.mem_filter.1 hv).2]
      _ = (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
            (fun v => residue v = [none]), coeff v) • F [none] := by
              rw [Finset.sum_smul]
      _ = _ := by rfl
  · calc
      (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
          (fun v => ¬ residue v = [none]), coeff v • F (residue v)) =
          ∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
            (fun v => residue v = []), coeff v • F [] := by
              apply Finset.sum_congr
              · ext v
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hn
                  rcases hexhaustive v with hnil | hanchor
                  · exact hnil
                  · exact (hn hanchor).elim
                · intro hnil hanchor
                  simpa [hnil] using hanchor
              · intro v hv
                rw [(Finset.mem_filter.1 hv).2]
      _ = (∑ v ∈ (Finset.univ : Finset (Fin n → ReducerSymbol)).filter
            (fun v => residue v = []), coeff v) • F [] := by
              rw [Finset.sum_smul]
      _ = _ := by rfl

private theorem crossed_word_sum_reindex (H : List ReducerSymbol → Mat6) :
    (∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
        (fun v => isCrossedResidue (allWord v)), H (allWord v)) =
      ∑ y : Fin 6, ∑ z ∈ Finset.univ.erase y,
        H [some y, some z, none, some y, some z] := by
  classical
  let K : List ReducerSymbol → Mat6 := fun w =>
    if isCrossedResidue w then H w else 0
  have hcollapse (x z : Fin 6) :
      (∑ x' : Fin 6, ∑ z' : Fin 6,
        if x = x' ∧ z = z' ∧ x ≠ z then
          H [some x, some z, none, some x', some z'] else 0) =
        if x ≠ z then H [some x, some z, none, some x, some z] else 0 := by
    by_cases hxz : x = z
    · simp [hxz]
    · rw [if_pos hxz]
      rw [Fintype.sum_eq_single x]
      · rw [Fintype.sum_eq_single z]
        · simp [hxz]
        · intro z' hzz'
          simp [hzz', Ne.symm hzz']
      · intro x' hxx'
        simp [hxx', Ne.symm hxx']
  have hexpand :
      (∑ v : Fin 5 → ReducerSymbol, K (allWord v)) =
        ∑ s0 : ReducerSymbol, ∑ s1 : ReducerSymbol,
        ∑ s2 : ReducerSymbol, ∑ s3 : ReducerSymbol,
        ∑ s4 : ReducerSymbol, K [s0, s1, s2, s3, s4] := by
    rw [CompleteMUBFiveMoment.sum_allWord_succ_reindex 4 K]
    apply Finset.sum_congr rfl
    intro s0 hs0
    rw [CompleteMUBFiveMoment.sum_allWord_succ_reindex 3
      (fun w => K (s0 :: w))]
    apply Finset.sum_congr rfl
    intro s1 hs1
    rw [CompleteMUBFiveMoment.sum_allWord_succ_reindex 2
      (fun w => K (s0 :: s1 :: w))]
    apply Finset.sum_congr rfl
    intro s2 hs2
    rw [CompleteMUBFiveMoment.sum_allWord_succ_reindex 1
      (fun w => K (s0 :: s1 :: s2 :: w))]
    apply Finset.sum_congr rfl
    intro s3 hs3
    rw [CompleteMUBFiveMoment.sum_allWord_succ_reindex 0
      (fun w => K (s0 :: s1 :: s2 :: s3 :: w))]
    apply Finset.sum_congr rfl
    intro s4 hs4
    simp [allWord]
  calc
    (∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
        (fun v => isCrossedResidue (allWord v)), H (allWord v)) =
      ∑ v : Fin 5 → ReducerSymbol, K (allWord v) := by
          rw [Finset.sum_filter]
    _ = _ := by
      rw [hexpand]
      simp [K, isCrossedResidue, hcollapse]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hlhs :
          (∑ z : Fin 6,
            if x = z then 0 else H [some x, some z, none, some x, some z]) =
          ∑ z ∈ (Finset.univ : Finset (Fin 6)).erase x,
            H [some x, some z, none, some x, some z] := by
        rw [show (Finset.univ : Finset (Fin 6)).erase x =
            Finset.univ.filter (fun z => z ≠ x) by ext z; simp]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hzx : z = x
        · simp [hzx]
        · simp [hzx, Ne.symm hzx]
      rw [hlhs]
      have herase := Finset.sum_erase_add
        (Finset.univ : Finset (Fin 6))
        (fun z => H [some x, some z, none, some x, some z])
        (Finset.mem_univ x)
      exact (eq_sub_iff_add_eq).2 herase

private theorem crossed_word_reduces_explicit (y z : Fin 6) (h : y ≠ z) :
    reduceProjectorWord 5 [some y, some z, none, some y, some z] =
      (0, [some y, some z, none, some y, some z]) := by
  have hd : reducerStepD [some y, some z, none, some y, some z] = none := by
    simp [reducerStepD, h]
  have hs : reducerStepS [some y, some z, none, some y, some z] = none := by
    simp [reducerStepS, reducerStepSAt, h, Ne.symm h]
  have hx : reducerStepX [some y, some z, none, some y, some z] = none := by
    simp [reducerStepX, h, Ne.symm h]
  simp [reduceProjectorWord, hd, hs, hx]

private theorem crossed_word_reduces_to_self
    (v : Fin 5 → ReducerSymbol) (h : isCrossedResidue (allWord v)) :
    reduceProjectorWord 5 (allWord v) = (0, allWord v) := by
  have hw : allWord v = [v 0, v 1, v 2, v 3, v 4] := by
    simp [allWord, List.ofFn_succ]
  rw [hw] at h ⊢
  generalize v 0 = s0 at h ⊢
  generalize v 1 = s1 at h ⊢
  generalize v 2 = s2 at h ⊢
  generalize v 3 = s3 at h ⊢
  generalize v 4 = s4 at h ⊢
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;>
    simp_all [isCrossedResidue]
  rcases h with ⟨rfl, rfl, hne⟩
  exact crossed_word_reduces_explicit _ _ hne

private theorem reduced_sum_fifth_three_residues
    (F : List ReducerSymbol → Mat6) :
    (∑ v : Fin 5 → ReducerSymbol,
      ((1 / 6 : ℂ) ^ (reduceProjectorWord 5 (allWord v)).1) •
        F (reduceProjectorWord 5 (allWord v)).2) =
      (∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
          (fun v => (reduceProjectorWord 5 (allWord v)).2 = [none]),
          (1 / 6 : ℂ) ^ (reduceProjectorWord 5 (allWord v)).1) • F [none] +
      (∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
          (fun v => (reduceProjectorWord 5 (allWord v)).2 = []),
          (1 / 6 : ℂ) ^ (reduceProjectorWord 5 (allWord v)).1) • F [] +
      ∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
          (fun v => isCrossedResidue (allWord v)), F (allWord v) := by
  classical
  let out : (Fin 5 → ReducerSymbol) → Nat × List ReducerSymbol := fun v =>
    reduceProjectorWord 5 (allWord v)
  let coeff : (Fin 5 → ReducerSymbol) → ℂ := fun v => (1 / 6 : ℂ) ^ (out v).1
  have hpoint (v : Fin 5 → ReducerSymbol) :
      coeff v • F (out v).2 =
        (if (out v).2 = [none] then coeff v • F [none] else 0) +
        (if (out v).2 = [] then coeff v • F [] else 0) +
        (if isCrossedResidue (allWord v) then F (allWord v) else 0) := by
    rcases all_word_5_exhaustive v with hnil | hanchor | hcross
    · have hncross : ¬isCrossedResidue (allWord v) := by
        intro hc
        have hr := crossed_word_reduces_to_self v hc
        rw [hr] at hnil
        change allWord v = [] at hnil
        rw [hnil] at hc
        simp [isCrossedResidue] at hc
      simp [out, hnil, hncross]
    · have hncross : ¬isCrossedResidue (allWord v) := by
        intro hc
        have hr := crossed_word_reduces_to_self v hc
        rw [hr] at hanchor
        change allWord v = [none] at hanchor
        rw [hanchor] at hc
        simp [isCrossedResidue] at hc
      simp [out, hanchor, hncross]
    · rcases hcross with ⟨hout, hc⟩
      change out v = (0, allWord v) at hout
      rw [hout]
      have hnanchor : allWord v ≠ [none] := by
        intro hw
        rw [hw] at hc
        simp [isCrossedResidue] at hc
      have hnnil : allWord v ≠ [] := by
        intro hw
        rw [hw] at hc
        simp [isCrossedResidue] at hc
      simp [coeff, hout, hc, hnanchor, hnnil]
  calc
    (∑ v : Fin 5 → ReducerSymbol, coeff v • F (out v).2) =
        ∑ v : Fin 5 → ReducerSymbol,
          ((if (out v).2 = [none] then coeff v • F [none] else 0) +
          (if (out v).2 = [] then coeff v • F [] else 0) +
          (if isCrossedResidue (allWord v) then F (allWord v) else 0)) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hpoint v
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
      rw [← Finset.sum_smul, ← Finset.sum_smul]

/-- Exact first conditional moment, obtained from the all-word histogram. -/
theorem anchored_first_moment_all_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ 1) =
      (46656 : ℂ) • projector U a + (46656 : ℂ) • (1 : Mat6) := by
  rw [assignment_moment_eq_reduced_words U B hMUB a 1]
  rw [reduced_sum_two_residues 1
    (fun w => ∑ j : Assignment6,
      evalAssignmentWord (projector U a)
        (fun y b => projector (B y) b) j w)
    all_word_1_exhaustive]
  rw [CompleteMUBFiveMoment.weighted_residue_eq_counts 1 (by omega) [none],
    CompleteMUBFiveMoment.weighted_residue_eq_counts 1 (by omega) []]
  rw [assignment_eval_anchor, assignment_eval_nil]
  rcases all_word_1_counts with ⟨hp0, hi1⟩
  have hp1 : allWordCount 1 1 [none] = 0 := by decide
  have hi0 : allWordCount 1 0 [] = 0 := by decide
  have hp2 := allWordCount_eq_zero_of_fuel_lt 1 2 [none] (by omega)
  have hp3 := allWordCount_eq_zero_of_fuel_lt 1 3 [none] (by omega)
  have hp4 := allWordCount_eq_zero_of_fuel_lt 1 4 [none] (by omega)
  have hp5 := allWordCount_eq_zero_of_fuel_lt 1 5 [none] (by omega)
  have hi2 := allWordCount_eq_zero_of_fuel_lt 1 2 [] (by omega)
  have hi3 := allWordCount_eq_zero_of_fuel_lt 1 3 [] (by omega)
  have hi4 := allWordCount_eq_zero_of_fuel_lt 1 4 [] (by omega)
  have hi5 := allWordCount_eq_zero_of_fuel_lt 1 5 [] (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hi0, hi1, hi2, hi3, hi4, hi5]
  norm_num

/-- Exact second conditional moment, obtained from the all-word histogram. -/
theorem anchored_second_moment_all_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ 2) =
      (139968 : ℂ) • projector U a + (85536 : ℂ) • (1 : Mat6) := by
  rw [assignment_moment_eq_reduced_words U B hMUB a 2]
  rw [reduced_sum_two_residues 2
    (fun w => ∑ j : Assignment6,
      evalAssignmentWord (projector U a)
        (fun y b => projector (B y) b) j w)
    all_word_2_exhaustive]
  rw [CompleteMUBFiveMoment.weighted_residue_eq_counts 2 (by omega) [none],
    CompleteMUBFiveMoment.weighted_residue_eq_counts 2 (by omega) []]
  rw [assignment_eval_anchor, assignment_eval_nil]
  rcases all_word_2_counts with ⟨hp0, hp1, hi1, hi2⟩
  have hp2 : allWordCount 2 2 [none] = 0 := by decide
  have hi0 : allWordCount 2 0 [] = 0 := by decide
  have hp3 := allWordCount_eq_zero_of_fuel_lt 2 3 [none] (by omega)
  have hp4 := allWordCount_eq_zero_of_fuel_lt 2 4 [none] (by omega)
  have hp5 := allWordCount_eq_zero_of_fuel_lt 2 5 [none] (by omega)
  have hi3 := allWordCount_eq_zero_of_fuel_lt 2 3 [] (by omega)
  have hi4 := allWordCount_eq_zero_of_fuel_lt 2 4 [] (by omega)
  have hi5 := allWordCount_eq_zero_of_fuel_lt 2 5 [] (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hi0, hi1, hi2, hi3, hi4, hi5]
  norm_num
  module

/-- Exact third conditional moment, obtained from the all-word histogram. -/
theorem anchored_third_moment_all_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ 3) =
      (396576 : ℂ) • projector U a + (196992 : ℂ) • (1 : Mat6) := by
  rw [assignment_moment_eq_reduced_words U B hMUB a 3]
  rw [reduced_sum_two_residues 3
    (fun w => ∑ j : Assignment6,
      evalAssignmentWord (projector U a)
        (fun y b => projector (B y) b) j w)
    all_word_3_exhaustive]
  rw [CompleteMUBFiveMoment.weighted_residue_eq_counts 3 (by omega) [none],
    CompleteMUBFiveMoment.weighted_residue_eq_counts 3 (by omega) []]
  rw [assignment_eval_anchor, assignment_eval_nil]
  rcases all_word_3_counts with ⟨hp0, hp1, hp2, hi1, hi2, hi3⟩
  have hp3 : allWordCount 3 3 [none] = 0 := by decide
  have hi0 : allWordCount 3 0 [] = 0 := by decide
  have hp4 := allWordCount_eq_zero_of_fuel_lt 3 4 [none] (by omega)
  have hp5 := allWordCount_eq_zero_of_fuel_lt 3 5 [none] (by omega)
  have hi4 := allWordCount_eq_zero_of_fuel_lt 3 4 [] (by omega)
  have hi5 := allWordCount_eq_zero_of_fuel_lt 3 5 [] (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hi0, hi1, hi2, hi3, hi4, hi5]
  norm_num
  module

/-- Exact fourth conditional moment, obtained from the all-word histogram. -/
theorem anchored_fourth_moment_all_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ 4) =
      (1130112 : ℂ) • projector U a + (504144 : ℂ) • (1 : Mat6) := by
  rw [assignment_moment_eq_reduced_words U B hMUB a 4]
  rw [reduced_sum_two_residues 4
    (fun w => ∑ j : Assignment6,
      evalAssignmentWord (projector U a)
        (fun y b => projector (B y) b) j w)
    all_word_4_exhaustive]
  rw [CompleteMUBFiveMoment.weighted_residue_eq_counts 4 (by omega) [none],
    CompleteMUBFiveMoment.weighted_residue_eq_counts 4 (by omega) []]
  rw [assignment_eval_anchor, assignment_eval_nil]
  rcases all_word_4_counts with ⟨hp0, hp1, hp2, hp3,
    hi1, hi2, hi3, hi4⟩
  have hp4 : allWordCount 4 4 [none] = 0 := by
    set_option maxRecDepth 100000 in decide
  have hi0 : allWordCount 4 0 [] = 0 := by
    set_option maxRecDepth 100000 in decide
  have hp5 := allWordCount_eq_zero_of_fuel_lt 4 5 [none] (by omega)
  have hi5 := allWordCount_eq_zero_of_fuel_lt 4 5 [] (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hi0, hi1, hi2, hi3, hi4, hi5]
  norm_num
  module

/-- Exact fifth conditional moment, including the crossed equality orbit. -/
theorem anchored_fifth_moment_all_words
    (U : Mat6) (B : Fin 6 → Mat6)
    (hMUB : IsMUBFamily (Fin.cons U B)) (a : Fin 6) :
    (∑ j : Assignment6, anchoredSelectedSum U B a j ^ 5) =
      (3256848 : ℂ) • projector U a + (1363824 : ℂ) • (1 : Mat6) := by
  rw [assignment_moment_eq_reduced_words U B hMUB a 5]
  rw [reduced_sum_fifth_three_residues
    (fun w => ∑ j : Assignment6,
      evalAssignmentWord (projector U a)
        (fun y b => projector (B y) b) j w)]
  rw [CompleteMUBFiveMoment.weighted_residue_eq_counts 5 (by omega) [none],
    CompleteMUBFiveMoment.weighted_residue_eq_counts 5 (by omega) []]
  rw [assignment_eval_anchor, assignment_eval_nil]
  have hcross :
      (∑ v ∈ (Finset.univ : Finset (Fin 5 → ReducerSymbol)).filter
          (fun v => isCrossedResidue (allWord v)),
          ∑ j : Assignment6,
            evalAssignmentWord (projector U a)
              (fun y b => projector (B y) b) j (allWord v)) =
        (1296 : ℂ) • ((1 : Mat6) - projector U a) := by
    rw [crossed_word_sum_reindex
      (fun w => ∑ j : Assignment6,
        evalAssignmentWord (projector U a)
          (fun y b => projector (B y) b) j w)]
    let G := fun (y z : Fin 6) (j : Assignment6) =>
      evalAssignmentWord (projector U a)
        (fun x b => projector (B x) b) j
        [some y, some z, none, some y, some z]
    have herase (x : Fin 6) :
        (Finset.univ : Finset (Fin 6)).erase x =
          Finset.univ.filter (fun t => t ≠ x) := by
      ext t
      simp
    have hswap :
        (∑ y : Fin 6, ∑ z ∈ Finset.univ.erase y, ∑ j : Assignment6, G y z j) =
          ∑ z : Fin 6, ∑ y ∈ Finset.univ.erase z, ∑ j : Assignment6, G y z j := by
      simp_rw [herase, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : y = z
      · simp [h]
      · simp [h, Ne.symm h]
    change (∑ y : Fin 6, ∑ z ∈ Finset.univ.erase y,
      ∑ j : Assignment6, G y z j) = _
    rw [hswap]
    calc
      (∑ z : Fin 6, ∑ y ∈ Finset.univ.erase z,
          ∑ j : Assignment6, G y z j) =
          ∑ z : Fin 6, ∑ j : Assignment6,
            ∑ y ∈ Finset.univ.erase z, G y z j := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.sum_comm]
      _ = ∑ j : Assignment6, ∑ z : Fin 6,
          ∑ y ∈ Finset.univ.erase z, G y z j := by
            rw [Finset.sum_comm]
      _ = (1296 : ℂ) • ((1 : Mat6) - projector U a) := by
            simpa [G, evalAssignmentWord, evalReducerWord, mul_assoc] using
              assignment_crossed_orbit U B hMUB a
  rw [hcross]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [all_word_5_p0, all_word_5_p1, all_word_5_p2, all_word_5_p3,
    all_word_5_p4, all_word_5_p5, all_word_5_i0, all_word_5_i1,
    all_word_5_i2, all_word_5_i3, all_word_5_i4, all_word_5_i5]
  norm_num
  module

end CompleteMUBDegreeFiveCount

open Matrix MUBCP

namespace CompleteMUBFiveMoment

/-- Any chosen basis of a complete family can be moved to the head, with the
remaining six bases enumerated by `succAbove`. -/
lemma isMUBFamily_cons_succAbove (V : Fin 7 → Mat6)
    (hV : IsMUBFamily V) (r : Fin 7) :
    IsMUBFamily (Fin.cons (V r) (fun y : Fin 6 => V (r.succAbove y))) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun y => ?_) i
    · simpa using hV.1 r
    · simpa using hV.1 (r.succAbove y)
  · intro i
    refine Fin.cases ?_ (fun y => ?_) i
    · intro j
      refine Fin.cases ?_ (fun z => ?_) j
      · intro hij a b
        exact (hij rfl).elim
      · intro hij a b
        have hm := hV.2 r (r.succAbove z) (Fin.ne_succAbove r z) a b
        simpa using hm
    · intro j
      refine Fin.cases ?_ (fun z => ?_) j
      · intro hij a b
        have hm := hV.2 (r.succAbove y) r (Fin.succAbove_ne r y) a b
        simpa using hm
      · intro hij a b
        have hyz : y ≠ z := by simpa using hij
        have hne : r.succAbove y ≠ r.succAbove z := by simpa using hyz
        have hm := hV.2 (r.succAbove y) (r.succAbove z) hne a b
        simpa using hm

/-- Expand the fifth power of a six-term noncommutative matrix sum into its
five independent basis-label coordinates. -/
lemma fifth_power_fin6_sum_expansion (q : Fin 6 → Mat6) :
    (∑ y, q y) ^ 5 =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, q a * q b * q c * q d * q e := by
  calc
    (∑ y, q y) ^ 5 =
        (∑ a, q a) * ((∑ b, q b) * ((∑ c, q c) *
          ((∑ d, q d) * (∑ e, q e)))) := by
      simp [pow_succ, Matrix.mul_assoc]
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        q a * (q b * (q c * (q d * q e))) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        q a * q b * q c * q d * q e := by
      simp only [Matrix.mul_assoc]

end CompleteMUBFiveMoment

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
  ComplexConjugate

namespace CompleteMUBDegreeFiveAssembly

noncomputable section

abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℂ
abbrev Assignment6 := Fin 7 → Fin 6

def selectedSum (P : Fin 7 → Fin 6 → Mat6) (j : Assignment6) : Mat6 :=
  ∑ x, P x (j x)

def conditionalPower (P : Fin 7 → Fin 6 → Mat6)
    (m : ℕ) (x : Fin 7) (a : Fin 6) : Mat6 :=
  ∑ j : Assignment6, if j x = a then selectedSum P j ^ m else 0

/-- The five exact conditional power identities used by the assembly theorem.
The coefficients are the raw sums over the `6^6` assignments with one outcome fixed. -/
structure FifthMomentIdentities (P : Fin 7 → Fin 6 → Mat6) : Prop where
  power_one : ∀ x a,
    conditionalPower P 1 x a =
      (46656 : ℝ) • P x a + (46656 : ℝ) • (1 : Mat6)
  power_two : ∀ x a,
    conditionalPower P 2 x a =
      (139968 : ℝ) • P x a + (85536 : ℝ) • (1 : Mat6)
  power_three : ∀ x a,
    conditionalPower P 3 x a =
      (396576 : ℝ) • P x a + (196992 : ℝ) • (1 : Mat6)
  power_four : ∀ x a,
    conditionalPower P 4 x a =
      (1130112 : ℝ) • P x a + (504144 : ℝ) • (1 : Mat6)
  power_five : ∀ x a,
    conditionalPower P 5 x a =
      (3256848 : ℝ) • P x a + (1363824 : ℝ) • (1 : Mat6)

def shiftedProduct (S : Mat6) : Mat6 :=
  (S - (1 / 2 : ℝ) • (1 : Mat6)) *
    (S - (7 / 4 : ℝ) • (1 : Mat6))

/-- Congruence form of `S(S-I/2)^2(S-7I/4)^2`; positivity is immediate. -/
def degreeFiveKernel (S : Mat6) : Mat6 :=
  Matrix.conjTranspose (shiftedProduct S) * S * shiftedProduct S

def degreeFivePolynomial (S : Mat6) : Mat6 :=
  S ^ 5 - (9 / 2 : ℝ) • S ^ 4 + (109 / 16 : ℝ) • S ^ 3 -
    (63 / 16 : ℝ) • S ^ 2 + (49 / 64 : ℝ) • S

def candidateParent (P : Fin 7 → Fin 6 → Mat6) (j : Assignment6) : Mat6 :=
  (1 / 1174257 : ℝ) • degreeFiveKernel (selectedSum P j)

def IsDepolarizingParent (P : Fin 7 → Fin 6 → Mat6) (eta : ℝ)
    (G : Assignment6 → Mat6) : Prop :=
  (∀ j, (G j).PosSemidef) ∧
  (∑ j, G j) = 1 ∧
  ∀ x a,
    (∑ j, if j x = a then G j else 0) =
      eta • P x a + ((1 - eta) / 6) • (1 : Mat6)

theorem degreeFiveKernel_posSemidef {S : Mat6} (hS : S.PosSemidef) :
    (degreeFiveKernel S).PosSemidef := by
  exact hS.conjTranspose_mul_mul_same (shiftedProduct S)

theorem degreeFiveKernel_eq_polynomial {S : Mat6} (hS : S.IsHermitian) :
    degreeFiveKernel S = degreeFivePolynomial S := by
  unfold degreeFiveKernel shiftedProduct degreeFivePolynomial
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hS.eq]
  norm_num
  simp only [sub_mul, mul_sub, add_mul, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_mul, mul_one, pow_succ, pow_zero, mul_assoc]
  module

theorem selectedSum_posSemidef
    {P : Fin 7 → Fin 6 → Mat6}
    (hP : ∀ x a, (P x a).PosSemidef) (j : Assignment6) :
    (selectedSum P j).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun x _ =>
    Matrix.nonneg_iff_posSemidef.mpr (hP x (j x))

theorem conditionalKernel_eq
    {P : Fin 7 → Fin 6 → Mat6}
    (hP : ∀ x a, (P x a).PosSemidef)
    (hm : FifthMomentIdentities P) (x : Fin 7) (a : Fin 6) :
    (∑ j : Assignment6,
      if j x = a then degreeFiveKernel (selectedSum P j) else 0) =
      (357615 : ℝ) • P x a + (136107 : ℝ) • (1 : Mat6) := by
  have hk (j : Assignment6) :
      degreeFiveKernel (selectedSum P j) =
        degreeFivePolynomial (selectedSum P j) :=
    degreeFiveKernel_eq_polynomial (selectedSum_posSemidef hP j).isHermitian
  simp_rw [hk]
  have hexpand :
      (∑ j : Assignment6,
        if j x = a then degreeFivePolynomial (selectedSum P j) else 0) =
        conditionalPower P 5 x a -
          (9 / 2 : ℝ) • conditionalPower P 4 x a +
          (109 / 16 : ℝ) • conditionalPower P 3 x a -
          (63 / 16 : ℝ) • conditionalPower P 2 x a +
          (49 / 64 : ℝ) • conditionalPower P 1 x a := by
    have hpoint (j : Assignment6) :
        (if j x = a then degreeFivePolynomial (selectedSum P j) else 0) =
          (if j x = a then selectedSum P j ^ 5 else 0) -
          (9 / 2 : ℝ) • (if j x = a then selectedSum P j ^ 4 else 0) +
          (109 / 16 : ℝ) • (if j x = a then selectedSum P j ^ 3 else 0) -
          (63 / 16 : ℝ) • (if j x = a then selectedSum P j ^ 2 else 0) +
          (49 / 64 : ℝ) • (if j x = a then selectedSum P j else 0) := by
      by_cases h : j x = a <;> simp [h, degreeFivePolynomial]
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      conditionalPower, pow_one]
    repeat rw [← Finset.smul_sum]
  rw [hexpand, hm.power_five x a, hm.power_four x a,
    hm.power_three x a, hm.power_two x a, hm.power_one x a]
  module

theorem conditionalCandidate_eq
    {P : Fin 7 → Fin 6 → Mat6}
    (hP : ∀ x a, (P x a).PosSemidef)
    (hm : FifthMomentIdentities P) (x : Fin 7) (a : Fin 6) :
    (∑ j : Assignment6,
      if j x = a then candidateParent P j else 0) =
      (4415 / 14497 : ℝ) • P x a +
        (5041 / 43491 : ℝ) • (1 : Mat6) := by
  rw [show (∑ j : Assignment6,
      if j x = a then candidateParent P j else 0) =
      (1 / 1174257 : ℝ) •
        ∑ j : Assignment6,
          if j x = a then degreeFiveKernel (selectedSum P j) else 0 by
    calc
      _ = ∑ j : Assignment6, (1 / 1174257 : ℝ) •
          (if j x = a then degreeFiveKernel (selectedSum P j) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : j x = a <;> simp [h, candidateParent]
      _ = _ := by rw [Finset.smul_sum]]
  rw [conditionalKernel_eq hP hm x a]
  module

theorem parentAssembly
    {P : Fin 7 → Fin 6 → Mat6}
    (hP : ∀ x a, (P x a).PosSemidef)
    (hcomplete : ∀ x, ∑ a, P x a = 1)
    (hm : FifthMomentIdentities P) :
    IsDepolarizingParent P (4415 / 14497) (candidateParent P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    apply Matrix.nonneg_iff_posSemidef.mp
    exact smul_nonneg (by norm_num) <|
      Matrix.nonneg_iff_posSemidef.mpr <|
        degreeFiveKernel_posSemidef (selectedSum_posSemidef hP j)
  · have hpartition (x : Fin 7) :
        (∑ j : Assignment6, candidateParent P j) =
          ∑ a : Fin 6, ∑ j : Assignment6,
            if j x = a then candidateParent P j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp
    rw [hpartition 0]
    simp_rw [conditionalCandidate_eq hP hm]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hcomplete 0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    module
  · intro x a
    rw [conditionalCandidate_eq hP hm x a]
    congr 1
    norm_num

theorem generalizedVisibility_conversion :
    (1 + 5 * (4415 / 14497 : ℝ)) / 6 = 18286 / 43491 := by
  norm_num


end
end CompleteMUBDegreeFiveAssembly

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix MUBCP

namespace CompleteMUBDegreeFiveParent

abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℂ
abbrev FullAssignment := Fin 7 → Fin 6
abbrev ReducedAssignment := Fin 6 → Fin 6

/-- Split a seven-basis assignment into its value at one chosen basis and the
six values on the complementary bases. -/
def splitAssignment7 (x : Fin 7) :
    FullAssignment ≃ (Fin 6 × ReducedAssignment) :=
  (Equiv.piCongrLeft' (fun _ : Fin 7 => Fin 6) (finSuccEquiv' x)).trans
    Equiv.piOptionEquivProd

@[simp] theorem splitAssignment7_fst (x : Fin 7) (j : FullAssignment) :
    (splitAssignment7 x j).1 = j x := by
  simp [splitAssignment7, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

@[simp] theorem splitAssignment7_snd (x : Fin 7) (j : FullAssignment)
    (y : Fin 6) :
    (splitAssignment7 x j).2 y = j (x.succAbove y) := by
  simp [splitAssignment7, Equiv.piCongrLeft', Equiv.piOptionEquivProd]

/-- Fixing one outcome in the seven-basis conditional power is exactly the
anchored six-coordinate assignment moment after moving that basis to the head. -/
theorem conditionalPower_projectors_eq_anchored
    (V : Fin 7 → Mat6) (m : ℕ) (x : Fin 7) (a : Fin 6) :
    CompleteMUBDegreeFiveAssembly.conditionalPower
        (fun z b => projector (V z) b) m x a =
      ∑ j : ReducedAssignment,
        CompleteMUBDegreeFiveCount.anchoredSelectedSum
          (V x) (fun y => V (x.succAbove y)) a j ^ m := by
  unfold CompleteMUBDegreeFiveAssembly.conditionalPower
    CompleteMUBDegreeFiveAssembly.selectedSum
  let E := splitAssignment7 x
  let g : Fin 6 × ReducedAssignment → Mat6 := fun p =>
    if p.1 = a then
      (projector (V x) p.1 +
        ∑ y : Fin 6, projector (V (x.succAbove y)) (p.2 y)) ^ m
    else 0
  calc
    (∑ j : FullAssignment,
      if j x = a then (∑ z, projector (V z) (j z)) ^ m else 0) =
        ∑ j : FullAssignment, g (E j) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [g, E, splitAssignment7_fst, splitAssignment7_snd]
          congr 2
          exact Fin.sum_univ_succAbove
            (fun z => projector (V z) (j z)) x
    _ = ∑ p : Fin 6 × ReducedAssignment, g p := E.sum_comp g
    _ = ∑ b : Fin 6, ∑ j : ReducedAssignment, g (b, j) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : ReducedAssignment,
        CompleteMUBDegreeFiveCount.anchoredSelectedSum
          (V x) (fun y => V (x.succAbove y)) a j ^ m := by
      rw [Finset.sum_eq_single a]
      · simp [g, CompleteMUBDegreeFiveCount.anchoredSelectedSum]
      · intro b _ hba
        simp [g, hba]
      · simp

theorem projector_posSemidef (U : Mat6) (a : Fin 6) :
    (projector U a).PosSemidef := by
  unfold projector
  exact Matrix.posSemidef_vecMulVec_self_star (fun i => U i a)

theorem complete_family_projector_sum
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) (x : Fin 7) :
    ∑ a, projector (V x) a = 1 := by
  exact CompleteMUBDegreeFiveCount.mubcp_projector_sum (V x) (hV.1 x)

theorem complete_family_power_one
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) (x : Fin 7) (a : Fin 6) :
    CompleteMUBDegreeFiveAssembly.conditionalPower
        (fun z b => projector (V z) b) 1 x a =
      (46656 : ℝ) • projector (V x) a + (46656 : ℝ) • (1 : Mat6) := by
  rw [conditionalPower_projectors_eq_anchored]
  have hx := CompleteMUBFiveMoment.isMUBFamily_cons_succAbove V hV x
  rw [CompleteMUBDegreeFiveCount.anchored_first_moment_all_words
    (V x) (fun y => V (x.succAbove y)) hx a]
  ext i j
  norm_num [RCLike.real_smul_eq_coe_smul]

theorem complete_family_power_two
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) (x : Fin 7) (a : Fin 6) :
    CompleteMUBDegreeFiveAssembly.conditionalPower
        (fun z b => projector (V z) b) 2 x a =
      (139968 : ℝ) • projector (V x) a + (85536 : ℝ) • (1 : Mat6) := by
  rw [conditionalPower_projectors_eq_anchored]
  have hx := CompleteMUBFiveMoment.isMUBFamily_cons_succAbove V hV x
  rw [CompleteMUBDegreeFiveCount.anchored_second_moment_all_words
    (V x) (fun y => V (x.succAbove y)) hx a]
  ext i j
  norm_num [RCLike.real_smul_eq_coe_smul]

theorem complete_family_power_three
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) (x : Fin 7) (a : Fin 6) :
    CompleteMUBDegreeFiveAssembly.conditionalPower
        (fun z b => projector (V z) b) 3 x a =
      (396576 : ℝ) • projector (V x) a + (196992 : ℝ) • (1 : Mat6) := by
  rw [conditionalPower_projectors_eq_anchored]
  have hx := CompleteMUBFiveMoment.isMUBFamily_cons_succAbove V hV x
  rw [CompleteMUBDegreeFiveCount.anchored_third_moment_all_words
    (V x) (fun y => V (x.succAbove y)) hx a]
  ext i j
  norm_num [RCLike.real_smul_eq_coe_smul]

theorem complete_family_power_four
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) (x : Fin 7) (a : Fin 6) :
    CompleteMUBDegreeFiveAssembly.conditionalPower
        (fun z b => projector (V z) b) 4 x a =
      (1130112 : ℝ) • projector (V x) a + (504144 : ℝ) • (1 : Mat6) := by
  rw [conditionalPower_projectors_eq_anchored]
  have hx := CompleteMUBFiveMoment.isMUBFamily_cons_succAbove V hV x
  rw [CompleteMUBDegreeFiveCount.anchored_fourth_moment_all_words
    (V x) (fun y => V (x.succAbove y)) hx a]
  ext i j
  norm_num [RCLike.real_smul_eq_coe_smul]

/-- Assemble the exact five conditional moments once the fifth anchored moment
has been supplied; the first four are already unconditional consequences of a
complete dimension-six MUB family. -/
theorem projectorMomentIdentities_of_fifth
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V)
    (hfive : ∀ x : Fin 7, ∀ a : Fin 6,
      (∑ j : ReducedAssignment,
        CompleteMUBDegreeFiveCount.anchoredSelectedSum
          (V x) (fun y => V (x.succAbove y)) a j ^ 5) =
        (3256848 : ℂ) • projector (V x) a +
          (1363824 : ℂ) • (1 : Mat6)) :
    CompleteMUBDegreeFiveAssembly.FifthMomentIdentities
      (fun x a => projector (V x) a) := by
  constructor
  · exact complete_family_power_one V hV
  · exact complete_family_power_two V hV
  · exact complete_family_power_three V hV
  · exact complete_family_power_four V hV
  · intro x a
    rw [conditionalPower_projectors_eq_anchored, hfive x a]
    ext i j
    norm_num [RCLike.real_smul_eq_coe_smul]

theorem complete_mub_degree_five_parent_of_anchored_fifth
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V)
    (hfive : ∀ x : Fin 7, ∀ a : Fin 6,
      (∑ j : ReducedAssignment,
        CompleteMUBDegreeFiveCount.anchoredSelectedSum
          (V x) (fun y => V (x.succAbove y)) a j ^ 5) =
        (3256848 : ℂ) • projector (V x) a +
          (1363824 : ℂ) • (1 : Mat6)) :
    CompleteMUBDegreeFiveAssembly.IsDepolarizingParent
      (fun x a => projector (V x) a) (4415 / 14497)
      (CompleteMUBDegreeFiveAssembly.candidateParent
        (fun x a => projector (V x) a)) := by
  exact CompleteMUBDegreeFiveAssembly.parentAssembly
    (fun x a => projector_posSemidef (V x) a)
    (complete_family_projector_sum V hV)
    (projectorMomentIdentities_of_fifth V hV hfive)

/-- Any complete family of seven mutually unbiased bases in dimension six has
the explicit degree-five parent POVM at depolarizing visibility `4415/14497`.
The `IsDepolarizingParent` conclusion simultaneously certifies positivity,
normalization, and every noisy projector marginal. -/
theorem complete_mub_degree_five_parent
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) :
    CompleteMUBDegreeFiveAssembly.IsDepolarizingParent
      (fun x a => projector (V x) a) (4415 / 14497)
      (CompleteMUBDegreeFiveAssembly.candidateParent
        (fun x a => projector (V x) a)) := by
  apply complete_mub_degree_five_parent_of_anchored_fifth V hV
  intro x a
  exact CompleteMUBDegreeFiveCount.anchored_fifth_moment_all_words
    (V x) (fun y => V (x.succAbove y))
    (CompleteMUBFiveMoment.isMUBFamily_cons_succAbove V hV x) a

/-- The parent POVM result together with its generalized-visibility value. -/
theorem complete_mub_degree_five_parent_and_visibility
    (V : Fin 7 → Mat6) (hV : IsMUBFamily V) :
    CompleteMUBDegreeFiveAssembly.IsDepolarizingParent
        (fun x a => projector (V x) a) (4415 / 14497)
        (CompleteMUBDegreeFiveAssembly.candidateParent
          (fun x a => projector (V x) a)) ∧
      (1 + 5 * (4415 / 14497 : ℝ)) / 6 = 18286 / 43491 := by
  exact ⟨complete_mub_degree_five_parent V hV,
    CompleteMUBDegreeFiveAssembly.generalizedVisibility_conversion⟩


end CompleteMUBDegreeFiveParent
