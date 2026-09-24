import Mathlib

/-!
# Permanent determinantal complexity: ceiling(n²/2) + 1 in characteristic zero

For every characteristic-zero field F, all natural numbers n and m, and every
m by m matrix L of polynomials over F in n by n variables, if each entry has
total degree at most one and det(L) is the ordinary permanent polynomial,
`permanent_determinantal_bound_all_sizes` proves

    n * n + (if 3 <= n then 2 else 0) <= 2 * m.

Thus n² <= 2m for every n, and n² + 2 <= 2m whenever n >= 3. Equivalently,
dc(perm_n) >= ceiling(n²/2) + 1 for every n >= 3, both even and odd.
`permanent_determinantal_bound_ceiling` states the rounded integer bound using
natural-number division: (n*n + 1)/2 + 1 <= m.
There are no additional Hessian, embedding, algebraic-closure, or
minimum-attainment hypotheses: the result applies to every affine
determinantal representation, hence in particular to one of minimum size.

## The existing theorem subsumed

Thierry Mignon and Nicolas Ressayre, "A quadratic bound for the determinant
and permanent problem", International Mathematics Research Notices 2004,
no. 79, pp. 4241-4253, Theorem 2 in the authors' version, proves
dc(perm_n) >= n²/2 over every characteristic-zero field.

`mignon_ressayre_theorem_two` recovers its complete field and size scope.
For every n >= 3, the rounded integer lower bound increases by one, from
ceiling(n²/2) to ceiling(n²/2) + 1. This is an additive improvement, not an
asymptotic improvement or a claim of priority over all subsequent literature.

Authors' version: https://math.univ-lyon1.fr/~ressayre/PDFs/permdet.pdf
Published article: https://doi.org/10.1155/S1073792804142566

The proof combines the nondegenerate Hessian at the Mignon-Ressayre point,
zero spaces spanning the tangent hyperplane, and homogeneity: adjoining the
base point to an affine zero direction space gives a linear zero space,
whose Hessian-isotropic dimension bound supplies the parity refinement.
The small sizes are proved separately. This file imports only Mathlib.
-/

variable {F : Type} [Field F] [CharZero F]

section
/-! ## Hessian identities -/

namespace PermanentBound.Hessian

open MvPolynomial

section Euler

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def grad (f : MvPolynomial ι K) (x : ι → K) : ι → K :=
  fun i => MvPolynomial.eval x (pderiv i f)

noncomputable def hess (f : MvPolynomial ι K) (x : ι → K) : Matrix ι ι K :=
  fun i j => MvPolynomial.eval x (pderiv j (pderiv i f))

theorem euler_eval {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d) (x : ι → K) :
    ∑ i, x i * grad f x i = (d : K) * MvPolynomial.eval x f := by
  have h := congrArg (MvPolynomial.eval x) hf.sum_X_mul_pderiv
  simpa [grad, map_sum, map_mul, MvPolynomial.eval_X, nsmul_eq_mul] using h

theorem hess_mulVec_self {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d) (x : ι → K) :
    (hess f x).mulVec x = ((d - 1 : ℕ) : K) • grad f x := by
  funext i
  have h := euler_eval (hf.pderiv (i := i)) x
  simp only [grad] at h
  simp only [Matrix.mulVec, dotProduct, hess, Pi.smul_apply, smul_eq_mul, grad]
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem self_tangent_of_eval_eq_zero {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d)
    {x : ι → K} (hx : MvPolynomial.eval x f = 0) : ∑ i, x i * grad f x i = 0 := by
  rw [euler_eval hf, hx, mul_zero]

theorem radical {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d) (x v : ι → K)
    (hv : ∑ i, v i * grad f x i = 0) : v ⬝ᵥ ((hess f x).mulVec x) = 0 := by
  rw [hess_mulVec_self hf, dotProduct_smul]
  have : v ⬝ᵥ grad f x = 0 := hv
  rw [this, smul_zero]

theorem self_radical {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d) {x : ι → K}
    (hx : MvPolynomial.eval x f = 0) : x ⬝ᵥ ((hess f x).mulVec x) = 0 :=
  radical hf x x (self_tangent_of_eval_eq_zero hf hx)

theorem grad_dot_solution_eq_zero {d : ℕ} {f : MvPolynomial ι K} (hf : f.IsHomogeneous d)
    {x : ι → K} (hx : MvPolynomial.eval x f = 0) (hd : (d : K) ≠ 1) :
    grad f x ⬝ᵥ (((d : K) - 1)⁻¹ • x) = 0 := by
  rw [dotProduct_smul, dotProduct_comm]
  have : x ⬝ᵥ grad f x = 0 := self_tangent_of_eval_eq_zero hf hx
  rw [this, smul_zero]

end Euler

section Isotropic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem two_mul_finrank_le_of_isotropic {B : LinearMap.BilinForm K V} (hB : B.IsRefl)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) {W : Submodule K V}
    (hW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have h1 : W ≤ B.orthogonal W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    exact hW w hw v hv
  have h2 : B.orthogonal ⊤ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
    exact hnd v fun w => hB w v (hv w Submodule.mem_top)
  have h3 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hB W
  rw [h2, inf_bot_eq, finrank_bot, add_zero] at h3
  have h4 := Submodule.finrank_mono h1
  omega

variable [NeZero (2 : K)]

theorem isotropic_of_vanishes_on_affine (Q : QuadraticMap K V K) {x : V} (hx : Q x = 0)
    {U : Submodule K V} (h : ∀ u ∈ U, Q (x + u) = 0) :
    (∀ u ∈ U, Q u = 0) ∧ ∀ u ∈ U, ∀ u' ∈ U, QuadraticMap.polar Q u u' = 0 := by
  have key : ∀ u ∈ U, Q u = 0 ∧ QuadraticMap.polar Q x u = 0 := by
    intro u hu
    have h1 := h u hu
    have h2 := h ((2 : K) • u) (U.smul_mem _ hu)
    rw [QuadraticMap.map_add (⇑Q) x u, hx, zero_add] at h1
    rw [QuadraticMap.map_add (⇑Q) x ((2 : K) • u), hx, zero_add, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, smul_eq_mul] at h2
    have hsum : 2 * Q u = 0 := by linear_combination h2 - 2 * h1
    have hQ : Q u = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h (NeZero.ne 2)
      · exact h
    exact ⟨hQ, by linear_combination h1 - hQ⟩
  refine ⟨fun u hu => (key u hu).1, fun u hu u' hu' => ?_⟩
  have h3 := (key (u + u') (U.add_mem hu hu')).1
  rw [QuadraticMap.map_add (⇑Q) u u', (key u hu).1, (key u' hu').1, zero_add, zero_add] at h3
  exact h3

end Isotropic

theorem mr_bound_of_covering_and_isotropy {N m g : ℕ} (hcov : N ≤ m + g) (hiso : 2 * g ≤ N) :
    N ≤ 2 * m := by omega

end PermanentBound.Hessian

end
section
/-! ## Affine zero spaces -/

namespace PermanentBound.AffineZeroSpaces

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m] {ι : Type*} [Fintype ι]

structure AffineMat (K : Type*) [Field K] (m ι : Type*) [Fintype m] [Fintype ι] where
  A0 : Matrix m m K
  L : (ι → K) →ₗ[K] Matrix m m K

namespace AffineMat

variable (A : AffineMat K m ι)

def eval (x : ι → K) : Matrix m m K := A.A0 + A.L x

theorem eval_add_linear (x u : ι → K) : A.eval (x + u) = A.eval x + A.L u := by
  simp only [eval, map_add, add_assoc]

end AffineMat

def leftMul (w : m → K) : Matrix m m K →ₗ[K] (m → K) where
  toFun M := Matrix.vecMul w M
  map_add' M N := Matrix.vecMul_add M N w
  map_smul' c M := by simp [Matrix.vecMul_smul]

@[simp] theorem leftMul_apply (w : m → K) (M : Matrix m m K) : leftMul w M = Matrix.vecMul w M := rfl

def kmap (A : AffineMat K m ι) (w : m → K) : (ι → K) →ₗ[K] (m → K) := (leftMul w).comp A.L

@[simp] theorem kmap_apply (A : AffineMat K m ι) (w : m → K) (x : ι → K) :
    kmap A w x = Matrix.vecMul w (A.L x) := rfl

theorem det_eq_zero_of_vecMul_eq_zero {M : Matrix m m K} {w : m → K} (hw : w ≠ 0)
    (h : Matrix.vecMul w M = 0) : M.det = 0 :=
  Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw, h⟩

theorem exists_leftKernel {M : Matrix m m K} (h : M.det = 0) :
    ∃ w : m → K, w ≠ 0 ∧ Matrix.vecMul w M = 0 :=
  Matrix.exists_vecMul_eq_zero_iff.mpr h

def kernelSlice (A : AffineMat K m ι) (w : m → K) : Set (ι → K) :=
  {y | Matrix.vecMul w (A.eval y) = 0}

theorem det_eq_zero_of_mem_kernelSlice (A : AffineMat K m ι) {w : m → K} (hw : w ≠ 0) {y : ι → K}
    (hy : y ∈ kernelSlice A w) : (A.eval y).det = 0 :=
  det_eq_zero_of_vecMul_eq_zero hw hy

theorem add_mem_kernelSlice (A : AffineMat K m ι) {w : m → K} {y u : ι → K}
    (hy : y ∈ kernelSlice A w) (hu : u ∈ LinearMap.ker (kmap A w)) : y + u ∈ kernelSlice A w := by
  simp only [kernelSlice, Set.mem_setOf_eq] at hy ⊢
  rw [A.eval_add_linear, Matrix.vecMul_add, hy, zero_add]
  exact LinearMap.mem_ker.mp hu

theorem card_le_card_add_finrank_ker (A : AffineMat K m ι) (w : m → K) :
    Fintype.card ι ≤ Fintype.card m + Module.finrank K (LinearMap.ker (kmap A w)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (kmap A w)
  have h2 : Module.finrank K (LinearMap.range (kmap A w)) ≤ Fintype.card m := by
    calc Module.finrank K (LinearMap.range (kmap A w)) ≤ Module.finrank K (m → K) :=
          Submodule.finrank_le _
      _ = Fintype.card m := by simp
  have h3 : Module.finrank K (ι → K) = Fintype.card ι := by simp
  omega

theorem covering (A : AffineMat K m ι) (x : ι → K) (hx : (A.eval x).det = 0) :
    ∃ U : Submodule K (ι → K), (∀ u ∈ U, (A.eval (x + u)).det = 0) ∧
      Fintype.card ι ≤ Fintype.card m + Module.finrank K U := by
  obtain ⟨w, hw, hwx⟩ := exists_leftKernel hx
  refine ⟨LinearMap.ker (kmap A w), fun u hu => ?_, card_le_card_add_finrank_ker A w⟩
  exact det_eq_zero_of_mem_kernelSlice A hw (add_mem_kernelSlice A hwx hu)

def VanishesOn (f : (ι → K) → K) (x : ι → K) (U : Submodule K (ι → K)) : Prop :=
  ∀ u ∈ U, f (x + u) = 0

theorem vanishesOn_bot (f : (ι → K) → K) (x : ι → K) : VanishesOn f x ⊥ ↔ f x = 0 := by
  constructor
  · intro h; simpa using h 0 (Submodule.zero_mem _)
  · intro h u hu; rw [Submodule.mem_bot] at hu; simpa [hu] using h

theorem dc_lower_bound_of_covering (A : AffineMat K m ι) {f : (ι → K) → K}
    (hf : ∀ x, f x = (A.eval x).det) (g : ℕ) (x : ι → K) (hx : f x = 0)
    (hg : ∀ U : Submodule K (ι → K), VanishesOn f x U → Module.finrank K U ≤ g) :
    Fintype.card ι ≤ Fintype.card m + g := by
  obtain ⟨U, hU, hcard⟩ := covering A x (by rw [← hf]; exact hx)
  have := hg U (fun u hu => by rw [hf]; exact hU u hu)
  omega

section Homogeneous

open MvPolynomial

variable {d : ℕ}

theorem degree_eq_sum_univ (e : ι →₀ ℕ) : e.degree = ∑ i, e i := by
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp
  · intro i; simp

theorem eval_smul_of_isHomogeneous (f : MvPolynomial ι K) (hf : f.IsHomogeneous d) (t : K)
    (v : ι → K) : MvPolynomial.eval (t • v) f = t ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i, e i = d := by
    rw [← degree_eq_sum_univ]
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp he) (hf.coeff_eq_zero hne)
  calc MvPolynomial.coeff e f * ∏ i, (t • v) i ^ e i
      = MvPolynomial.coeff e f * ∏ i, (t ^ e i * v i ^ e i) := by
        simp [mul_pow]
    _ = MvPolynomial.coeff e f * ((∏ i, t ^ e i) * ∏ i, v i ^ e i) := by
        rw [Finset.prod_mul_distrib]
    _ = t ^ d * (MvPolynomial.coeff e f * ∏ i, v i ^ e i) := by
        rw [Finset.prod_pow_eq_pow_sum, hdeg]; ring

noncomputable def linePoly (f : MvPolynomial ι K) (x u : ι → K) : Polynomial K :=
  MvPolynomial.aeval (fun i => Polynomial.C (u i) + Polynomial.X * Polynomial.C (x i)) f

theorem linePoly_eval (f : MvPolynomial ι K) (x u : ι → K) (s : K) :
    (linePoly f x u).eval s = MvPolynomial.eval (s • x + u) f := by
  have h3 : (Polynomial.aeval s) (linePoly f x u) = (linePoly f x u).eval s :=
    congrFun (Polynomial.coe_aeval_eq_eval s) _
  rw [← h3]
  unfold linePoly
  have h := MvPolynomial.comp_aeval (R := K) (S₁ := Polynomial K)
    (fun i => Polynomial.C (u i) + Polynomial.X * Polynomial.C (x i)) (Polynomial.aeval s)
  have h2 := congrArg (fun φ => φ f) h
  simp only [AlgHom.comp_apply] at h2
  rw [h2]
  have h5 : (fun i => (Polynomial.aeval s) (Polynomial.C (u i) + Polynomial.X * Polynomial.C (x i)))
      = s • x + u := by
    funext i
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Algebra.algebraMap_self_apply]
    ring
  rw [h5]
  exact congrFun (congrArg (fun φ : MvPolynomial ι K →+* K => (φ : MvPolynomial ι K → K))
    (MvPolynomial.coe_aeval_eq_eval (s • x + u))) f

variable [Infinite K]

theorem eval_eq_zero_of_vanishesOn_affine (f : MvPolynomial ι K) (hf : f.IsHomogeneous d)
    {x : ι → K} {U : Submodule K (ι → K)} (h : ∀ u ∈ U, MvPolynomial.eval (x + u) f = 0) :
    ∀ u ∈ U, ∀ s : K, MvPolynomial.eval (s • x + u) f = 0 := by
  intro u hu
  have hroots : ∀ s : K, s ≠ 0 → (linePoly f x u).eval s = 0 := by
    intro s hs
    rw [linePoly_eval]
    have hmem : s⁻¹ • u ∈ U := U.smul_mem _ hu
    have hx' := h _ hmem
    have hsc : s • x + u = s • (x + s⁻¹ • u) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [hsc, eval_smul_of_isHomogeneous f hf, hx', mul_zero]
  have hzero : linePoly f x u = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({0}ᶜ : Set K))
    · intro s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
      exact Polynomial.IsRoot.def.mpr (hroots s hs)
    · exact Set.Infinite.diff Set.infinite_univ (Set.finite_singleton 0) |>.mono (by
        intro s hs; simp only [Set.mem_diff, Set.mem_univ, true_and] at hs; exact hs)
  intro s
  rw [← linePoly_eval, hzero, Polynomial.eval_zero]

theorem vanishes_on_span_sup (f : MvPolynomial ι K) (hf : f.IsHomogeneous d)
    {x : ι → K} {U : Submodule K (ι → K)} (h : ∀ u ∈ U, MvPolynomial.eval (x + u) f = 0) :
    ∀ v ∈ (K ∙ x) ⊔ U, MvPolynomial.eval v f = 0 := by
  intro v hv
  rcases Submodule.mem_sup.mp hv with ⟨y, hy, u, hu, rfl⟩
  rcases Submodule.mem_span_singleton.mp hy with ⟨s, rfl⟩
  exact eval_eq_zero_of_vanishesOn_affine f hf h u hu s

theorem le_span_sup {x : ι → K} {U : Submodule K (ι → K)} :
    U ≤ (K ∙ x) ⊔ U ∧ x ∈ (K ∙ x) ⊔ U :=
  ⟨le_sup_right, Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)⟩

end Homogeneous

theorem mr_shape {N m g : ℕ} (hcov : N ≤ m + g) (hiso : 2 * g ≤ N) : N ≤ 2 * m := by omega

end PermanentBound.AffineZeroSpaces

end
section
open scoped Matrix

/-! ## Zero spaces of the permanent -/

namespace PermanentBound.PermanentZeroSpaces

open MvPolynomial PermanentBound.AffineZeroSpaces PermanentBound.Hessian

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]

noncomputable def permPoly (m K : Type*) [Fintype m] [DecidableEq m] [Field K] :
    MvPolynomial (m × m) K :=
  (Matrix.mvPolynomialX m m K).permanent

def toMat (x : m × m → K) : Matrix m m K := Matrix.of fun i j => x (i, j)

theorem permPoly_isHomogeneous : (permPoly m K).IsHomogeneous (Fintype.card m) := by
  unfold permPoly Matrix.permanent
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset m)
    (fun i => Matrix.mvPolynomialX m m K (σ i) i) (fun _ => 1)
    (fun i _ => by rw [Matrix.mvPolynomialX_apply]; exact MvPolynomial.isHomogeneous_X K _)
  simpa using h

theorem eval_permPoly (x : m × m → K) :
    MvPolynomial.eval x (permPoly m K) = (toMat x).permanent := by
  unfold permPoly Matrix.permanent toMat
  simp only [map_sum, map_prod, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.of_apply]

variable [Infinite K] {M : Type*} [Fintype M] [DecidableEq M]

theorem exists_linear_permZero_space (A : AffineMat K M (m × m))
    (hrep : ∀ x : m × m → K, (A.eval x).det = (toMat x).permanent)
    (p : m × m → K) (hp : (toMat p).permanent = 0) :
    ∃ V : Submodule K (m × m → K), p ∈ V ∧
      Fintype.card m * Fintype.card m ≤ Fintype.card M + Module.finrank K V ∧
      ∀ q ∈ V, (toMat q).permanent = 0 := by
  obtain ⟨U, hU, hcard⟩ := covering A p (by rw [hrep]; exact hp)
  refine ⟨(K ∙ p) ⊔ U, (le_span_sup (x := p) (U := U)).2, ?_, ?_⟩
  · have h1 := Submodule.finrank_mono (le_span_sup (x := p) (U := U)).1
    rw [Fintype.card_prod] at hcard
    omega
  · intro q hq
    have hvan : ∀ u ∈ U, MvPolynomial.eval (p + u) (permPoly m K) = 0 := by
      intro u hu; rw [eval_permPoly, ← hrep]; exact hU u hu
    have := vanishes_on_span_sup (permPoly m K) permPoly_isHomogeneous hvan q hq
    rwa [eval_permPoly] at this

theorem card_le_of_permZero_bound (A : AffineMat K M (m × m))
    (hrep : ∀ x : m × m → K, (A.eval x).det = (toMat x).permanent) (g : ℕ)
    (p : m × m → K) (hp : (toMat p).permanent = 0)
    (hbound : ∀ V : Submodule K (m × m → K), p ∈ V → (∀ q ∈ V, (toMat q).permanent = 0) →
      Module.finrank K V ≤ g) :
    Fintype.card m * Fintype.card m ≤ Fintype.card M + g := by
  obtain ⟨V, hpV, hcard, hV⟩ := exists_linear_permZero_space A hrep p hp
  have := hbound V hpV hV
  omega

section DotForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dotForm (H : Matrix ι ι K) : LinearMap.BilinForm K (ι → K) :=
  LinearMap.mk₂ K (fun v w => v ⬝ᵥ H.mulVec w)
    (fun v v' w => by simp [add_dotProduct])
    (fun c v w => by simp [smul_dotProduct])
    (fun v w w' => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c v w => by simp [Matrix.mulVec_smul, dotProduct_smul])

@[simp] theorem dotForm_apply (H : Matrix ι ι K) (v w : ι → K) :
    dotForm H v w = v ⬝ᵥ H.mulVec w := rfl

theorem dotForm_isRefl (H : Matrix ι ι K) (hH : Hᵀ = H) : (dotForm H).IsRefl := by
  intro v w h
  simp only [dotForm_apply] at h ⊢
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH, dotProduct_comm]
  exact h

end DotForm

theorem mr_of_hessian_nondegenerate (A : AffineMat K M (m × m))
    (hrep : ∀ x : m × m → K, (A.eval x).det = (toMat x).permanent)
    (p : m × m → K) (hp : (toMat p).permanent = 0) (H : Matrix (m × m) (m × m) K)
    (hsymm : Hᵀ = H) (hnd : ∀ v, (∀ w, v ⬝ᵥ H.mulVec w = 0) → v = 0)
    (hlink : ∀ V : Submodule K (m × m → K), p ∈ V → (∀ q ∈ V, (toMat q).permanent = 0) →
      ∀ v ∈ V, ∀ w ∈ V, v ⬝ᵥ H.mulVec w = 0) :
    Fintype.card m * Fintype.card m ≤ 2 * Fintype.card M := by
  obtain ⟨V, hpV, hcard, hV⟩ := exists_linear_permZero_space A hrep p hp
  have hiso := two_mul_finrank_le_of_isotropic (dotForm_isRefl H hsymm) hnd (W := V)
    (fun v hv w hw => hlink V hpV hV v hv w hw)
  have hdim : Module.finrank K (m × m → K) = Fintype.card m * Fintype.card m := by
    simp [Fintype.card_prod]
  omega

end PermanentBound.PermanentZeroSpaces

end
section
open scoped Matrix

/-! ## Second-order Taylor identities -/

namespace PermanentBound.TaylorExpansion

open MvPolynomial PermanentBound.Hessian
  PermanentBound.PermanentZeroSpaces PermanentBound.AffineZeroSpaces

variable {K : Type*} [Field K] {ι τ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq τ]

theorem pderiv_aeval (g : ι → MvPolynomial τ K) (t : τ) (f : MvPolynomial ι K) :
    pderiv t (aeval g f) = ∑ i, pderiv t (g i) * aeval g (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j ih =>
    simp only [map_mul, MvPolynomial.aeval_X, pderiv_mul, pderiv_X, ih, map_add,
      Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j]
      simp [mul_comm]

theorem pderiv_comm (i j : ι) (f : MvPolynomial ι K) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n ih =>
    simp only [pderiv_mul, pderiv_X, map_add, ih, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem hess_transpose (f : MvPolynomial ι K) (y : ι → K) : (hess f y)ᵀ = hess f y := by
  ext i j
  simp only [Matrix.transpose_apply, hess, pderiv_comm]

noncomputable def planeSub (y u v : ι → K) : ι → MvPolynomial (Fin 2) K :=
  fun i => C (y i) + X 0 * C (u i) + X 1 * C (v i)

noncomputable def planePoly (f : MvPolynomial ι K) (y u v : ι → K) : MvPolynomial (Fin 2) K :=
  aeval (planeSub y u v) f

theorem eval_planeSub (y u v : ι → K) (x : Fin 2 → K) :
    (fun i => eval x (planeSub y u v i)) = y + x 0 • u + x 1 • v := by
  funext i
  simp [planeSub]

theorem eval_aeval_planeSub (y u v : ι → K) (x : Fin 2 → K) (h : MvPolynomial ι K) :
    eval x (aeval (planeSub y u v) h) = eval (y + x 0 • u + x 1 • v) h := by
  have hc := MvPolynomial.comp_aeval (R := K) (S₁ := MvPolynomial (Fin 2) K) (planeSub y u v)
    (MvPolynomial.aeval x)
  have h2 := congrArg (fun φ => φ h) hc
  simp only [AlgHom.comp_apply] at h2
  have h3 : (MvPolynomial.aeval x) (aeval (planeSub y u v) h) = eval x (aeval (planeSub y u v) h) :=
    congrFun (congrArg (fun φ : MvPolynomial (Fin 2) K →+* K => (φ : MvPolynomial (Fin 2) K → K))
      (MvPolynomial.coe_aeval_eq_eval x)) _
  rw [← h3, h2]
  have h4 : (fun i => (MvPolynomial.aeval x) (planeSub y u v i)) = y + x 0 • u + x 1 • v := by
    rw [← eval_planeSub y u v x]
    funext i
    exact congrFun (congrArg (fun φ : MvPolynomial (Fin 2) K →+* K =>
      (φ : MvPolynomial (Fin 2) K → K)) (MvPolynomial.coe_aeval_eq_eval x)) _
  rw [h4]
  exact congrFun (congrArg (fun φ : MvPolynomial ι K →+* K => (φ : MvPolynomial ι K → K))
    (MvPolynomial.coe_aeval_eq_eval (y + x 0 • u + x 1 • v))) h

theorem eval_planePoly (f : MvPolynomial ι K) (y u v : ι → K) (x : Fin 2 → K) :
    eval x (planePoly f y u v) = eval (y + x 0 • u + x 1 • v) f :=
  eval_aeval_planeSub y u v x f

theorem pderiv_zero_planeSub (y u v : ι → K) (i : ι) :
    pderiv (0 : Fin 2) (planeSub y u v i) = C (u i) := by
  simp [planeSub, pderiv_mul, pderiv_X, Pi.single_apply]

theorem pderiv_one_planeSub (y u v : ι → K) (i : ι) :
    pderiv (1 : Fin 2) (planeSub y u v i) = C (v i) := by
  simp [planeSub, pderiv_mul, pderiv_X, Pi.single_apply]

theorem pderiv_pderiv_planePoly (f : MvPolynomial ι K) (y u v : ι → K) :
    pderiv (1 : Fin 2) (pderiv (0 : Fin 2) (planePoly f y u v))
      = ∑ i, ∑ j, C (u i) * C (v j) * aeval (planeSub y u v) (pderiv j (pderiv i f)) := by
  unfold planePoly
  rw [pderiv_aeval]
  simp only [pderiv_zero_planeSub, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add,
    pderiv_aeval, pderiv_one_planeSub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_pderiv_pderiv_planePoly (f : MvPolynomial ι K) (y u v : ι → K) :
    eval (0 : Fin 2 → K) (pderiv (1 : Fin 2) (pderiv (0 : Fin 2) (planePoly f y u v)))
      = u ⬝ᵥ ((hess f y).mulVec v) := by
  rw [pderiv_pderiv_planePoly]
  simp only [map_sum, map_mul, eval_C, eval_aeval_planeSub, Pi.zero_apply, zero_smul, add_zero,
    dotProduct, Matrix.mulVec, hess, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [Infinite K]

theorem hess_isotropic_of_vanishes (f : MvPolynomial ι K) (V : Submodule K (ι → K))
    (hV : ∀ x ∈ V, eval x f = 0) {y u v : ι → K} (hy : y ∈ V) (hu : u ∈ V) (hv : v ∈ V) :
    u ⬝ᵥ ((hess f y).mulVec v) = 0 := by
  have hQ : planePoly f y u v = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_planePoly, map_zero]
    exact hV _ (V.add_mem (V.add_mem hy (V.smul_mem _ hu)) (V.smul_mem _ hv))
  rw [← eval_pderiv_pderiv_planePoly, hQ, map_zero, map_zero, map_zero]

theorem mr_of_hessian_nondegenerate_perm {m : Type*} [Fintype m] [DecidableEq m]
    {M : Type*} [Fintype M] [DecidableEq M] (A : AffineMat K M (m × m))
    (hrep : ∀ x : m × m → K, (A.eval x).det = (toMat x).permanent)
    (p : m × m → K) (hp : (toMat p).permanent = 0)
    (hnd : ∀ v, (∀ w, v ⬝ᵥ ((hess (permPoly m K) p).mulVec w) = 0) → v = 0) :
    Fintype.card m * Fintype.card m ≤ 2 * Fintype.card M := by
  refine mr_of_hessian_nondegenerate A hrep p hp (hess (permPoly m K) p) (hess_transpose _ _) hnd
    ?_
  intro V hpV hV u hu w hw
  exact hess_isotropic_of_vanishes (permPoly m K) V
    (fun x hx => by rw [eval_permPoly]; exact hV x hx) hpV hu hw

end PermanentBound.TaylorExpansion

end
section
/-! ## Two-slice dimension bounds -/

namespace PermanentBound.TwoSliceDimension

open MvPolynomial PermanentBound.AffineZeroSpaces
  PermanentBound.Hessian

section TwoSlice

open PermanentBound.TaylorExpansion PermanentBound.PermanentZeroSpaces

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eval_pderiv_zero_planePoly (f : MvPolynomial ι K) (y u v : ι → K) :
    eval (0 : Fin 2 → K) (pderiv (0 : Fin 2) (planePoly f y u v)) = u ⬝ᵥ grad f y := by
  unfold planePoly
  rw [pderiv_aeval]
  simp only [pderiv_zero_planeSub, map_sum, map_mul, eval_C, eval_aeval_planeSub, Pi.zero_apply,
    zero_smul, add_zero, dotProduct, grad]

variable [Infinite K]

theorem grad_orth_of_affine_zero (f : MvPolynomial ι K) (y : ι → K)
    (D : Submodule K (ι → K)) (hD : ∀ δ ∈ D, eval (y + δ) f = 0) {δ : ι → K} (hδ : δ ∈ D) :
    δ ⬝ᵥ grad f y = 0 := by
  have hQ : planePoly f y δ 0 = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_planePoly, map_zero, smul_zero, add_zero]
    exact hD _ (D.smul_mem _ hδ)
  rw [← eval_pderiv_zero_planePoly f y δ 0, hQ, map_zero, map_zero]

theorem hess_orth_of_affine_zero (f : MvPolynomial ι K) (y : ι → K)
    (D : Submodule K (ι → K)) (hD : ∀ δ ∈ D, eval (y + δ) f = 0) {v δ : ι → K} (hv : v ∈ D)
    (hδ : δ ∈ D) : v ⬝ᵥ ((hess f y).mulVec δ) = 0 := by
  have hQ : planePoly f y v δ = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_planePoly, map_zero, add_assoc]
    exact hD _ (D.add_mem (D.smul_mem _ hv) (D.smul_mem _ hδ))
  rw [← eval_pderiv_pderiv_planePoly, hQ, map_zero, map_zero, map_zero]

def orth (W : Submodule K (ι → K)) : Submodule K (ι → K) :=
  (dotForm (1 : Matrix ι ι K)).orthogonal W

theorem mem_orth {W : Submodule K (ι → K)} {g : ι → K} :
    g ∈ orth W ↔ ∀ δ ∈ W, δ ⬝ᵥ g = 0 := by
  simp [orth, LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho, dotForm_apply,
    Matrix.one_mulVec]

theorem finrank_orth (W : Submodule K (ι → K)) :
    Module.finrank K (orth W) + Module.finrank K W = Fintype.card ι := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := dotForm (1 : Matrix ι ι K)) W
  have hker : LinearMap.ker (dotForm (1 : Matrix ι ι K)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    funext i
    have := congrFun (congrArg DFunLike.coe hg) (Pi.single i 1)
    simp only [dotForm_apply, Matrix.one_mulVec, dotProduct_single, mul_one,
      LinearMap.zero_apply] at this
    rw [Pi.zero_apply]
    exact this
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at h
  unfold orth
  omega

theorem two_slices {d : ℕ} (f : MvPolynomial ι K) (hf : f.IsHomogeneous d) (y : ι → K)
    (hnd : ∀ v, (hess f y).mulVec v = 0 → v = 0)
    (DW DU : Submodule K (ι → K)) (hW : ∀ δ ∈ DW, eval (y + δ) f = 0)
    (hU : ∀ δ ∈ DU, eval (y + δ) f = 0) :
    Module.finrank K DW + Module.finrank K DU ≤ Fintype.card ι ∧
      (Module.finrank K DW + Module.finrank K DU = Fintype.card ι → y ∈ DW ⊓ DU) := by
  have hmap : ∀ v ∈ DW ⊓ DU, (hess f y).mulVec v ∈ orth (DW ⊔ DU) := by
    intro v hv
    rw [mem_orth]
    intro δ hδ
    rw [Submodule.mem_sup] at hδ
    obtain ⟨a, ha, b, hb, rfl⟩ := hδ
    rw [add_dotProduct, hess_orth_of_affine_zero f y DW hW ha hv.1,
      hess_orth_of_affine_zero f y DU hU hb hv.2, add_zero]
  let T : (DW ⊓ DU : Submodule K (ι → K)) →ₗ[K] orth (DW ⊔ DU) :=
    LinearMap.codRestrict (orth (DW ⊔ DU)) ((hess f y).mulVecLin.domRestrict (DW ⊓ DU))
      (fun v => hmap v v.2)
  have hTinj : Function.Injective T := by
    intro a b hab
    apply Subtype.ext
    have h : (hess f y).mulVec (a : ι → K) = (hess f y).mulVec (b : ι → K) :=
      congrArg Subtype.val hab
    have : (hess f y).mulVec ((a : ι → K) - b) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    exact sub_eq_zero.mp (hnd _ this)
  have hdim := LinearMap.finrank_le_finrank_of_injective hTinj
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq DW DU
  have horth := finrank_orth (DW ⊔ DU)
  refine ⟨by omega, fun heq => ?_⟩
  have hfr : Module.finrank K (DW ⊓ DU : Submodule K (ι → K))
      = Module.finrank K (orth (DW ⊔ DU)) := by omega
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hTinj
  have hgrad : grad f y ∈ orth (DW ⊔ DU) := by
    rw [mem_orth]
    intro δ hδ
    rw [Submodule.mem_sup] at hδ
    obtain ⟨a, ha, b, hb, rfl⟩ := hδ
    rw [add_dotProduct, grad_orth_of_affine_zero f y DW hW ha,
      grad_orth_of_affine_zero f y DU hU hb, add_zero]
  obtain ⟨⟨v, hv⟩, hTv⟩ := hTsurj ⟨grad f y, hgrad⟩
  have hHv : (hess f y).mulVec v = grad f y := congrArg Subtype.val hTv
  have hE := hess_mulVec_self hf y
  have h0 : (hess f y).mulVec (y - ((d - 1 : ℕ) : K) • v) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hHv, hE, sub_self]
  have hy : y = ((d - 1 : ℕ) : K) • v := sub_eq_zero.mp (hnd _ h0)
  rw [hy]
  exact Submodule.smul_mem _ _ hv

def rightKmap {m : Type*} [Fintype m] (A : AffineMat K m ι) (u : m → K) :
    (ι → K) →ₗ[K] (m → K) where
  toFun δ := (A.L δ).mulVec u
  map_add' y z := by simp [map_add, Matrix.add_mulVec]
  map_smul' c y := by
    simp only [map_smul, RingHom.id_apply]
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

@[simp] theorem rightKmap_apply {m : Type*} [Fintype m] (A : AffineMat K m ι) (u : m → K)
    (δ : ι → K) : rightKmap A u δ = (A.L δ).mulVec u := rfl

theorem card_le_card_add_finrank_ker_right {m : Type*} [Fintype m] (A : AffineMat K m ι)
    (u : m → K) :
    Fintype.card ι ≤ Fintype.card m + Module.finrank K (LinearMap.ker (rightKmap A u)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (rightKmap A u)
  have h2 := Submodule.finrank_le (LinearMap.range (rightKmap A u))
  rw [Module.finrank_fintype_fun_eq_card] at h h2
  omega

theorem kernel_of_A0 {m : Type*} [Fintype m] [DecidableEq m] (A : AffineMat K m ι)
    (f : MvPolynomial ι K) {d : ℕ} (hf : f.IsHomogeneous d)
    (hrep : ∀ x, (A.eval x).det = eval x f) (h2m : 2 * Fintype.card m ≤ Fintype.card ι)
    (y : ι → K) (hnd : ∀ v, (hess f y).mulVec v = 0 → v = 0)
    (w u : m → K) (hw : w ≠ 0) (hu : u ≠ 0) (hwy : Matrix.vecMul w (A.eval y) = 0)
    (huy : (A.eval y).mulVec u = 0) :
    Matrix.vecMul w A.A0 = 0 ∧ A.A0.mulVec u = 0 := by
  have hW : ∀ δ ∈ LinearMap.ker (kmap A w), eval (y + δ) f = 0 := by
    intro δ hδ
    rw [LinearMap.mem_ker, kmap_apply] at hδ
    rw [← hrep]
    apply det_eq_zero_of_vecMul_eq_zero hw
    rw [AffineMat.eval_add_linear, Matrix.vecMul_add, hwy, hδ, add_zero]
  have hU : ∀ δ ∈ LinearMap.ker (rightKmap A u), eval (y + δ) f = 0 := by
    intro δ hδ
    rw [LinearMap.mem_ker, rightKmap_apply] at hδ
    rw [← hrep]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨u, hu, ?_⟩
    rw [AffineMat.eval_add_linear, Matrix.add_mulVec, huy, hδ, add_zero]
  obtain ⟨hle, htight⟩ := two_slices f hf y hnd _ _ hW hU
  have h1 := card_le_card_add_finrank_ker A w
  have h2 := card_le_card_add_finrank_ker_right A u
  have heq : Module.finrank K (LinearMap.ker (kmap A w))
      + Module.finrank K (LinearMap.ker (rightKmap A u)) = Fintype.card ι := by omega
  have hy := htight heq
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, kmap_apply, rightKmap_apply] at hy
  have hev : A.eval y = A.A0 + A.L y := rfl
  rw [hev, Matrix.vecMul_add, hy.1, add_zero] at hwy
  rw [hev, Matrix.add_mulVec, hy.2, add_zero] at huy
  exact ⟨hwy, huy⟩

end TwoSlice

end PermanentBound.TwoSliceDimension

end
section
open scoped Matrix

/-! ## Tangent-space and corank bounds -/

namespace PermanentBound.TangentBound

open MvPolynomial PermanentBound.AffineZeroSpaces
  PermanentBound.Hessian PermanentBound.TaylorExpansion
  PermanentBound.PermanentZeroSpaces

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Univariate

theorem derivative_aeval_poly (φ : ι → Polynomial K) (g : MvPolynomial ι K) :
    Polynomial.derivative (aeval φ g)
      = ∑ i, Polynomial.derivative (φ i) * aeval φ (pderiv i g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j ih =>
    simp only [map_mul, MvPolynomial.aeval_X, Polynomial.derivative_mul, ih, pderiv_mul, pderiv_X,
      map_add, Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j]
      simp [mul_comm]

theorem derivative_linePoly_eval_zero (g : MvPolynomial ι K) (x δ : ι → K) :
    (Polynomial.derivative (linePoly g δ x)).eval 0 = δ ⬝ᵥ grad g x := by
  unfold linePoly
  rw [derivative_aeval_poly]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.derivative_X, zero_add, one_mul, mul_zero, add_zero, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := linePoly_eval (pderiv i g) δ x 0
  unfold linePoly at h
  rw [h]
  simp [grad]

variable [Infinite K]

theorem dirDeriv_eq_zero_of_infinite_zeros (g : MvPolynomial ι K) (x δ : ι → K)
    (h : {t : K | eval (t • δ + x) g = 0}.Infinite) : δ ⬝ᵥ grad g x = 0 := by
  have hq : linePoly g δ x = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine h.mono ?_
    intro t ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, linePoly_eval]
    exact ht
  rw [← derivative_linePoly_eval_zero, hq, map_zero, Polynomial.eval_zero]

theorem finite_zeros_of_ne_zero (g : MvPolynomial ι K) (x δ : ι → K) (h0 : eval x g ≠ 0) :
    {t : K | eval (t • δ + x) g = 0}.Finite := by
  have hne : linePoly g δ x ≠ 0 := by
    intro h
    have := linePoly_eval g δ x 0
    rw [h, Polynomial.eval_zero, zero_smul, zero_add] at this
    exact h0 this.symm
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, linePoly_eval]
  exact ht

end Univariate

section Hessian

noncomputable def hessPoly (f : MvPolynomial ι K) : Matrix ι ι (MvPolynomial ι K) :=
  fun i j => pderiv j (pderiv i f)

theorem map_hessPoly (f : MvPolynomial ι K) (y : ι → K) :
    (hessPoly f).map (eval y) = hess f y := rfl

theorem eval_det_hessPoly (f : MvPolynomial ι K) (y : ι → K) :
    eval y (hessPoly f).det = (hess f y).det := by
  rw [RingHom.map_det]; rfl

theorem det_ne_zero_of_injective (H : Matrix ι ι K) (h : ∀ v, H.mulVec v = 0 → v = 0) :
    H.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (h v hHv)

theorem injective_of_det_ne_zero (H : Matrix ι ι K) (h : H.det ≠ 0) :
    ∀ v, H.mulVec v = 0 → v = 0 := by
  intro v hv
  by_contra hne
  exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hne, hv⟩)

end Hessian

section PolyMatrix

variable {M : Type*} [Fintype M] [DecidableEq M]

def Lc (A : AffineMat K M ι) (j : ι) : Matrix M M K := A.L (fun j' => if j = j' then 1 else 0)

theorem L_eq_sum (A : AffineMat K M ι) (y : ι → K) : A.L y = ∑ j, y j • Lc A j := by
  rw [LinearMap.pi_apply_eq_sum_univ A.L y]; rfl

noncomputable def polyMat (A : AffineMat K M ι) : Matrix M M (MvPolynomial ι K) :=
  fun a b => C (A.A0 a b) + ∑ j, C (Lc A j a b) * X j

theorem eval_polyMat (A : AffineMat K M ι) (y : ι → K) (a b : M) :
    eval y (polyMat A a b) = A.eval y a b := by
  simp only [polyMat, map_add, map_sum, map_mul, eval_C, eval_X, AffineMat.eval, Matrix.add_apply,
    L_eq_sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem map_polyMat (A : AffineMat K M ι) (y : ι → K) : (polyMat A).map (eval y) = A.eval y := by
  ext a b; exact eval_polyMat A y a b

theorem pderiv_polyMat (A : AffineMat K M ι) (j : ι) (a b : M) :
    pderiv j (polyMat A a b) = C (Lc A j a b) := by
  simp [polyMat, pderiv_X, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem det_polyMat [Infinite K] (A : AffineMat K M ι) (f : MvPolynomial ι K)
    (hrep : ∀ x, (A.eval x).det = eval x f) : (polyMat A).det = f := by
  apply MvPolynomial.funext
  intro y
  rw [← hrep y, ← map_polyMat A y, RingHom.map_det]
  rfl

def adjRow (A : AffineMat K M ι) (y : ι → K) (i₀ : M) : M → K :=
  fun a => (A.eval y).adjugate i₀ a

theorem eval_adjugate_polyMat (A : AffineMat K M ι) (y : ι → K) (i₀ a : M) :
    eval y ((polyMat A).adjugate i₀ a) = adjRow A y i₀ a := by
  unfold adjRow
  rw [← map_polyMat A y]
  have h := RingHom.map_adjugate (eval y) (polyMat A)
  have h2 := congrFun (congrFun h i₀) a
  simpa using h2

theorem adjRow_vecMul (A : AffineMat K M ι) (y : ι → K) (i₀ : M) :
    adjRow A y i₀ ᵥ* A.eval y = (A.eval y).det • Pi.single i₀ 1 := by
  funext b
  have h := congrFun (congrFun (Matrix.adjugate_mul (A.eval y)) i₀) b
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  simp only [Matrix.vecMul, dotProduct, adjRow, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [h]
  by_cases hb : i₀ = b
  · subst hb; simp
  · simp [hb, Ne.symm hb]

noncomputable def jac (A : AffineMat K M ι) (p : ι → K) (i₀ : M) : Matrix M ι K :=
  fun a j => eval p (pderiv j ((polyMat A).adjugate i₀ a))

noncomputable def Ψ (A : AffineMat K M ι) (p : ι → K) (i₀ : M) : (ι → K) →ₗ[K] (M → K) :=
  (jac A p i₀).mulVecLin

theorem Ψ_apply (A : AffineMat K M ι) (p : ι → K) (i₀ : M) (δ : ι → K) :
    Ψ A p i₀ δ = (jac A p i₀).mulVec δ := rfl

theorem entry_identity [Infinite K] (A : AffineMat K M ι) (f : MvPolynomial ι K)
    (hrep : ∀ x, (A.eval x).det = eval x f) (p : ι → K) (i₀ b : M) (j : ι) :
    ∑ a, jac A p i₀ a j * A.eval p a b + ∑ a, adjRow A p i₀ a * Lc A j a b
      = grad f p j * (1 : Matrix M M K) i₀ b := by
  have hadj : (polyMat A).adjugate * polyMat A = f • (1 : Matrix M M (MvPolynomial ι K)) := by
    rw [Matrix.adjugate_mul, det_polyMat A f hrep]
  have hb := congrFun (congrFun hadj i₀) b
  have h1 := congrArg (fun q => eval p (pderiv j q)) hb
  simp only [Matrix.mul_apply, map_sum, pderiv_mul, map_add, map_mul, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, eval_polyMat, pderiv_polyMat, eval_adjugate_polyMat, eval_C,
    Finset.sum_add_distrib] at h1
  simp only [jac]
  rw [h1]
  by_cases hib : i₀ = b
  · simp [hib, grad, Matrix.one_apply]
  · simp [hib, grad, Matrix.one_apply]

theorem key_identity [Infinite K] (A : AffineMat K M ι) (f : MvPolynomial ι K)
    (hrep : ∀ x, (A.eval x).det = eval x f) (p : ι → K) (i₀ : M) (δ : ι → K) :
    Ψ A p i₀ δ ᵥ* A.eval p + adjRow A p i₀ ᵥ* A.L δ = (δ ⬝ᵥ grad f p) • Pi.single i₀ 1 := by
  funext b
  rw [L_eq_sum]
  simp only [Pi.add_apply, Matrix.vecMul, dotProduct, Ψ_apply, Matrix.mulVec, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Pi.single_apply]
  have e1 : ∑ a, (∑ j, jac A p i₀ a j * δ j) * A.eval p a b
      = ∑ j, δ j * ∑ a, jac A p i₀ a j * A.eval p a b := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, adjRow A p i₀ a * ∑ j, δ j * Lc A j a b
      = ∑ j, δ j * ∑ a, adjRow A p i₀ a * Lc A j a b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  have e3 : ∀ j, δ j * ∑ a, jac A p i₀ a j * A.eval p a b + δ j * ∑ a, adjRow A p i₀ a * Lc A j a b
      = δ j * grad f p j * (1 : Matrix M M K) i₀ b := by
    intro j
    rw [← mul_add, entry_identity A f hrep p i₀ b j, mul_assoc]
  simp only [e3]
  rw [← Finset.sum_mul]
  simp only [Matrix.one_apply]
  by_cases hib : i₀ = b
  · subst hib; simp
  · simp [hib, Ne.symm hib]

end PolyMatrix

section Assembly

open PermanentBound.TwoSliceDimension

variable {M : Type*} [Fintype M] [DecidableEq M] [Infinite K]

def leftKer (A : AffineMat K M ι) : Submodule K (M → K) := LinearMap.ker (Matrix.vecMulLinear A.A0)

theorem mem_leftKer {A : AffineMat K M ι} {w : M → K} : w ∈ leftKer A ↔ w ᵥ* A.A0 = 0 := by
  simp [leftKer, Matrix.vecMulLinear_apply]

theorem tangent_bound (A : AffineMat K M ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (hrep : ∀ x, (A.eval x).det = eval x f)
    (h2m : 2 * Fintype.card M ≤ Fintype.card ι) (p : ι → K) (hp0 : p ≠ 0)
    (hnd : ∀ v, (hess f p).mulVec v = 0 → v = 0) {ιs : Type*} (V : ιs → Submodule K (ι → K))
    (hV : ∀ i, p ∈ V i ∧ ∀ q ∈ V i, eval q f = 0) :
    2 * Module.finrank K (⨆ i, V i : Submodule K (ι → K))
      ≤ Fintype.card ι + 2 * Module.finrank K (leftKer A) := by
  classical
  by_cases hne : Nonempty ιs
  swap
  · have hbot : (⨆ i, V i : Submodule K (ι → K)) = ⊥ := by
      rw [not_nonempty_iff] at hne
      exact iSup_of_empty V
    rw [hbot, finrank_bot]
    omega
  obtain ⟨i₁⟩ := hne
  have hpf : eval p f = 0 := (hV i₁).2 p (hV i₁).1
  have hgrad : grad f p ≠ 0 := by
    intro h0
    have h := hess_mulVec_self hf p
    rw [h0, smul_zero] at h
    exact hp0 (hnd p h)
  have hdetp : (A.eval p).det = 0 := by rw [hrep, hpf]
  obtain ⟨u, hu, hAu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetp

  have hrow : ∃ i₀, adjRow A p i₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hgz : ∀ δ, δ ⬝ᵥ grad f p = 0 := by
      intro δ
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, u i₀ ≠ 0 := by
        by_contra h
        push_neg at h
        exact hu (funext h)
      have hk := congrArg (fun v => v ⬝ᵥ u) (key_identity A f hrep p i₀ δ)
      simp only [add_dotProduct, hall i₀, Matrix.zero_vecMul, zero_dotProduct, add_zero,
        smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul] at hk
      rw [← Matrix.dotProduct_mulVec, hAu, dotProduct_zero] at hk
      exact (mul_eq_zero.mp hk.symm).resolve_right hi₀
    apply hgrad
    funext j
    have := hgz (Pi.single j 1)
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hrow
  set w := adjRow A p i₀ with hw
  have hwA : w ᵥ* A.eval p = 0 := by rw [hw, adjRow_vecMul, hdetp, zero_smul]
  obtain ⟨hwA0, -⟩ := kernel_of_A0 A f hf hrep h2m p hnd w u hi₀ hu hwA hAu

  set DW := LinearMap.ker (kmap A w) with hDW
  have hDWzero : ∀ q ∈ DW, eval q f = 0 := by
    intro q hq
    rw [LinearMap.mem_ker, kmap_apply] at hq
    rw [← hrep]
    apply det_eq_zero_of_vecMul_eq_zero hi₀
    show w ᵥ* (A.A0 + A.L q) = 0
    rw [Matrix.vecMul_add, hwA0, hq, add_zero]
  have hpDW : p ∈ DW := by
    rw [LinearMap.mem_ker, kmap_apply]
    have h : w ᵥ* A.eval p = w ᵥ* A.A0 + w ᵥ* A.L p := by
      show w ᵥ* (A.A0 + A.L p) = _
      rw [Matrix.vecMul_add]
    rw [hwA, hwA0, zero_add] at h
    exact h.symm
  have hDWdim : 2 * Module.finrank K DW ≤ Fintype.card ι := by
    have hnd' : ∀ v, (∀ w', dotForm (hess f p) v w' = 0) → v = 0 := by
      intro v hv
      apply hnd v
      funext a
      have h := hv (Pi.single a 1)
      rw [dotForm_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hess_transpose] at h
      simpa using h
    have h := two_mul_finrank_le_of_isotropic (dotForm_isRefl (hess f p) (hess_transpose f p)) hnd'
      (W := DW) (fun a ha b hb => by
        rw [dotForm_apply]
        exact hess_isotropic_of_vanishes f DW hDWzero hpDW ha hb)
    rwa [Module.finrank_fintype_fun_eq_card] at h

  have hT_grad : ∀ x ∈ (⨆ i, V i : Submodule K (ι → K)), x ⬝ᵥ grad f p = 0 := by
    intro x hx
    have hle : (⨆ i, V i : Submodule K (ι → K))
        ≤ LinearMap.ker ((dotForm (1 : Matrix ι ι K)) (grad f p)) := by
      refine iSup_le fun i => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      show grad f p ⬝ᵥ ((1 : Matrix ι ι K) *ᵥ y) = 0
      rw [Matrix.one_mulVec, dotProduct_comm]
      exact grad_orth_of_affine_zero f p (V i)
        (fun δ hδ => (hV i).2 _ ((V i).add_mem (hV i).1 hδ)) hy
    have h := hle hx
    rw [LinearMap.mem_ker] at h
    change grad f p ⬝ᵥ ((1 : Matrix ι ι K) *ᵥ x) = 0 at h
    rwa [Matrix.one_mulVec, dotProduct_comm] at h

  have hΨ_line : ∀ i, ∀ δ ∈ V i, Ψ A p i₀ δ ∈ leftKer A := by
    intro i δ hδ
    rw [mem_leftKer]
    funext b
    let g : MvPolynomial ι K := ∑ a, (polyMat A).adjugate i₀ a * C (A.A0 a b)
    have hg_eval : ∀ y, eval y g = (adjRow A y i₀ ᵥ* A.A0) b := by
      intro y
      simp [g, map_sum, map_mul, eval_C, eval_adjugate_polyMat, Matrix.vecMul, dotProduct]
    have hg_dir : δ ⬝ᵥ grad g p = (Ψ A p i₀ δ ᵥ* A.A0) b := by
      simp only [dotProduct, grad, g, map_sum, pderiv_mul, pderiv_C, mul_zero, add_zero, map_mul,
        eval_C, Ψ_apply, Matrix.vecMul, Matrix.mulVec, jac, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
    have hfin1 : {t : K | eval (t • δ + p) (hessPoly f).det = 0}.Finite :=
      finite_zeros_of_ne_zero _ p δ (by rw [eval_det_hessPoly]; exact det_ne_zero_of_injective _ hnd)
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, adjRow A p i₀ a₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi₀ (funext h)
    have hfin2 : {t : K | eval (t • δ + p) ((polyMat A).adjugate i₀ a₀) = 0}.Finite :=
      finite_zeros_of_ne_zero _ p δ (by rw [eval_adjugate_polyMat]; exact ha₀)
    have hinf : {t : K | eval (t • δ + p) g = 0}.Infinite := by
      have hcompl : ({t : K | eval (t • δ + p) (hessPoly f).det = 0}
          ∪ {t | eval (t • δ + p) ((polyMat A).adjugate i₀ a₀) = 0})ᶜ
          ⊆ {t | eval (t • δ + p) g = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
        obtain ⟨ht1, ht2⟩ := ht
        have hyV : t • δ + p ∈ V i := (V i).add_mem ((V i).smul_mem t hδ) (hV i).1
        have hyf : eval (t • δ + p) f = 0 := (hV i).2 _ hyV
        have hndy : ∀ v, (hess f (t • δ + p)).mulVec v = 0 → v = 0 :=
          injective_of_det_ne_zero _ (by rw [← eval_det_hessPoly]; exact ht1)
        have hwy : adjRow A (t • δ + p) i₀ ≠ 0 := by
          intro h
          apply ht2
          rw [eval_adjugate_polyMat]
          exact congrFun h a₀
        have hdety : (A.eval (t • δ + p)).det = 0 := by rw [hrep, hyf]
        obtain ⟨u', hu', hAu'⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdety
        have hwyA : adjRow A (t • δ + p) i₀ ᵥ* A.eval (t • δ + p) = 0 := by
          rw [adjRow_vecMul, hdety, zero_smul]
        obtain ⟨h0, -⟩ := kernel_of_A0 A f hf hrep h2m (t • δ + p) hndy _ u' hwy hu' hwyA hAu'
        show eval (t • δ + p) g = 0
        rw [hg_eval, h0]
        rfl
      exact Set.Infinite.mono hcompl ((hfin1.union hfin2).infinite_compl)
    have h := dirDeriv_eq_zero_of_infinite_zeros g p δ hinf
    rw [hg_dir] at h
    exact h

  set T : Submodule K (ι → K) := ⨆ i, V i with hT
  have hΨT : ∀ x ∈ T, Ψ A p i₀ x ∈ leftKer A := by
    intro x hx
    have hle : T ≤ (leftKer A).comap (Ψ A p i₀) :=
      iSup_le fun i y hy => Submodule.mem_comap.mpr (hΨ_line i y hy)
    exact Submodule.mem_comap.mp (hle hx)
  let Ψ' : T →ₗ[K] (M → K) := (Ψ A p i₀).domRestrict T
  have hrange : LinearMap.range Ψ' ≤ leftKer A := by
    rintro _ ⟨x, rfl⟩
    exact hΨT x x.2
  have hker : (LinearMap.ker Ψ').map T.subtype ≤ DW := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : Ψ A p i₀ (x : ι → K) = 0 := hx
    have hk := key_identity A f hrep p i₀ x
    rw [hx', Matrix.zero_vecMul, zero_add, hT_grad x x.2, zero_smul] at hk
    rw [Submodule.subtype_apply, LinearMap.mem_ker, kmap_apply]
    exact hk
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ'
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  omega

end Assembly

section Corank

variable {M : Type*} [Fintype M] [DecidableEq M]

noncomputable def pencil (A0 B : Matrix M M K) : Matrix M M (Polynomial K) :=
  A0.map (Polynomial.C : K →+* Polynomial K)
    + (Polynomial.X : Polynomial K) • B.map (Polynomial.C : K →+* Polynomial K)

theorem X_pow_dvd_det_pencil (S : Finset M) (A0 B : Matrix M M K)
    (hS : ∀ i ∈ S, ∀ j, A0 i j = 0) :
    (Polynomial.X : Polynomial K) ^ S.card ∣ (pencil A0 B).det := by
  unfold pencil
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply Dvd.dvd.mul_left
  set T : Finset M := S.map σ.symm.toEmbedding with hT
  have hcard : T.card = S.card := Finset.card_map _
  have hmem : ∀ i ∈ T, σ i ∈ S := by
    intro i hi
    rw [hT, Finset.mem_map_equiv] at hi
    simpa using hi
  rw [← Finset.prod_sdiff (Finset.subset_univ T), ← hcard, ← Finset.prod_const]
  apply Dvd.dvd.mul_left
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hS _ (hmem i hi),
    map_zero, zero_add]
  exact dvd_mul_right _ _

theorem det_pencil_eq [Infinite K] (A : AffineMat K M ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (hrep : ∀ x, (A.eval x).det = eval x f) (x₀ : ι → K) :
    (pencil A.A0 (A.L x₀)).det = Polynomial.C (eval x₀ f) * Polynomial.X ^ d := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h1 : Polynomial.eval t (pencil A.A0 (A.L x₀)).det
      = ((pencil A.A0 (A.L x₀)).map (Polynomial.eval t)).det := by
    have := RingHom.map_det (Polynomial.evalRingHom t) (pencil A.A0 (A.L x₀))
    simpa [RingHom.mapMatrix_apply] using this
  have h2 : (pencil A.A0 (A.L x₀)).map (Polynomial.eval t) = A.eval (t • x₀) := by
    ext i j
    simp [pencil, AffineMat.eval, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, map_smul]
      <;> ring
  rw [h1, h2, hrep, eval_smul_of_isHomogeneous f hf, mul_comm]

theorem finrank_leftKer_le [Infinite K] (A : AffineMat K M ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (hrep : ∀ x, (A.eval x).det = eval x f) (x₀ : ι → K)
    (hx₀ : eval x₀ f ≠ 0) : Module.finrank K (leftKer A) ≤ d := by
  classical
  set k := Module.finrank K (leftKer A) with hk
  let b := Module.finBasis K (leftKer A)
  have hli : LinearIndependent K (fun i : Fin k => (b i : M → K)) :=
    b.linearIndependent.map' (leftKer A).subtype (Submodule.ker_subtype _)
  have hs : LinearIndepOn K id (Set.range (fun i : Fin k => (b i : M → K))) :=
    hli.linearIndepOn_id
  let bext := Module.Basis.extend hs
  let _ : Fintype (hs.extend (Set.subset_univ _)) := FiniteDimensional.fintypeBasisIndex bext
  have hcardE : Fintype.card M = Fintype.card (hs.extend (Set.subset_univ _)) := by
    have := Module.finrank_eq_card_basis bext
    rwa [Module.finrank_fintype_fun_eq_card] at this
  let e : M ≃ hs.extend (Set.subset_univ _) := Fintype.equivOfCardEq hcardE
  let U : Matrix M M K := fun i => (e i : M → K)
  have hUrows : U.row = bext ∘ e := by
    funext i
    simp [U, bext, Module.Basis.extend_apply_self, Matrix.row]
  have hUunit : IsUnit U := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit, hUrows]
    exact bext.linearIndependent.comp e e.injective

  let ι' : Fin k → M := fun i =>
    e.symm ⟨(b i : M → K), hs.subset_extend _ (Set.mem_range_self i)⟩
  have hι' : Function.Injective ι' := by
    intro i j hij
    have := congrArg (fun x => ((e x : hs.extend (Set.subset_univ _)) : M → K)) hij
    simp only [ι', Equiv.apply_symm_apply] at this
    exact hli.injective this
  set S : Finset M := Finset.univ.image ι' with hS
  have hScard : S.card = k := by
    rw [hS, Finset.card_image_of_injective _ hι', Finset.card_univ, Fintype.card_fin]
  have hSrows : ∀ i ∈ S, ∀ j, (U * A.A0) i j = 0 := by
    intro i hi j
    rw [hS, Finset.mem_image] at hi
    obtain ⟨l, -, rfl⟩ := hi
    have hker : (b l : M → K) ᵥ* A.A0 = 0 := mem_leftKer.mp (b l).2
    have hrow : U (ι' l) = (b l : M → K) := by
      simp [U, ι', Equiv.apply_symm_apply]
    show ∑ a, U (ι' l) a * A.A0 a j = 0
    rw [hrow]
    exact congrFun hker j

  have hdvd := X_pow_dvd_det_pencil S (U * A.A0) (U * A.L x₀) hSrows
  rw [hScard] at hdvd
  have hfac : pencil (U * A.A0) (U * A.L x₀)
      = U.map (Polynomial.C : K →+* Polynomial K) * pencil A.A0 (A.L x₀) := by
    simp only [pencil]
    rw [Matrix.mul_add, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul]
  rw [hfac, Matrix.det_mul, det_pencil_eq A f hf hrep x₀] at hdvd
  have hUC : IsUnit (U.map (Polynomial.C : K →+* Polynomial K)).det := by
    have : (U.map (Polynomial.C : K →+* Polynomial K)).det = Polynomial.C U.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hUunit).map Polynomial.C
  rw [hUC.dvd_mul_left] at hdvd
  by_contra hlt
  push_neg at hlt
  rw [Polynomial.X_pow_dvd_iff] at hdvd
  have := hdvd d hlt
  rw [Polynomial.coeff_C_mul_X_pow] at this
  simp at this
  exact hx₀ this

end Corank

end PermanentBound.TangentBound

end
section
/-! ## Row scaling and permanent-zero subspaces -/

namespace PermanentBound.RowScaling

section RowScaling

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]

theorem permanent_diagonal_mul (d : m → K) (M : Matrix m m K) :
    (Matrix.diagonal d * M).permanent = (∏ i, d i) * M.permanent := by
  unfold Matrix.permanent
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.diagonal_mul]
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ d]

def rowScale (p : Matrix m m K) : (m → K) →ₗ[K] Matrix m m K where
  toFun d := Matrix.diagonal d * p
  map_add' a b := by rw [← Matrix.add_mul, Matrix.diagonal_add]; rfl
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Matrix.diagonal_smul, Matrix.smul_mul]

@[simp] theorem rowScale_apply (p : Matrix m m K) (d : m → K) :
    rowScale p d = Matrix.diagonal d * p := rfl

theorem permanent_rowScale (p : Matrix m m K) (hp : p.permanent = 0) (d : m → K) :
    (rowScale p d).permanent = 0 := by
  rw [rowScale_apply, permanent_diagonal_mul, hp, mul_zero]

theorem rowScale_injective (p : Matrix m m K) (hp : ∀ i, p i ≠ 0) :
    Function.Injective (rowScale p) := by
  intro a b hab
  funext i
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hp i)
  have h := congrFun (congrFun hab i) j
  simp only [rowScale_apply, Matrix.diagonal_mul] at h
  exact mul_right_cancel₀ hj h

theorem self_mem_range_rowScale (p : Matrix m m K) : p ∈ LinearMap.range (rowScale p) :=
  ⟨1, by simp⟩

theorem exists_permZero_space_through (p : Matrix m m K) (hp : p.permanent = 0)
    (hrows : ∀ i, p i ≠ 0) :
    ∃ U : Submodule K (Matrix m m K), p ∈ U ∧ Module.finrank K U = Fintype.card m ∧
      ∀ q ∈ U, q.permanent = 0 := by
  refine ⟨LinearMap.range (rowScale p), self_mem_range_rowScale p, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (rowScale_injective p hrows)]
    simp
  · rintro q ⟨d, rfl⟩
    exact permanent_rowScale p hp d

end RowScaling

section Lagrangian

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem invariant_of_lagrangian_pair (B₁ B₂ : LinearMap.BilinForm K V) (T : V →ₗ[K] V)
    (hT : ∀ v w, B₁ (T v) w = B₂ v w) (W : Submodule K V)
    (hLag : ∀ v, (∀ w ∈ W, B₁ v w = 0) → v ∈ W)
    (h2 : ∀ v ∈ W, ∀ w ∈ W, B₂ v w = 0) : ∀ v ∈ W, T v ∈ W :=
  fun v hv => hLag _ fun w hw => by rw [hT]; exact h2 v hv w hw

theorem pow_mem_of_invariant (T : V →ₗ[K] V) (W : Submodule K V) (hT : ∀ v ∈ W, T v ∈ W)
    (z : V) (hz : z ∈ W) : ∀ k : ℕ, (T ^ k) z ∈ W := by
  intro k
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih

variable [FiniteDimensional K V]

theorem krylov_dependent_of_proper_invariant (T : V →ₗ[K] V) (W : Submodule K V)
    (hW : W ≠ ⊤) (hT : ∀ v ∈ W, T v ∈ W) (z : V) (hz : z ∈ W) :
    ¬ LinearIndependent K (fun k : Fin (Module.finrank K V) => (T ^ (k : ℕ)) z) := by
  intro hli
  have hspan : Submodule.span K (Set.range fun k : Fin (Module.finrank K V) => (T ^ (k : ℕ)) z)
      ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact pow_mem_of_invariant T W hT z hz k
  have hcard := linearIndependent_iff_card_eq_finrank_span.mp hli
  rw [Fintype.card_fin] at hcard
  have htop : Submodule.span K (Set.range fun k : Fin (Module.finrank K V) => (T ^ (k : ℕ)) z)
      = ⊤ := Submodule.eq_top_of_finrank_eq hcard.symm
  exact hW (top_le_iff.mp (htop ▸ hspan))

end Lagrangian

section Perm2

variable {K : Type*} [Field K] [NeZero (2 : K)] {m : Type*}

def perm2 (y y' : m → K) (k l : m) : K := y k * y' l + y l * y' k

theorem perm2_zero_of_triple (y y' : m → K) {a b c : m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hb : y b ≠ 0) (hc : y c ≠ 0)
    (h : ∀ k l, k ≠ l → perm2 y y' k l = 0) : y' a = 0 := by
  have h1 := h a b hab
  have h2 := h a c hac
  have h3 := h b c hbc
  simp only [perm2] at h1 h2 h3
  have key : 2 * (y b * y c * y' a) = 0 := by
    linear_combination -(y a * h3) + y b * h2 + y c * h1
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (NeZero.ne 2)
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hb
      · exact absurd h hc
    · exact h

theorem perm2_forces_zero (y y' : m → K) {a b c : m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : y a ≠ 0) (hb : y b ≠ 0) (hc : y c ≠ 0)
    (h : ∀ k l, k ≠ l → perm2 y y' k l = 0) : y' = 0 := by
  funext k
  by_cases hka : k = a
  · subst hka; exact perm2_zero_of_triple y y' hab hbc hac hb hc h
  by_cases hkb : k = b
  · subst hkb; exact perm2_zero_of_triple y y' (Ne.symm hab) hac hbc ha hc h
  by_cases hkc : k = c
  · subst hkc; exact perm2_zero_of_triple y y' (Ne.symm hac) hab (Ne.symm hbc) ha hb h
  by_cases hyk : y k = 0
  · have h1 := h a k (Ne.symm hka)
    simp only [perm2, hyk, zero_mul, add_zero] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h ha
    · exact h
  · exact perm2_zero_of_triple y y' hka hab hkb ha hb h

end Perm2

section BlockTriangular

variable {K : Type*} [Field K] {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂]

theorem linearIndependent_of_block_triangular (v : ι₁ ⊕ ι₂ → (κ₁ ⊕ κ₂ → K))
    (hzero : ∀ i : ι₂, ∀ c : κ₁, v (Sum.inr i) (Sum.inl c) = 0)
    (h1 : LinearIndependent K (fun i : ι₁ => fun c : κ₁ => v (Sum.inl i) (Sum.inl c)))
    (h2 : LinearIndependent K (fun i : ι₂ => fun c : κ₂ => v (Sum.inr i) (Sum.inr c))) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff] at h1 h2 ⊢
  intro g hg
  have hg' : ∀ x, (∑ i, g i • v i) x = 0 := fun x => by rw [hg]; rfl

  have hleft : ∀ i : ι₁, g (Sum.inl i) = 0 := by
    apply h1 (fun i => g (Sum.inl i))
    funext c
    have := hg' (Sum.inl c)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, hzero,
      mul_zero, Finset.sum_const_zero, add_zero] at this
    simpa using this

  have hright : ∀ i : ι₂, g (Sum.inr i) = 0 := by
    apply h2 (fun i => g (Sum.inr i))
    funext c
    have := hg' (Sum.inr c)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, hleft,
      zero_mul, Finset.sum_const_zero, zero_add] at this
    simpa using this
  intro i
  cases i with
  | inl i => exact hleft i
  | inr i => exact hright i

theorem linearIndependent_single_row {κ : Type*} (r : κ → K) (hr : r ≠ 0) :
    LinearIndependent K (fun _ : Unit => r) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fintype.sum_unique] at hg
  rcases smul_eq_zero.mp hg with h | h
  · have : i = default := Subsingleton.elim _ _
    rw [this]; exact h
  · exact absurd h hr

end BlockTriangular

end PermanentBound.RowScaling

end
section
/-! ## Row and column zero spaces -/

namespace PermanentBound.RowColumnSpaces

open PermanentBound.RowScaling

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]

theorem prod_updateRow (M : Matrix m m K) (i₀ : m) (w : m → K) (σ : Equiv.Perm m) :
    ∏ j, (M.updateRow i₀ w) (σ j) j
      = w (σ.symm i₀) * ∏ j ∈ Finset.univ.erase (σ.symm i₀), M (σ j) j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (σ.symm i₀))]
  congr 1
  · simp [Matrix.updateRow_apply]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have h : σ j ≠ i₀ := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (by rw [← h, Equiv.symm_apply_apply])
    simp [Matrix.updateRow_ne h]

theorem permanent_updateRow_add (M : Matrix m m K) (i₀ : m) (u v : m → K) :
    (M.updateRow i₀ (u + v)).permanent
      = (M.updateRow i₀ u).permanent + (M.updateRow i₀ v).permanent := by
  unfold Matrix.permanent
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_updateRow, prod_updateRow, prod_updateRow, Pi.add_apply, add_mul]

def rowFunctional (p : Matrix m m K) (i₀ : m) : (m → K) →ₗ[K] K where
  toFun b := (p.updateRow i₀ b).permanent
  map_add' u v := permanent_updateRow_add p i₀ u v
  map_smul' c u := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact Matrix.permanent_updateRow_smul p i₀ c u

@[simp] theorem rowFunctional_apply (p : Matrix m m K) (i₀ : m) (b : m → K) :
    rowFunctional p i₀ b = (p.updateRow i₀ b).permanent := rfl

def ext0 (i₀ : m) : ({i // i ≠ i₀} → K) →ₗ[K] (m → K) where
  toFun t i := if h : i = i₀ then 0 else t ⟨i, h⟩
  map_add' a b := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem ext0_apply_of_ne (i₀ : m) (t : {i // i ≠ i₀} → K) {i : m} (h : i ≠ i₀) :
    ext0 i₀ t i = t ⟨i, h⟩ := by
  simp [ext0, h]

def phi (p : Matrix m m K) (i₀ : m) :
    (({i // i ≠ i₀} → K) × (m → K)) →ₗ[K] Matrix m m K where
  toFun x := (Matrix.diagonal (ext0 i₀ x.1) * p).updateRow i₀ x.2
  map_add' x y := by
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.add_apply, Prod.fst_add, Prod.snd_add, map_add,
      Matrix.diagonal_mul, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, map_smul,
      Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem phi_apply (p : Matrix m m K) (i₀ : m) (x : ({i // i ≠ i₀} → K) × (m → K)) :
    phi p i₀ x = (Matrix.diagonal (ext0 i₀ x.1) * p).updateRow i₀ x.2 := rfl

theorem phi_eq_diagonal_mul (p : Matrix m m K) (i₀ : m) (x : ({i // i ≠ i₀} → K) × (m → K)) :
    phi p i₀ x = Matrix.diagonal (fun i => if i = i₀ then (1 : K) else ext0 i₀ x.1 i)
      * p.updateRow i₀ x.2 := by
  ext i j
  simp only [phi_apply, Matrix.updateRow_apply, Matrix.diagonal_mul]
  split_ifs <;> simp

theorem permanent_phi_eq_zero (p : Matrix m m K) (i₀ : m) (x : ({i // i ≠ i₀} → K) × (m → K))
    (hb : x.2 ∈ LinearMap.ker (rowFunctional p i₀)) : (phi p i₀ x).permanent = 0 := by
  rw [phi_eq_diagonal_mul, permanent_diagonal_mul]
  have : (p.updateRow i₀ x.2).permanent = 0 := LinearMap.mem_ker.mp hb
  rw [this, mul_zero]

theorem phi_injective (p : Matrix m m K) (i₀ : m) (hrows : ∀ i, p i ≠ 0) :
    Function.Injective (phi p i₀) := by
  intro x y hxy
  have hrow : ∀ i j, phi p i₀ x i j = phi p i₀ y i j := fun i j => by rw [hxy]
  refine Prod.ext ?_ ?_
  · funext ⟨i, hi⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hrows i)
    have h := hrow i j
    simp only [phi_apply, Matrix.updateRow_ne hi, Matrix.diagonal_mul,
      ext0_apply_of_ne i₀ _ hi] at h
    exact mul_right_cancel₀ hj h
  · funext j
    have h := hrow i₀ j
    simpa [phi_apply, Matrix.updateRow_self] using h

def phiRes (p : Matrix m m K) (i₀ : m) :
    (({i // i ≠ i₀} → K) × LinearMap.ker (rowFunctional p i₀)) →ₗ[K] Matrix m m K :=
  (phi p i₀).comp (LinearMap.prodMap LinearMap.id (LinearMap.ker (rowFunctional p i₀)).subtype)

theorem phiRes_injective (p : Matrix m m K) (i₀ : m) (hrows : ∀ i, p i ≠ 0) :
    Function.Injective (phiRes p i₀) := by
  intro x y h
  have := phi_injective p i₀ hrows h
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply, Submodule.subtype_apply] at this
  obtain ⟨h1, h2⟩ := Prod.mk.inj this
  exact Prod.ext h1 (Subtype.ext h2)

theorem card_ne_eq (i₀ : m) : Fintype.card {i // i ≠ i₀} = Fintype.card m - 1 := by
  have h := Fintype.card_subtype_compl (fun i : m => i = i₀)
  rw [Fintype.card_subtype_eq] at h
  exact h

theorem exists_permZero_space_two_n_sub_two (p : Matrix m m K) (i₀ : m)
    (hp : p.permanent = 0) (hrows : ∀ i, p i ≠ 0) (hℓ : rowFunctional p i₀ ≠ 0) :
    ∃ V : Submodule K (Matrix m m K), p ∈ V ∧
      Module.finrank K V = 2 * Fintype.card m - 2 ∧ ∀ q ∈ V, q.permanent = 0 := by
  refine ⟨LinearMap.range (phiRes p i₀), ?_, ?_, ?_⟩
  ·
    have hker : p i₀ ∈ LinearMap.ker (rowFunctional p i₀) := by
      rw [LinearMap.mem_ker, rowFunctional_apply, Matrix.updateRow_eq_self]; exact hp
    refine ⟨(fun _ => 1, ⟨p i₀, hker⟩), ?_⟩
    ext i j
    simp only [phiRes, LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Submodule.subtype_apply, phi_apply, Matrix.updateRow_apply, Matrix.diagonal_mul]
    split_ifs with h
    · subst h; rfl
    · rw [ext0_apply_of_ne i₀ _ h, one_mul]
  · rw [LinearMap.finrank_range_of_inj (phiRes_injective p i₀ hrows), Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, card_ne_eq]
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
    rw [Module.finrank_fintype_fun_eq_card] at h
    omega
  · rintro q ⟨x, rfl⟩
    exact permanent_phi_eq_zero p i₀ _ x.2.2

end PermanentBound.RowColumnSpaces

end
section
/-! ## The Mignon-Ressayre point -/

namespace PermanentBound.MignonRessayrePoint

open PermanentBound.RowColumnSpaces

variable {K : Type*} [Field K] {n : ℕ}

def J (n : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.of fun _ _ => 1

def mrRow (n : ℕ) [NeZero n] : Fin n → K := fun j => 1 - (if j = 0 then (n : K) else 0)

def mrPoint (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) K := (J n).updateRow 0 (mrRow n)

theorem sum_mrRow [NeZero n] : ∑ j, mrRow (K := K) n j = 0 := by
  simp only [mrRow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem updateRow_J_comp (i₀ : Fin n) (v : Fin n → K) (τ : Equiv.Perm (Fin n)) :
    ((J n).updateRow i₀ v).submatrix id τ = (J n).updateRow i₀ (v ∘ τ) := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, Matrix.updateRow_apply, J, Matrix.of_apply,
    Function.comp_apply]

theorem rowFunctional_J_single (i₀ j j' : Fin n) :
    rowFunctional (J n) i₀ (Pi.single j (1 : K)) = rowFunctional (J n) i₀ (Pi.single j' 1) := by
  simp only [rowFunctional_apply]
  have h := Matrix.permanent_permute_rows (Equiv.swap j j')
    ((J (K := K) n).updateRow i₀ (Pi.single j' 1))
  rw [updateRow_J_comp] at h
  rw [← h]
  congr 2
  funext i
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases hi : i = j
  · subst hi; simp
  · by_cases hi' : i = j'
    · subst hi'; simp [Equiv.swap_apply_right, Pi.single_apply, hi, Ne.symm hi]
    · rw [Equiv.swap_apply_of_ne_of_ne hi hi']; simp [Pi.single_apply, hi, hi', Ne.symm hi, Ne.symm hi']

theorem rowFunctional_J (i₀ : Fin n) (b : Fin n → K) [NeZero n] :
    rowFunctional (J n) i₀ b = (∑ j, b j) * rowFunctional (J n) i₀ (Pi.single 0 1) := by
  conv_lhs => rw [← Finset.univ_sum_single b]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Pi.single j (b j) = b j • Pi.single j (1 : K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, rowFunctional_J_single i₀ j 0]

theorem permanent_mrPoint [NeZero n] : (mrPoint (K := K) n).permanent = 0 := by
  have h := rowFunctional_J (K := K) (0 : Fin n) (mrRow n)
  rw [rowFunctional_apply, sum_mrRow, zero_mul] at h
  exact h

end PermanentBound.MignonRessayrePoint

end
section
/-! ## Row-functional ranges -/

namespace PermanentBound.RowFunctional
open PermanentBound.RowColumnSpaces PermanentBound.MignonRessayrePoint PermanentBound.PermanentZeroSpaces

theorem mem_range_phiRes {m : Type*} [Fintype m] [DecidableEq m] (p : Matrix m m F) (i₀ : m)
    (hp : p.permanent = 0) : p ∈ LinearMap.range (phiRes p i₀) := by
  have hker : p i₀ ∈ LinearMap.ker (rowFunctional p i₀) := by
    rw [LinearMap.mem_ker, rowFunctional_apply, Matrix.updateRow_eq_self]; exact hp
  refine ⟨(fun _ => 1, ⟨p i₀, hker⟩), ?_⟩
  ext i j
  simp only [phiRes, phi, LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
    Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.updateRow_apply,
    Matrix.diagonal_mul, ext0]
  split_ifs with h
  · rw [h]
  · simp [h]

theorem single_row_mem_range_phiRes {m : Type*} [Fintype m] [DecidableEq m] (p : Matrix m m F)
    (i₀ : m) (b : m → F) (hb : rowFunctional p i₀ b = 0) :
    Matrix.updateRow (0 : Matrix m m F) i₀ b ∈ LinearMap.range (phiRes p i₀) := by
  refine ⟨(0, ⟨b, LinearMap.mem_ker.mpr hb⟩), ?_⟩
  ext i j
  simp only [phiRes, phi, LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
    Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.updateRow_apply,
    Matrix.diagonal_mul, ext0, map_zero]
  split_ifs <;> simp

end PermanentBound.RowFunctional

end
section
open scoped Matrix

/-! ## Spanning the tangent hyperplane -/

namespace PermanentBound.TangentSpanning

open PermanentBound.RowColumnSpaces PermanentBound.MignonRessayrePoint
  PermanentBound.PermanentZeroSpaces PermanentBound.RowFunctional

variable {n : ℕ} [NeZero n]

theorem permanent_two_equal_unit_rows (M : Matrix (Fin n) (Fin n) F) (i₁ i₂ c : Fin n)
    (h : i₁ ≠ i₂) (h1 : M i₁ = Pi.single c 1) (h2 : M i₂ = Pi.single c 1) : M.permanent = 0 := by
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  by_cases hk : σ.symm i₁ = c
  · apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i₂))
    rw [Equiv.apply_symm_apply, h2, Pi.single_apply, if_neg]
    intro heq
    exact h (σ.symm.injective (hk.trans heq.symm))
  · apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i₁))
    rw [Equiv.apply_symm_apply, h1, Pi.single_apply, if_neg hk]

theorem permanent_J : (J (K := F) n).permanent = (n.factorial : F) := by
  unfold Matrix.permanent
  simp [PermanentBound.MignonRessayrePoint.J, Fintype.card_perm]

theorem rowFunctional_J_single_ne_zero (i : Fin n) :
    rowFunctional (J (K := F) n) i (Pi.single 0 1) ≠ 0 := by
  intro h0
  have h := rowFunctional_J (K := F) i (fun _ => 1)
  rw [rowFunctional_apply, h0, mul_zero] at h
  have hJ : (J (K := F) n).updateRow i (fun _ => 1) = J n := by
    ext r s; simp [PermanentBound.MignonRessayrePoint.J, Matrix.updateRow_apply]
  rw [hJ, permanent_J] at h
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) h

theorem mrRow_eq : mrRow (K := F) n = (fun _ => (1 : F)) - (n : F) • Pi.single 0 1 := by
  funext j
  simp only [mrRow, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem rowFunctional_mr_single_ne_zero (i : Fin n) :
    rowFunctional (mrPoint (K := F) n) i (Pi.single 0 1) ≠ 0 := by
  by_cases hi : i = 0
  · subst hi
    have : (mrPoint (K := F) n).updateRow 0 (Pi.single 0 1)
        = (J (K := F) n).updateRow 0 (Pi.single 0 1) := by
      ext r s
      simp only [mrPoint, Matrix.updateRow_apply]
      split_ifs <;> rfl
    rw [rowFunctional_apply, this]
    exact rowFunctional_J_single_ne_zero 0
  ·
    set Mi : Matrix (Fin n) (Fin n) F := (J (K := F) n).updateRow i (Pi.single 0 1) with hMi
    have hcomm : (mrPoint (K := F) n).updateRow i (Pi.single 0 1) = Mi.updateRow 0 (mrRow n) := by
      ext r s
      simp only [mrPoint, hMi, Matrix.updateRow_apply]
      by_cases hr : r = i
      · subst hr; simp [hi]
      · simp [hr]
    rw [rowFunctional_apply, hcomm]
    have hlin := rowFunctional_apply Mi 0 (mrRow n)
    rw [← hlin, mrRow_eq, map_sub, map_smul, smul_eq_mul, rowFunctional_apply, rowFunctional_apply]
    have hzero : (Mi.updateRow 0 (Pi.single 0 1)).permanent = 0 :=
      permanent_two_equal_unit_rows _ 0 i 0 (Ne.symm hi) (by simp)
        (by rw [Matrix.updateRow_ne hi]; simp [hMi])
    have hones : Mi.updateRow 0 (fun _ => (1 : F)) = Mi := by
      ext r s
      by_cases hr : r = 0
      · subst hr
        simp [hMi, Matrix.updateRow_ne (Ne.symm hi), PermanentBound.MignonRessayrePoint.J]
      · simp [Matrix.updateRow_ne hr]
    rw [hzero, mul_zero, sub_zero, hones]
    exact rowFunctional_J_single_ne_zero i

noncomputable def Kr (i : Fin n) : Submodule F (Fin n → F) :=
  LinearMap.ker (rowFunctional (mrPoint (K := F) n) i)

theorem finrank_Kr (i : Fin n) : Module.finrank F ((Kr (F := F)) i) = n - 1 := by
  have hne : rowFunctional (mrPoint (K := F) n) i ≠ 0 := by
    intro h
    exact rowFunctional_mr_single_ne_zero i (by rw [h]; rfl)
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  unfold Kr
  omega

noncomputable def sumF : (Fin n → F) →ₗ[F] F := ∑ j, LinearMap.proj j

theorem sumF_apply (b : Fin n → F) : (sumF (F := F)) b = ∑ j, b j := by
  simp [sumF, LinearMap.sum_apply]

noncomputable def Kc : Submodule F (Fin n → F) := LinearMap.ker (sumF (F := F))

theorem finrank_Kc : Module.finrank F ((Kc (F := F) (n := n))) = n - 1 := by
  have hne : ((sumF (F := F)) : (Fin n → F) →ₗ[F] F) ≠ 0 := by
    intro h
    have := congrArg (fun φ => φ (Pi.single (0 : Fin n) (1 : F))) h
    simp [sumF_apply] at this
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  unfold Kc
  omega

noncomputable def curryLinN : (Fin n × Fin n → F) →ₗ[F] Matrix (Fin n) (Fin n) F :=
  (LinearEquiv.curry F F (Fin n) (Fin n)).toLinearMap

theorem curryLinN_apply (q : Fin n × Fin n → F) : (curryLinN (F := F)) q = toMat q := rfl

noncomputable def VrowN (i₀ : Fin n) : Submodule F (Fin n × Fin n → F) :=
  (LinearMap.range (phiRes (mrPoint (K := F) n) i₀)).comap (curryLinN (F := F))

noncomputable def VcolN : Submodule F (Fin n × Fin n → F) :=
  ((LinearMap.range (phiRes (mrPoint (K := F) n)ᵀ 0)).map
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) F F).toLinearMap).comap (curryLinN (F := F))

noncomputable def VN : Option (Fin n) → Submodule F (Fin n × Fin n → F)
  | some i => (VrowN (F := F)) i
  | none => (VcolN (F := F))

noncomputable def pMRN : Fin n × Fin n → F := fun ij => mrPoint (K := F) n ij.1 ij.2

theorem toMat_pMRN : toMat ((pMRN (F := F) (n := n))) = mrPoint (K := F) n := by ext i j; rfl

theorem VN_spec (o : Option (Fin n)) :
    (pMRN (F := F)) ∈ (VN (F := F)) o ∧ ∀ q ∈ (VN (F := F)) o, (toMat q).permanent = 0 := by
  cases o with
  | some i =>
    refine ⟨?_, ?_⟩
    · show (pMRN (F := F)) ∈ (VrowN (F := F)) i
      rw [VrowN, Submodule.mem_comap, curryLinN_apply, toMat_pMRN]
      exact mem_range_phiRes _ i permanent_mrPoint
    · intro q hq
      change q ∈ (VrowN (F := F)) i at hq
      rw [VrowN, Submodule.mem_comap, curryLinN_apply] at hq
      obtain ⟨x, hx⟩ := hq
      rw [← hx]
      exact permanent_phi_eq_zero _ i _ x.2.2
  | none =>
    refine ⟨?_, ?_⟩
    · show (pMRN (F := F)) ∈ (VcolN (F := F))
      rw [VcolN, Submodule.mem_comap, curryLinN_apply, toMat_pMRN]
      refine ⟨(mrPoint (K := F) n)ᵀ, mem_range_phiRes _ 0 (by
        rw [Matrix.permanent_transpose]; exact permanent_mrPoint), ?_⟩
      simp
    · intro q hq
      change q ∈ (VcolN (F := F)) at hq
      rw [VcolN, Submodule.mem_comap, curryLinN_apply] at hq
      obtain ⟨M, ⟨x, hx⟩, hM⟩ := hq
      rw [← hM]
      show Mᵀ.permanent = 0
      rw [Matrix.permanent_transpose, ← hx]
      exact permanent_phi_eq_zero _ 0 _ x.2.2

theorem mem_VrowN_of_single (i : Fin n) (q : Fin n × Fin n → F)
    (hq : ∀ r s, r ≠ i → q (r, s) = 0) (hb : (fun s => q (i, s)) ∈ (Kr (F := F)) i) : q ∈ (VrowN (F := F)) i := by
  rw [VrowN, Submodule.mem_comap, curryLinN_apply]
  have : toMat q = Matrix.updateRow (0 : Matrix (Fin n) (Fin n) F) i (fun s => q (i, s)) := by
    ext r s
    simp only [toMat, Matrix.of_apply, Matrix.updateRow_apply, Matrix.zero_apply]
    split_ifs with h
    · rw [h]
    · exact hq r s h
  rw [this]
  exact single_row_mem_range_phiRes _ i _ (LinearMap.mem_ker.mp hb)

theorem rowFunctional_mrT_zero (b : Fin n → F) :
    rowFunctional (mrPoint (K := F) n)ᵀ 0 b = rowFunctional (J (K := F) n) 0 b := by
  simp only [rowFunctional_apply]
  congr 1
  ext r s
  by_cases hr : r = 0
  · subst hr; simp
  · rw [Matrix.updateRow_ne hr, Matrix.updateRow_ne hr]
    simp [mrPoint, Matrix.transpose_apply, Matrix.updateRow_apply, mrRow, hr, PermanentBound.MignonRessayrePoint.J]

theorem mem_VcolN_of_single_col (q : Fin n × Fin n → F)
    (hq : ∀ r s, s ≠ 0 → q (r, s) = 0) (hb : (fun r => q (r, 0)) ∈ (Kc (F := F))) : q ∈ (VcolN (F := F)) := by
  rw [VcolN, Submodule.mem_comap, curryLinN_apply]
  have hker : rowFunctional (mrPoint (K := F) n)ᵀ 0 (fun r => q (r, 0)) = 0 := by
    rw [rowFunctional_mrT_zero, rowFunctional_J]
    have : ∑ j, q (j, 0) = 0 := by
      have h := LinearMap.mem_ker.mp hb
      rwa [sumF_apply] at h
    rw [this, zero_mul]
  refine ⟨Matrix.updateRow (0 : Matrix (Fin n) (Fin n) F) 0 (fun r => q (r, 0)),
    single_row_mem_range_phiRes _ 0 _ hker, ?_⟩
  show (Matrix.updateRow (0 : Matrix (Fin n) (Fin n) F) 0 (fun r => q (r, 0)))ᵀ = toMat q
  ext r s
  simp only [toMat, Matrix.of_apply, Matrix.transpose_apply, Matrix.updateRow_apply,
    Matrix.zero_apply]
  split_ifs with h
  · rw [h]
  · exact (hq r s h).symm

noncomputable def Rmap : (∀ i : Fin n, (Kr (F := F)) i) →ₗ[F] (Fin n × Fin n → F) where
  toFun x := fun ij => (x ij.1 : Fin n → F) ij.2
  map_add' x y := by funext ij; simp
  map_smul' c x := by funext ij; simp

theorem Rmap_injective : Function.Injective ((Rmap (F := F) (n := n))) := by
  intro x y h
  funext i
  apply Subtype.ext
  funext s
  exact congrFun h (i, s)

theorem Rmap_mem (x : ∀ i : Fin n, (Kr (F := F)) i) : (Rmap (F := F)) x ∈ ⨆ o, (VN (F := F)) o := by
  have hsum : (Rmap (F := F)) x = ∑ i, (fun ij => if ij.1 = i then (x i : Fin n → F) ij.2 else 0) := by
    funext ij
    simp only [Rmap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
    rw [Finset.sum_eq_single ij.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (some i) ?_
  show _ ∈ (VrowN (F := F)) i
  refine mem_VrowN_of_single i _ (fun r s hr => by simp [hr]) ?_
  simpa using (x i).2

noncomputable def Cmap : (Kc (F := F) (n := n)) →ₗ[F] (Fin n × Fin n → F) where
  toFun b := fun ij => if ij.2 = 0 then (b : Fin n → F) ij.1 else 0
  map_add' x y := by funext ij; by_cases h : ij.2 = 0 <;> simp [h]
  map_smul' c x := by funext ij; by_cases h : ij.2 = 0 <;> simp [h]

theorem Cmap_injective : Function.Injective ((Cmap (F := F) (n := n))) := by
  intro x y h
  apply Subtype.ext
  funext r
  have := congrFun h (r, 0)
  simpa [Cmap] using this

theorem Cmap_mem (b : (Kc (F := F) (n := n))) : (Cmap (F := F)) b ∈ ⨆ o, (VN (F := F)) o := by
  refine Submodule.mem_iSup_of_mem none ?_
  show _ ∈ (VcolN (F := F))
  apply mem_VcolN_of_single_col
  · intro r s hs; simp [Cmap, hs]
  · simpa [Cmap] using b.2

theorem range_inf_eq_bot :
    LinearMap.range ((Rmap (F := F) (n := n))) ⊓ LinearMap.range ((Cmap (F := F) (n := n))) = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨⟨x, rfl⟩, ⟨b, hb⟩⟩
  rw [Submodule.mem_bot]

  have hrow : ∀ i, (x i : Fin n → F) = (b : Fin n → F) i • Pi.single 0 1 := by
    intro i
    funext s
    have h := congrFun hb (i, s)
    simp only [Cmap, LinearMap.coe_mk, AddHom.coe_mk, Rmap] at h
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at h ⊢ with hs
    · rw [← h, mul_one]
    · rw [← h, mul_zero]
  have hzero : ∀ i, (b : Fin n → F) i = 0 := by
    intro i
    have hk := LinearMap.mem_ker.mp (x i).2
    rw [hrow i, map_smul, smul_eq_mul] at hk
    exact (mul_eq_zero.mp hk).resolve_right (rowFunctional_mr_single_ne_zero i)
  funext ij
  simp only [Rmap, LinearMap.coe_mk, AddHom.coe_mk, hrow, Pi.smul_apply, hzero, zero_smul,
    Pi.zero_apply]

theorem tangentSpanned_all :
    ∃ (ιs : Type) (_ : Fintype ιs) (V : ιs → Submodule F (Fin n × Fin n → F)),
      (∀ i, (fun ij => mrPoint (K := F) n ij.1 ij.2) ∈ V i ∧
        ∀ q ∈ V i, (toMat q).permanent = 0) ∧
      n * n - 1 ≤ Module.finrank F (⨆ i, V i : Submodule F (Fin n × Fin n → F)) := by
  refine ⟨Option (Fin n), inferInstance, VN, VN_spec, ?_⟩
  have hR : Module.finrank F (LinearMap.range ((Rmap (F := F) (n := n)))) = n * (n - 1) := by
    rw [LinearMap.finrank_range_of_inj Rmap_injective, Module.finrank_pi_fintype]
    simp [finrank_Kr]
  have hC : Module.finrank F (LinearMap.range ((Cmap (F := F) (n := n)))) = n - 1 := by
    rw [LinearMap.finrank_range_of_inj Cmap_injective, finrank_Kc]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ((Rmap (F := F) (n := n))))
    (LinearMap.range ((Cmap (F := F) (n := n))))
  rw [range_inf_eq_bot, finrank_bot, add_zero, hR, hC] at hsup
  have hle : LinearMap.range ((Rmap (F := F) (n := n))) ⊔ LinearMap.range ((Cmap (F := F) (n := n))) ≤ ⨆ o, (VN (F := F)) o := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩; exact Rmap_mem x
    · rintro _ ⟨b, rfl⟩; exact Cmap_mem b
  have := Submodule.finrank_mono hle
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  have : n * (n - 1) + (n - 1) = n * n - 1 := by
    rcases n with _ | k
    · omega
    · have h : (k + 1) * (k + 1) = (k + 1) * k + k + 1 := by ring
      simp only [Nat.add_sub_cancel]
      omega
  omega

end PermanentBound.TangentSpanning

end
section
/-! ## Functoriality of the permanent -/

namespace PermanentBound.PermanentFunctoriality
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

theorem permanent_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix ι ι R) :
    f M.permanent = (M.map f).permanent := by
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

end PermanentBound.PermanentFunctoriality

end
section
/-! ## Derivatives of the permanent -/

namespace PermanentBound.PermanentDerivatives

open MvPolynomial PermanentBound.Hessian Matrix
  PermanentBound.PermanentZeroSpaces

section RowLinearity

variable {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]

theorem prod_updateRow (M : Matrix m m R) (i₀ : m) (w : m → R) (σ : Equiv.Perm m) :
    ∏ j, (M.updateRow i₀ w) (σ j) j
      = w (σ.symm i₀) * ∏ j ∈ Finset.univ.erase (σ.symm i₀), M (σ j) j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (σ.symm i₀))]
  congr 1
  · simp [Matrix.updateRow_apply]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have h : σ j ≠ i₀ := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (by rw [← h, Equiv.symm_apply_apply])
    simp [Matrix.updateRow_ne h]

theorem permanent_updateRow_add (M : Matrix m m R) (i₀ : m) (u v : m → R) :
    (M.updateRow i₀ (u + v)).permanent
      = (M.updateRow i₀ u).permanent + (M.updateRow i₀ v).permanent := by
  unfold Matrix.permanent
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_updateRow, prod_updateRow, prod_updateRow, Pi.add_apply, add_mul]

def rowFun (M : Matrix m m R) (i₀ : m) : (m → R) →ₗ[R] R where
  toFun b := (M.updateRow i₀ b).permanent
  map_add' u v := permanent_updateRow_add M i₀ u v
  map_smul' c u := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact Matrix.permanent_updateRow_smul M i₀ c u

@[simp] theorem rowFun_apply (M : Matrix m m R) (i₀ : m) (b : m → R) :
    rowFun M i₀ b = (M.updateRow i₀ b).permanent := rfl

theorem row_eq_sum_single (w : m → R) : w = ∑ j, w j • Pi.single j (1 : R) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']

theorem permanent_row_expansion (M : Matrix m m R) (a : m) :
    M.permanent = ∑ j, M a j * (M.updateRow a (Pi.single j 1)).permanent := by
  have h1 : M.permanent = rowFun M a (M a) := by
    rw [rowFun_apply, Matrix.updateRow_eq_self]
  have h2 : rowFun M a (M a) = ∑ j, M a j * rowFun M a (Pi.single j 1) := by
    conv_lhs => rw [row_eq_sum_single (M a)]
    rw [map_sum]
    simp [map_smul]
  rw [h1, h2]
  rfl

end RowLinearity

section Leibniz

variable {K : Type*} [CommRing K] {σ : Type*} [DecidableEq σ]

theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → MvPolynomial σ K)
    (v : σ) :
    pderiv v (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ k ∈ s.erase i, f k) * pderiv v (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hia),
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

theorem pderiv_permanent_eq_zero {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m (MvPolynomial σ K)) (v : σ) (hM : ∀ i j, pderiv v (M i j) = 0) :
    pderiv v M.permanent = 0 := by
  unfold Matrix.permanent
  rw [map_sum]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [pderiv_finset_prod]
  exact Finset.sum_eq_zero fun i _ => by rw [hM, mul_zero]

end Leibniz

section Permanent

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]

theorem permPoly_eq : permPoly m K = (Matrix.mvPolynomialX m m K).permanent := rfl

theorem pderiv_entry_updateRow (a : m) (w : m → K) (b : m) (i j : m) :
    pderiv (a, b) (((Matrix.mvPolynomialX m m K).updateRow a (fun k => C (w k))) i j) = 0 := by
  by_cases hi : i = a
  · subst hi; simp [Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne hi, Matrix.mvPolynomialX_apply, pderiv_X, Pi.single_apply,
      if_neg (by simp [hi])]

theorem pderiv_entry_updateRow₂ (a c : m) (w w' : m → K) (d : m) (i j : m) :
    pderiv (c, d) ((((Matrix.mvPolynomialX m m K).updateRow a (fun k => C (w k))).updateRow c
      (fun k => C (w' k))) i j) = 0 := by
  by_cases hi : i = c
  · subst hi; simp [Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne hi]
    by_cases hia : i = a
    · subst hia; simp [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hia, Matrix.mvPolynomialX_apply, pderiv_X, Pi.single_apply,
        if_neg (by simp [hi])]

theorem single_eq_C (j : m) :
    (Pi.single j (1 : MvPolynomial (m × m) K) : m → MvPolynomial (m × m) K)
      = fun k => C (if k = j then (1 : K) else 0) := by
  funext k
  simp only [Pi.single_apply]
  split_ifs <;> simp

theorem pderiv_permPoly (a b : m) :
    pderiv (a, b) (permPoly m K)
      = ((Matrix.mvPolynomialX m m K).updateRow a (Pi.single b 1)).permanent := by
  rw [permPoly_eq, permanent_row_expansion _ a, map_sum]
  rw [Finset.sum_eq_single b]
  · rw [pderiv_mul, Matrix.mvPolynomialX_apply, pderiv_X, Pi.single_eq_same, one_mul,
      single_eq_C, pderiv_permanent_eq_zero _ _ (pderiv_entry_updateRow a _ b), mul_zero,
      add_zero]
  · intro j _ hj
    rw [pderiv_mul, Matrix.mvPolynomialX_apply, pderiv_X, Pi.single_apply,
      if_neg (by simp [hj]), zero_mul, single_eq_C,
      pderiv_permanent_eq_zero _ _ (pderiv_entry_updateRow a _ b), mul_zero, add_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem pderiv_pderiv_permPoly_ne (a b c d : m) (hac : a ≠ c) :
    pderiv (c, d) (pderiv (a, b) (permPoly m K))
      = (((Matrix.mvPolynomialX m m K).updateRow a (Pi.single b 1)).updateRow c
          (Pi.single d 1)).permanent := by
  rw [pderiv_permPoly, permanent_row_expansion _ c, map_sum]
  rw [Finset.sum_eq_single d]
  · rw [pderiv_mul, Matrix.updateRow_ne (Ne.symm hac), Matrix.mvPolynomialX_apply, pderiv_X,
      Pi.single_eq_same, one_mul, single_eq_C, single_eq_C,
      pderiv_permanent_eq_zero _ _ (pderiv_entry_updateRow₂ a c _ _ d), mul_zero, add_zero]
  · intro j _ hj
    rw [pderiv_mul, Matrix.updateRow_ne (Ne.symm hac), Matrix.mvPolynomialX_apply, pderiv_X,
      Pi.single_apply, if_neg (by simp [hj]), zero_mul, single_eq_C, single_eq_C,
      pderiv_permanent_eq_zero _ _ (pderiv_entry_updateRow₂ a c _ _ d), mul_zero, add_zero]
  · intro h; exact absurd (Finset.mem_univ d) h

theorem pderiv_pderiv_permPoly_eq (a b d : m) :
    pderiv (a, d) (pderiv (a, b) (permPoly m K)) = 0 := by
  rw [pderiv_permPoly, single_eq_C]
  exact pderiv_permanent_eq_zero _ _ (pderiv_entry_updateRow a _ d)

theorem map_updateRow_C (M : Matrix m m (MvPolynomial (m × m) K)) (a : m) (w : m → K)
    (p : m × m → K) :
    (M.updateRow a (fun k => C (w k))).map (eval p) = (M.map (eval p)).updateRow a w := by
  ext i j
  by_cases hi : i = a
  · subst hi; simp
  · simp [Matrix.updateRow_ne hi]

theorem map_𝕏 (p : m × m → K) : (Matrix.mvPolynomialX m m K).map (eval p) = toMat p := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, eval_X, toMat, Matrix.of_apply]

theorem hess_permPoly_apply (p : m × m → K) (a b c d : m) :
    hess (permPoly m K) p (a, b) (c, d)
      = if a = c then 0
        else (((toMat p).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)).permanent := by
  unfold hess
  split_ifs with hac
  · subst hac; rw [pderiv_pderiv_permPoly_eq, map_zero]
  · rw [pderiv_pderiv_permPoly_ne a b c d hac, single_eq_C, single_eq_C]
    have h := PermanentBound.PermanentFunctoriality.permanent_map (eval p)
      ((((Matrix.mvPolynomialX m m K).updateRow a (fun k => C (if k = b then (1 : K) else 0))).updateRow c
        (fun k => C (if k = d then (1 : K) else 0))))
    have e1 : (fun k => if k = b then (1 : K) else 0) = Pi.single b 1 := by
      funext k; simp [Pi.single_apply]
    have e2 : (fun k => if k = d then (1 : K) else 0) = Pi.single d 1 := by
      funext k; simp [Pi.single_apply]
    rw [h, map_updateRow_C, map_updateRow_C, map_𝕏, e1, e2]

theorem hess_permPoly_apply_same_col (p : m × m → K) (a b c : m) (hac : a ≠ c) :
    hess (permPoly m K) p (a, b) (c, b) = 0 := by
  rw [hess_permPoly_apply, if_neg hac]
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  by_cases hk : σ.symm a = b
  · apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm c))
    rw [Equiv.apply_symm_apply, Matrix.updateRow_self, Pi.single_apply, if_neg]
    intro heq
    exact hac (σ.symm.injective (hk.trans heq.symm))
  · apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm a))
    rw [Equiv.apply_symm_apply, Matrix.updateRow_ne hac, Matrix.updateRow_self, Pi.single_apply,
      if_neg hk]

end Permanent

end PermanentBound.PermanentDerivatives

end
section
/-! ## Explicit Hessian entries -/

namespace PermanentBound.HessianEntries

open MvPolynomial PermanentBound.Hessian Matrix
  PermanentBound.PermanentZeroSpaces PermanentBound.PermanentDerivatives
  PermanentBound.MignonRessayrePoint PermanentBound.RowColumnSpaces
  PermanentBound.TangentSpanning

variable {n : ℕ} [NeZero n]

local notation "JJ" => PermanentBound.MignonRessayrePoint.J (K := F) n

theorem rowFunctional_J_single_eq (a b : Fin n) :
    rowFunctional JJ a (Pi.single b 1) = ((n - 1).factorial : F) := by
  have h := rowFunctional_J (K := F) a (fun _ => 1)
  have hJ : (JJ).updateRow a (fun _ => 1) = JJ := by
    ext r s; simp [PermanentBound.MignonRessayrePoint.J, Matrix.updateRow_apply]
  rw [rowFunctional_apply, hJ, permanent_J] at h
  rw [rowFunctional_J_single a b 0]
  have hn : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hfac : (n.factorial : F) = (n : F) * ((n - 1).factorial : F) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
    simp [Nat.factorial_succ]
  rw [hfac] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact mul_left_cancel₀ hn h.symm

theorem permanent_swap_cols (M : Matrix (Fin n) (Fin n) F) (c d d' : Fin n)
    (hrows : ∀ r, r ≠ c → ∀ k, M r (Equiv.swap d d' k) = M r k) :
    (M.updateRow c (Pi.single d' 1)).permanent = (M.updateRow c (Pi.single d 1)).permanent := by
  have h := Matrix.permanent_permute_rows (Equiv.swap d d') (M.updateRow c (Pi.single d' 1))
  rw [← h]
  congr 1
  ext r k
  simp only [Matrix.submatrix_apply, id_eq, Matrix.updateRow_apply]
  split_ifs with hr
  · by_cases hk : k = d
    · subst hk; simp [Pi.single_apply, eq_comm]
    · by_cases hk' : k = d'
      · subst hk'; simp [Pi.single_apply, eq_comm]
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
        simp [Pi.single_apply, hk, hk']
  · exact hrows r hr k

theorem perm_J_two_units (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d) :
    (((JJ).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)).permanent
      = ((n - 2).factorial : F) := by
  classical
  set M := (JJ).updateRow a (Pi.single b 1) with hM

  have hsym : ∀ d', d' ≠ b → (M.updateRow c (Pi.single d' 1)).permanent
      = (M.updateRow c (Pi.single d 1)).permanent := by
    intro d' hd'
    apply permanent_swap_cols M c d d'
    intro r hr k
    by_cases hra : r = a
    · subst hra
      simp only [hM, Matrix.updateRow_self, Pi.single_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_of_ne_of_ne hbd (Ne.symm hd')]
    · simp [hM, Matrix.updateRow_ne hra, PermanentBound.MignonRessayrePoint.J]

  have hzero : (M.updateRow c (Pi.single b 1)).permanent = 0 :=
    permanent_two_equal_unit_rows _ a c b hac
      (by rw [Matrix.updateRow_ne hac, hM, Matrix.updateRow_self]) (by simp)

  have hsum : ∑ d', (M.updateRow c (Pi.single d' 1)).permanent = ((n - 1).factorial : F) := by
    have h1 : (∑ d', (M.updateRow c (Pi.single d' 1)).permanent)
        = rowFun M c (∑ d' : Fin n, (Pi.single d' (1 : F) : Fin n → F)) := by
      rw [map_sum]; rfl
    rw [h1]
    have h2 : (∑ d' : Fin n, (Pi.single d' (1 : F) : Fin n → F)) = fun _ => (1 : F) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    rw [h2, rowFun_apply]
    have h3 : M.updateRow c (fun _ => (1 : F)) = M := by
      ext r s
      by_cases hr : r = c
      · subst hr; simp [hM, Matrix.updateRow_ne (Ne.symm hac), PermanentBound.MignonRessayrePoint.J]
      · simp [Matrix.updateRow_ne hr]
    rw [h3, hM, ← rowFunctional_apply, rowFunctional_J_single_eq]

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hzero, zero_add] at hsum
  rw [Finset.sum_congr rfl (fun d' hd' => hsym d' (Finset.ne_of_mem_erase hd'))] at hsum
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn1 : ((n - 1 : ℕ) : F) ≠ 0 := by
    have : 2 ≤ n := by
      by_contra h
      push_neg at h
      have : a = c := Fin.ext (by omega)
      exact hac this
    exact Nat.cast_ne_zero.mpr (by omega)
  have hfac : ((n - 1).factorial : F) = ((n - 1 : ℕ) : F) * ((n - 2).factorial : F) := by
    obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by
      have : 2 ≤ n := by
        by_contra h; push_neg at h
        exact hac (Fin.ext (by omega))
      omega⟩
    rw [hk, Nat.factorial_succ]
    have : n - 2 = k := by omega
    rw [this]; push_cast; ring
  rw [hfac] at hsum
  exact mul_left_cancel₀ hn1 hsum

theorem perm_J_three_units (a b c d : Fin n) (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c)
    (hb : b ≠ 0) (hd : d ≠ 0) (hbd : b ≠ d) :
    ((((JJ).updateRow 0 (Pi.single 0 1)).updateRow a (Pi.single b 1)).updateRow c
      (Pi.single d 1)).permanent = ((n - 3).factorial : F) := by
  classical
  set M := ((JJ).updateRow 0 (Pi.single 0 1)).updateRow a (Pi.single b 1) with hM
  have hsym : ∀ d', d' ≠ b → d' ≠ 0 → (M.updateRow c (Pi.single d' 1)).permanent
      = (M.updateRow c (Pi.single d 1)).permanent := by
    intro d' hd'b hd'0
    apply permanent_swap_cols M c d d'
    intro r hr k
    by_cases hra : r = a
    · subst hra
      simp only [hM, Matrix.updateRow_self, Pi.single_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_of_ne_of_ne hbd (Ne.symm hd'b)]
    · by_cases hr0 : r = 0
      · subst hr0
        simp only [hM, Matrix.updateRow_ne hra, Matrix.updateRow_self, Pi.single_apply,
          Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm hd) (Ne.symm hd'0)]
      · simp [hM, Matrix.updateRow_ne hra, Matrix.updateRow_ne hr0,
          PermanentBound.MignonRessayrePoint.J]
  have hzero_b : (M.updateRow c (Pi.single b 1)).permanent = 0 :=
    permanent_two_equal_unit_rows _ a c b hac
      (by rw [Matrix.updateRow_ne hac, hM, Matrix.updateRow_self]) (by simp)
  have hzero_0 : (M.updateRow c (Pi.single 0 1)).permanent = 0 :=
    permanent_two_equal_unit_rows _ 0 c 0 (Ne.symm hc)
      (by rw [Matrix.updateRow_ne (Ne.symm hc), hM, Matrix.updateRow_ne (Ne.symm ha),
        Matrix.updateRow_self]) (by simp)
  have hsum : ∑ d', (M.updateRow c (Pi.single d' 1)).permanent = ((n - 2).factorial : F) := by
    have h1 : (∑ d', (M.updateRow c (Pi.single d' 1)).permanent)
        = rowFun M c (∑ d' : Fin n, (Pi.single d' (1 : F) : Fin n → F)) := by
      rw [map_sum]; rfl
    rw [h1]
    have h2 : (∑ d' : Fin n, (Pi.single d' (1 : F) : Fin n → F)) = fun _ => (1 : F) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    rw [h2, rowFun_apply]
    have h3 : M.updateRow c (fun _ => (1 : F)) = M := by
      ext r s
      by_cases hr : r = c
      · subst hr
        simp [hM, Matrix.updateRow_ne (Ne.symm hac), Matrix.updateRow_ne hc,
          PermanentBound.MignonRessayrePoint.J]
      · simp [Matrix.updateRow_ne hr]
    rw [h3, hM]
    exact perm_J_two_units 0 0 a b (Ne.symm ha) (Ne.symm hb)

  have hb0 : b ≠ 0 := hb
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hzero_b, zero_add] at hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hb0, Finset.mem_univ 0⟩),
    hzero_0, zero_add] at hsum
  rw [Finset.sum_congr rfl (fun d' hd' => hsym d' (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hd'))
    (Finset.ne_of_mem_erase hd'))] at hsum
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hb0, Finset.mem_univ 0⟩),
    Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have h3n : 3 ≤ n := by
    by_contra h
    push_neg at h

    have := Fin.val_lt_of_le a (le_refl n)
    have := Fin.val_lt_of_le c (le_refl n)
    have ha' : (a : ℕ) ≠ 0 := fun h' => ha (Fin.ext h')
    have hc' : (c : ℕ) ≠ 0 := fun h' => hc (Fin.ext h')
    have hac' : (a : ℕ) ≠ (c : ℕ) := fun h' => hac (Fin.ext h')
    omega
  have hn2 : ((n - 1 - 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : ((n - 2).factorial : F) = ((n - 1 - 1 : ℕ) : F) * ((n - 3).factorial : F) := by
    obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
    rw [hk, Nat.factorial_succ]
    have e1 : n - 1 - 1 = k + 1 := by omega
    have e2 : n - 3 = k := by omega
    rw [e1, e2]; push_cast; ring
  rw [hfac] at hsum
  exact mul_left_cancel₀ hn2 hsum

noncomputable abbrev pMR : Fin n × Fin n → F := fun ij => mrPoint (K := F) n ij.1 ij.2

theorem toMat_pMR : toMat ((pMR (F := F) (n := n))) = mrPoint (K := F) n := by ext i j; rfl

theorem hess_mr_apply (a b c d : Fin n) :
    hess (permPoly (Fin n) F) (pMR (F := F)) (a, b) (c, d)
      = if a = c ∨ b = d then 0
        else if a = 0 ∨ c = 0 then ((n - 2).factorial : F)
        else -((n - 3).factorial : F) * (mrRow (K := F) n b + mrRow (K := F) n d) := by
  rw [hess_permPoly_apply, toMat_pMR]
  by_cases hac : a = c
  · simp [hac]
  rw [if_neg hac]
  by_cases hbd : b = d
  · subst hbd
    rw [if_pos (Or.inr rfl)]
    exact permanent_two_equal_unit_rows _ a c b hac
      (by rw [Matrix.updateRow_ne hac, Matrix.updateRow_self]) (by simp)
  rw [if_neg (by simp [hac, hbd])]
  by_cases h0 : a = 0 ∨ c = 0
  · rw [if_pos h0]
    rcases h0 with ha | hc
    · subst ha
      have : ((mrPoint (K := F) n).updateRow 0 (Pi.single b 1)) = (JJ).updateRow 0 (Pi.single b 1) := by
        ext r s
        simp only [mrPoint, Matrix.updateRow_apply]
        split_ifs <;> rfl
      rw [this]
      exact perm_J_two_units 0 b c d hac hbd
    · subst hc
      have : ((mrPoint (K := F) n).updateRow a (Pi.single b 1)).updateRow 0 (Pi.single d 1)
          = ((JJ).updateRow a (Pi.single b 1)).updateRow 0 (Pi.single d 1) := by
        ext r s
        simp only [mrPoint, Matrix.updateRow_apply]
        split_ifs <;> rfl
      rw [this]
      exact perm_J_two_units a b 0 d hac hbd
  · rw [if_neg h0]
    push_neg at h0
    obtain ⟨ha, hc⟩ := h0

    have hcomm : ((mrPoint (K := F) n).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)
        = (((JJ).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)).updateRow 0
            (mrRow (K := F) n) := by
      ext r s
      simp only [mrPoint, Matrix.updateRow_apply]
      by_cases hr0 : r = 0
      · subst hr0; simp [Ne.symm ha, Ne.symm hc]
      · simp [hr0]
    rw [hcomm]
    set M := ((JJ).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1) with hM
    have hlin : (M.updateRow 0 (mrRow (K := F) n)).permanent
        = M.permanent - (n : F) * (M.updateRow 0 (Pi.single 0 1)).permanent := by
      have := rowFun_apply M 0 (mrRow (K := F) n)
      rw [← this, mrRow_eq, map_sub, map_smul, smul_eq_mul, rowFun_apply, rowFun_apply]
      congr 2
      ext r s
      by_cases hr : r = 0
      · subst hr; simp [hM, Matrix.updateRow_ne (Ne.symm hc), Matrix.updateRow_ne (Ne.symm ha),
          PermanentBound.MignonRessayrePoint.J]
      · simp [Matrix.updateRow_ne hr]
    rw [hlin, hM, perm_J_two_units a b c d hac hbd]

    have hthree : ((((JJ).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)).updateRow 0
        (Pi.single 0 1)).permanent
        = if b = 0 ∨ d = 0 then 0 else ((n - 3).factorial : F) := by
      have hcomm' : (((JJ).updateRow a (Pi.single b 1)).updateRow c (Pi.single d 1)).updateRow 0
          (Pi.single 0 1)
          = (((JJ).updateRow 0 (Pi.single 0 1)).updateRow a (Pi.single b 1)).updateRow c
            (Pi.single d 1) := by
        ext r s
        simp only [Matrix.updateRow_apply]
        by_cases hr0 : r = 0
        · subst hr0; simp [Ne.symm ha, Ne.symm hc]
        · simp [hr0]
      rw [hcomm']
      by_cases hb : b = 0
      · subst hb
        rw [if_pos (Or.inl rfl)]
        exact permanent_two_equal_unit_rows _ 0 a 0 (Ne.symm ha)
          (by rw [Matrix.updateRow_ne (Ne.symm hc), Matrix.updateRow_ne (Ne.symm ha),
            Matrix.updateRow_self])
          (by rw [Matrix.updateRow_ne hac, Matrix.updateRow_self])
      by_cases hd : d = 0
      · subst hd
        rw [if_pos (Or.inr rfl)]
        exact permanent_two_equal_unit_rows _ 0 c 0 (Ne.symm hc)
          (by rw [Matrix.updateRow_ne (Ne.symm hc), Matrix.updateRow_ne (Ne.symm ha),
            Matrix.updateRow_self])
          (by simp)
      rw [if_neg (by simp [hb, hd])]
      exact perm_J_three_units a b c d ha hc hac hb hd hbd
    rw [hthree]

    have h3n : 3 ≤ n := by
      by_contra h
      push_neg at h
      have ha' : (a : ℕ) ≠ 0 := fun h' => ha (Fin.ext h')
      have hc' : (c : ℕ) ≠ 0 := fun h' => hc (Fin.ext h')
      have hac' : (a : ℕ) ≠ (c : ℕ) := fun h' => hac (Fin.ext h')
      have := a.isLt
      have := c.isLt
      omega
    have hfac : ((n - 2).factorial : F) = ((n - 2 : ℕ) : F) * ((n - 3).factorial : F) := by
      obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
      rw [hk, Nat.factorial_succ]
      have e2 : n - 3 = k := by omega
      rw [e2]; push_cast; ring
    have hcast : ((n - 2 : ℕ) : F) = (n : F) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    simp only [mrRow]
    by_cases hb : b = 0
    · subst hb
      have hd : d ≠ 0 := Ne.symm hbd
      simp only [if_true, hd, if_false, true_or, hfac, hcast]
      ring
    · by_cases hd : d = 0
      · subst hd
        simp only [hb, if_false, if_true, or_true, hfac, hcast]
        ring
      · simp only [hb, hd, if_false, or_self, hfac, hcast]
        ring

end PermanentBound.HessianEntries

end
section
/-! ## A five-dimensional matrix algebra -/

namespace PermanentBound.MatrixAlgebra

variable {n : ℕ} [NeZero n]

def Jm : Matrix (Fin n) (Fin n) F := Matrix.of fun _ _ => 1

def Rm : Matrix (Fin n) (Fin n) F := Matrix.of fun i _ => if i = 0 then 1 else 0

def Cm : Matrix (Fin n) (Fin n) F := Matrix.of fun _ j => if j = 0 then 1 else 0

def Em : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

@[simp] theorem Jm_apply (i j : Fin n) : (Jm (F := F)) i j = 1 := rfl
@[simp] theorem Rm_apply (i j : Fin n) : (Rm (F := F)) i j = if i = 0 then 1 else 0 := rfl
@[simp] theorem Cm_apply (i j : Fin n) : (Cm (F := F)) i j = if j = 0 then 1 else 0 := rfl
@[simp] theorem Em_apply (i j : Fin n) : (Em (F := F)) i j = if i = 0 ∧ j = 0 then 1 else 0 := rfl

theorem sum_ite_zero (f : Fin n → F) : (∑ k : Fin n, if k = 0 then f k else 0) = f 0 := by
  simp [Finset.sum_ite_eq']

theorem sum_const_n (c : F) : (∑ _k : Fin n, c) = (n : F) * c := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem J_mul_J : ((Jm (F := F)) : Matrix (Fin n) (Fin n) F) * (Jm (F := F)) = (n : F) • (Jm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, sum_const_n]

theorem J_mul_R : ((Jm (F := F)) : Matrix (Fin n) (Fin n) F) * (Rm (F := F)) = (Jm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, Finset.sum_ite_eq']

theorem J_mul_C : ((Jm (F := F)) : Matrix (Fin n) (Fin n) F) * (Cm (F := F)) = (n : F) • (Cm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, sum_const_n]

theorem J_mul_E : ((Jm (F := F)) : Matrix (Fin n) (Fin n) F) * (Em (F := F)) = (Cm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']

theorem R_mul_J : ((Rm (F := F)) : Matrix (Fin n) (Fin n) F) * (Jm (F := F)) = (n : F) • (Rm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, sum_const_n]

theorem R_mul_R : ((Rm (F := F)) : Matrix (Fin n) (Fin n) F) * (Rm (F := F)) = (Rm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, Finset.sum_ite_eq']

theorem R_mul_C : ((Rm (F := F)) : Matrix (Fin n) (Fin n) F) * (Cm (F := F)) = (n : F) • (Em (F := F)) := by
  ext i j; simp [Matrix.mul_apply, sum_const_n, ite_and]; split_ifs <;> simp

theorem R_mul_E : ((Rm (F := F)) : Matrix (Fin n) (Fin n) F) * (Em (F := F)) = (Em (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem C_mul_J : ((Cm (F := F)) : Matrix (Fin n) (Fin n) F) * (Jm (F := F)) = (Jm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, Finset.sum_ite_eq']

theorem C_mul_R : ((Cm (F := F)) : Matrix (Fin n) (Fin n) F) * (Rm (F := F)) = (Jm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, Finset.sum_ite_eq']

theorem C_mul_C : ((Cm (F := F)) : Matrix (Fin n) (Fin n) F) * (Cm (F := F)) = (Cm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, Finset.sum_ite_eq']

theorem C_mul_E : ((Cm (F := F)) : Matrix (Fin n) (Fin n) F) * (Em (F := F)) = (Cm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']

theorem E_mul_J : ((Em (F := F)) : Matrix (Fin n) (Fin n) F) * (Jm (F := F)) = (Rm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']

theorem E_mul_R : ((Em (F := F)) : Matrix (Fin n) (Fin n) F) * (Rm (F := F)) = (Rm (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']

theorem E_mul_C : ((Em (F := F)) : Matrix (Fin n) (Fin n) F) * (Cm (F := F)) = (Em (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem E_mul_E : ((Em (F := F)) : Matrix (Fin n) (Fin n) F) * (Em (F := F)) = (Em (F := F)) := by
  ext i j; simp [Matrix.mul_apply, ite_and, Finset.sum_ite_eq']
  split_ifs <;> simp_all

end PermanentBound.MatrixAlgebra

end
section
/-! ## An explicit Hessian inverse -/

namespace PermanentBound.HessianInverse

open Kronecker PermanentBound.MatrixAlgebra PermanentBound.HessianEntries Matrix
  PermanentBound.Hessian PermanentBound.PermanentZeroSpaces
  PermanentBound.MignonRessayrePoint

variable {n : ℕ} [NeZero n]

noncomputable def A1 : Matrix (Fin n) (Fin n) F := (Jm (F := F)) + (-1 : F) • 1 + (-1 : F) • (Rm (F := F)) + (-1 : F) • (Cm (F := F)) + (2 : F) • (Em (F := F))
noncomputable def A2 : Matrix (Fin n) (Fin n) F := (Rm (F := F)) + (Cm (F := F)) + (-2 : F) • (Em (F := F))
noncomputable def A3 : Matrix (Fin n) (Fin n) F := 1 + (-1 : F) • (Em (F := F))
noncomputable def A4 : Matrix (Fin n) (Fin n) F := (Em (F := F))
noncomputable def B1 : Matrix (Fin n) (Fin n) F := (Jm (F := F)) + (-1 : F) • 1
noncomputable def B2 : Matrix (Fin n) (Fin n) F :=
  (2 : F) • (Jm (F := F)) + (-2 : F) • 1 + (-(n : F)) • (Rm (F := F)) + (-(n : F)) • (Cm (F := F)) + (2 * (n : F)) • (Em (F := F))
noncomputable def D1 : Matrix (Fin n) (Fin n) F :=
  (4 : F) • (Em (F := F)) + (((n : F) - 2) ^ 2) • (A3 (F := F)) + (2 : F) • (A2 (F := F)) + (2 - (n : F)) • (A1 (F := F))
noncomputable def D2 : Matrix (Fin n) (Fin n) F :=
  (2 * (2 - (n : F))) • (Em (F := F)) + (2 * (2 - (n : F))) • (A3 (F := F)) + (2 : F) • (A2 (F := F)) + (2 : F) • (A1 (F := F))
noncomputable def D3 : Matrix (Fin n) (Fin n) F :=
  (4 * (2 - (n : F))) • (Em (F := F)) + (-((n : F) - 2) ^ 3) • (A3 (F := F)) + (2 * (2 - (n : F))) • (A2 (F := F))
    + (((n : F) - 2) ^ 2) • (A1 (F := F))
noncomputable def D4 : Matrix (Fin n) (Fin n) F :=
  (4 * ((n : F) - 1) * ((n : F) - 2)) • (Em (F := F)) + (4 * (2 - (n : F))) • (A3 (F := F))
    + (2 * (2 - (n : F))) • (A2 (F := F)) + (4 : F) • (A1 (F := F))

noncomputable def Hk : Matrix (Fin n × Fin n) (Fin n × Fin n) F :=
  ((n - 2).factorial : F) • ((A2 (F := F)) ⊗ₖ (B1 (F := F))) + (-((n - 3).factorial : F)) • ((A1 (F := F)) ⊗ₖ (B2 (F := F)))

noncomputable def Mk : Matrix (Fin n × Fin n) (Fin n × Fin n) F :=
  (A1 (F := F)) ⊗ₖ (D1 (F := F)) + (A2 (F := F)) ⊗ₖ (D2 (F := F)) + (A3 (F := F)) ⊗ₖ (D3 (F := F)) + (A4 (F := F)) ⊗ₖ (D4 (F := F))

noncomputable def invCoeff' (n : ℕ) [NeZero n] (a b c d : Fin n) : F :=
  let z : F := (n : F)
  if a ≠ c ∧ a ≠ 0 ∧ c ≠ 0 then
    (if b = d then (if b = 0 then 4 else (z - 2) ^ 2) else (if b = 0 ∨ d = 0 then 2 else 2 - z))
  else if a ≠ c then
    (if b = d then 2 * (2 - z) else 2)
  else if a ≠ 0 then
    (if b = d then (if b = 0 then 4 * (2 - z) else -(z - 2) ^ 3)
     else (if b = 0 ∨ d = 0 then 2 * (2 - z) else (z - 2) ^ 2))
  else
    (if b = d then (if b = 0 then 4 * (z - 1) * (z - 2) else 4 * (2 - z))
     else (if b = 0 ∨ d = 0 then 2 * (2 - z) else 4))

theorem A1_apply (a c : Fin n) : (A1 (F := F)) a c = 1 - (if a = c then 1 else 0) - (if a = 0 then 1 else 0)
    - (if c = 0 then 1 else 0) + 2 * (if a = 0 ∧ c = 0 then 1 else 0) := by
  simp [A1, Matrix.one_apply]; ring
theorem A2_apply (a c : Fin n) : (A2 (F := F)) a c = (if a = 0 then 1 else 0) + (if c = 0 then 1 else 0)
    - 2 * (if a = 0 ∧ c = 0 then 1 else 0) := by
  simp [A2]; ring
theorem A3_apply (a c : Fin n) : (A3 (F := F)) a c = (if a = c then 1 else 0) - (if a = 0 ∧ c = 0 then 1 else 0) := by
  simp [A3, Matrix.one_apply]; ring
theorem A4_apply (a c : Fin n) : (A4 (F := F)) a c = (if a = 0 ∧ c = 0 then 1 else 0) := rfl
theorem B1_apply (b d : Fin n) : (B1 (F := F)) b d = 1 - (if b = d then 1 else 0) := by
  simp [B1, Matrix.one_apply]; ring
theorem B2_apply (b d : Fin n) : (B2 (F := F)) b d = 2 - 2 * (if b = d then 1 else 0) - (n : F) * (if b = 0 then 1 else 0)
    - (n : F) * (if d = 0 then 1 else 0) + 2 * (n : F) * (if b = 0 ∧ d = 0 then 1 else 0) := by
  simp [B2, Matrix.one_apply]; ring

theorem hess_eq_Hk : hess (permPoly (Fin n) F) (pMR (F := F)) = (Hk (F := F)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [hess_mr_apply]
  simp only [Hk, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
    A1_apply, A2_apply, B1_apply, B2_apply, mrRow]
  by_cases hac : a = c <;> by_cases hbd : b = d <;> by_cases ha : a = 0 <;> by_cases hc : c = 0 <;>
    by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hac) <;> (try subst hbd) <;> (try subst ha) <;> (try subst hc) <;>
    (try subst hb) <;> (try subst hd) <;>
    first
    | exact absurd rfl hac
    | exact absurd rfl hbd
    | exact absurd rfl ha
    | exact absurd rfl hc
    | exact absurd rfl hb
    | exact absurd rfl hd
    | (simp only [*, mrRow, if_true, if_false, and_true, true_and, and_false, false_and, or_true,
        true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, eq_self_iff_true,
        mul_zero, mul_one, zero_mul, one_mul, sub_zero, zero_sub, add_zero, zero_add]
       first | done | ring)

theorem Mk_R1 (a b c d : Fin n) (hac : a ≠ c) (ha : a ≠ 0) (hc : c ≠ 0) :
    (Mk (F := F)) (a, b) (c, d) = (invCoeff' (F := F)) n a b c d := by
  simp only [Mk, Matrix.add_apply, Matrix.kroneckerMap_apply, invCoeff', D1, D2, D3, D4,
    Matrix.smul_apply, smul_eq_mul, A1_apply, A2_apply, A3_apply, A4_apply, Em_apply, ne_eq, hac, ha, hc, if_false, and_self, and_false, false_and, not_false_eq_true,
    true_and, and_true, if_true]
  by_cases hbd : b = d <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hbd) <;> (try subst hb) <;> (try subst hd) <;>
    split_ifs <;> simp_all [eq_comm] <;> first | done | ring | simp

theorem Mk_R2a (b c d : Fin n) (hc : c ≠ 0) :
    (Mk (F := F)) (0, b) (c, d) = (invCoeff' (F := F)) n 0 b c d := by
  have hac : (0 : Fin n) ≠ c := Ne.symm hc
  simp only [Mk, Matrix.add_apply, Matrix.kroneckerMap_apply, invCoeff', D1, D2, D3, D4,
    Matrix.smul_apply, smul_eq_mul, A1_apply, A2_apply, A3_apply, A4_apply, Em_apply, ne_eq, hac, hc, if_false, and_self, and_false, false_and, not_false_eq_true, true_and,
    and_true, if_true, not_true_eq_false, false_or, or_false]
  by_cases hbd : b = d <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hbd) <;> (try subst hb) <;> (try subst hd) <;>
    split_ifs <;> simp_all [eq_comm] <;> first | done | ring | simp

theorem Mk_R2b (a b d : Fin n) (ha : a ≠ 0) :
    (Mk (F := F)) (a, b) (0, d) = (invCoeff' (F := F)) n a b 0 d := by
  simp only [Mk, Matrix.add_apply, Matrix.kroneckerMap_apply, invCoeff', D1, D2, D3, D4,
    Matrix.smul_apply, smul_eq_mul, A1_apply, A2_apply, A3_apply, A4_apply, Em_apply, ne_eq, ha, if_false, and_self, and_false, false_and, not_false_eq_true, true_and,
    and_true, if_true, not_true_eq_false, false_or, or_false]
  by_cases hbd : b = d <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hbd) <;> (try subst hb) <;> (try subst hd) <;>
    split_ifs <;> simp_all [eq_comm] <;> first | done | ring | simp

theorem Mk_R3 (a b d : Fin n) (ha : a ≠ 0) :
    (Mk (F := F)) (a, b) (a, d) = (invCoeff' (F := F)) n a b a d := by
  simp only [Mk, Matrix.add_apply, Matrix.kroneckerMap_apply, invCoeff', D1, D2, D3, D4,
    Matrix.smul_apply, smul_eq_mul, A1_apply, A2_apply, A3_apply, A4_apply, Em_apply, ne_eq, ha, if_false, and_self, and_false, false_and, not_false_eq_true, true_and,
    and_true, if_true, not_true_eq_false, false_or, or_false]
  by_cases hbd : b = d <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hbd) <;> (try subst hb) <;> (try subst hd) <;>
    split_ifs <;> simp_all [eq_comm] <;> first | done | ring | simp

theorem Mk_R4 (b d : Fin n) :
    (Mk (F := F)) (0, b) (0, d) = (invCoeff' (F := F)) n 0 b 0 d := by
  simp only [Mk, Matrix.add_apply, Matrix.kroneckerMap_apply, invCoeff', D1, D2, D3, D4,
    Matrix.smul_apply, smul_eq_mul, A1_apply, A2_apply, A3_apply, A4_apply, Em_apply, ne_eq, if_false, and_self, and_false, false_and, not_false_eq_true, true_and,
    and_true, if_true, not_true_eq_false, false_or, or_false]
  by_cases hbd : b = d <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
    (try subst hbd) <;> (try subst hb) <;> (try subst hd) <;>
    split_ifs <;> simp_all [eq_comm] <;> first | done | ring | simp

theorem Mk_eq : (Mk (F := F)) = Matrix.of (fun (ab cd : Fin n × Fin n) => (invCoeff' (F := F)) n ab.1 ab.2 cd.1 cd.2) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [Matrix.of_apply]
  by_cases hac : a = c
  · subst hac
    by_cases ha : a = 0
    · subst ha; exact Mk_R4 b d
    · exact Mk_R3 a b d ha
  · by_cases ha : a = 0
    · subst ha; exact Mk_R2a b c d (Ne.symm hac)
    · by_cases hc : c = 0
      · subst hc; exact Mk_R2b a b d ha
      · exact Mk_R1 a b c d hac ha hc

macro "algebra_tac" : tactic =>
  `(tactic| (simp only [A1, A2, A3, A4, B1, B2, D1, D2, D3, D4, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, J_mul_J, J_mul_R, J_mul_C, J_mul_E, R_mul_J, R_mul_R, R_mul_C,
      R_mul_E, C_mul_J, C_mul_R, C_mul_C, C_mul_E, E_mul_J, E_mul_R, E_mul_C, E_mul_E, smul_smul,
      smul_add, add_smul]; module))

theorem A2_mul_A1 : ((A2 (F := F)) : Matrix (Fin n) (Fin n) F) * (A1 (F := F)) = ((n : F) - 2 : F) • (Rm (F := F)) + (2 - (n : F) : F) • (Em (F := F)) := by algebra_tac

theorem A2_mul_A2 : ((A2 (F := F)) : Matrix (Fin n) (Fin n) F) * (A2 (F := F)) = (1 : F) • (Jm (F := F)) + (-1 : F) • (Rm (F := F)) + (-1 : F) • (Cm (F := F)) + ((n : F) : F) • (Em (F := F)) := by algebra_tac

theorem A2_mul_A3 : ((A2 (F := F)) : Matrix (Fin n) (Fin n) F) * (A3 (F := F)) = (1 : F) • (Rm (F := F)) + (-1 : F) • (Em (F := F)) := by algebra_tac

theorem A2_mul_A4 : ((A2 (F := F)) : Matrix (Fin n) (Fin n) F) * (A4 (F := F)) = (1 : F) • (Cm (F := F)) + (-1 : F) • (Em (F := F)) := by algebra_tac

theorem A1_mul_A1 : ((A1 (F := F)) : Matrix (Fin n) (Fin n) F) * (A1 (F := F)) = (1 : F) • (1 : Matrix (Fin n) (Fin n) F) + ((n : F) - 3 : F) • (Jm (F := F)) + (3 - (n : F) : F) • (Rm (F := F)) + (3 - (n : F) : F) • (Cm (F := F)) + ((n : F) - 4 : F) • (Em (F := F)) := by algebra_tac

theorem A1_mul_A2 : ((A1 (F := F)) : Matrix (Fin n) (Fin n) F) * (A2 (F := F)) = ((n : F) - 2 : F) • (Cm (F := F)) + (2 - (n : F) : F) • (Em (F := F)) := by algebra_tac

theorem A1_mul_A3 : ((A1 (F := F)) : Matrix (Fin n) (Fin n) F) * (A3 (F := F)) = (-1 : F) • (1 : Matrix (Fin n) (Fin n) F) + (1 : F) • (Jm (F := F)) + (-1 : F) • (Rm (F := F)) + (-1 : F) • (Cm (F := F)) + (2 : F) • (Em (F := F)) := by algebra_tac

theorem A1_mul_A4 : ((A1 (F := F)) : Matrix (Fin n) (Fin n) F) * (A4 (F := F)) = 0 := by algebra_tac

theorem B1_mul_D1 : ((B1 (F := F)) : Matrix (Fin n) (Fin n) F) * (D1 (F := F)) = (-(n : F)^2 + 3*(n : F) - 2 : F) • (1 : Matrix (Fin n) (Fin n) F) + ((n : F) : F) • (Jm (F := F)) + (-(n : F) : F) • (Rm (F := F)) + ((n : F) : F) • (Cm (F := F)) + ((n : F)^2 - 2*(n : F) : F) • (Em (F := F)) := by algebra_tac

theorem B1_mul_D2 : ((B1 (F := F)) : Matrix (Fin n) (Fin n) F) * (D2 (F := F)) = (2*(n : F) - 2 : F) • (1 : Matrix (Fin n) (Fin n) F) := by algebra_tac

theorem B1_mul_D3 : ((B1 (F := F)) : Matrix (Fin n) (Fin n) F) * (D3 (F := F)) = ((n : F)^3 - 5*(n : F)^2 + 8*(n : F) - 4 : F) • (1 : Matrix (Fin n) (Fin n) F) + (-(n : F)^2 + 2*(n : F) : F) • (Jm (F := F)) + ((n : F)^2 - 2*(n : F) : F) • (Rm (F := F)) + (-(n : F)^2 + 2*(n : F) : F) • (Cm (F := F)) + (-(n : F)^3 + 4*(n : F)^2 - 4*(n : F) : F) • (Em (F := F)) := by algebra_tac

theorem B1_mul_D4 : ((B1 (F := F)) : Matrix (Fin n) (Fin n) F) * (D4 (F := F)) = (4*(n : F) - 4 : F) • (1 : Matrix (Fin n) (Fin n) F) + (-2*(n : F) : F) • (Jm (F := F)) + (2*(n : F) : F) • (Rm (F := F)) + (2*(n : F)^2 - 2*(n : F) : F) • (Cm (F := F)) + (-4*(n : F)^2 + 4*(n : F) : F) • (Em (F := F)) := by algebra_tac

theorem B2_mul_D1 : ((B2 (F := F)) : Matrix (Fin n) (Fin n) F) * (D1 (F := F)) = (-2*(n : F)^2 + 6*(n : F) - 4 : F) • (1 : Matrix (Fin n) (Fin n) F) := by algebra_tac

theorem B2_mul_D2 : ((B2 (F := F)) : Matrix (Fin n) (Fin n) F) * (D2 (F := F)) = (4*(n : F) - 4 : F) • (1 : Matrix (Fin n) (Fin n) F) + (-2*(n : F) : F) • (Jm (F := F)) + (2*(n : F) : F) • (Rm (F := F)) + (2*(n : F)^2 - 2*(n : F) : F) • (Cm (F := F)) + (-4*(n : F)^2 + 4*(n : F) : F) • (Em (F := F)) := by algebra_tac

theorem B2_mul_D3 : ((B2 (F := F)) : Matrix (Fin n) (Fin n) F) * (D3 (F := F)) = (2*(n : F)^3 - 10*(n : F)^2 + 16*(n : F) - 8 : F) • (1 : Matrix (Fin n) (Fin n) F) := by algebra_tac

theorem B2_mul_D4 : ((B2 (F := F)) : Matrix (Fin n) (Fin n) F) * (D4 (F := F)) = (8*(n : F) - 8 : F) • (1 : Matrix (Fin n) (Fin n) F) + (2*(n : F)^2 - 8*(n : F) : F) • (Jm (F := F)) + (-2*(n : F)^2 + 8*(n : F) : F) • (Rm (F := F)) + (-4*(n : F)^3 + 14*(n : F)^2 - 8*(n : F) : F) • (Cm (F := F)) + (6*(n : F)^3 - 24*(n : F)^2 + 16*(n : F) : F) • (Em (F := F)) := by algebra_tac

theorem Hk_mul_Mk (hn : 3 ≤ n) : (Hk (F := F)) * (Mk (F := F)) = (2 * ((n : F) - 1) * ((n - 1).factorial : F)) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) F) := by

  have hF2 : ((n - 2).factorial : F) = ((n : F) - 2) * ((n - 3).factorial : F) := by
    obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
    rw [hk, Nat.factorial_succ]
    have e : n - 3 = k := by omega
    rw [e]; push_cast
    have : (n : F) = (k : F) + 3 := by
      have : n = k + 3 := by omega
      rw [this]; push_cast; ring
    rw [this]; ring
  have hF1 : ((n - 1).factorial : F) = ((n : F) - 1) * ((n : F) - 2) * ((n - 3).factorial : F) := by
    obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 2 := ⟨n - 3, by omega⟩
    rw [hk, Nat.factorial_succ, Nat.factorial_succ]
    have e : n - 3 = k := by omega
    rw [e]; push_cast
    have : (n : F) = (k : F) + 3 := by
      have : n = k + 3 := by omega
      rw [this]; push_cast; ring
    rw [this]; ring
  rw [hF1, ← show ((1 : Matrix (Fin n) (Fin n) F) ⊗ₖ (1 : Matrix (Fin n) (Fin n) F))
      = (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) F) from Matrix.one_kronecker_one]
  simp only [Hk, Mk, hF2, add_mul, mul_add, smul_mul_assoc, ← Matrix.mul_kronecker_mul,
    A2_mul_A1, A2_mul_A2, A2_mul_A3, A2_mul_A4, A1_mul_A1, A1_mul_A2, A1_mul_A3, A1_mul_A4,
    B1_mul_D1, B1_mul_D2, B1_mul_D3, B1_mul_D4, B2_mul_D1, B2_mul_D2, B2_mul_D3, B2_mul_D4]

  simp only [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Matrix.zero_kronecker, Matrix.kronecker_zero, smul_add, smul_smul,
    smul_zero, add_zero, zero_add]
  module

end PermanentBound.HessianInverse

end
namespace AlgebraicComplexity.Valiant
noncomputable def permanentPoly (n : ℕ) : MvPolynomial (Fin n × Fin n) F :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent
end AlgebraicComplexity.Valiant

namespace Matrix

def HasDetRep {ι : Type} (m : ℕ) (f : MvPolynomial ι F) : Prop :=
  ∃ L : Matrix (Fin m) (Fin m) (MvPolynomial ι F),
    (∀ i j, (L i j).totalDegree ≤ 1) ∧ L.det = f
end Matrix

/-! ## Affine polynomial-matrix representations -/

namespace PermanentBound.AffineRepresentation
open MvPolynomial Matrix PermanentBound.AffineZeroSpaces PermanentBound.PermanentZeroSpaces
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem support_totalDegree_le_one {p : MvPolynomial ι F} (hp : p.totalDegree ≤ 1)
    {d : ι →₀ ℕ} (hd : d ∈ p.support) : d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  have h1 := (MvPolynomial.le_totalDegree hd).trans hp
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
  by_cases h0 : ∀ i, d i = 0
  · left; ext i; exact h0 i
  · right
    push Not at h0
    obtain ⟨i, hi⟩ := h0
    refine ⟨i, ?_⟩
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset ι) (fun j => d j) (Finset.mem_univ i)
    have hrest : ∑ j ∈ Finset.univ.erase i, d j = 0 := by
      have hpos : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hi
      omega
    have hdi : d i = 1 := by
      have hpos : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hi
      omega
    ext j
    by_cases hji : j = i
    · subst hji; simp [hdi]
    · have : d j = 0 := by
        have := (Finset.sum_eq_zero_iff.mp hrest) j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        exact this
      simp [Finsupp.single_apply, Ne.symm hji, this]

theorem eq_C_add_sum_of_totalDegree_le_one {p : MvPolynomial ι F} (hp : p.totalDegree ≤ 1) :
    p = C (coeff 0 p) + ∑ i, C (coeff (Finsupp.single i 1) p) * X i := by
  ext d
  rw [coeff_add, coeff_C, coeff_sum]
  simp only [coeff_C_mul, coeff_X']
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · by_cases hsing : ∃ i, d = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hsing
      rw [if_neg (Ne.symm hd0), zero_add, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [if_neg, mul_zero]
        intro h
        exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
      · intro h; exact absurd (Finset.mem_univ i) h
    · have hnot : d ∉ p.support := by
        intro hmem
        rcases support_totalDegree_le_one hp hmem with h | h
        · exact hd0 h
        · exact hsing h
      rw [MvPolynomial.notMem_support_iff.mp hnot, if_neg (Ne.symm hd0), zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg, mul_zero]
      intro h; exact hsing ⟨i, h.symm⟩

theorem eval_of_totalDegree_le_one {p : MvPolynomial ι F} (hp : p.totalDegree ≤ 1) (x : ι → F) :
    eval x p = coeff 0 p + ∑ i, coeff (Finsupp.single i 1) p * x i := by
  conv_lhs => rw [eq_C_add_sum_of_totalDegree_le_one hp]
  simp [map_sum]

noncomputable def linPart (L : Matrix (Fin m) (Fin m) (MvPolynomial ι F)) :
    (ι → F) →ₗ[F] Matrix (Fin m) (Fin m) F where
  toFun x := Matrix.of fun i j => ∑ k, coeff (Finsupp.single k 1) (L i j) * x k
  map_add' a b := by
    ext i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext i j
    simp [Finset.mul_sum, mul_left_comm]

noncomputable def affineOf (L : Matrix (Fin m) (Fin m) (MvPolynomial ι F)) : AffineMat F (Fin m) ι where
  A0 := Matrix.of fun i j => coeff 0 (L i j)
  L := linPart L

theorem affineOf_eval (L : Matrix (Fin m) (Fin m) (MvPolynomial ι F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1) (x : ι → F) :
    (affineOf L).eval x = L.map (eval x) := by
  ext i j
  simp only [AffineMat.eval, affineOf, linPart, Matrix.add_apply, Matrix.of_apply, Matrix.map_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [eval_of_totalDegree_le_one (hL i j)]

theorem affineMat_of_hasDetRep {f : MvPolynomial ι F} (h : Matrix.HasDetRep m f) :
    ∃ A : AffineMat F (Fin m) ι, ∀ x, (A.eval x).det = eval x f := by
  obtain ⟨L, hL, hdet⟩ := h
  refine ⟨affineOf L, fun x => ?_⟩
  rw [affineOf_eval L hL, ← hdet, RingHom.map_det]
  rfl

theorem eval_permanentPoly (n : ℕ) (x : Fin n × Fin n → F) :
    eval x (AlgebraicComplexity.Valiant.permanentPoly (F := F) n) = (toMat x).permanent := by
  rw [AlgebraicComplexity.Valiant.permanentPoly]
  exact eval_permPoly x
end PermanentBound.AffineRepresentation

/-! ## The determinantal lower bound -/

namespace PermanentBound.Bound
open scoped Matrix
open MvPolynomial Matrix PermanentBound.AffineZeroSpaces PermanentBound.Hessian PermanentBound.PermanentZeroSpaces PermanentBound.TaylorExpansion PermanentBound.MignonRessayrePoint PermanentBound.RowColumnSpaces PermanentBound.TangentBound PermanentBound.AffineRepresentation PermanentBound.HessianEntries PermanentBound.HessianInverse

theorem mr_shape_perm {K : Type*} [Field K] [Infinite K] {m : Type*} [Fintype m]
    [DecidableEq m] {M : Type*} [Fintype M] [DecidableEq M] (A : AffineMat K M (m × m))
    (hrep : ∀ x : m × m → K, (A.eval x).det = (toMat x).permanent) (p : m × m → K)
    (hp : (toMat p).permanent = 0)
    (hnd : ∀ v, (∀ w, v ⬝ᵥ ((hess (permPoly m K) p).mulVec w) = 0) → v = 0) :
    Fintype.card m * Fintype.card m ≤ 2 * Fintype.card M :=
  mr_of_hessian_nondegenerate_perm A hrep p hp hnd

def MRHessianNondegenerate (n : ℕ) [NeZero n] : Prop :=
  ∀ v : Fin n × Fin n → F,
    (∀ w, v ⬝ᵥ ((hess (permPoly (Fin n) F)
      (fun ij => PermanentBound.MignonRessayrePoint.mrPoint (K := F) n ij.1 ij.2)).mulVec w) = 0)
    → v = 0

theorem permanent_J {K : Type*} [Field K] (n : ℕ) :
    (PermanentBound.MignonRessayrePoint.J (K := K) n).permanent = (n.factorial : K) := by
  unfold Matrix.permanent
  simp [PermanentBound.MignonRessayrePoint.J, Fintype.card_perm]

noncomputable def pMR (n : ℕ) [NeZero n] : Fin n × Fin n → F :=
  fun ij => mrPoint (K := F) n ij.1 ij.2

def TangentSpanned (n : ℕ) [NeZero n] : Prop :=
  ∃ (ιs : Type) (_ : Fintype ιs) (V : ιs → Submodule F (Fin n × Fin n → F)),
    (∀ i, (pMR (F := F)) n ∈ V i ∧ ∀ q ∈ V i, (toMat q).permanent = 0) ∧
      n * n - 1 ≤ Module.finrank F (⨆ i, V i : Submodule F (Fin n × Fin n → F))

def TangentBound (n : ℕ) [NeZero n] : Prop :=
  ∀ {M : Type} [Fintype M] [DecidableEq M] (A : AffineMat F M (Fin n × Fin n)),
    (∀ x, (A.eval x).det = (toMat x).permanent) → 2 * Fintype.card M = n * n →
    (∀ v, (hess (permPoly (Fin n) F) ((pMR (F := F)) n)).mulVec v = 0 → v = 0) →
    ∀ (ιs : Type) [Fintype ιs] (V : ιs → Submodule F (Fin n × Fin n → F)),
      (∀ i, (pMR (F := F)) n ∈ V i ∧ ∀ q ∈ V i, (toMat q).permanent = 0) →
      2 * Module.finrank F (⨆ i, V i : Submodule F (Fin n × Fin n → F)) ≤ n * n + 2 * n

theorem no_half_representation (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h1 : MRHessianNondegenerate (F := F) n) (h2 : TangentSpanned (F := F) n) (h3 : TangentBound (F := F) n)
    {M : Type} [Fintype M] [DecidableEq M] (A : AffineMat F M (Fin n × Fin n))
    (hrep : ∀ x, (A.eval x).det = (toMat x).permanent) :
    2 * Fintype.card M ≠ n * n := by
  intro h2m
  obtain ⟨ιs, _, V, hV, hspan⟩ := h2
  have hnd : ∀ v, (hess (permPoly (Fin n) F) ((pMR (F := F)) n)).mulVec v = 0 → v = 0 := by
    intro v hv
    apply h1 v
    intro w
    have hv' : (hess (permPoly (Fin n) F)
      (fun ij => mrPoint (K := F) n ij.1 ij.2)).mulVec v = 0 := hv
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hess_transpose, hv', zero_dotProduct]
  have hb := h3 A hrep h2m hnd ιs V hV
  have h9 : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
  omega

theorem two_dc_ge_succ (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h1 : MRHessianNondegenerate (F := F) n) (h2 : TangentSpanned (F := F) n) (h3 : TangentBound (F := F) n)
    {M : Type} [Fintype M] [DecidableEq M] (A : AffineMat F M (Fin n × Fin n))
    (hrep : ∀ x, (A.eval x).det = (toMat x).permanent) :
    n * n + 1 ≤ 2 * Fintype.card M := by
  have hp : (toMat ((pMR (F := F)) n)).permanent = 0 := by
    have : toMat ((pMR (F := F)) n) = mrPoint (K := F) n := by ext i j; rfl
    rw [this]; exact permanent_mrPoint
  have hmr := mr_shape_perm A hrep ((pMR (F := F)) n) hp h1
  have hne := no_half_representation n hn h1 h2 h3 A hrep
  simp only [Fintype.card_fin] at hmr
  omega

theorem pMR_ne_zero (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (pMR (F := F)) n ≠ 0 := by
  intro h
  have := congrFun h (⟨1, by omega⟩, 0)
  simp [pMR, mrPoint, PermanentBound.MignonRessayrePoint.J, Matrix.updateRow_apply, Fin.ext_iff] at this

theorem tangentBound (n : ℕ) [NeZero n] (hn : 2 ≤ n) : TangentBound (F := F) n := by
  intro M _ _ A hrep h2m hnd ιs _ V hV
  have hrep' : ∀ x, (A.eval x).det = eval x (permPoly (Fin n) F) := fun x => by
    rw [eval_permPoly]; exact hrep x
  have hV' : ∀ i, (pMR (F := F)) n ∈ V i ∧ ∀ q ∈ V i, eval q (permPoly (Fin n) F) = 0 := fun i =>
    ⟨(hV i).1, fun q hq => by rw [eval_permPoly]; exact (hV i).2 q hq⟩
  have hb := tangent_bound A (permPoly (Fin n) F) permPoly_isHomogeneous hrep'
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega) ((pMR (F := F)) n) (pMR_ne_zero n hn) hnd V hV'
  have hJ : eval (fun ij => PermanentBound.MignonRessayrePoint.J (K := F) n ij.1 ij.2)
      (permPoly (Fin n) F) ≠ 0 := by
    rw [eval_permPoly]
    have : toMat (fun ij => PermanentBound.MignonRessayrePoint.J (K := F) n ij.1 ij.2)
        = PermanentBound.MignonRessayrePoint.J (K := F) n := by ext i j; rfl
    rw [this, permanent_J]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc := finrank_leftKer_le A (permPoly (Fin n) F) permPoly_isHomogeneous hrep' _ hJ
  simp only [Fintype.card_prod, Fintype.card_fin] at hb hc
  omega

theorem two_dc_ge_succ_of_certificates (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h1 : MRHessianNondegenerate (F := F) n) (h2 : TangentSpanned (F := F) n) {m : ℕ}
    (h : Matrix.HasDetRep m (AlgebraicComplexity.Valiant.permanentPoly (F := F) n)) : n * n + 1 ≤ 2 * m := by
  obtain ⟨A, hA⟩ := affineMat_of_hasDetRep h
  have hrep : ∀ x : Fin n × Fin n → F, (A.eval x).det = (toMat x).permanent := fun x => by
    rw [hA, eval_permanentPoly]
  have := two_dc_ge_succ n hn h1 h2 (tangentBound n (by omega)) A hrep
  simpa using this

theorem tangentSpanned_all (n : ℕ) [NeZero n] : TangentSpanned (F := F) n :=
  PermanentBound.TangentSpanning.tangentSpanned_all

theorem two_dc_ge_succ_of_hessian (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h1 : MRHessianNondegenerate (F := F) n) {m : ℕ}
    (h : Matrix.HasDetRep m (AlgebraicComplexity.Valiant.permanentPoly (F := F) n)) : n * n + 1 ≤ 2 * m :=
  two_dc_ge_succ_of_certificates n hn h1 (tangentSpanned_all n) h

noncomputable def invCoeff (n : ℕ) [NeZero n] (a b c d : Fin n) : F :=
  let z : F := (n : F)
  if a ≠ c ∧ a ≠ 0 ∧ c ≠ 0 then
    (if b = d then (if b = 0 then 4 else (z - 2) ^ 2) else (if b = 0 ∨ d = 0 then 2 else 2 - z))
  else if a ≠ c then
    (if b = d then 2 * (2 - z) else 2)
  else if a ≠ 0 then
    (if b = d then (if b = 0 then 4 * (2 - z) else -(z - 2) ^ 3)
     else (if b = 0 ∨ d = 0 then 2 * (2 - z) else (z - 2) ^ 2))
  else
    (if b = d then (if b = 0 then 4 * (z - 1) * (z - 2) else 4 * (2 - z))
     else (if b = 0 ∨ d = 0 then 2 * (2 - z) else 4))

def InverseCertificate (n : ℕ) [NeZero n] : Prop :=
  hess (permPoly (Fin n) F) ((pMR (F := F)) n) * (Matrix.of fun (ab cd : Fin n × Fin n) =>
      (invCoeff (F := F)) n ab.1 ab.2 cd.1 cd.2)
    = (2 * ((n : F) - 1) * ((n - 1).factorial : F)) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) F)

theorem hessian_of_certificate (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (h : InverseCertificate (F := F) n) : MRHessianNondegenerate (F := F) n := by
  intro v hv
  change ∀ w, v ⬝ᵥ ((hess (permPoly (Fin n) F) ((pMR (F := F)) n)).mulVec w) = 0 at hv
  unfold InverseCertificate at h
  have hvec : v ᵥ* hess (permPoly (Fin n) F) ((pMR (F := F)) n) = 0 := by
    ext b
    have := hv (Pi.single b 1)
    rw [Matrix.dotProduct_mulVec] at this
    simpa using this
  have h2 := congrArg (fun u => u ᵥ* (Matrix.of fun (ab cd : Fin n × Fin n) =>
    (invCoeff (F := F)) n ab.1 ab.2 cd.1 cd.2)) hvec
  simp only [Matrix.vecMul_vecMul, h, Matrix.zero_vecMul, Matrix.vecMul_smul,
    Matrix.vecMul_one] at h2
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exfalso
    have h1 : ((n : F) - 1) ≠ 0 := by
      intro h'
      have : (n : F) = 1 := by linear_combination h'
      have : n = 1 := by exact_mod_cast this
      omega
    have h3 : ((n - 1).factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    exact (mul_ne_zero (mul_ne_zero two_ne_zero h1) h3) h0
  · exact h0

theorem certificate (n : ℕ) [NeZero n] (hn : 3 ≤ n) : InverseCertificate (F := F) n := by
  unfold InverseCertificate
  have e : (Matrix.of fun (ab cd : Fin n × Fin n) => (invCoeff (F := F)) n ab.1 ab.2 cd.1 cd.2) = (Mk (F := F)) := by
    rw [Mk_eq]; rfl
  have hH : hess (permPoly (Fin n) F) ((pMR (F := F)) n) = (Hk (F := F)) := hess_eq_Hk
  rw [e, hH]
  exact Hk_mul_Mk hn

theorem hessian_all (n : ℕ) [NeZero n] (hn : 3 ≤ n) : MRHessianNondegenerate (F := F) n :=
  hessian_of_certificate n (by omega) (certificate n hn)

theorem two_dc_ge_succ_unconditional (n : ℕ) (hn : 3 ≤ n) {m : ℕ}
    (h : Matrix.HasDetRep m (AlgebraicComplexity.Valiant.permanentPoly (F := F) n)) : n * n + 1 ≤ 2 * m := by
  haveI : NeZero n := ⟨by omega⟩
  exact two_dc_ge_succ_of_hessian n hn (hessian_all n hn) h
end PermanentBound.Bound

theorem permanent_determinantal_lower_bound (n : ℕ) (hn : 3 ≤ n) {m : ℕ}
    (h : Matrix.HasDetRep m (AlgebraicComplexity.Valiant.permanentPoly (F := F) n)) :
    n * n + 1 ≤ 2 * m := by
  exact PermanentBound.Bound.two_dc_ge_succ_unconditional n hn h



namespace PermanentSmallSizes
open MvPolynomial Matrix
open PermanentBound.Hessian PermanentBound.MignonRessayrePoint
open PermanentBound.PermanentZeroSpaces PermanentBound.PermanentDerivatives
variable {F : Type} [Field F] [CharZero F]

theorem permanent_two_entries (A : Matrix (Fin 2) (Fin 2) F) :
    A.permanent = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Matrix.permanent, huniv, Finset.sum_pair (by decide : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1)]
  simp [Fin.prod_univ_two, Equiv.swap_apply_def]
  ring

theorem hess_perm_two (p : Fin 2 × Fin 2 → F) (x y : Fin 2 × Fin 2) :
    hess (permPoly (Fin 2) F) p x y = if x.1 ≠ y.1 ∧ x.2 ≠ y.2 then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  rw [hess_permPoly_apply]
  fin_cases a <;> fin_cases c <;> fin_cases b <;> fin_cases d <;>
    simp [permanent_two_entries, Matrix.updateRow_apply, toMat]

theorem hess_perm_two_nondegenerate :
    ∀ v : Fin 2 × Fin 2 → F,
      (∀ w, v ⬝ᵥ ((hess (permPoly (Fin 2) F)
        (fun ij => mrPoint (K := F) 2 ij.1 ij.2)).mulVec w) = 0) → v = 0 := by
  intro v hv
  funext ⟨a, b⟩
  have key : ∀ (a b : Fin 2), v (a, b) = 0 := by
    intro a b
    have h := hv (Pi.single (a + 1, b + 1) 1)
    rw [Matrix.dotProduct_mulVec] at h
    simp only [dotProduct_single, mul_one] at h
    simp only [Matrix.vecMul, dotProduct, hess_perm_two] at h
    fin_cases a <;> fin_cases b <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two] at h <;> simpa using h
  exact key a b

theorem no_size_zero_one
    (L : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin 1 × Fin 1) F))
    (hdet : L.det = (Matrix.mvPolynomialX (Fin 1) (Fin 1) F).permanent) : False := by
  have h := congrArg (MvPolynomial.eval (fun _ => (0 : F))) hdet
  simp [Matrix.det_isEmpty, Matrix.permanent, Matrix.mvPolynomialX] at h
end PermanentSmallSizes


/-! ## Homogeneous affine zero spaces and the parity-uniform strengthening -/
namespace PermanentBound.Refinement
open MvPolynomial Matrix
open PermanentBound.AffineZeroSpaces PermanentBound.Hessian PermanentBound.PermanentZeroSpaces PermanentBound.TaylorExpansion
open scoped Matrix
open PermanentBound.TwoSliceDimension PermanentBound.TangentBound
theorem affine_zero_contains_base {K : Type} [Field K] [Infinite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (f : MvPolynomial ι K) (hf : f.IsHomogeneous d) (y : ι → K)
    (hnd : ∀ v, (hess f y).mulVec v = 0 → v = 0)
    (U : Submodule K (ι → K)) (hU : ∀ u ∈ U, eval (y + u) f = 0)
    (hlarge : Fintype.card ι ≤ 2 * Module.finrank K U + 1) : y ∈ U := by
  classical
  let S : Submodule K (ι → K) := (K ∙ y) ⊔ U
  have hUS : U ≤ S := le_sup_right
  have hyS : y ∈ S := (le_span_sup (x := y) (U := U)).2
  have hS : ∀ x ∈ S, eval x f = 0 := vanishes_on_span_sup f hf hU
  have hnd' : ∀ v, (∀ w, dotForm (hess f y) v w = 0) → v = 0 := by
    intro v hv
    apply hnd v
    funext a
    have h := hv (Pi.single a 1)
    rw [dotForm_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hess_transpose] at h
    simpa using h
  have hb := two_mul_finrank_le_of_isotropic
    (dotForm_isRefl (hess f y) (hess_transpose f y)) hnd' (W := S)
    (fun a ha b hb => hess_isotropic_of_vanishes f S hS hyS ha hb)
  rw [Module.finrank_fintype_fun_eq_card] at hb
  have hdim : Module.finrank K U = Module.finrank K S := by
    have := Submodule.finrank_mono hUS
    omega
  have heq : U = S := Submodule.eq_of_le_of_finrank_eq hUS hdim
  rw [heq]
  exact hyS

section
variable {K : Type} [Field K] [Infinite K] {ι : Type} [Fintype ι] [DecidableEq ι]
theorem kernel_of_A0_plus_one {m : Type*} [Fintype m] [DecidableEq m] (A : AffineMat K m ι)
    (f : MvPolynomial ι K) {d : ℕ} (hf : f.IsHomogeneous d)
    (hrep : ∀ x, (A.eval x).det = eval x f) (h2m : 2 * Fintype.card m ≤ Fintype.card ι + 1)
    (y : ι → K) (hnd : ∀ v, (hess f y).mulVec v = 0 → v = 0)
    (w u : m → K) (hw : w ≠ 0) (hu : u ≠ 0) (hwy : Matrix.vecMul w (A.eval y) = 0)
    (huy : (A.eval y).mulVec u = 0) :
    Matrix.vecMul w A.A0 = 0 ∧ A.A0.mulVec u = 0 := by
  have hW : ∀ δ ∈ LinearMap.ker (kmap A w), eval (y + δ) f = 0 := by
    intro δ hδ
    rw [LinearMap.mem_ker, kmap_apply] at hδ
    rw [← hrep]
    apply det_eq_zero_of_vecMul_eq_zero hw
    rw [AffineMat.eval_add_linear, Matrix.vecMul_add, hwy, hδ, add_zero]
  have hU : ∀ δ ∈ LinearMap.ker (rightKmap A u), eval (y + δ) f = 0 := by
    intro δ hδ
    rw [LinearMap.mem_ker, rightKmap_apply] at hδ
    rw [← hrep]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨u, hu, ?_⟩
    rw [AffineMat.eval_add_linear, Matrix.add_mulVec, huy, hδ, add_zero]
  have h1 := card_le_card_add_finrank_ker A w
  have h2 := card_le_card_add_finrank_ker_right A u
  have hyW := affine_zero_contains_base f hf y hnd _ hW (by omega)
  have hyU := affine_zero_contains_base f hf y hnd _ hU (by omega)
  rw [LinearMap.mem_ker, kmap_apply] at hyW
  rw [LinearMap.mem_ker, rightKmap_apply] at hyU
  have hev : A.eval y = A.A0 + A.L y := rfl
  rw [hev, Matrix.vecMul_add, hyW, add_zero] at hwy
  rw [hev, Matrix.add_mulVec, hyU, add_zero] at huy
  exact ⟨hwy, huy⟩

variable {M : Type} [Fintype M] [DecidableEq M]
theorem tangent_bound_plus_one (A : AffineMat K M ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (hrep : ∀ x, (A.eval x).det = eval x f)
    (h2m : 2 * Fintype.card M ≤ Fintype.card ι + 1) (p : ι → K) (hp0 : p ≠ 0)
    (hnd : ∀ v, (hess f p).mulVec v = 0 → v = 0) {ιs : Type*} (V : ιs → Submodule K (ι → K))
    (hV : ∀ i, p ∈ V i ∧ ∀ q ∈ V i, eval q f = 0) :
    2 * Module.finrank K (⨆ i, V i : Submodule K (ι → K))
      ≤ Fintype.card ι + 2 * Module.finrank K (leftKer A) := by
  classical
  by_cases hne : Nonempty ιs
  swap
  · have hbot : (⨆ i, V i : Submodule K (ι → K)) = ⊥ := by
      rw [not_nonempty_iff] at hne
      exact iSup_of_empty V
    rw [hbot, finrank_bot]
    omega
  obtain ⟨i₁⟩ := hne
  have hpf : eval p f = 0 := (hV i₁).2 p (hV i₁).1
  have hgrad : grad f p ≠ 0 := by
    intro h0
    have h := hess_mulVec_self hf p
    rw [h0, smul_zero] at h
    exact hp0 (hnd p h)
  have hdetp : (A.eval p).det = 0 := by rw [hrep, hpf]
  obtain ⟨u, hu, hAu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetp

  have hrow : ∃ i₀, adjRow A p i₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hgz : ∀ δ, δ ⬝ᵥ grad f p = 0 := by
      intro δ
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, u i₀ ≠ 0 := by
        by_contra h
        push_neg at h
        exact hu (funext h)
      have hk := congrArg (fun v => v ⬝ᵥ u) (key_identity A f hrep p i₀ δ)
      simp only [add_dotProduct, hall i₀, Matrix.zero_vecMul, zero_dotProduct, add_zero,
        smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul] at hk
      rw [← Matrix.dotProduct_mulVec, hAu, dotProduct_zero] at hk
      exact (mul_eq_zero.mp hk.symm).resolve_right hi₀
    apply hgrad
    funext j
    have := hgz (Pi.single j 1)
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hrow
  set w := adjRow A p i₀ with hw
  have hwA : w ᵥ* A.eval p = 0 := by rw [hw, adjRow_vecMul, hdetp, zero_smul]
  obtain ⟨hwA0, -⟩ := kernel_of_A0_plus_one A f hf hrep h2m p hnd w u hi₀ hu hwA hAu

  set DW := LinearMap.ker (kmap A w) with hDW
  have hDWzero : ∀ q ∈ DW, eval q f = 0 := by
    intro q hq
    rw [LinearMap.mem_ker, kmap_apply] at hq
    rw [← hrep]
    apply det_eq_zero_of_vecMul_eq_zero hi₀
    show w ᵥ* (A.A0 + A.L q) = 0
    rw [Matrix.vecMul_add, hwA0, hq, add_zero]
  have hpDW : p ∈ DW := by
    rw [LinearMap.mem_ker, kmap_apply]
    have h : w ᵥ* A.eval p = w ᵥ* A.A0 + w ᵥ* A.L p := by
      show w ᵥ* (A.A0 + A.L p) = _
      rw [Matrix.vecMul_add]
    rw [hwA, hwA0, zero_add] at h
    exact h.symm
  have hDWdim : 2 * Module.finrank K DW ≤ Fintype.card ι := by
    have hnd' : ∀ v, (∀ w', dotForm (hess f p) v w' = 0) → v = 0 := by
      intro v hv
      apply hnd v
      funext a
      have h := hv (Pi.single a 1)
      rw [dotForm_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hess_transpose] at h
      simpa using h
    have h := two_mul_finrank_le_of_isotropic (dotForm_isRefl (hess f p) (hess_transpose f p)) hnd'
      (W := DW) (fun a ha b hb => by
        rw [dotForm_apply]
        exact hess_isotropic_of_vanishes f DW hDWzero hpDW ha hb)
    rwa [Module.finrank_fintype_fun_eq_card] at h

  have hT_grad : ∀ x ∈ (⨆ i, V i : Submodule K (ι → K)), x ⬝ᵥ grad f p = 0 := by
    intro x hx
    have hle : (⨆ i, V i : Submodule K (ι → K))
        ≤ LinearMap.ker ((dotForm (1 : Matrix ι ι K)) (grad f p)) := by
      refine iSup_le fun i => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      show grad f p ⬝ᵥ ((1 : Matrix ι ι K) *ᵥ y) = 0
      rw [Matrix.one_mulVec, dotProduct_comm]
      exact grad_orth_of_affine_zero f p (V i)
        (fun δ hδ => (hV i).2 _ ((V i).add_mem (hV i).1 hδ)) hy
    have h := hle hx
    rw [LinearMap.mem_ker] at h
    change grad f p ⬝ᵥ ((1 : Matrix ι ι K) *ᵥ x) = 0 at h
    rwa [Matrix.one_mulVec, dotProduct_comm] at h

  have hΨ_line : ∀ i, ∀ δ ∈ V i, Ψ A p i₀ δ ∈ leftKer A := by
    intro i δ hδ
    rw [mem_leftKer]
    funext b
    let g : MvPolynomial ι K := ∑ a, (polyMat A).adjugate i₀ a * C (A.A0 a b)
    have hg_eval : ∀ y, eval y g = (adjRow A y i₀ ᵥ* A.A0) b := by
      intro y
      simp [g, map_sum, map_mul, eval_C, eval_adjugate_polyMat, Matrix.vecMul, dotProduct]
    have hg_dir : δ ⬝ᵥ grad g p = (Ψ A p i₀ δ ᵥ* A.A0) b := by
      simp only [dotProduct, grad, g, map_sum, pderiv_mul, pderiv_C, mul_zero, add_zero, map_mul,
        eval_C, Ψ_apply, Matrix.vecMul, Matrix.mulVec, jac, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
    have hfin1 : {t : K | eval (t • δ + p) (hessPoly f).det = 0}.Finite :=
      finite_zeros_of_ne_zero _ p δ (by rw [eval_det_hessPoly]; exact det_ne_zero_of_injective _ hnd)
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, adjRow A p i₀ a₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi₀ (funext h)
    have hfin2 : {t : K | eval (t • δ + p) ((polyMat A).adjugate i₀ a₀) = 0}.Finite :=
      finite_zeros_of_ne_zero _ p δ (by rw [eval_adjugate_polyMat]; exact ha₀)
    have hinf : {t : K | eval (t • δ + p) g = 0}.Infinite := by
      have hcompl : ({t : K | eval (t • δ + p) (hessPoly f).det = 0}
          ∪ {t | eval (t • δ + p) ((polyMat A).adjugate i₀ a₀) = 0})ᶜ
          ⊆ {t | eval (t • δ + p) g = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
        obtain ⟨ht1, ht2⟩ := ht
        have hyV : t • δ + p ∈ V i := (V i).add_mem ((V i).smul_mem t hδ) (hV i).1
        have hyf : eval (t • δ + p) f = 0 := (hV i).2 _ hyV
        have hndy : ∀ v, (hess f (t • δ + p)).mulVec v = 0 → v = 0 :=
          injective_of_det_ne_zero _ (by rw [← eval_det_hessPoly]; exact ht1)
        have hwy : adjRow A (t • δ + p) i₀ ≠ 0 := by
          intro h
          apply ht2
          rw [eval_adjugate_polyMat]
          exact congrFun h a₀
        have hdety : (A.eval (t • δ + p)).det = 0 := by rw [hrep, hyf]
        obtain ⟨u', hu', hAu'⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdety
        have hwyA : adjRow A (t • δ + p) i₀ ᵥ* A.eval (t • δ + p) = 0 := by
          rw [adjRow_vecMul, hdety, zero_smul]
        obtain ⟨h0, -⟩ := kernel_of_A0_plus_one A f hf hrep h2m (t • δ + p) hndy _ u' hwy hu' hwyA hAu'
        show eval (t • δ + p) g = 0
        rw [hg_eval, h0]
        rfl
      exact Set.Infinite.mono hcompl ((hfin1.union hfin2).infinite_compl)
    have h := dirDeriv_eq_zero_of_infinite_zeros g p δ hinf
    rw [hg_dir] at h
    exact h

  set T : Submodule K (ι → K) := ⨆ i, V i with hT
  have hΨT : ∀ x ∈ T, Ψ A p i₀ x ∈ leftKer A := by
    intro x hx
    have hle : T ≤ (leftKer A).comap (Ψ A p i₀) :=
      iSup_le fun i y hy => Submodule.mem_comap.mpr (hΨ_line i y hy)
    exact Submodule.mem_comap.mp (hle hx)
  let Ψ' : T →ₗ[K] (M → K) := (Ψ A p i₀).domRestrict T
  have hrange : LinearMap.range Ψ' ≤ leftKer A := by
    rintro _ ⟨x, rfl⟩
    exact hΨT x x.2
  have hker : (LinearMap.ker Ψ').map T.subtype ≤ DW := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : Ψ A p i₀ (x : ι → K) = 0 := hx
    have hk := key_identity A f hrep p i₀ x
    rw [hx', Matrix.zero_vecMul, zero_add, hT_grad x x.2, zero_smul] at hk
    rw [Submodule.subtype_apply, LinearMap.mem_ker, kmap_apply]
    exact hk
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ'
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  omega

end

theorem permanent_determinantal_bound_plus_two {F : Type} [Field F] [CharZero F]
    (n m : ℕ) (hn : 3 ≤ n)
    (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent) :
    n*n + 2 ≤ 2*m := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨A, hA⟩ := PermanentBound.AffineRepresentation.affineMat_of_hasDetRep
    (f := AlgebraicComplexity.Valiant.permanentPoly (F := F) n) ⟨L, hL, hdet⟩
  have hrep : ∀ x, (A.eval x).det = eval x (permPoly (Fin n) F) := by
    intro x
    rw [hA, PermanentBound.AffineRepresentation.eval_permanentPoly, eval_permPoly]
  have hnd : ∀ v, (hess (permPoly (Fin n) F) (PermanentBound.Bound.pMR (F := F) n)).mulVec v = 0 → v = 0 := by
    intro v hv
    apply PermanentBound.Bound.hessian_all n hn v
    intro w
    have hv' : (hess (permPoly (Fin n) F)
      (fun ij => PermanentBound.MignonRessayrePoint.mrPoint (K := F) n ij.1 ij.2)).mulVec v = 0 := hv
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hess_transpose, hv', zero_dotProduct]
  obtain ⟨ιs, _, V, hV, hspan⟩ := PermanentBound.Bound.tangentSpanned_all (F := F) n
  have hV' : ∀ i, PermanentBound.Bound.pMR (F := F) n ∈ V i ∧ ∀ q ∈ V i, eval q (permPoly (Fin n) F) = 0 :=
    fun i => ⟨(hV i).1, fun q hq => by rw [eval_permPoly]; exact (hV i).2 q hq⟩
  by_contra hfail
  have h2m : 2 * Fintype.card (Fin m) ≤ Fintype.card (Fin n × Fin n) + 1 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hb := tangent_bound_plus_one A (permPoly (Fin n) F) permPoly_isHomogeneous hrep h2m
    (PermanentBound.Bound.pMR (F := F) n) (PermanentBound.Bound.pMR_ne_zero n (by omega)) hnd V hV'
  have hJ : eval (fun ij => PermanentBound.MignonRessayrePoint.J (K := F) n ij.1 ij.2)
      (permPoly (Fin n) F) ≠ 0 := by
    rw [eval_permPoly]
    have : toMat (fun ij => PermanentBound.MignonRessayrePoint.J (K := F) n ij.1 ij.2)
        = PermanentBound.MignonRessayrePoint.J (K := F) n := by ext i j; rfl
    rw [this, PermanentBound.Bound.permanent_J]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc := finrank_leftKer_le A (permPoly (Fin n) F) permPoly_isHomogeneous hrep _ hJ
  simp only [Fintype.card_prod, Fintype.card_fin] at hb hc
  have hn2 : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
  omega

end PermanentBound.Refinement

theorem permanent_determinantal_bound_plus_two {F : Type} [Field F] [CharZero F]
    (n m : ℕ) (hn : 3 ≤ n)
    (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent) :
    n*n + 2 ≤ 2*m := by
  exact PermanentBound.Refinement.permanent_determinantal_bound_plus_two n m hn L hL hdet

theorem permanent_determinantal_bound_all_sizes {F : Type} [Field F] [CharZero F]
    (n m : ℕ) (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent) :
    n * n + (if 3 ≤ n then 2 else 0) ≤ 2 * m := by
  by_cases hn : 3 ≤ n
  · rw [if_pos hn]
    exact permanent_determinantal_bound_plus_two n m hn L hL hdet
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl
  · simp
  · have hm : m ≠ 0 := by
      intro hm
      subst m
      exact PermanentSmallSizes.no_size_zero_one L hdet
    norm_num
    omega
  · obtain ⟨A, hA⟩ := PermanentBound.AffineRepresentation.affineMat_of_hasDetRep
      (f := AlgebraicComplexity.Valiant.permanentPoly (F := F) 2) (m := m) ⟨L, hL, hdet⟩
    have hrep : ∀ x : Fin 2 × Fin 2 → F,
        (A.eval x).det = (PermanentBound.PermanentZeroSpaces.toMat x).permanent := by
      intro x
      rw [hA, PermanentBound.AffineRepresentation.eval_permanentPoly]
    have hp : (PermanentBound.PermanentZeroSpaces.toMat
        (fun ij : Fin 2 × Fin 2 => PermanentBound.MignonRessayrePoint.mrPoint (K := F) 2 ij.1 ij.2)).permanent = 0 := by
      change (PermanentBound.MignonRessayrePoint.mrPoint (K := F) 2).permanent = 0
      exact PermanentBound.MignonRessayrePoint.permanent_mrPoint
    have hb := PermanentBound.Bound.mr_shape_perm A hrep _ hp
      PermanentSmallSizes.hess_perm_two_nondegenerate
    simpa using hb

/-- Mignon-Ressayre, Theorem 2, recovered over every characteristic-zero field. -/
theorem mignon_ressayre_theorem_two {F : Type} [Field F] [CharZero F]
    (n m : ℕ) (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent) :
    n * n ≤ 2 * m := by
  have h := permanent_determinantal_bound_all_sizes n m L hL hdet
  omega


/-- Strict integer improvement for every even permanent size at least four. -/
theorem permanent_determinantal_bound_even {F : Type} [Field F] [CharZero F]
    (k m : ℕ) (hk : 2 ≤ k)
    (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin (2*k) × Fin (2*k)) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin (2*k)) (Fin (2*k)) F).permanent) :
    2*k*k + 1 ≤ m := by
  have h := permanent_determinantal_bound_all_sizes (2*k) m L hL hdet
  rw [if_pos (by omega : 3 ≤ 2*k)] at h
  have he : (2*k)*(2*k) = 2*(2*k*k) := by ring
  omega

/-- The rounded integer improvement, uniformly for even and odd sizes. -/
theorem permanent_determinantal_bound_ceiling {F : Type} [Field F] [CharZero F]
    (n m : ℕ) (hn : 3 ≤ n)
    (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin n) (Fin n) F).permanent) :
    (n*n + 1)/2 + 1 ≤ m := by
  have h := permanent_determinantal_bound_plus_two n m hn L hL hdet
  omega

/-- Strict integer improvement for every odd permanent size at least three. -/
theorem permanent_determinantal_bound_odd {F : Type} [Field F] [CharZero F]
    (k m : ℕ) (hk : 1 ≤ k)
    (L : Matrix (Fin m) (Fin m) (MvPolynomial (Fin (2*k+1) × Fin (2*k+1)) F))
    (hL : ∀ i j, (L i j).totalDegree ≤ 1)
    (hdet : L.det = (Matrix.mvPolynomialX (Fin (2*k+1)) (Fin (2*k+1)) F).permanent) :
    2*k*k + 2*k + 2 ≤ m := by
  have h := permanent_determinantal_bound_plus_two (2*k+1) m (by omega) L hL hdet
  have he : (2*k+1)*(2*k+1) = 2*(2*k*k+2*k)+1 := by ring
  omega
