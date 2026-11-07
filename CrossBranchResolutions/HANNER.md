# The missing complex Hanner inequality from a positive Hessian formula

Status: complete informal proof, independently checked by four workers; not Lean verified or externally peer reviewed. The theorem answers the Steinhaus missing-range question stated in Section 3.2 of Jenkins and Tkocz, *Complex Hanner's inequality for many functions*. Publication priority has not been established.

## 1. The theorem

Let n be a positive integer, let 1 ≤ p ≤ 2, and let ξ₁,…,ξₙ be independent random variables uniformly distributed on the complex unit circle. For arbitrary complex-valued functions f₁,…,fₙ in Lᵖ([0,1]),

\[
\mathbb E\int_0^1\left|\sum_{i=1}^n \xi_i f_i(s)\right|^p\,ds
\ \geq\
\mathbb E\left|\sum_{i=1}^n \xi_i\|f_i\|_p\right|^p.
\tag{1}
\]

There is no restriction on n or on the relative sizes or supports of the functions. The direction is reversed when p ≥ 2. At p = 2 both sides equal the sum of the squared norms.

The source paper proves the p ≥ 2 Steinhaus direction and explicitly leaves the reverse direction for 1 < p < 2 open. Its Lemma 2 reduces the problem to convexity of a phase-averaged moment. Our proof establishes that convexity through a positive-semidefinite matrix identity, including every off-diagonal contribution together.

Primary source: Jonathan Jenkins and Tomasz Tkocz, [arXiv:2207.09122v2](https://arxiv.org/html/2207.09122v2), Lemma 2 and Section 3.2; [author-hosted PDF](https://www.math.cmu.edu/~ttkocz/mypapers/mathematics/complex-hanner.pdf).

## 2. A regularized moment

For p > 0, ε > 0 and x ∈ (0,∞)ⁿ, put

\[
a_i=x_i^{1/p},\qquad S=\sum_i a_i\xi_i,\qquad
T=\varepsilon+|S|^2,\qquad
F_{p,\varepsilon}(x)=\mathbb E T^{p/2}.
\]

Define real random variables and a real symmetric matrix by

\[
u_i=\operatorname{Re}(\overline S\xi_i),\qquad
v_i=\operatorname{Im}(\overline S\xi_i),\qquad
C_{ij}=\operatorname{Re}(\overline{\xi_i}\xi_j).
\]

Let

\[
w=T^{(p-4)/2},\qquad D=\operatorname{diag}(a_i^{p-1}),\qquad
K=D(\nabla^2F_{p,\varepsilon})D.
\]

All differentiation under the expectation is valid: on every compact subset of the positive orthant, the phase torus is compact, T ≥ ε, and the integrand and its relevant derivatives are continuous and uniformly bounded.

We will prove the exact identity

\[
\boxed{\quad
K=(2-p)\,\mathbb E\left[w\left(vv^{\mathsf T}+\frac{\varepsilon}{p}C\right)\right].
\quad}\tag{2}
\]

Both matrices inside the expectation are positive semidefinite. In particular, for any real vector b,

\[
b^{\mathsf T}Cb=\left|\sum_i b_i\xi_i\right|^2\geq 0.
\tag{3}
\]

Thus (2) proves convexity for 0 < p ≤ 2 and concavity for p ≥ 2.

## 3. Direct differentiation

Write ξ_i = exp(iθ_i), with independent uniform θ_i on [0,2π]. The elementary identities needed below are

\[
\partial_{a_j}T=2u_j,\qquad
\partial_{a_j}u_i=C_{ij},\qquad
u_i u_j+v_i v_j=|S|^2 C_{ij}.
\tag{4}
\]

Since ∂a_i/∂x_i = a_i^{1-p}/p,

\[
\partial_{x_i}F_{p,\varepsilon}
=a_i^{1-p}\,\mathbb E[T^{(p-2)/2}u_i].
\tag{5}
\]

For i ≠ j, this gives

\[
K_{ij}=\frac1p\mathbb E\big[w\{T C_{ij}+(p-2)u_i u_j\}\big]
=\frac1p\mathbb E\big[w\{(p-1)u_i u_j+v_i v_j+\varepsilon C_{ij}\}\big].
\tag{6}
\]

For the diagonal, differentiating the prefactor in (5) additionally gives

\[
K_{ii}=\frac1p\mathbb E[w\{T+(p-2)u_i^2\}]
+\frac{1-p}{p a_i}\mathbb E[T^{(p-2)/2}u_i].
\tag{7}
\]

## 4. Angular integration by parts

The relevant angular derivatives are

\[
\partial_{\theta_j}T=-2a_jv_j,\qquad
\partial_{\theta_j}v_i=-a_j C_{ij}\quad(i\ne j),\qquad
\partial_{\theta_i}v_i=u_i-a_i.
\tag{8}
\]

The integral of the derivative of a smooth periodic function is zero. Apply this to T^((p−2)/2)v_i, differentiating with respect to θ_j for i ≠ j. After dividing by −a_j,

\[
0=\mathbb E\big[w\{(p-2)v_i v_j+T C_{ij}\}\big]
=\mathbb E\big[w\{u_i u_j+(p-1)v_i v_j+\varepsilon C_{ij}\}\big].
\tag{9}
\]

Substituting (9) into (6) yields

\[
K_{ij}=(2-p)\mathbb E\big[w\{v_i v_j+(\varepsilon/p)C_{ij}\}\big]
\qquad(i\ne j).
\tag{10}
\]

For the diagonal, differentiate the same periodic function with respect to θ_i instead. Equation (8) gives

\[
\frac1{a_i}\mathbb E[T^{(p-2)/2}u_i]
=\mathbb E[T^{(p-2)/2}]+(p-2)\mathbb E[w v_i^2].
\tag{11}
\]

Insert this in (7) and use T = ε + u_i² + v_i². The result is

\[
K_{ii}=(2-p)\mathbb E[w\{v_i^2+\varepsilon/p\}].
\tag{12}
\]

Since C_ii = 1, equations (10) and (12) prove (2). No assumption is made that individual off-diagonal terms have a particular sign.

## 5. Removing regularization and zero-coordinate restrictions

The diagonal matrix D is invertible on the positive orthant, so congruence by D preserves positive or negative semidefiniteness. Equations (2)–(3) therefore imply the stated convexity or concavity of F_(p,ε).

As ε decreases to zero,

\[
F_{p,\varepsilon}(x)\longrightarrow
\Phi_p(x):=\mathbb E\left|\sum_i x_i^{1/p}\xi_i\right|^p.
\tag{13}
\]

For fixed x the convergence follows from continuity and a bounded integrand on the compact torus. Passing to the limit in the defining two-point convexity inequality proves that Φ_p is convex for 0 < p ≤ 2. The identical argument proves concavity for p ≥ 2. Continuity of Φ_p extends these conclusions to the entire closed orthant [0,∞)ⁿ, by adding δ to every coordinate and then letting δ decrease to zero.

The proof never differentiates a singular integrand at S = 0. In particular, configurations with canceling coefficients are included.

## 6. Returning to functions

Fix 1 ≤ p ≤ 2 and let x_i(s)=|f_i(s)|^p. Independent uniform phases absorb the arguments of the complex numbers f_i(s), including arbitrary phase choices when f_i(s)=0. Hence

\[
\mathbb E\left|\sum_i\xi_i f_i(s)\right|^p=\Phi_p(x(s)).
\]

The bound Φ_p(x) ≤ n^(p−1) Σ_i x_i ensures integrability. Jensen's inequality for the continuous convex function Φ_p now gives

\[
\int_0^1\Phi_p(x(s))\,ds
\geq\Phi_p\left(\int_0^1x(s)\,ds\right)
=\mathbb E\left|\sum_i\xi_i\|f_i\|_p\right|^p.
\]

This is (1). The proof includes p = 1 directly; it does not assume that an arbitrary L¹ function belongs to any Lᵖ space with p > 1. For p ≥ 2, use concave Jensen instead. All exchanges with the phase expectation also follow from Tonelli and the displayed integrability bound.

## 7. Scope, novelty and verification

This proves the full finite-family Steinhaus inequality in the missing range, rather than a bounded-n case or a result with supplied structural data. It does not prove the corresponding Rademacher problem or a noncommutative Schatten-norm inequality.

The source paper supplies the problem and the standard convexity/Jensen reduction. The calculation in Sections 2–4 is the proposed additional proof. The regularizer supplies the εC/p term in (2), which is itself positive semidefinite; discarding that term before differentiation would invalidate the regularized identity.

Independent symbolic checks reproduced both off-diagonal and diagonal calculations and verified the match to the stated problem. Companion numerical checks are diagnostics only, not a proof of the universal identity. No Lean certificate is supplied. Searches have not established priority for the formula or for resolving the missing range; this document claims the displayed mathematical argument, not verified first publication.
