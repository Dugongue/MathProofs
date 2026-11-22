# Curvature of Steinhaus and Gaussian energies

The Hanner argument in the MathProofs portfolio identifies the sign of the Hessian of a Steinhaus moment. The comparison below controls the magnitude of the whole Hessian by the Gaussian Hessian. The resulting equality classification applies to random amplitudes in every complex space that embeds complex-linearly and isometrically in $L^p$.

## 1. Theorems

Let $\xi_i$ be independent and uniform on the complex unit circle. For $x\in\mathbb R_+^n$, write
$$
\Phi_p(x)=\mathbb E\left|\sum_i x_i^{1/p}\xi_i\right|^p,\qquad
\Psi_p(x)=\left(\sum_i x_i^{2/p}\right)^{p/2}.
$$
The second expression is the normalized Gaussian counterpart of the first. For $p\ne2$, let $s_p=\operatorname{sgn}(2-p)$ and define the signed Jensen deficit of a function $F$ by
$$
\Delta_F(X)=s_p\bigl(\mathbb EF(X)-F(\mathbb EX)\bigr)
$$
for any random $X\in\mathbb R_+^n$ with integrable coordinates.

**Theorem 1.** For every $1<p<\infty$, $p\ne2$, there are positive constants $c_p,C_p$ independent of $n$ such that
$$
c_p s_p\nabla^2\Psi_p(x)
\preceq s_p\nabla^2\Phi_p(x)
\preceq C_p s_p\nabla^2\Psi_p(x)\qquad (x_i>0).
$$
Here $\preceq$ denotes the positive semidefinite order. The functions are twice continuously differentiable on that orthant. In particular,
$$
c_p\Delta_{\Psi_p}(X)\le\Delta_{\Phi_p}(X)\le C_p\Delta_{\Psi_p}(X)
$$
on the entire closed orthant. For $1<p<2$ one may take $c_p=(p/2)3^{(p-4)/2}$ and $C_p=4p/(p-1)$. Any valid upper constant grows at least as fast as $1/(p-1)$ as $p\downarrow1$. At $p=1$ the lower deficit bound still holds with $c_1=1/(2\cdot3^{3/2})$, and no finite uniform upper bound holds even when $n=2$. At $p=2$ both energies are the same linear function.

**Theorem 2.** Let $U$ be a complex normed space admitting a complex-linear isometry into $L^{p}$, $1\le p<\infty$. Fix a finite list $u_i\in U$, and set
$$
\Phi_{p,U}(x)=\mathbb E\left\|\sum_i x_i^{1/p}\xi_i u_i\right\|^p,\qquad
\Psi_{p,U}(x)=\frac{\mathbb E\left\|\sum_i x_i^{1/p}\gamma_i u_i\right\|^p}{\mathbb E|\gamma_1|^p},
$$
where the $\gamma_i$ are independent standard circular complex Gaussians, with $\mathbb E|\gamma_i|^2=1$. The deficit comparisons of Theorem 1 hold with the same constants for these intrinsic energies. Suppose $p\ne2$. Discard indices with $u_i=0$ or $\mathbb EX_i=0$. Join $i,j$ if
$$
s_p\left(\|u_i\|^p+\|u_j\|^p-\mathbb E\|\xi_i u_i+\xi_j u_j\|^p\right)>0.
$$
The two deficits vanish simultaneously, exactly when the random variables $X_i/\mathbb EX_i$ agree almost surely within every connected component of this graph. For the list of nonzero vectors, the graph components also give the finest partition of the list whose spans form an internal $\ell_p$ direct sum with the inherited norm.

For scalar functions $f_i\in L^p$, take $X_i=|f_i|^p$ on the underlying probability space. Theorem 1 compares the Hanner deficit to the deficit of the mixed $\ell^{2/p}$ power function. It gives equality exactly when the active $|f_i|^p$ are proportional to a single nonnegative profile. Scalar phases play no role in this criterion. Under Theorem 2, scalar functions multiplied by fixed vector directions can have independent equality profiles precisely across the direct-sum components.

## 2. The curvature identity

Fix $x_i>0$ and $\varepsilon>0$. Put $a_i=x_i^{1/p}$, $A^2=\sum_i a_i^2$, $D=\operatorname{diag}(a_i^{p-1})$, $S=\sum_i a_i\xi_i$, $T=\varepsilon+|S|^2$, and $F_\varepsilon=\mathbb ET^{p/2}$. For a real direction $b$ put $B=\sum_i b_i\xi_i$ and $g=\operatorname{Im}(\bar S B)$. The regularized phase-Hessian formula gives
$$
b^{\mathsf T}D\nabla^2 F_\varepsilon(x)Db
=(2-p)\mathbb E\left[T^{(p-4)/2}\left(g^2+\frac{\varepsilon}{p}|B|^2\right)\right].
\tag{1}
$$
Here is a derivation. Write $u_i=\operatorname{Re}(\bar S\xi_i)$, $v_i=\operatorname{Im}(\bar S\xi_i)$, and $C_{ij}=\operatorname{Re}(\bar\xi_i\xi_j)$. Direct differentiation shows that the rescaled Hessian has $(i,j)$ entry
$$
p^{-1}\mathbb E\bigl[T^{(p-4)/2}(TC_{ij}+(p-2)u_i u_j)\bigr]
+\mathbf1_{i=j}\frac{1-p}{pa_i}\mathbb E[T^{(p-2)/2}u_i].
$$
Writing $\xi_j=e^{i\theta_j}$, integration of $\partial_{\theta_j}(T^{(p-2)/2}v_i)$ yields
$$
\mathbb E[T^{(p-4)/2}(TC_{ij}+(p-2)v_iv_j)]=0\quad(i\ne j),\qquad
\frac1{a_i}\mathbb E[T^{(p-2)/2}u_i]=\mathbb E[T^{(p-2)/2}]+(p-2)\mathbb E[T^{(p-4)/2}v_i^2].
$$
The identities use $\partial_{\theta_j}T=-2a_jv_j$, $\partial_{\theta_j}v_i=-a_jC_{ij}$ for $i\ne j$, and $\partial_{\theta_i}v_i=u_i-a_i$. Use $u_i u_j+v_i v_j=|S|^2 C_{ij}$ to obtain (1). All differentiations are under a smooth bounded regularized integral on compact subsets of the open orthant. [Portfolio Hessian proof](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/CrossBranchResolutions/HANNER.md)

Direct differentiation of the Gaussian energy gives
$$
b^{\mathsf T}D\nabla^2\Psi_p(x)Db
=\frac{2-p}{p}A^{p-4}\bigl(A^2\|b\|_2^2-\langle a,b\rangle^2\bigr).
\tag{2}
$$
Replacing $b$ by $b_0=b-\langle a,b\rangle a/A^2$ leaves $g$ unchanged, and $A^2\|b_0\|_2^2=A^2\|b\|_2^2-\langle a,b\rangle^2$.

## 3. A Fourier estimate and the lower bound

On the $n$-torus,
$$
g=\sum_{i\ne j}c_{ij}\xi_i\bar\xi_j,\qquad c_{ij}=\frac{b_i a_j-a_i b_j}{2i}.
$$
Orthogonality of characters gives
$$
\mathbb Eg^2=\sum_{i\ne j}|c_{ij}|^2=\tfrac12 A^2\|b_0\|_2^2.
\tag{3}
$$
Moreover $\mathbb E(|S|^2g^2)\le3A^2\mathbb Eg^2$. To see this, expand $Sg$ into terms $c_{ij}a_k\xi_i\xi_k\bar\xi_j$. Terms with $k=j$ give coefficients $\sum_{j\ne i}c_{ij}a_j$ at frequency $\xi_i$, whose squared moduli sum to at most $A^2\sum_{i\ne j}|c_{ij}|^2$ by Cauchy–Schwarz. Terms with $k\ne j$ have one negative coordinate in their frequency. That coordinate identifies $j$, and the positive coordinates identify the unordered pair $i,k$ with multiplicity, so at most two terms share a frequency. Their squared coefficients sum to at most $2A^2\sum_{i\ne j}|c_{ij}|^2$. These cases use disjoint frequencies.

If $1\le p\le4$ and $\mathbb Eg^2>0$, Jensen in the probability measure with density $g^2/\mathbb Eg^2$, for the decreasing convex function $t^{(p-4)/2}$, gives
$$
\mathbb E[T^{(p-4)/2}g^2]\ge(\varepsilon+3A^2)^{(p-4)/2}\mathbb Eg^2.
\tag{4}
$$
If $\mathbb Eg^2=0$ the inequality holds directly. For $p>4$ write $B_0=\sum (b_0)_i\xi_i$. Since $g^2\le |S|^2|B_0|^2$, we have
$$
\mathbb E[g^2\mathbf1_{|S|<A/2}]\le\tfrac14 A^2\mathbb E|B_0|^2=\tfrac12\mathbb Eg^2.
$$
On the complementary event $T^{(p-4)/2}\ge(A/2)^{p-4}$. This gives the lower bound $\tfrac12(A/2)^{p-4}\mathbb Eg^2$ for the left side of (4). Equations (1)–(4) therefore yield $c_p=(p/2)3^{(p-4)/2}$ when $1\le p\le4,\ p\ne2$, and $c_p=(p/4)2^{4-p}$ for $p>4$, in the limit $\varepsilon\downarrow0$. At $p=1$, the lower comparison already holds for the Jensen deficits. On any positive closed segment the factor relating (4) to (2) tends uniformly to $c_1$, and $F_\varepsilon$ tends to $\Phi_1$, so integrating the second derivative along the segment shows that $\Phi_1-c_1\Psi_1$ is convex. Continuity extends this to boundary segments.

## 4. A weighted small-denominator estimate and the upper bound

For $0<\alpha<1$, the sharp negative-moment inequality of Rapaport, Tkocz, and Wu gives, for $A>0$,
$$
\mathbb E|S|^{-\alpha}\le K_\alpha A^{-\alpha},\qquad
K_\alpha=\mathbb E|(\xi_1+\xi_2)/\sqrt2|^{-\alpha}\le\frac1{1-\alpha}.
\tag{5}
$$
The last bound follows from $\sin t\ge2t/\pi$ on $[0,\pi/2]$ in the one-angle integral for $K_\alpha$. This also bounds any translated phase sum $S+z$ with the same constant and variance bound $A$. Indeed, circular invariance of $S$ gives the same norm distribution after replacing $z$ by $|z|$ times an independent uniform phase, and the squared coefficient norm of the enlarged sum is at least $A^2$. [Rapaport–Tkocz–Wu, Theorem 1](https://arxiv.org/html/2512.09077v2#S1)

The following weighted version preserves the order $1/(1-\alpha)$:
$$
\mathbb E[|S|^{-\alpha}|B|^2]\le 4K_\alpha A^{-\alpha}\|b\|_2^2.
\tag{6}
$$
If some $a_i^2\ge A^2/2$, split $B=b_i\xi_i+B'$ and apply $|B|^2\le2(|b_i|^2+|B'|^2)$. For the first term use (5). For the second, condition on all phases except $\xi_i$ and use the translated estimate at radius $a_i\ge A/\sqrt2$. If all $a_i^2<A^2/2$, select a set accumulating variance until it first reaches $A^2/4$. Its variance is at most $3A^2/4$. Both it and its complement therefore have coefficient norm at least $A/2$. Write $B=B_1+B_2$ according to this split. In each of the two terms of $2(|B_1|^2+|B_2|^2)$, condition on the phases specifying that term and apply the translated estimate to the other block of $S$. Independence, $\mathbb E|B_j|^2=\sum_{i\in j}b_i^2$, and $2^\alpha\le2$ give (6).

Take $\alpha=2-p$ for $1<p<2$. The unregularized term in (1) satisfies
$$
\mathbb E[|S|^{p-4}g^2]\le \mathbb E[|S|^{p-2}|B_0|^2]
\le \frac{4}{p-1} A^{p-2}\|b_0\|_2^2.
\tag{7}
$$
The term proportional to $\varepsilon$ in (1) tends to zero. Away from $S=0$ this is pointwise, and its absolute value is bounded by $p^{-1}|S|^{p-2}|B|^2$ because $\varepsilon\le T$. The latter is integrable by (6). Conditioning on any nonzero term shows that $S=0$ has probability zero. For clarity, the convergence of Hessians is uniform on compact subsets of the positive orthant. The coefficients $b$ used to test a fixed Hessian direction after rescaling by $D$ stay bounded there. Choose $\alpha'$ with $\alpha<\alpha'<1$. Estimate (5) bounds the integrals of $|S|^{-\alpha'}$ on the compact set since $A$ is bounded below there. The part of each integrand on $|S|<\delta$ is therefore bounded in integral by a constant times $\delta^{\alpha'-\alpha}$. On $|S|\ge\delta$ the integrands converge uniformly. This also proves continuity of the limit by uniform integrability and pointwise continuity outside the null zero set at each fixed $x$. First derivatives converge uniformly by the same reasoning, or by their direct differentiated formula bounded by a constant times $T^{(p-1)/2}$. Integrating the converging derivatives along compact segments identifies the limit Hessian with the classical Hessian of $\Phi_p$.

For $p>2$, the unregularized phase term is dominated by $|S|^{p-2}|B|^2$, and the regularized phase term, including the $\varepsilon$-part, by a constant times $T^{(p-2)/2}|B|^2$. On compact sets these bounds are uniform and the integrands extend continuously to $(\varepsilon,S)=(0,0)$ with value zero. For an integer $m\ge\max(1,p-2)$, orthogonality of characters gives
$$
\mathbb E|S|^{2m}
=\sum_{|\nu|=m}\binom{m}{\nu}^{2}\prod_i a_i^{2\nu_i}
\le m! A^{2m}.
$$
Thus Cauchy–Schwarz and monotonicity of moments give
$$
\mathbb E[|S|^{p-4}g^2]\le \mathbb E[|S|^{p-2}|B_0|^2]
\le\sqrt2(m!)^{(p-2)/(2m)}A^{p-2}\|b_0\|_2^2 .
$$
Use $m=2$ in the integer-moment bound for $B_0$ to get its factor $\sqrt2$. Comparing (7) and its $p>2$ analogue with (2) gives $C_p=4p/(p-1)$ for $1<p<2$, and $C_p=p\sqrt2(m!)^{(p-2)/(2m)}$ for $p>2$. At $p=4$ the limiting weight $T^{(p-4)/2}$ is one, so the entire Hessian is exactly twice that of $\Psi_4$.

The Hessian comparison says the two signed differences $s_p(\Phi_p-c_p\Psi_p)$ and $s_p(C_p\Psi_p-\Phi_p)$ are convex on the positive orthant. They extend continuously and convexly to the closed orthant. The functions are bounded by a multiple of $\sum_i x_i$ for fixed $n,p$, so Jensen applies and proves the deficit comparisons.

## 5. Sharp endpoint behavior

Take two coordinates, $x=(1,1)$, and $b=(1,-1)$. Here $D=I$. With $t$ uniform on $[0,\pi]$, the magnitudes of $S$ and $B$ are $2|\cos t|$ and $2\sin t$, and $\bar S B$ is purely imaginary. The ratio of the quadratic forms of $\nabla^2\Phi_p$ and $\nabla^2\Psi_p$ is
$$
p\,2^{p/2}\mathbb E\bigl[|\cos t|^{p-2}\sin^2 t\bigr].
$$
For $|t-\pi/2|\le1/2$, $|\cos t|\le |t-\pi/2|$ and $\sin^2 t\ge\cos^2(1/2)$. Integration gives a lower bound of order $1/(p-1)$ as $p\downarrow1$. Any two-sided Jensen comparison also implies the Hessian comparison for symmetric two-point laws by taking their separation to zero.

At $p=1$, let $X$ take $(1+h,1-h)$ and $(1-h,1+h)$ with equal probabilities, $0<h<1/4$. Then $\Delta_{\Psi_1}(X)=\sqrt{2+2h^2}-\sqrt2$ is of order $h^2$. The other deficit is
$$
2\,\mathbb E\left[\sqrt{\cos^2 t+h^2\sin^2 t}-|\cos t|\right].
$$
Rationalizing the difference and restricting to $h\le |t-\pi/2|\le1/2$ bounds this deficit below by a positive constant times $h^2\log(1/h)$. For the reverse bound, the difference on $|t-\pi/2|\le h$ is at most $h$. Outside this interval, rationalization and $|\cos t|\ge (2/\pi)|t-\pi/2|$ bound it by a constant times $h^2/|t-\pi/2|$. Hence the logarithmic order is exact.

## 6. Intrinsic energies and the equality graph

Let $T_U:U\to L^p(\Omega,\mu)$ be the isometry and $w_i(\omega)=|T_Uu_i(\omega)|^p$. Fubini and invariance of each phase under complex rotations give
$$
\Phi_{p,U}(x)=\int_\Omega\Phi_p\big((w_i(\omega)x_i)_i\big)\,d\mu(\omega).
$$
The same identity holds for $\Psi$, by the exact Gaussian law with variance $\sum_i |T_Uu_i(\omega)|^2x_i^{2/p}$. In particular the model energy is independent of the choice of isometry. Integrating the scalar deficit comparisons proves the vector ones. Finite sums and the $L^p$ norm bounds ensure all phase, Gaussian and amplitude expectations here are finite.

For the scalar model with positive mean vector, the signed function $s_p\Psi_p$ has a supporting gradient at the mean, with the corresponding supporting linear function touching exactly on its nonnegative ray. In fact (2) has precisely the radial kernel in the positive orthant. Along a segment from the mean to a vector outside its ray, the tangent direction fails to be radial at every interior point before the endpoint, so the signed second derivative is positive there. This proves strictness even for a boundary endpoint, and homogeneity gives equality on the ray. Coordinates with zero means vanish almost surely and may be removed. The difference from the supporting function is nonnegative, so its expectation is zero exactly when the random vector belongs to that ray almost surely. For a single surviving coordinate this criterion holds automatically.

At almost every $\omega$, apply this argument to $X_i w_i(\omega)$ after dropping the coordinates with $w_i(\omega)=0$. Its zero-deficit condition says $X_i/\mathbb EX_i$ coincide almost surely for all coordinates active at $\omega$. For each pair $i,j$ whose supports overlap with positive measure, Fubini then requires this equality almost surely. Conversely, for every pair with no positive-measure overlap, the two coordinates are never both active outside a single null set, because there are only finitely many pairs. If the equality criterion holds on graph components, almost every $\omega$ sees only compatible profiles and its scalar deficit is zero.

It remains to connect this overlap graph to the intrinsic expression. For $a,b>0$, $\mathbb E|a\xi_1+b\xi_2|^p\le(a^2+b^2)^{p/2}<a^p+b^p$ for $p<2$, and both inequalities reverse for $p>2$. The first comparison is Jensen applied to the squared magnitude, whose expectation is $a^2+b^2$. If $a=0$ or $b=0$ the corresponding difference is zero. Integrating gives the asserted intrinsic graph. Distinct components have disjoint representing supports up to null sets, so the norms of sums split as the sum of $p$-th powers of the component norms. The supports also make this sum direct. Any internal $\ell_p$ direct sum partition of the list forces the intrinsic expression to vanish across its parts, so it cannot separate any edge and must coarsen the connected components.

## 7. Research scope

Jenkins and Tkocz use the sign of the scalar Hessian to obtain Hanner inequalities. The portfolio's angular calculation supplies the exact curvature formula used here. Known sphere Khinchin deficits quantify a comparison of the moment with a Gaussian moment or with the balanced coefficient vector. The estimates above compare the full Hessians everywhere and hence all Jensen deficits, with an endpoint order and an equality graph. The weighted negative-moment bound uses the sharp unweighted theorem of Rapaport, Tkocz, and Wu. The proofs here are written, and publication priority for the new comparisons remains provisional. [Jenkins–Tkocz, §§2–3](https://arxiv.org/html/2207.09122v2) · [Jakimiuk–Tang–Tkocz, sphere Khinchin deficits](https://doi.org/10.1007/s00209-026-04016-5)

This suggests studying Gaussian comparison of randomized moment curvatures for other rotation laws and other normed spaces. Two concrete problems are to determine the optimal comparison constants already for circle phases, and to characterize the complex normed spaces for which phase and Gaussian Jensen deficits are uniformly equivalent for every list of vectors.

## 8. Exact spherical curvature and the higher-dimensional endpoint

Let $d\ge2$ and $U_i$ be independent and uniform on the unit sphere of $\mathbb R^d$. Fix $p>0$, $x_i>0$, and set $a_i=x_i^{1/p}$, $D=\operatorname{diag}(a_i^{p-1})$, $S=\sum a_iU_i$, $B=\sum b_iU_i$, and $T=\varepsilon+|S|^2$. Write $F_{\varepsilon,d}=\mathbb ET^{p/2}$ and $\Phi_{p,d}=\mathbb E|S|^p$. Then the exact identity is
$$
b^{\mathsf T}D\nabla^2F_{\varepsilon,d}Db
=(2-p)\mathbb E\!\left[T^{(p-4)/2}
\left(\frac{d+p-2}{p(d-1)}|S\wedge B|^2+\frac{\varepsilon}{p}|B|^2\right)\right],
\tag{8}
$$
where $|v\wedge w|^2=|v|^2|w|^2-\langle v,w\rangle^2$. In particular $\Phi_{p,d}$ is convex on the closed nonnegative orthant for $0<p<2$, linear at $p=2$, and concave for $p>2$.

To prove (8), for each unordered coordinate pair choose the skew matrix $J$ generating rotation in that coordinate plane. Its sign can be chosen either way. Write $L_{j,J}$ for differentiation under the rotation $U_j\mapsto e^{tJ}U_j$. The integral of $L_{j,J}$ of a smooth function vanishes by rotation invariance. Put $v_i^J=\langle S,JU_i\rangle$, $u_i=\langle S,U_i\rangle$, $C_{ij}=\langle U_i,U_j\rangle$, and $w=T^{(p-4)/2}$. We have $L_{j,J}T=2a_jv_j^J$. For $i\ne j$, $L_{j,J}v_i^J=a_j\langle JU_j,JU_i\rangle$. For $i=j$, the derivative is $a_i|JU_i|^2+\langle S,J^2U_i\rangle$. Each coordinate belongs to $d-1$ planes, giving $\sum_JJ^2=-(d-1)I$ and $\sum_J\langle JU_j,JU_i\rangle=(d-1)C_{ij}$. The coordinate formula for the wedge product gives
$$
W_{ij}:=\sum_Jv_i^Jv_j^J=|S|^2C_{ij}-u_i u_j.
$$
Integrating $L_{j,J}(T^{(p-2)/2}v_i^J)$, summing over $J$, and dividing by $a_j$ yields
$$
\mathbb E[w((d-1)TC_{ij}+(p-2)W_{ij})]=0\quad(i\ne j).
$$
For $i=j$ the same calculation gives
$$
a_i^{-1}\mathbb E[T^{(p-2)/2}u_i]
=\mathbb E[T^{(p-2)/2}]+\frac{p-2}{d-1}\mathbb E[wW_{ii}].
$$
The direct differentiation formula from Section 2 uses only the scalar inner-product identities defining $C,u_i$, so it is valid here. For $i\ne j$, its summand $TC_{ij}+(p-2)u_iu_j$ becomes $(p-1)TC_{ij}-(p-2)W_{ij}-(p-2)\varepsilon C_{ij}$. Use the off-diagonal integral to replace the first term. On the diagonal, after substituting the diagonal integral, the coefficients of $W_{ii}$ and of $\varepsilon C_{ii}$ are the same as the off-diagonal coefficients. Contracting against $b$ and using $\sum_{ij}b_i b_j W_{ij}=|S\wedge B|^2$ proves (8). The sphere is compact, so regularized differentiation is under a bounded smooth integrand, and $\varepsilon\downarrow0$ preserves the inequalities for convexity and concavity. Continuity covers zero coordinates. The earlier qualitative result for $p\ge1$ in dimensions $d\ge3$ is Jenkins and Tkocz's Theorem 1. [Jenkins–Tkocz](https://arxiv.org/html/2207.09122v2#S1)

**Higher-dimensional endpoint theorem.** For all $d\ge3$ and $1\le p<2$, $\Phi_{p,d}$ is twice continuously differentiable on the positive orthant and
$$
\frac23\,5^{-3/2}\nabla^2\Psi_p
\preceq \nabla^2\Phi_{p,d}
\preceq 6\sqrt2\,\nabla^2\Psi_p .
\tag{9}
$$
These absolute constants compare the Jensen deficits on the closed orthant as well. Thus the singularity witnessed at $p=1$ for circle phases disappears in all sphere dimensions $d\ge3$.

For the lower bound, again replace $b$ by $b_0$ orthogonal to the coefficient vector $a$, which leaves $S\wedge B$ unchanged. Write $G=S\wedge B$ and $A=\|a\|_2$. The expansion in pairs and the invariance under independent changes of signs give
$$
\mathbb E|G|^2=(1-1/d)A^2\|b_0\|_2^2.
$$
In detail, only matching pairs survive, each with mean $\mathbb E|U_i\wedge U_j|^2=1-1/d$ by the covariance $I/d$ of a uniform unit vector. The pair coefficients are $a_i b_j-a_j b_i$, whose squared sum is $A^2\|b_0\|_2^2$. To bound $\mathbb E(|S|^2|G|^2)$, introduce independent signs multiplying the fixed vectors $U_i$, and expand the tensor $S\otimes G$ in the orthogonal basis of sign characters. Conditional on $U_i$, let $G_{ij}$ be the wedge coefficient vector for pair $i<j$. Terms with three distinct indices have at most three representations at each frequency and have total squared coefficients at most $3A^2\sum_{i<j}|G_{ij}|^2$. At each single-index frequency $i$, the squared coefficient is at most $A^2\sum_{j\ne i}|G_{\min(i,j),\max(i,j)}|^2$ by Cauchy–Schwarz. Together these give $\mathbb E(|S|^2|G|^2)\le5 A^2\mathbb E|G|^2$, since the marginal distribution of signed $U_i$ is unchanged. Apply weighted Jensen as in (4). Comparing with (2) yields a lower constant $(d+p-2)5^{(p-4)/2}/d$, which is at least the one in (9).

For the upper bound, a spherical negative-moment estimate uniform in $d\ge3$ is
$$
\mathbb E\left|\sum_i a_iU_i\right|^{-1}\le\frac{\sqrt2}{A}.
\tag{10}
$$
In $d=3$, this is Ball's cube-slicing inequality in its spherical form, as stated by Chasapis, König, and Tkocz in equation (2). For $d>3$, project to three fixed coordinates. A projected independent spherical vector has the form $R_iV_i$, with $V_i$ uniform on the unit sphere of $\mathbb R^3$ and independent of radius $R_i$. Rotation invariance of $S$ gives $\mathbb E|PS|^{-1}=\mathbb E R_1^{-1}\mathbb E|S|^{-1}$ for that projection $P$. The factor $\mathbb E R_1^{-1}$ is finite and positive. For example, represent a uniform unit vector by normalizing a standard Gaussian and condition on its first three coordinates, whose inverse Euclidean radius has finite mean. Applying the dimension-three bound conditionally gives the upper bound $\sqrt2\,\mathbb E(\sum a_i^2R_i^2)^{-1/2}$ for the projected negative moment. Convex Jensen with weights $a_i^2/A^2$ bounds this by $(\sqrt2/A)\mathbb E R_1^{-1}$, so cancellation proves (10). [Chasapis–König–Tkocz, equation (2)](https://arxiv.org/html/2011.12251)

For $0<\alpha\le1$, Jensen gives $K_\alpha\le\sqrt2$ for the analogue of (5) from (10). Translating by a fixed vector can again be replaced by adding an independent uniform sphere increment of the same norm. The proof of (6) applies unchanged to Euclidean vector sums, since it only uses the squared norm triangle bound, independent sums with zero mean, and the translated negative-moment estimate. Therefore
$$
\mathbb E[|S|^{p-4}|G|^2]\le
\mathbb E[|S|^{p-2}|\textstyle\sum_i (b_0)_i U_i|^2]
\le4\sqrt2 A^{p-2}\|b_0\|_2^2.
$$
The final factor in (8) relative to the Gaussian Hessian is at most $(d+p-2)/(d-1)\le3/2$, giving the upper constant in (9).

To justify limiting differentiation at $p=1$ as well, for fixed $d\ge3$ and $1<\alpha'<2$ there is a uniform bound $\sup_z\mathbb E|U+z|^{-\alpha'}<\infty$. For $|z|<1/2$ or $|z|>2$, use $|U+z|\ge1/2$. Otherwise put $t=\langle U,z/|z|\rangle$, which has bounded density proportional to $(1-t^2)^{(d-3)/2}$ on $[-1,1]$. Then $|U+z|^2=(1-|z|)^2+2|z|(1+t)\ge1+t$, and $(1+t)^{-\alpha'/2}$ is integrable. Conditioning on one summand whose coefficient is bounded below on a positive compact set now bounds the $\alpha'$-negative moments uniformly there. The compact convergence argument of Section 4 applies to (8), including the vanishing $\varepsilon$ term. Finally (9) passes to Jensen deficits by convexity on the positive orthant and continuity. The Gaussian model again has a strictly radial Hessian kernel, so equality holds only for a common amplitude profile on the active indices.
