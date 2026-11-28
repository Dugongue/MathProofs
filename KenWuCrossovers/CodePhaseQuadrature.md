# Sharp negative exchangeable phase coefficients at every order

Let \(m\ge2\) be fixed. For \(N\ge2m\), let \(\mathcal E_{m,N}\) be the exchangeable probability laws on \(\mathbb T^N\) with \((2m-1)\)-coordinate marginals equal to product Haar. Set

\[
a_m(Z)=\mathbb E[Z_1\cdots Z_m\overline Z_{m+1}\cdots\overline Z_{2m}].
\]

**Theorem.** For every fixed \(m\ge2\),
\[
\lim_{N\to\infty}N^m\min_{Z\in\mathcal E_{m,N}}a_m(Z)
=-\lfloor m/2\rfloor!\,\lceil m/2\rceil!.
\]
The same limit holds when the infimum is over smooth, strictly positive densities with these exact marginals. This proves the higher-order sharpness conjecture in [Finite extendibility and hidden phase moments](https://github.com/Dugongue/MathProofs/blob/main/GeometryOfPartiallyObservedLaws/Extensions.md#5-conjectures-and-tests). The proof uses exact root-of-unity histogram constraints, as in the symbol-count and correlation checks of [Ken Wu's ternary Legendre pair](https://kenwu-lab.wooqianghao.workers.dev/papers/ternary-legendre-pair-35/). The construction works at every sufficiently large \(N\), with no restriction to special lengths.

## The scalar bound

Write \(r=\lfloor m/2\rfloor\) and \(\delta=m-2r\). For \(Y_N=|\sum_i Z_i|^2/N\), let \(\nu_N\) be its law under independent Haar phases. By ordered expansion, all moments through degree \(m-1\) agree with \(\nu_N\) and

\[
\mathbb E Y_N^m-\int y^m\,d\nu_N(y)=\frac{(N)_{2m}}{N^m}a_m(Z).
\tag{1}
\]

Indeed any potentially different term must use \(2m\) distinct indices. Here \((N)_j=N(N-1)\cdots(N-j+1)\). The independent moments of each fixed degree \(j\) tend to \(j!\). The terms with \(j\) distinct positive indices contribute \(j!(N)_j/N^j\) and all other terms contribute \(O_j(N^{-1})\).

Let \(P\) be the monic polynomial of degree \(r\) orthogonal to degrees below \(r\) for \(y^\delta e^{-y}\,dy\) on \([0,\infty)\). The monic nonnegative polynomial \(D(y)=y^\delta P(y)^2\) has degree \(m\). By (1),

\[
\frac{(N)_{2m}}{N^m}a_m(Z)
\ge-\int D(y)\,d\nu_N(y)
\ \longrightarrow\ -r!(r+\delta)! .
\]

For the integral, the monic Rodrigues formula
\[
P(y)=(-1)^r y^{-\delta}e^y\frac{d^r}{dy^r}\big(y^{r+\delta}e^{-y}\big)
\]
verifies orthogonality by \(r\) integrations by parts. Applying those integrations against \(P\) itself gives \(r!\int_0^\infty y^{r+\delta}e^{-y}\,dy=r!(r+\delta)!\).

There is a nonnegative random variable \(Y_*\) supported on the zeros of \(D\) and matching the first \(m-1\) exponential moments. The orthogonal polynomial has \(r\) distinct positive roots. Otherwise the product over its sign-changing roots in \((0,\infty)\) has degree below \(r\) and its product with \(P\) has fixed nonzero sign, contradicting orthogonality. Use the \(r\) roots and, for \(\delta=1\), the node \(0\). Assign each node the integral of its Lagrange cardinal polynomial against \(e^{-y}\,dy\). Division by \(y^\delta P(y)\) shows exactness for degrees through \(m-1\), since the quotient has degree at most \(r-1\) and integrates to zero after multiplication by the divisor. Applying exactness to the squares of the cardinal polynomials proves positivity of the weights. In particular

\[
\mathbb E Y_*^m=m!-r!(r+\delta)! .
\tag{2}
\]

## A finite empirical moment realization lemma

Fix \(q\ge3\), let \(\lambda=(1/q,\dots,1/q)\) and let \(E=\{x\in\mathbb R^q\mid\sum_jx_j=0\}\). Put

\[
\Gamma_N=\{(c-N\lambda)/\sqrt N:c\in\mathbb N^q,\ \textstyle\sum_j c_j=N\}\subset E.
\]

Let \(G\) be the Gaussian on \(E\) with covariance \(q^{-1}I_E\). Suppose a law \(\mu\) on \(E\) has finite moments through degree \(h+1\) and agrees with \(G\) on all polynomials through degree \(h\), where \(h\ge1\). There exist laws \(\mu_N\) supported on \(\Gamma_N\) with the following two properties:

1. Their degree-\(h\) polynomial moments agree **exactly** with the centered, scaled histogram of \(N\) independent uniform \(q\)-ary draws.
2. Their moments through degree \(h+1\) converge to the corresponding moments of \(\mu\).

To prove this, fix linear coordinates on \(E\), write \(F(x)\) for the vector of all monomials of degrees 1 through \(h\), and put \(b=\mathbb E F(G)\). For every nonzero real direction \(u\) in this vector space, the polynomial \(u\cdot(F-b)\) is nonzero, has Gaussian mean zero, and takes both signs because \(G\) has full support. By compactness of the unit sphere of directions, there are finitely many points \(x_\ell\in E\) and \(a>0\) with
\[
\max_\ell u\cdot(F(x_\ell)-b)\ge a
\quad\text{for every unit }u.
\]
For instance choose one positive witness per direction, take a finite subcover of the corresponding open neighborhoods of directions, and take the positive minimum of the resulting maximum function. Hence the convex hull of the vectors \(F(x_\ell)\) contains the closed radius-\(a\) ball about \(b\), by finite-dimensional hyperplane separation. All these points admit approximations \(x_{\ell,N}\in\Gamma_N\) with error \(O_q(N^{-1/2})\). Round the counts \(N/q+\sqrt N x_j\) to integers totaling \(N\), with bounded errors, and observe that the counts are positive for large \(N\). Their moment-vector convex hull therefore contains the radius-\(a/2\) ball for large \(N\).

For a preliminary law \(\widetilde\mu_N\) round samples of \(\mu\) to that same grid inside the radius-\(N^{1/4}\) ball. Send the discarded tail to a grid point tending to zero. Within the ball positivity of the approximated counts holds uniformly for large \(N\). The rounded variables tend pointwise to the original sample and are bounded in norm by \(|x|+O_q(1)\). Dominated convergence gives convergence of their moments through degree \(h+1\). Let \(\widetilde b_N=\int F\,d\widetilde\mu_N\). The target moments \(b_N\) of the independent scaled histogram converge to \(b\). This follows by expanding moments of the sum of independent centered bounded vectors divided by \(\sqrt N\). Any term using a summation index once vanishes. The surviving terms of leading order pair the indices, and each pair contributes the common covariance; the pair expansions are the Gaussian moments. Terms with fewer distinct indices tend to zero.

Put \(e_N=|b_N-\widetilde b_N|\to0\). When \(e_N>0\), choose \(\varepsilon_N=\sqrt{e_N}\) for all sufficiently large \(N\). Then
\[
b_N'=\widetilde b_N+(b_N-\widetilde b_N)/\varepsilon_N\longrightarrow b
\]
lies in the buffer convex hull. Choose a probability law \(\eta_N\) on the rounded buffer points with this moment vector. The mixture
\[
\mu_N=(1-\varepsilon_N)\widetilde\mu_N+\varepsilon_N\eta_N
\]
has the exact target vector \(b_N\). Its degree-\((h+1)\) moments converge because the buffer stays bounded and its mixture weight vanishes. If \(e_N=0\), use the preliminary law. This proves both properties.

## Constructing exchangeable phase laws

Fix any integer \(q>m\), \(q\ge3\), and put \(\omega=\exp(2\pi i/q)\). The two vectors \(v=(\operatorname{Re}\omega^j)_j\) and \(w=(\operatorname{Im}\omega^j)_j\) are orthogonal in \(E\), have equal squared norm \(q/2\), and are orthogonal to \(\mathbf1\). Consequently the first Fourier coordinate \(L(G)=v\cdot G+i\,w\cdot G\) is a standard circular Gaussian, with real and imaginary variances \(1/2\). Its squared radius is exponential of mean one, and its orthogonal complement in \(E\) is independent of it. To define \(\mu\), replace that first Fourier coordinate by \(\sqrt{Y_*}e^{i\Theta}\) for an independent uniform angle \(\Theta\) and keep the orthogonal Gaussian components independent. Integration of the angular harmonics shows equality with the original complex Gaussian on every polynomial in the two components through degree \(2m-1\): a moment \(z^a\overline z^b\) vanishes when \(a\ne b\), and otherwise it uses a squared-radius moment of degree at most \(m-1\). The independent other components therefore give agreement on all polynomials on \(E\) of degree at most \(2m-1\).

Apply the histogram realization lemma with \(h=2m-1\). Draw counts \(c\) associated to the resulting grid variable, then place \(c_j\) copies of \(\omega^j\) uniformly in the \(N\) coordinates. This law is exchangeable. A specified ordered tuple of \(a\le2m-1\) symbols with multiplicities \(d_j\) has conditional probability \(\prod_j(c_j)_{d_j}/(N)_a\). Its numerator is a polynomial of degree \(a\) in the scaled grid coordinates. The exact moment identities give its independent uniform value \(q^{-a}\) after averaging. Thus every one of the required finite-alphabet marginals is independent, exactly. Moreover

\[
N^{-1/2}\sum_i Z_i=L((c-N\lambda)/\sqrt N)
\]
so the degree-\(m\) energy moment converges to (2). The independent finite-alphabet phase energy moments through degree \(m\) have exactly the same values as those under independent Haar: all charges in the expansion lie between \(-m\) and \(m\), and \(q>m\). Hence (1) applies with \(\nu_N\) unchanged. We obtain discrete laws attaining the desired asymptotic coefficient before passing to continuous phases.

Finally, multiply the phases by independent \(e^{iV_i}\) with \(V_i\) uniform on the centered sector \([-\pi/q,\pi/q]\). The equal sectors partition \(\mathbb T\) up to endpoints, so every required marginal becomes exactly product Haar. The balanced coefficient is multiplied by \(\rho_q^{2m}\) with \(\rho_q=\sin(\pi/q)/(\pi/q)\). For each fixed \(q\) this construction holds at every sufficiently large \(N\). Taking the upper limit in \(N\) and then \(q\to\infty\) gives the desired upper bound on the minimum, matching the scalar lower bound. The set of laws with the given marginals is weakly compact, and the balanced coefficient is continuous, so the minimum exists for each \(N\). To achieve the same limit using smooth positive densities, convolve each coordinate with independent circular noise having a smooth strictly positive approximate-identity density. This keeps the marginal laws exact, makes the joint density smooth and positive, and can be chosen with first Fourier coefficient tending to 1 as \(N\to\infty\).

The Gauss and Gauss–Radau moment calculations are classical. Earlier work applies a univariate discrete moment problem to \(k\)-wise independent bits. Here the empirical moment realization simultaneously enforces all finite-alphabet histogram moments and supports a radial extremizer whose independent circular sectors give exact Haar marginals. The use of the Legendre pair's count representation is methodological. [Classical Gaussian quadrature](https://dlmf.nist.gov/3.5), [Peled, Yadin and Yehudayoff on the binary moment problem](https://arxiv.org/abs/0801.0059).
