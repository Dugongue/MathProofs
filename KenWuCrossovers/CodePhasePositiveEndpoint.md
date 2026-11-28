# The positive exchangeable phase constant exists and is strictly below one half

Let \(\mathcal E_{2,N}\) be the exchangeable laws of \(N\) unit complex phases with every three-coordinate marginal equal to product Haar, and put \(a_2(Z)=\mathbb E[Z_1Z_2\overline{Z_3Z_4}]\). Then the limit

\[
C=\lim_{N\to\infty}N\max_{Z\in\mathcal E_{2,N}} a_2(Z)
\]

exists, is an effectively computable real number, and satisfies

\[
\frac{32}{\pi^4}\le C<\frac12-2^{-36}.
\]

This settles existence of the positive endpoint in [Finite extendibility and hidden phase moments](https://github.com/Dugongue/MathProofs/blob/main/GeometryOfPartiallyObservedLaws/Extensions.md#5-conjectures-and-tests) and shows that continuous Haar marginals cause a strict asymptotic gap from its auxiliary four-phase optimum \(1/2\). It gives an exact variational characterization with an explicit alphabet-approximation error. A closed-form evaluation remains open. The discrete programs use exact empirical symbol-count moments, in the spirit of [Ken Wu's root-of-unity correlation certificate](https://kenwu-lab.wooqianghao.workers.dev/papers/ternary-legendre-pair-35/).

## Normalization and an exact finite-alphabet program

For either Haar phases or uniform \(q\)-th roots with \(q\ge3\), set \(M=N^{-1}\sum_i Z_i\). Under the three-wise independence requirement,

\[
N a_2=\frac{N^4}{(N)_4}\left(N\mathbb E|M|^4-\frac{2-1/N}{N}\right).
\tag{1}
\]

This follows by expanding the fourth moment. The independent baseline \( \mathbb E|\sqrt N M|^4=2-1/N\) is common to both alphabets because coordinate charges have absolute value at most two. The only differing terms are those with four distinct indices, each of moment \(a_2\). In particular it suffices to optimize \(N\mathbb E|M|^4\).

Fix \(q\ge3\), write \(\lambda=(1/q,\ldots,1/q)\), \(E=\{\sum_jx_j=0\}\subset\mathbb R^q\), and \(\Sigma=q^{-1}I_E\). Write \(L(x)=\sum_j x_j e^{2\pi ij/q}\). If \(\mu\) is the empirical frequency vector of the \(q\) symbols, put \(x=\mu-\lambda\). As shown in the [negative endpoint proof](CodePhaseQuadrature.md), the required three-coordinate marginal condition is exactly agreement with the independent centered histogram on every polynomial of degree at most three. Its first, second and third centered moments are respectively zero, \(\Sigma/N\), and \(T/N^2\), where \(T\) is the centered third tensor of one uniform symbol. The objective is \(N\mathbb E|L(x)|^4\). Conversely, every law of the integer counts with those three moments defines a valid exchangeable phase law by uniform random placement.

Use the compact set

\[
K_q=\{(r,u):0\le r\le2,\ u\in E,\ |u|=1,\ \lambda+ru\text{ is a probability vector}\}.
\]

Define \(\mathcal A_q\) as the maximum of

\[
\int_{K_q}r^2|L(u)|^4\,d\eta
\]

over finite positive measures \(\eta\) on \(K_q\) subject to

\[
\int uu^{\mathsf T}\,d\eta=\Sigma,\qquad
\int r\,u^{\otimes3}\,d\eta=0 .
\tag{2}
\]

The constraints fix the total mass \(\operatorname{tr}\Sigma\). The feasible set is compact for weak convergence and is nonempty by taking directions at \(r=0\) with covariance \(\Sigma\). The maximum is therefore attained.

For the upper bound, each empirical law gives the measure which places weight \(N|x|^2\) at \((|x|,x/|x|)\) on an outcome \(x\ne0\) and no weight on \(x=0\), then averages over outcomes. This measure has the covariance constraint exactly, has third integral \(T/N\), and its objective equals that of the phase law. Compactness gives a feasible limit along any subsequence achieving the upper limit. Thus \(\limsup_N \max N\mathbb E|M|^4\le\mathcal A_q\) in the discrete alphabet.

For the lower bound, take an optimizer represented by finitely many atoms. This representation follows by applying finite-dimensional convexity to the entries in (2), the objective, and total mass. Fix \(0<\delta<1\). Multiply the masses at positive radii by \(1-\delta\), and use the covariance left over for a typical Gaussian population. More explicitly, for each such atom \((r_j,u_j)\) with reduced weight \(w_j\), set \(x_j=r_j u_j\) and \(\alpha_j=w_j/r_j^2\). The positive-radius covariance

\[
J=\sum_j\alpha_j x_jx_j^{\mathsf T}
\]

satisfies \(J\le(1-\delta)\Sigma\), and \(\sum_j\alpha_j x_j^{\otimes3}=0\). Let the rare outcome \(j\) have probability \(\alpha_j/N\), with histogram frequencies within \(O_q(1/N)\) of \(\lambda+x_j\). Such rounding preserves nonnegative coordinates and total count. For the remaining probability, draw a centered Gaussian on \(E\) with covariance \(\Sigma-J\), then round to the centered scaled count grid as in the negative endpoint proof. The latter distribution has bounded moments through degree four and moments converging to that Gaussian. In the scaled coordinates \(\sqrt N x\), the rare outcomes contribute \(O(N^{-1/2})\) to degree one, converge to \(J\) in degree two, and contribute \(O(N^{-1/2})\) in degree three. For degree three, the potential term \(\sqrt N\sum_j\alpha_j x_j^{\otimes3}\) cancels exactly, and rounding accounts for the stated error. The three moment tensors of the mixture therefore converge to those of the full Gaussian with covariance \(\Sigma\).

Now correct the mixture to the exact independent multinomial moments through degree three. Use the bounded buffer point construction of [the finite empirical moment realization lemma](CodePhaseQuadrature.md#a-finite-empirical-moment-realization-lemma) with \(h=3\). Its proof only requires convergence of the preliminary moments through degree three for this correction. The correction changes the law by replacing an \(o(1)\) part by a law supported on a common bounded region in the scaled coordinates. Typical and buffer outcomes contribute \(o(1)\) to \(N\mathbb E|L(x)|^4\), since their scaled fourth moments stay bounded and the conversion factor is \(1/N\). The rare outcomes have limiting objective

\[
\sum_j\alpha_j|L(x_j)|^4=(1-\delta)\mathcal A_q .
\]

Rounding and the \(o(1)\) mixture leave this limit unchanged. The corrected law has the exact marginal constraint. Letting \(\delta\downarrow0\) proves that the discrete optimum converges to \(\mathcal A_q\).

This is an effective finite program. By Carathéodory's theorem the number of atoms needed is at most one plus the number of real moment and objective coordinates, at most \(3+q^2+q^3\). The variables are those atoms and their nonnegative weights. All constraints, including the sphere and simplex constraints of \(K_q\), are polynomial with real algebraic coefficients. The optimum is computable by real quantifier elimination. The construction uses the exact finite-alphabet sampling law. In particular, logarithmically or asymptotically approximate low-marginal constraints are unnecessary.

## Uniform reduction from Haar to roots of unity

Let \(B_N\) and \(B_{N,q}\) denote the Haar and discrete maxima of \(N\mathbb E|M|^4\). Quantize a Haar phase to the nearest \(q\)-th root, using a fixed choice on the null sector boundaries. Then the rounded phases are three-wise independent uniform roots. In the other direction, independently jitter each root by a uniform angle in its sector, obtaining three-wise independent Haar phases. In both directions the phase differences \(D_i\) are pairwise independent, centered, and have \(|D_i|\le\pi/q\). Thus

\[
\mathbb E|M-M'|^2\le\frac{\pi^2}{q^2N},
\qquad
\mathbb E(|M|+|M'|)^2\le\frac4N .
\]

Because \(|M|,|M'|\le1\), the absolute difference of their fourth powers is at most \(2|M-M'|(|M|+|M'|)\). Cauchy–Schwarz yields

\[
|B_N-B_{N,q}|\le\frac{4\pi}{q}.
\tag{3}
\]

For each fixed \(q\), \(B_{N,q}\to\mathcal A_q\). Equation (3) proves that the upper and lower limits of \(B_N\) differ by at most \(8\pi/q\) for every \(q\), so they agree. Its limit is \(C\) by (1), and \(|C-\mathcal A_q|\le4\pi/q\) is the asserted effective rate of alphabet approximation. The lower bound \(32/\pi^4\) now follows from the previously proved four-phase construction along powers of two in [the portfolio proof](https://github.com/Dugongue/MathProofs/blob/main/GeometryOfPartiallyObservedLaws/Extensions.md#2-sharp-fourth-order-bounds).

## Why the limiting value is strictly below one half

For a Haar phase law let \(\nu\) be its random empirical measure, rotated to make its first Fourier coefficient a nonnegative real \(t\). If the coefficient is zero, leave the measure unrotated. Put \(M_j(\nu)=\int z^j\,d\nu(z)\) and \(v(\nu)=\int(\operatorname{Re}z-t)^2\,d\nu(z)\). The third-moment identity gives

\[
\mathbb E[ t^2\operatorname{Re}M_2(\nu)]=N^{-2}.
\]

Indeed, before rotating, the left side is the real part of the expectation of the square of the empirical first coefficient times the conjugate of the empirical second coefficient. Only the terms with all three indices equal survive. Since \(\operatorname{Re}M_2(\nu)=2t^2+2v-1\), and \(N\mathbb E t^2=1\), this identity gives

\[
N\mathbb E t^4=\frac12+\frac1{2N}-N\mathbb E[t^2v].
\tag{4}
\]

Take laws with \(N\mathbb E t^4\to C\), tilt their empirical-measure laws by the density \(Nt^2\), and pass to a weakly convergent subsequence of these probability laws. Write \(\tau\) for the limit, \(x=t^2\), and \(\epsilon=1/2-C\). The rotated laws are supported on the closed set with real nonnegative first coefficient, where the functions involved are continuous. Equation (4) and the definition of the tilt give
\[
\mathbb E_\tau x=1/2-\epsilon,\qquad \mathbb E_\tau v=\epsilon .
\]
Pairwise Haar independence gives \(N\mathbb E|M_j|^2=1\) for every \(j\ge1\), since rotation preserves the absolute value. For any fixed \(\eta>0\), the tilted integral of \(|M_j|^2/(x+\eta)\) is at most one. The same holds under \(\tau\) by weak convergence.

Use the Chebyshev polynomial \(T_j(\cos\theta)=\cos(j\theta)\). Its derivative on \([-1,1]\) is bounded in modulus by \(j^2\), using \(|\sin(j\theta)|\le j|\sin\theta|\) and continuity at the endpoints. Therefore
\[
|\operatorname{Re}M_j-T_j(t)|\le j^2\sqrt v ,
\qquad
\mathbb E_\tau\frac{T_j(t)^2}{x+\eta}\le 1+\frac{2j^2\sqrt\epsilon}{\eta}.
\tag{5}
\]
The second estimate uses \(|T_j(t)|,|\operatorname{Re}M_j|\le1\), the pairwise bound, and Cauchy–Schwarz on \(\sqrt v\).

For \(1\le j<m\) let \(w_j=2(m-j)/(m(m-1))\). The weights sum to one. The identity
\[
1+2\sum_{j=1}^{m-1}(1-j/m)\cos(2j\theta)
=m^{-1}\left|\sum_{j=0}^{m-1}e^{2ij\theta}\right|^2
\]
shows that \(\sum_j w_jT_j(t)^2\ge\beta=(m-2)/(2(m-1))\). Write \(J=\sum_jw_jj^2\) and \(M_*=\mathbb E_\tau(x+\eta)^{-1}\). Averaging (5) gives \(M_*\le(1+2J\sqrt\epsilon/\eta)/\beta\).

Now \(T_4(t)=-1+8(x-1/2)^2\), so \(T_4(t)^2\ge1-16(x-1/2)^2\). For \(a=1/2+\eta\),
\[
\mathbb E_\tau\frac{(x-1/2)^2}{x+\eta}
=-a-\epsilon+a^2 M_* .
\]
Consequently the \(j=4\) lower bound from this polynomial and the upper bound in (5) imply, with \(A=(16a^2-1)/\beta>0\),
\[
16a-1-A+16\epsilon\le (32+2JA)\sqrt\epsilon/\eta .
\]
Take \(m=16\) and \(\eta=1/64\), so \(\beta=7/15\), \(J=136/3<46\), \(a=33/64\), and \(A=12495/1792<7\). The left side is greater than \(1/4\). If \(\epsilon\le2^{-36}\), the right side is less than \(43264/2^{18}<1/4\). This proves the advertised strict quantitative gap.

The formula for \(\mathcal A_q\) is a compact finite-alphabet moment optimization, while the quantitative gap uses the first fifteen Fourier modes of the Haar pair marginals. Together they prove existence, effective approximation and a genuine difference from the finite four-phase extremum. [Real algebraic quantifier elimination, Basu–Pollack–Roy](https://link.springer.com/book/10.1007/3-540-33099-2).
