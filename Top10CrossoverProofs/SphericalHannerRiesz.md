# Sharp Hanner curvature for spherical Riesz moments

Let \(U_1,\ldots,U_n\) be independent uniform unit vectors in \(\mathbb R^d\), with integer \(d\ge2\). For \(p\ne0\) and \(x_i>0\), put
\[
\Phi_{p,d}(x)=\mathbb E\left|\sum_i x_i^{1/p}U_i\right|^p.
\]
Then \(\Phi_{p,d}\) is finite for every \(n,x\) exactly when \(p>1-d\). Its curvature for all \(n\) has the following sharp ranges.

| Exponent | Curvature |
| --- | --- |
| \(0<p<2\) | Convex |
| \(p=2\) | Linear |
| \(p>2\) | Concave |
| \(2-d\le p<0\) | Concave |
| \(1-d<p<2-d\) | Neither convex nor concave, already for \(n=2\) |

The positive range extends to the closed nonnegative orthant. Apart from homogeneity rays, the convexity or concavity is strict in the open ranges giving a sign. At the Riesz endpoint \(p=2-d<0\), the moment is linear on each dominance chamber \(x_i^{1/p}\ge\sum_{j\ne i}x_j^{1/p}\); strict concavity holds in nonradial directions within the open strict polygon region. For \(p=0\), the limit in log-amplitude coordinates is
\[
L_d(v)=\mathbb E\log\left|\sum_i e^{v_i}U_i\right|,
\qquad
\lim_{p\to0}\frac{\Phi_{p,d}(e^{pv_1},\ldots,e^{pv_n})-1}{p}=L_d(v).
\]
Here \(L_d(v+c\mathbf1)=L_d(v)+c\). It is convex, strictly in directions modulo translation for \(d\ge3\). For \(d=2\) it equals \(v_i\) on the \(i\)th dominance chamber and is strictly convex modulo translation within the strict polygon region.

The positive-range spherical inequality is known for \(p\ge2\) and for \(1\le p\le2\) when \(d\ge3\) by [Jenkins and Tkocz, Theorem 1 and Section 3.2](https://par.nsf.gov/servlets/purl/10414688). The portfolio's complex Hanner argument covers the circle. The new scope here is the complete Riesz range and its endpoints, using a single spherical Hessian identity, and a uniform quantitative comparison with the Euclidean Hanner deficit. The negative powers here use \(x_i^{1/p}\) as amplitudes. The Schur-curvature results of [Chasapis, Singh and Tkocz, Theorem 6](https://doi.org/10.2140/apde.2024.17.2509) use \(\sqrt{x_i}\). Priority for the negative-moment curvature theorem remains provisional.

## Spherical integration by parts

Let \(f\) be twice continuously differentiable on \([0,\infty)\), and put \(S=\sum_i a_iU_i\), \(s=|S|^2\), \(u_i=U_i\cdot S\), \(C_{ij}=U_i\cdot U_j\), and \(G=sC-uu^{\mathsf T}\). For any real \(b\),
\[
b^{\mathsf T}Gb
=\left|S\wedge\sum_i b_iU_i\right|^2\ge0.
\]
For the \(j\)th sphere integrate the divergence of \(f'(s)Y_{ij}\), where
\[
Y_{ij}=C_{ij}S-u_jU_i.
\]
This is tangent to the sphere of \(U_j\). Write \(S=R+a_jU_j\), with \(R\) fixed when integrating this sphere. For \(i\ne j\), the first part \(C_{ij}R-(U_j\cdot R)U_i\) is induced by a fixed skew-symmetric map and has zero divergence. The remaining part \(a_j(C_{ij}U_j-U_i)\) equals minus \(a_j\) times the spherical gradient of \(C_{ij}\). The spherical Laplacian of a linear function is \(-(d-1)\) times that function. Hence the divergence of \(Y_{ij}\) is \(a_j(d-1)C_{ij}\). For \(i=j\), the field is the spherical gradient of \(U_j\cdot R\), so its divergence is \(-(d-1)(u_j-a_j)\). In both cases \(\nabla_{U_j}s\cdot Y_{ij}=2a_jG_{ij}\). Integration by parts gives
\[
\begin{aligned}
\mathbb E f'(s)C_{ij}&=-\frac{2}{d-1}\mathbb E f''(s)G_{ij} &&(i\ne j),\\
\frac1{a_i}\mathbb E f'(s)u_i&=\mathbb E f'(s)+\frac{2}{d-1}\mathbb E f''(s)G_{ii}.
\end{aligned}
\]

More generally, for any \(q\ne0\), write \(a_i=x_i^{1/q}\), \(D=\operatorname{diag}(a_i^{q-1})\), \(F(x)=\mathbb E f(s)\). Direct differentiation using \(\partial_{a_i}s=2u_i\) and \(\partial_{a_j}u_i=C_{ij}\) gives
\[
q^2(D\nabla^2F D)_{ij}
=\mathbb E\big[2f'(s)C_{ij}+4f''(s)u_i u_j
-2(q-1)\delta_{ij}f'(s)u_i/a_i\big].
\]
Inserting the two integration identities and replacing \(uu^{\mathsf T}\) by \(sC-G\) yields the universal radial-potential identity
\[
q^2D\nabla^2F D
=\mathbb E\left[
\big(2(2-q)f'(s)+4sf''(s)\big)C
-\frac{4(d+q-2)}{d-1} f''(s)G
\right].
\]
Every calculation uses smooth functions on a compact product of spheres. In particular the identity may be applied with positive regularization before any singular limit.

## The power ranges and the sharp obstruction

Take \(f(s)=(s+\varepsilon)^{p/2}\), \(q=p\). With \(T=s+\varepsilon\), this specializes to
\[
D\nabla^2\mathbb E T^{p/2}D
=\frac{2-p}{p}\,
\mathbb E\left[
T^{(p-4)/2}
\left(\frac{p+d-2}{d-1}G+\varepsilon C\right)
\right].
\]
Since both \(G\) and \(C\) are positive semidefinite, the sign is immediate in all the listed convex and concave ranges. Monotone convergence applies for negative powers and bounded convergence for positive powers. In fact, conditioning on all directions but one gives the bound
\(\mathbb P(|S|\le r)\le C_d(r/a_i)^{d-1}\) for \(0<r<a_i/2\), uniformly in the conditioned directions. The part of a unit sphere inside any ball of radius \(r/a_i\) lies in a spherical cap of chordal radius at most \(2r/a_i\) about any of its points, and such caps have the stated surface measure bound. This gives moment finiteness for \(p>1-d\) and logarithm integrability. For \(n=2\) and both radii equal to \(1\), the cap at the antipode gives a matching lower bound of order \(r^{d-1}\), so finiteness fails for \(p\le1-d\). For the positive ranges the original expectation is continuous at zero amplitudes by bounded convergence.

In the open curvature ranges, the coefficient of \(G\) has a strict sign after multiplication by \((2-p)/p\). For a direction \(h\) in the \(x\) coordinates, the wedge test uses \(b=D^{-1}h\). If \(h\) is not proportional to \(x\), the vectors \(a,b\) are not proportional. Put all \(U_k=e_1\) except \(U_i=e_2\) for one index \(i\). If every such choice made the wedge zero, then \(b_i\sum_k a_k=a_i\sum_k b_k\) for every \(i\), a contradiction. The corresponding integrand is bounded away from zero on an open full-support event, uniformly under small perturbations of \(x,h\) and sufficiently small \(\varepsilon\). Integrating along any line segment then shows strict curvature off homogeneity rays after removal of \(\varepsilon\).

Let \(1-d<p<2-d\). For \(d\ge3\), put \(p_0=2-d\). Newton's spherical shell identity gives \(\mathbb E|U_1+U_2|^{p_0}=1\). Strict Jensen for the power \(p/p_0>1\), applied to the nonconstant variable \(|U_1+U_2|^{p_0}\), gives \(\Phi_{p,d}(1,1)>1\). In \(d=2\), the logarithmic shell identity gives \(\mathbb E\log|U_1+U_2|=0\), so strict Jensen for the exponential gives the same inequality. On the other hand the function \(y\mapsto\Phi_{p,d}(1,y)\) tends to \(0\) as \(y\downarrow0\), and to \(1\) as \(y\uparrow\infty\). These limits follow by factoring out the dominant amplitude and using uniform convergence of the residual norm to \(1\). A convex function on \((0,\infty)\) with finite limit at \(+\infty\) is nonincreasing, contradicting the limit at zero and the value at \(1\). A concave function with finite limit at \(+\infty\) is nondecreasing, contradicting the value at \(1\). This gives the sharp obstruction without differentiating a negative-power singularity.

For a two-step check when \(d=3\), \(U_1\cdot U_2\) is uniform on \([-1,1]\). Direct integration gives
\[
\mathbb E|aU_1+bU_2|^p=
\frac{(a+b)^{p+2}-|a-b|^{p+2}}{2ab(p+2)}
\quad(p>-2),
\]
and at \(p=-1\) this equals \(\max(a,b)^{-1}\). For \(n=1\), direct differentiation gives \((2-p)\varepsilon T^{(p-4)/2}/p\) in the rescaled Hessian, consistent with \(G=0\).

## A quantitative Hanner deficit comparison

Put
\[
\Psi_p(x)=\left(\sum_i x_i^{2/p}\right)^{p/2},
\qquad
c_{p,d}=\frac{p+d-2}{d}\left(1+\frac2d\right)^{(p-4)/2}.
\]
Then \(\Phi_{p,d}-c_{p,d}\Psi_p\) is convex for \(0<p<2\) and concave for \(2<p\le4\) or \(2-d<p<0\). In each range, its Jensen inequality bounds the Hanner deficit from below by \(c_{p,d}\) times the corresponding Euclidean Jensen deficit. This factor is independent of the number of summands. At \(p=4\), the stated factor \((d+2)/d\) is the largest possible since the Hessians are proportional everywhere.

To prove the comparison, abbreviate \(A=\sum_i a_i^2\), \(\omega_{ij}=a_i b_j-a_j b_i\), \(Q=\sum_{i<j}\omega_{ij}^2\), and \(Z=b^{\mathsf T}Gb\). The wedge expansion gives
\[
\mathbb E Z=\frac{d-1}{d}Q,\qquad
\mathbb E[Zs]=\frac{d-1}{d}
\left[AQ+\frac2d\left(AQ-\sum_{i<j}(a_i^2+a_j^2)\omega_{ij}^2\right)\right].
\]
For the second formula, use \(s=A+2\sum_{j<k} a_j a_k U_j\cdot U_k\) and \(Z=\left|\sum_{i<j}\omega_{ij}U_i\wedge U_j\right|^2\). Independent sign flips eliminate every contraction of a dot term with a wedge cross term except when the two wedge pairs share one index, and the remaining two indices are the dot pair. For distinct \(i,j,k\),
\[
\mathbb E[(U_i\wedge U_j)\cdot(U_i\wedge U_k)(U_j\cdot U_k)]
=\frac1d-\frac1{d^2}.
\]
This follows by expanding the wedge product and applying \(\mathbb E U_iU_i^{\mathsf T}=I/d\). The surviving sum is \(4(d-1)d^{-2}\sum_i\sum_{j<k:j,k\ne i} a_j a_k\omega_{ij}\omega_{ik}\). Expanding the square of \(\sum_j a_j\omega_{ij}\) converts this to the second formula, using \(\sum_i(\sum_j a_j\omega_{ij})^2=AQ\).

If \(Q>0\), the measure with density \(Z/\mathbb E Z\) has mean \(s\) at most \((1+2/d)A\). For \(\beta=(p-4)/2\le0\), Jensen for \(t^\beta\) and its monotonicity give
\[
\mathbb E[Z(\varepsilon+s)^\beta]\ \ge
\frac{d-1}{d}\,Q\,(\varepsilon+(1+2/d)A)^\beta.
\]
The same inequality holds for \(Q=0\). For a line direction \(h\), set \(b=D^{-1}h\). Direct differentiation of the Euclidean function gives \(h^{\mathsf T}\nabla^2\Psi_p h=(2-p)A^\beta Q/p\). Comparing with the power identity, discarding its \(\varepsilon C\) term of the same sign, gives the asserted curvature comparison as \(\varepsilon\downarrow0\). Rigorously, integrate the regularized bounds along a compact segment in the open orthant. The explicit lower bound converges uniformly on that segment, and the regularized values converge at each point. The direct fourth-moment identity is
\[
\Phi_{4,d}(x)=\left(1+\frac2d\right)\Psi_4(x)-\frac2d\sum_i x_i.
\]
It follows by squaring \(s=A+2\sum_{i<j}a_i a_jU_i\cdot U_j\) and applying sign symmetry and \(\mathbb E(U_i\cdot U_j)^2=1/d\). Thus equality of Hessians holds at \(p=4\), and the factor is optimal for \(n\ge2\).

On the simplex \(\sum_i x_i=1\), write \(s_x=\left|\sum_i\sqrt{x_i}U_i\right|^2\) and \(H(x)=-\sum_i x_i\log x_i\). The comparison also gives the entropy consequence
\[
x\longmapsto \mathbb E[s_x\log s_x]+\frac{2}{d+2}H(x)
\quad\text{is concave}.
\]
Indeed for \(p\ne2\), divide the curvature comparison, after subtracting its linear value \((1-c_{p,d})\sum_i x_i\) at the transition, by \(p-2\). Both sides of the transition give concave functions. The limits at \(p=2\) on the simplex use
\[
\left.\partial_p\Phi_{p,d}\right|_{p=2}
=\tfrac12\mathbb E[s_x\log s_x]+\tfrac12 H(x),
\qquad
\left.\partial_p\Psi_p\right|_{p=2}=\tfrac12 H(x).
\]
For the first identity differentiate the amplitudes \(x_i^{1/p}\), using \(\mathbb E(U_i\cdot U_j)=\delta_{ij}\). On the interior, the differentiated integrands are bounded for \(p\) in a compact neighborhood of \(2\), including when \(s_x=0\). Since \(c_{2,d}=d/(d+2)\), the stated entropy inequality follows. Continuity of \(t\log t\) at zero gives the boundary.

## The logarithmic limit and endpoint strictness

Let \(a_i=e^{v_i}\), \(A=\operatorname{diag}(a_i)\), \(T=s+\varepsilon\). Apply the same integration identities to the derivatives of \(L_\varepsilon(v)=\frac12\mathbb E\log T\). The chain rule gives \(A^{-1}\nabla^2L_\varepsilon A^{-1}=\mathbb E[ T^{-2}(TC-2uu^{\mathsf T})+\operatorname{diag}(T^{-1}u_i/a_i)]\). For the off-diagonal terms add \(1/(d-1)\) times the relation \(\mathbb E[T^{-2}((d-1)TC-2G)]_{ij}=0\); use the diagonal integration relation for the diagonal terms. The result is
\[
A^{-1}\nabla^2L_\varepsilon A^{-1}
=2\mathbb E\left[T^{-2}\left(\frac{d-2}{d-1}G+\varepsilon C\right)\right].
\]
Pointwise convergence and the negative-moment bound prove log convexity. The normalization in the statement follows by differentiating the moment at \(p=0\). For small \(p\), the absolute value of \((z^p-1)/p\) is bounded by \(C(1+z^{-\eta})\) for fixed \(\eta\in(0,d-1)\) and bounded \(z>0\). Strictness for \(d\ge3\) follows from the open wedge event as before, now with \(b=Ah\), so the only exceptional direction is translation.

The Newton kernel at \(p=2-d\) has spherical average \(\max(a,|R|)^{2-d}\) on the sphere of radius \(a\) centered at \(R\). The corresponding average of the planar logarithm is \(\log\max(a,|R|)\). For \(|R|>a\) both statements are the harmonic mean-value property. For \(|R|<a\) the average as a function of \(R\) is radial and harmonic in the ball, so it is constant and equal to its value at zero. The cap estimate gives continuity at \(|R|=a\). Conditioning on the other steps proves the stated linearity on dominance chambers.

For strictness at these two endpoints, suppose the strict polygon inequalities \(a_i<\sum_{j\ne i}a_j\) all hold. For any \(b\) not proportional to \(a\), choose \(i,j\) with \(b_i/a_i\ne b_j/a_j\). The remaining vectors can be chosen to have a positive resultant of length \(r\) strictly between \(|a_i-a_j|\) and \(a_i+a_j\). Indeed their possible resultant lengths form the closed interval from the positive part of twice their largest length minus their total length, to their total length. This follows by inductively adding one planar segment and using its triangle interval. The strict inequalities give overlap with the required open interval, also when a single remaining segment fixes \(r\). In a two-dimensional plane choose the two noncollinear vectors \(a_iU_i,a_jU_j\) with sum the negative of that resultant. Reflect them in the line of the resultant. The two configurations have the same zero sum \(S\), while their values of \(\sum b_kU_k\) differ, since the transverse components cancel with weights \(a_i,a_j\) and their ratio changes with \(b_i,b_j\).

Thus some configuration with \(S=0\) has \(\left|\sum b_iU_i\right|>0\) and two nonparallel directions. The derivative of the sum map in those sphere variables is onto \(\mathbb R^d\), because the two distinct orthogonal tangent hyperplanes span the whole ambient space. Local coordinates for this submersion and the positive product surface density give
\[
\mathbb E\left[\varepsilon(\varepsilon+s)^{-(d+2)/2}
\left|\sum_i b_iU_i\right|^2\right]\ \ge c>0
\]
for all sufficiently small \(\varepsilon\). To see the scaling, restrict to a fixed local box in the remaining coordinates and to the ball \( |S|\le\sqrt\varepsilon\) in the \(d\) image coordinates. Its volume is proportional to \(\varepsilon^{d/2}\), which cancels the lower bound proportional to \(\varepsilon^{-d/2}\) on the rest of the integrand. The bound is uniform under small changes in the amplitudes and \(b\). At \(p=2-d\) this is the \(C\) term of the power identity, with strictly negative prefactor; at \(p=0,d=2\) it is the \(C\) term of the log identity, with strictly positive prefactor. Integration on local line segments and passage to the pointwise limit give the stated strictness.
