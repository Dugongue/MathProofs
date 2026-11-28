# The Rademacher Hanner inequality for three functions in the missing exponent ranges

**Theorem.** Let \(u_1,u_2,u_3\) be real, complex, or Hilbert-valued \(L^p\) functions on any measure space, and let \(\varepsilon_i\) be independent uniform signs. Then
\[
\mathbb E\left\|\sum_{i=1}^3\varepsilon_i u_i\right\|_p^p
\ \ge\ \mathbb E\left|\sum_{i=1}^3\varepsilon_i\lVert u_i\rVert_p\right|^p\qquad(1\le p\le2),
\]
and the inequality reverses for \(p\ge2\). For \(1<p<\infty\) and \(p\ne2\), equality holds exactly when there is a common function \(v\) and measurable signs \(s_i(t)\) such that \(u_i(t)=s_i(t)\lVert u_i\rVert_p v(t)\) for every nonzero input, almost everywhere. In particular the three-function case holds throughout both Rademacher exponent ranges left open in Section 3.2 of Jenkins and Tkocz. A common dominance condition also suffices for the corresponding comparison for arbitrarily many real-valued functions. [Jenkins–Tkocz, *Complex Hanner's inequality for many functions*](https://arxiv.org/html/2207.09122v2#S3.SS2)

## A signed Laplacian for the Hessian

For positive \(x_i\), put \(a_i=x_i^{1/p}\), \(S=\sum_i a_i\varepsilon_i\), and \(F_p(x)=\mathbb E|S|^p\). Where all signed sums are nonzero and \(p>1\), define \(w_{ij}=\mathbb E[\varepsilon_i\varepsilon_j|S|^{p-2}]\) and \(D=\operatorname{diag}(x_i)\). Differentiating gives off-diagonal entries \((p-1)a_i a_jw_{ij}/p\) for \(D(\nabla^2F_p)D\). The row sums vanish since \(F_p\) is 1-homogeneous in \(x\). Consequently
\[
t^{\mathsf T}D(\nabla^2F_p)Dt=-\frac{p-1}{p}\sum_{i<j}a_i a_j w_{ij}(t_i-t_j)^2.
\tag{1}
\]
At \(p=2\) the moment is linear. Put \(q=p-2\) for the remaining cases and \(g(z)=\operatorname{sgn}(q)z^q\) on \(z>0\). This is increasing, and the desired curvature is equivalent to nonnegativity of the form on the right of (1) after replacing each \(-w_{ij}\) by \(\widetilde w_{ij}=\operatorname{sgn}(q) w_{ij}\). For \(q\ge1\), every \(\widetilde w_{ij}\) is nonnegative. Conditional on the other signs, its defining average is the iterated symmetric difference of the convex function \(z\mapsto|z|^q\) with positive steps \(a_i,a_j\), divided by four. A symmetric difference of a convex function is nondecreasing as its center increases, so the iterated difference is nonnegative. We use a different argument for \(-1<q<1\), \(q\ne0\).

## Dominance with any number of signs

Suppose \(a_1>\sum_{i>1}a_i\) and write \(\eta_i=\varepsilon_1\varepsilon_i\), \(i>1\). These are independent uniform signs, and \(|S|=a_1+\sum_{i>1}a_i\eta_i\). For a fixed \(i>1\), the conditional expected value over \(\eta_i\) of \(\eta_i g(|S|)\) is nonnegative by monotonicity. Hence \(b_i=\widetilde w_{1i}\ge0\), and conditioning the same way gives \(|\widetilde w_{ij}|\le\min(b_i,b_j)\) for \(i,j>1\). For any \(s\ge0\), set \(I_s=\{i>1:b_i>s\}\) and \(y_i=t_i-t_1\). The weighted variance identity gives
\[
\sum_{i<j\in I_s} a_i a_j(y_i-y_j)^2
\le \left(\sum_{i>1}a_i\right)\sum_{i\in I_s}a_i y_i^2.
\]
Integrating over \(s\) bounds the sum of all negative edge contributions by \((\sum_{i>1}a_i)\sum_{i>1}a_i b_i y_i^2\). The star at 1 contributes \(a_1\sum_{i>1}a_i b_i y_i^2\). This proves the desired Hessian sign in the strict dominance region.

For nonnegative constants \(r_i\) with \(\sum_{i>1}r_i\le1\), the conditions \(a_i\le r_i a_1\) define a convex cone in the \(x\)-coordinates, since they read \(x_i\le r_i^p x_1\). The moment is convex for \(p<2\) and concave for \(p>2\) on this cone. Indeed, first use a strictly smaller multiple of the quotas and positive coordinates, then use continuity, including when a quota is zero. Thus the theorem also holds for arbitrarily many real-valued functions whenever \(|u_i(t)|\le r_i|u_1(t)|\) almost everywhere with the same quotas. The quota assumption keeps all the averaging in a convex region.

## The triangle region for three signs

Order the amplitudes as \(a\ge b\ge c>0\), and suppose \(a<b+c\). Put
\[
d=b+c-a,\qquad A=2(b+c)-d,\qquad B=2b-d,\qquad C=2c-d.
\]
Then \(0<d\le c\), and \(|S|\) has values \(A,B,C,d\) after identifying opposite sign patterns. Let the vertices be labeled 1, 2, 3 in amplitude order \(a,b,c\). Direct averaging yields
\[
4(\widetilde w_{12},\widetilde w_{13},\widetilde w_{23})=
\big(g(A)+g(B)-g(C)-g(d),\ g(A)-g(B)+g(C)-g(d),\ g(A)-g(B)-g(C)+g(d)\big).
\]
The first two entries are positive. If the third is nonnegative the conclusion is immediate. Otherwise set \(h=-\widetilde w_{23}>0\) and
\[
U=g(A)-g(C),\quad V=g(A)-g(B),\quad X=g(B)-g(d),\quad W=g(C)-g(d).
\]
Then \(\widetilde w_{12}=h+U/2\), \(\widetilde w_{13}=h+V/2\), and \(4h=W-V=X-U\). In particular \(d<c\), so both \(X\) and \(W\) are positive. For positive conductances \(P,Q\) and real \(s,t\), the minimum of \(Ps^2+Qt^2\) with \(s-t\) fixed is \(PQ(s-t)^2/(P+Q)\), by completing the square. Applying this with \(P=ab(h+U/2)\), \(Q=ac(h+V/2)\) shows that the negative edge of conductance \(-bc h\) is dominated exactly when
\[
 b\frac{2V}{V+W}+c\frac{2U}{U+X}\ \ge\ d.
\tag{2}
\]

We bound the two ratios using the function \(g_*(z)=-1/z\), whose derivative is \(z^{-2}\). Indeed, \(g'(z)=|q|z^{-2}z^{q+1}\), and \(z^{q+1}\) is increasing. The intervals \([B,A]\) and \([d,C]\) for \(V,W\) are ordered from right to left. The intervals \([C,A]\) and \([d,B]\) for \(U,X\) also have both endpoints in that order. For the fixed positive density \(z^{-2}\), the average of an increasing function over the interval with both endpoints farther right is larger. To see this for overlapping intervals, remove the initial nonoverlap from the left interval and adjoin the terminal nonoverlap to the shared interval. Each operation increases the average. Thus \(V/W\) and \(U/X\) are at least those for \(g_*\), which are
\[
R_V=\frac{cCd}{(c-d)AB},\qquad R_U=\frac{bBd}{(b-d)AC}.
\]
We have \(2bR_V/(1+R_V)\ge dc/(b+c)\). Clearing positive factors reduces this to \(2bC(b+c)\ge(c-d)AB+cCd\). The difference expands to
\[
 d\big(2b^2+4b(c-d)+2c(b-d)+d^2\big),
\]
which is positive since \(0<d\le\min(b,c)\). Interchanging \(b,c\) gives \(2cR_U/(1+R_U)\ge db/(b+c)\). The sum proves (2), and therefore both Hessian claims throughout the triangle region.

## Global comparison and vector-valued functions

The Hessian conclusions on the generic positive orthant imply global curvature there. Indeed, along a segment whose initial point avoids the signed-sum zero sets, each signed sum is analytic in the segment parameter, extends analytically to an open neighborhood of the segment, and is nonzero at the initial point. Consequently it has only finitely many zeros. For \(p>1\), \(F_p\) is continuously differentiable along the segment, and the derivative has the required monotonicity on each of the finitely many pieces by the Hessian estimate. It has the same monotonicity across their endpoints by continuity. Approximation gives the assertion along every positive segment, and continuity extends it to the closed orthant. The endpoint \(p=1\) follows by letting \(p\downarrow1\) in the finite-sign moment at fixed \(x\). Jensen's inequality applied to \(x_i(t)=|u_i(t)|^p\) proves the theorem for real-valued functions on a probability space. For any measure space with \(\sum_i\lVert u_i\rVert_p^p>0\), normalize to a probability by density proportional to \(\sum_i |u_i|^p\) and divide the functions by the corresponding density to the power \(1/p\). This preserves their individual \(L^p\) norms and the signed-sum \(L^p\) norms.

For finite-dimensional real Hilbert-valued functions, let \(G\) be a standard Gaussian on the Hilbert space and apply the real-valued inequality on the product of the measure space and this Gaussian probability space to the functions \(\langle G,u_i(t)\rangle\). The formula \(\mathbb E_G |\langle G,v\rangle|^p=c_p\lVert v\rVert^p\) cancels the same factor \(c_p\) from both sides. Complex functions are included by using their real Hilbert structure. In a separable Hilbert space take a sequence of independent standard Gaussian coordinates in an orthonormal basis. Their pairings against the finite-dimensional projections of the functions are Cauchy in \(L^p\) on the product space, by the same Gaussian moment formula and \(L^p\) convergence of the projections. The limiting pairings have the intended joint Gaussian laws at almost every spatial point, by Fubini and convergence of the finite-dimensional covariances. This gives the general Hilbert-valued statement because strongly measurable functions have separable essential range.

## Equality away from the two endpoints

For \(p>1\), \(p\ne2\), the curvature is strict away from homogeneity rays. At positive regular points the dominant star proof gives strictness because each \(b_i>0\) and \(a_1>\sum_{i>1}a_i\). The triangle proof gives a positive star when its third edge is nonnegative, and the strict polynomial comparison in (2) gives a strict domination when the third edge is negative. These arguments also apply when \(q\ge1\), since the triangle edges are then all nonnegative. For two amplitudes the larger one is strictly dominant unless the two agree, and the same result follows by restricting to the interior of their two-coordinate face.

For two distinct points of the closed simplex \(\sum_i x_i=1\), their joining segment is positive in the common union of supports in its relative interior. With two coordinates in that union, the segment cannot be contained in the line of equal amplitudes. With three, a signed-sum zero relation on an entire open subsegment would have the form \(a_1=a_2+a_3\) after relabeling. The ratios \((x_2/x_1,x_3/x_1)\) follow a line segment in the positive quadrant, and they are nonconstant because the original segment is nonradial. The strictly concave function \((y,z)\mapsto y^{1/p}+z^{1/p}\) cannot equal one on a nonconstant segment. Thus some open part of the joining segment consists of regular points. On that part the Hessian is strictly signed. Since equality at any interior convex combination would make the globally convex or concave restriction affine on the entire segment, the simplex comparison is strict. By homogeneity and the probability normalization above, equality for scalar functions requires constancy of the normalized vector of their absolute values to the power \(p\).

Apply this scalar equality criterion to the Hilbert-valued Gaussian pairings. For each nonzero input put \(w_i=u_i/\lVert u_i\rVert_p\). At almost every spatial point and for almost every Gaussian sample, both \(\langle G,w_i-w_j\rangle\) and \(\langle G,w_i+w_j\rangle\) cannot be nonzero, because the absolute pairings of \(w_i,w_j\) agree. If both vectors \(w_i-w_j,w_i+w_j\) were nonzero, both corresponding scalar Gaussians would have continuous nondegenerate laws, contradicting that product-zero condition. Hence \(w_i=\pm w_j\) at almost every spatial point. Taking one nonzero normalized input as \(v\) gives the claimed representation. The signs are measurable by testing equality to \(v\), and the representation gives equality by invariance of the uniform signs under pointwise sign changes.

The theorem proves the first genuinely many-function case in the two open ranges. The unrestricted arbitrary-function problem remains open here. The earlier separate-convexity argument does not establish the joint curvature used by Jensen. [Discussion by Tomasz Tkocz](https://extremal010101.wordpress.com/2021/01/)

## Arbitrarily many functions with three common magnitude profiles

The same inequality holds for an arbitrary number of real-valued functions if their indices can be partitioned into at most three blocks such that, in block \(j\), one has \(|u_i(t)|=c_i v_j(t)\) almost everywhere for fixed \(c_i\ge0\) and a nonnegative \(L^p\) function \(v_j\). No pointwise dominance is required. It also holds for Hilbert-valued functions if within each block the normalized vectors agree up to measurable signs, so that \(u_i(t)=s_i(t)c_i v_j(t)\) for a common Hilbert-valued function \(v_j\) in that block.

For either statement, pointwise sign invariance lets us remove the \(s_i(t)\). The coefficient of \(v_j\) in the signed sum then has the law of \(Z_j=\sum_{i\in j}c_i\varepsilon_i\). The \(Z_j\) are independent and symmetric. Each may be represented in law as the product of an independent uniform sign and a nonnegative variable with the law of \(|Z_j|\), including when \(Z_j=0\) with positive probability. Condition on these latter variables, apply the three-function result to the scaled functions, and average. On the right the sum has coefficients \(Z_j\lVert v_j\rVert_p\), giving exactly the original right side. For \(p>1\), \(p\ne2\), the equality condition again says all nonzero normalized input functions agree pointwise up to signs. In fact, each active block has \(\mathbb P(|Z_j|>0)>0\). Independence gives positive probability that every active block survives. For each such realization equality in the conditional comparison requires the normalized block functions to agree up to signs. This is also sufficient.

## Sharp coefficient majorization for arbitrarily many symmetric summands

**Theorem.** Let \(\xi_1,\ldots,\xi_n\) be independent symmetric real random variables with finite \(p\)-th moments, where \(p\ge1\). The function
\[
G_p(x)=\mathbb E\Big|\sum_i x_i^{1/p}\xi_i\Big|^p
\]
is jointly convex in each pair of coordinates with the others fixed for \(p<2\), and jointly concave in each pair for \(p>2\). If the variables have a common law, this gives Schur convexity and Schur concavity respectively in the \(p\)-th powers. In particular, for \(\sum_i a_i^p=1\) and \(a_i\ge0\),
\[
\frac1n\,\mathbb E\Big|\sum_{i=1}^n \xi_i\Big|^p
\le\mathbb E\Big|\sum_{i=1}^n a_i \xi_i\Big|^p
\le\mathbb E|\xi_1|^p \qquad(1\le p<2),
\]
with both comparisons reversed for \(p>2\). For \(p>1\), \(p\ne2\), and a nonzero common law, the equal-amplitude and one-nonzero-amplitude configurations are the only extremizers, up to permutation. At \(p=2\) the values are equal. For uniform signs this gives the exact finite-length extremum at fixed coefficient \(\ell_p\) norm, governed by the absolute \(p\)-th moment of a centered binomial sum. This normalization uses the \(p\)-th powers of the coefficients. [Peskir on Schur majorization under the distinct squared-coefficient normalization](https://personalpages.manchester.ac.uk/staff/goran.peskir/khintchine.pdf)

Fix the coordinates other than \(i,j\), and let \(R\) be their sum. The variables \(\xi_i,\xi_j,R\) are independent and symmetric. Condition on their three absolute values and use independent uniform signs, exactly as above. This expresses the entire two-coordinate slice as
\[
\mathbb E F_p\big(|\xi_i|^p x_i, |\xi_j|^p x_j, |R|^p\big).
\]
The maps of the two coordinates in the integrand are linear, so the proved three-variable curvature gives the pairwise curvature in every dimension. For a common law each slice is symmetric in the two varied coordinates. Moving the two coordinates toward each other with their sum fixed therefore decreases \(G_p\) when \(p<2\), and increases it when \(p>2\). To see strictness, on the event that both corresponding magnitudes are positive, any two distinct points of the fixed-sum slice have nonproportional images under the two positive diagonal scalings. The third coordinate is fixed, so the strict simplex curvature and homogeneity of \(F_p\) give a strict comparison on that event. It has positive probability by independence and the nonzero-law hypothesis.

The majorization theorem expresses any majorization comparison as a finite sequence of pairwise averaging operations and permutations. Applying the proved comparisons gives the claimed Schur inequalities, with strictness whenever the vectors are not permutations at \(p>1\), \(p\ne2\). On the simplex the point with all coordinates \(1/n\) is majorized by every point, and every point is majorized by a vertex. Substituting these points gives the displayed constants and the equality statements.
