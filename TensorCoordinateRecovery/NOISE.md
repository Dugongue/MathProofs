# Stable recovery of paired tensor blocks in unknown nonorthogonal bases

**Theorem.** Let $A=(A_1,\ldots,A_s)$ be a real tensor given by square matrix slices of size $d$. Suppose there are invertible real matrices $X,Y$ and an unknown partition of the coordinates into positive-size sets $I_1,\ldots,I_q$ such that
$$
 A_k=X\left(\bigoplus_{a=1}^q c_{ak} I_{|I_a|}\right)Y^{-1}.
$$
Write $c_a=(c_{a1},\ldots,c_{as})$. Suppose $\|X\|,\|X^{-1}\|,\|Y\|,\|Y^{-1}\|\le K$, $\|A\|_F\le B$, and
$$
 \|c_a\|_2\ge\beta,\qquad
 \sigma_{\min}([c_a\ \ c_b])\ge\beta\quad(a\ne b),
 \qquad K,B\ge1,\quad0<\beta\le1.
$$
All matrix norms without a subscript are operator norms. Tensor Frobenius norm is the square root of the sum of the slice Frobenius squares. The partition, the bases, and the coefficient vectors are all hidden.

Let $R$ be the smallest power of two at least $100(d+1)(s+1)KB/\beta$. Given rational perturbed slices $\widetilde A$, rational bounds $K,B,\beta$, and an accuracy $0<\varepsilon<1/4$, assume
$$
 \|\widetilde A-A\|_F\le\varepsilon R^{-100}.
$$
There is a deterministic algorithm, polynomial in the binary input length, that returns exactly $q$ pairs of rational matrices approximating, up to a common permutation,
$$
 P_a=X E_{I_a}X^{-1},\qquad Q_a=Y E_{I_a}Y^{-1}.
$$
Each approximate pair has Frobenius error at most $\varepsilon$, and each tensor $(\widetilde P_a\widetilde A_k\widetilde Q_a)_k$ has aggregate Frobenius error at most $\varepsilon$ from $(P_a A_k Q_a)_k$. The bit bound is polynomial in the **lengths** of the binary bounds $K,B,\beta,\varepsilon$, including $\log R$.

The result allows arbitrary multiplicities $|I_a|$, repeated eigenvalues in every selected slice, and linearly dependent coefficient profiles as long as each pair of distinct profiles has rank two. If all multiplicities are one, the outputs recover the oblique projectors onto the left factor lines and the corresponding right dual factor lines by transposing the right projectors. Multiplicities give paired projectors onto the canonical blocks. No choice of coordinates within a repeated block is needed.

## Recover the algebra from all slices

Equip $W=M_d(\mathbb R)\oplus M_d(\mathbb R)$ with the Frobenius inner product and use coordinatewise matrix multiplication. Write $N=2d^2$. Form the raw linear map
$$
 L(S,T)=(S A_k-A_k T)_{k=1}^s .
$$
Under the hidden changes $S=X S_0 X^{-1},T=Y T_0Y^{-1}$ and the output change $Z_k=X Z_{0,k}Y^{-1}$, the map is a direct sum of two-column maps indexed by entries $(i,j)$. For $i\in I_a,j\in I_b$, the map on those two entries is $(x,y)\mapsto x c_b-y c_a$. For $a=b$, its only nonzero singular value is $\sqrt2\|c_a\|$. For $a\ne b$, its minimum singular value is at least $\beta$. The norm and inverse norm of each full domain and range change are at most $K^2$. Therefore for every $u\in W$,
$$
 \|Lu\|_F\ge\beta K^{-4}\operatorname{dist}(u,\ker L).
$$
Indeed the range change loses a factor $K^2$, and the distance to the transformed kernel is at most $K^2$ times the distance in clean coordinates.

The kernel $\mathcal K$ is precisely the image of $\mathcal D=\bigoplus_a M_{|I_a|}(\mathbb R)$ under
$$
 F(M)=(X M X^{-1},Y M Y^{-1}).
$$
It is an algebra under coordinatewise multiplication. Its center $Z$ is the span of the paired idempotents $f_a=F(E_{I_a})$. These are the primitive central idempotents of an algebra intrinsically defined by $A$, so they are independent of the chosen representation up to order.

Let $t=\varepsilon R^{-100}$ and $\delta=\|\widetilde A-A\|_F$. We will approximate spectral projectors to operator tolerance $t$ by a rational algorithm described below. Set $\gamma=\beta^2 K^{-8}$. The spectra of $L^*L$ on the kernel and its orthogonal complement lie in $\{0\}$ and $[\gamma,\infty)$, respectively. The noisy matrix $\widetilde L^*\widetilde L$ differs in operator norm by at most $12 B\delta$, using $\|L\|\le\sqrt2 B$ and $\|\widetilde L-L\|\le\sqrt2\delta$. Cut at $\gamma/2$ and use the low spectral projector. Weyl's inequality and the separated-subspace estimate give a rational approximate orthogonal projector $\widehat\Pi$ with
$$
 \|\widehat\Pi-\Pi\|\le R^{13}(\delta+t),
$$
where $\Pi$ is the orthogonal projector onto $\mathcal K$. For example, the operator perturbation contribution is at most $8(12B\delta)/\gamma$. To see the subspace estimate, for two Hermitian matrices restrict their difference between high and low spaces. The resulting Sylvester equation is inverted by integrating semigroups, at operator cost at most the reciprocal of the opposing spectral separation. Applying this to both directions bounds the difference of the two projectors. [Davis–Kahan spectral subspace perturbation](https://doi.org/10.1137/0707001)

## Recover the center even with repeated profiles

For the ambient matrix-unit coordinate basis $(e_j)_{j=1}^N$ of $W$, define
$$
 C u = \big((I-\Pi)u,\ ([\Pi u,\Pi e_j])_{j=1}^N\big).
$$
The projection factors insulate the commutator from components outside the algebra. The kernel of $C$ is precisely $Z$.

The following uniform lower bound controls this second kernel computation:
$$
 \|Cu\|\ge K^{-6}\operatorname{dist}(u,Z).
$$
To prove it, for each $m$-square block one has the matrix-unit identity
$$
 \sum_{i,j=1}^m \|[M,E_{ij}]\|_F^2
   =2m\|M-\operatorname{tr}(M)I_m/m\|_F^2.
$$
Indeed expanding each square gives two total squared-norm sums $m\|M\|_F^2$ and a total cross term $2|\operatorname{tr}(M)|^2$. Let $v=\Pi u=F(M)$. The map $w\mapsto [v,\Pi w]$ on $W$ has squared Hilbert–Schmidt norm $\sum_j\|[v,\Pi e_j]\|^2$. Precomposing by $F$ costs at most $\|F\|^2\le2K^4$ in this squared norm. In the other direction, $\|F(M')\|\ge\sqrt2 K^{-2}\|M'\|$. Since the commutator with $F(E_{ij})$ equals $F([M,E_{ij}])$, the sum over all within-block units is at least $4K^{-4}\operatorname{dist}(M,Z(\mathcal D))^2$. Also $\operatorname{dist}(v,Z)\le\sqrt2K^2\operatorname{dist}(M,Z(\mathcal D))$. Combining gives
$$
 \sum_j\|[v,\Pi e_j]\|^2\ge K^{-12}\operatorname{dist}(v,Z)^2.
$$
Adding $\|(I-\Pi)u\|^2$ proves the bound.

Use $\widehat\Pi$ in this formula for $C$ and cut the resulting Gram matrix at $K^{-12}/2$. Set $p=\|\widehat\Pi-\Pi\|$. The commutator operator difference per basis vector is at most $6p$ because $\|[u,v]\|$ in the ambient Frobenius norm is at most $2\|u\|\|v\|$. Thus $\|\widehat C-C\|\le(1+6\sqrt N)p$. Also $\|C\|\le1+2\sqrt N$. Their Gram difference is at most $R^5p$, including the term quadratic in $p$. The separated spectral projector estimate and accuracy $t$ give a rational approximate projector $\widehat Z$ with error
$$
 z=\|\widehat Z-\Pi_Z\|\le R^{32}(\delta+t),
$$
where $\Pi_Z$ is the true orthogonal projector onto the center. In particular the construction does not need the dimension of the algebra, the number of profiles, or their multiplicities in advance.

## Read central idempotents using symmetric matrices

Let $J:W\to W$ transpose both matrix coordinates. On $Z$ the form $\langle u,Jv\rangle$ equals the sum of the traces of the two coordinate products. In hidden coordinates it is $2\sum_a |I_a|u_av_a$ on block scalars. It is positive definite, even for nonorthogonal hidden frames. Specifically its eigenvalues on $Z$ are between $K^{-4}$ and $1$ relative to ambient Frobenius norm. Define the symmetric positive definite metric
$$
 G=\Pi_Z J\Pi_Z+I-\Pi_Z.
$$
Its eigenvalues are also in this interval. For $u_j=\Pi_Ze_j$, let $M_j$ be ambient left multiplication by $u_j$. Its restriction to $Z$ is self-adjoint for this metric. Define the symmetric matrix
$$
 B_j=\Pi_Z(JM_j+M_j^*J)\Pi_Z/2 .
$$
On $Z$, $B_j=G M_j$. On $Z^\perp$, $B_j$ is zero. Therefore for any factor $G=W_0^*W_0$,
$$
 H_j=W_0^{-*}B_jW_0^{-1}
$$
is symmetric. All $H_j$ commute, with common eigenlines spanned by $W_0 f_a$ and a common zero space $W_0Z^\perp$. On the line $W_0 f_a$ the $j$-th eigenvalue is $\chi_a(u_j)$, the scalar on block $a$ in the hidden coordinates of $u_j$.

We now compute rational approximations to this family using only $\widehat Z$. Replacing $\Pi_Z$ by $\widehat Z$ gives $\widehat G,\widehat B_j$ with errors bounded by $4z,8z$, respectively. In particular $\widehat G$ is positive definite. Take a rational $LDL^*$ decomposition of $\widehat G$, with a unit triangular $L$ and positive diagonal $D$, and use the factor $\widehat W=D^{1/2}L^*$. Its inverse norm is at most $2K^2$, and $\|\widehat W\|\le2$. The exact factorization is used only for the accuracy argument. Approximate the square roots in $D$ and their inverses by rational bisection. Fraction-free elimination bounds the bit lengths of $L,D$ and the exact triangular inverses by polynomial determinantal height bounds.

For comparison choose the exact factor $W_0=S\widehat W$, where
$$
 S=(\widehat W^{-*}G\widehat W^{-1})^{1/2}.
$$
Then $\|S-I\|,\|S^{-1}-I\|\le R^6 z$, by diagonalizing the positive definite matrix inside the square root, which differs from $I$ by at most $16K^4 z$. Hence matrices $\widehat H_j$ obtained by approximating $\widehat W^{-*}\widehat B_j\widehat W^{-1}$ symmetrically to accuracy $t$ satisfy
$$
 e=\max_j\|\widehat H_j-H_j\|\le R^{12}z+t.
$$
The dimension and condition bounds on $\widehat W$ make this absolute approximation possible with polynomially many bits.

For two different active labels, $\chi_a-\chi_b$ takes value one on $f_a$, and $\|f_a\|\le\sqrt{2d}K^2$. The same statement holds for distinguishing the active label from the common zero character using $\chi_a$. Applying Cauchy–Schwarz in the ambient coordinate basis shows that some $j$ distinguishes the corresponding eigenvalues by at least $1/(2d^{3/2}K^2)\ge R^{-2}$. Each ideal $|\chi_a(u_j)|\le1$, since $\|u_j\|\le1$ and the modulus of a matrix eigenvalue is at most its operator norm.

Put $h=R^{-4}$. For each $\widehat H_j$, compute its ordered real eigenvalues with multiplicity to accuracy $h/100$. Cut at each midpoint of a consecutive apparent gap larger than $h$. Weyl's inequality and $e<h/100$ ensure cut distance at least $h/3$ from either spectrum. Within a resulting interval the true spectrum has diameter at most $2Nh<R^{-2}$. Thus the common refinement of the true spectral partitions is exactly the individual active eigenlines together with the common zero space, if present.

Approximate every interval projector to accuracy $t$ for $\widehat H_j$. Its error relative to the ideal interval projector is at most $R^6(e+t)$, by the separated-subspace estimate at each boundary. The true interval projectors commute and have norm at most one. Hence an ordered product of at most $N$ approximate interval projectors differs from the corresponding true product by at most $R^9(e+t)$, by telescoping with individual factor norms at most one plus their errors. Compute products incrementally, keeping the ones whose trace exceeds $1/2$. The true trace is the intersection dimension and the trace error is at most $N R^9(e+t)<1/4$. It follows both that exactly the nonzero intersections remain and that at most $N$ products need to be retained at each step.

Let $R_a$ denote the ideal projector onto the line $W_0 f_a$. With $\mathbf 1=(I_d,I_d)$, the exact reconstruction is
$$
 f_a=W_0^{-1}R_a W_0\mathbf 1.
$$
This holds because $\sum_a f_a=\mathbf 1$ and the vectors $W_0 f_a$ are orthogonal. The formula gives zero on the common zero sector. Use $\widehat W$ and the computed products in the formula, with rational evaluation to accuracy $t$, and discard any output of Frobenius norm at most $1/2$. The zero sector is discarded and the active projectors retained, since the Frobenius norm of an active left projection is at least one. The reconstruction error is bounded by
$$
 R^{10}\big(z+R^9(e+t)+t\big)\le R^{65}(\delta+t),
$$
using $\|\mathbf 1\|\le\sqrt{2d}$, the bounds on $S,S^{-1},\widehat W,\widehat W^{-1}$, and the above estimates. Under the given promise it is less than $\varepsilon$. The aggregate tensor component errors are bounded by applying the product rule twice to $\widehat P_a\widetilde A_k\widehat Q_a$. The norms of the true idempotents are at most $K^2$, and the tensor Frobenius magnitude is at most $B$, so the component errors are at most $R^8$ times the sum of the projector error bound and $\delta$. They are also less than $\varepsilon$.

## Certified spectral projectors in binary precision

The threshold projectors in the preceding construction can be computed without time polynomial in the reciprocal of a small spectral gap. Here is a deterministic bit implementation. Subtract the rational threshold and divide by a known power of two so the spectrum is in $[-1,1]$ and avoids $(-u,u)$ for a supplied $u>0$. To compute the sign apply the matrix polynomial iteration
$$
 X_{j+1}=(3X_j-X_j^3)/2 .
$$
For unrounded iterates, the real scalar map $f(x)=(3x-x^3)/2$ is odd and preserves $[0,1]$. On $(0,1/2]$, $f(x)/x\ge 11/8$. On $[1/2,1]$, $1-f(x)\le(3/4)(1-x)$. Thus $k=O(\log(1/u)+\log(1/t))$ iterations suffice for scalar accuracy $t/4$, and also for operator accuracy by the spectral theorem.

Each matrix iterate can be rounded symmetrically to a dyadic grid. On matrices of operator norm at most two the polynomial is operator Lipschitz with constant eight, by expanding the difference of the cubes term by term in order. In dimension $m$, entrywise rounding to $p$ fractional bits costs at most $m2^{-p}$ in operator norm. Choose $p$ with $m2^{-p}8^{k+1}\le t/4$. Inductively all rounded iterates remain in the norm-two ball and the accumulated rounding error is at most $t/4$. Half the sum of the identity and this sign matrix approximates the high projector. Interval projectors are differences of thresholds. All scalings, polynomial evaluations, and rounding precisions use bit lengths polynomial in the input length and the logarithms of inverse gap and accuracy. The spectral norm bounds for the inputs here follow from the displayed inequalities or simple entrywise size bounds. The shift and divide inputs can also be rounded to the prescribed dyadic precision at the first step.

Ordered eigenvalue approximations are computed from the exact characteristic polynomial by squarefree decomposition and certified real-root isolation, retaining multiplicities. The polynomial has rational coefficients of polynomial bit height by the determinant bound. The required isolation/refinement costs polynomial time even when $h$ is exponentially small in binary length. All other matrix constructions have polynomial dimensions. Product depth in the refinement is at most $N$, and rational entry lengths are polynomial via a common denominator bound, since each product has at most $N$ factors. This verifies the full binary time bound, including the two raw kernel computations. [Certified real-root refinement](https://arxiv.org/abs/1104.1362) · [Matrix sign iteration and its classical antecedents](https://eprints.maths.manchester.ac.uk/1067/1/covered/MIMS_ep2008_39_Sample_chapter.pdf)

## Rectangular factors and an intrinsic generalization

The theorem also applies to rectangular slices of the form $A_k=U D_k V^*$ with thin, full-column-rank real factors $U,V$ of the same unknown column number $d$, provided their nonzero singular values lie in $[1/K,K]$. In this statement take $R$ to be the smallest power of two at least $100(d_1+d_2+1)(s+1)KB/\beta$ for the ambient row and column dimensions $d_1,d_2$, and use the noise promise $\delta\le\varepsilon R^{-150}$. The recovered projections act on the two signal spaces and are extended by zero on their orthogonal complements.

For the proof, the range of the horizontal slice concatenation is the range of $U$. Its smallest nonzero singular value is at least $\beta K^{-2}$. In fact applying its transpose to a vector in the range of $U$ first gives $U^*$ on that vector, then repeats each coordinate across the slices with coefficients from the corresponding $c_a$, then applies $V$ in every slice. The three steps have lower singular bounds $K^{-1},\beta,K^{-1}$. Apply the same argument to the concatenated transposes for $V$. By the Gram threshold argument above, the high support projectors of the noisy concatenations differ from the clean ones by at most $R^{10}\delta$. Their common rank $d$ can be determined from eigenvalue brackets at the threshold.

Here is a rational way to obtain sufficiently accurate frames of the noisy support projectors. Approximate an exact rank-$d$ spectral projector $H$ on an $m$-dimensional ambient space by a rational matrix $H'$ to accuracy $\zeta$. Greedily select $d$ columns of $H'$, at each step maximizing the distance to the span of those previously selected. These distances are compared by exact rational Gram elimination. For a span of fewer than $d$ columns, the sum of squared distances of the columns of $H$ to that span is at least one, since the orthogonal projector onto the span has rank less than $d$. Some column of $H'$ therefore has residual at least $1/\sqrt m-\zeta$. For $\zeta<1/(2\sqrt m)$, the chosen columns have all Gram–Schmidt pivots at least $1/(2\sqrt m)$ in norm. Their combined operator norm is at most $2$ as they are a column restriction of $H'$. The product of their singular values equals the product of these pivots, so their minimum singular value is at least $(4m)^{-m}$. Their exact orthonormal frame $W'$, obtained by triangular normalization of the Gram matrix, satisfies $\|(I-H)W'\|\le (4m)^m\zeta$. The frame $HW'(W'^*HW')^{-1/2}$ is an orthonormal frame for $H$ within $3(4m)^m\zeta$ of $W'$, by the spectral estimate for the positive Gram correction. The normalization of the rational column matrix uses a rational triangular decomposition and square roots of positive rational pivots, which can be approximated by bisection. Thus we can output a rational approximation within any prescribed binary tolerance of an actual orthonormal frame of $H$ in polynomial bit time. The factor $(4m)^m$ costs only $O(m\log m)$ additional bits. Apply the same projection and positive Gram correction from the noisy support to the clean support. Its frame error is at most three times the projector error. This latter step is for comparison only, and need not be computed.

Use the rational frames to compress the observed slices. If their numerical accuracy is $\varepsilon R^{-150}$, the compressed observation differs from the clean compression by at most $R^{13}(\delta+\varepsilon R^{-150})$. The clean compression has the square form already treated, with the same $K,B,\beta$ bounds, since the orthonormal clean frames span the factor ranges. In particular the compressed right factor transposed is the inverse of a square matrix of norm and inverse norm at most $K$. Apply the square theorem with tolerance $\varepsilon/R^{10}$, which admits this compressed noise by the chosen exponent $150$. Lift the output projections by the rational frames on their modes. The frame changes contribute at most $R^{14}(\delta+\varepsilon R^{-150})$ to the lifted Frobenius errors, by the product rule and $\|P_a\|,\|Q_a\|\le K^2$. Combining with the square theorem gives both projection and block errors at most $\varepsilon$, the latter again by expanding the two factors around the exact projections.

The center calculation itself works more generally for any raw rectangular slice family whose left–right intertwiner algebra has center isomorphic over $\mathbb R$ to a product of copies of $\mathbb R$. Supply lower positive bounds $\sigma,\tau,\lambda\le1$ for the nonzero singular values of $L,C$ and the smallest eigenvalue of $G$. The first two bounds replace the explicit model estimates for the two kernel computations. The center trace is positive because the primitive idempotents are mutually annihilating and the trace of each paired idempotent is its positive total rank. With $f_a$ a primitive pair, $\|f_a\|_F\le\sqrt{(d_1+d_2)/\lambda}$. This supplies the same character separation and spectral refinement without any hypothesis of scalar blocks. Taking $R$ to be the smallest power of two above $100(d_1+d_2+1)(s+1)B/(\sigma\tau\lambda)$ gives the same bounds with $\varepsilon R^{-100}$ noise. The result concerns the intrinsic central blocks of the intertwiner algebra, which can be larger than individual indecomposable summands.

For exact rational raw input, this center condition is deterministically recognizable in polynomial bit time. Compute $L,\Pi,C,\Pi_Z,G$ exactly by rational kernel bases, rational Gram inverses and commutators. Test positive definiteness of the trace form on the center by rational elimination. A nilpotent central element gives trace square zero. A finite-dimensional commutative reduced real algebra splits into copies of $\mathbb R$ and $\mathbb C$, and an imaginary unit in a complex component gives negative trace square on the nonzero corresponding representation. Thus the test recognizes precisely a split, reduced center. To get rational lower spectral bounds, a positive semidefinite rational Gram matrix of rank $r>0$ has nonzero eigenvalue product $b$ equal, up to sign, to its lowest nonzero characteristic coefficient. If $M\ge1$ bounds the norm then its smallest positive eigenvalue is at least $b/M^{r-1}$. These bounds have polynomial bit length. Thus exact input needs no supplied hidden frames or condition parameters for this more general applicability test and arbitrary-accuracy reconstruction.

## Comparisons and use

When every $|I_a|=1$, the basic tensor format coincides with the full-column two-factor and pairwise independent third-factor setting of classical simultaneous diagonalization. Robust two-contraction algorithms for this setting precede this result. The present proof works with the whole slice family through a common nullspace and uses its center to handle an arbitrary repeated profile as one canonical block. Error-controlled simultaneous block diagonalization by commutant calculations also has precedent for matrix *-algebras. The quantitative calculation here uses a left–right intertwiner algebra with general oblique hidden coordinates and a positive trace form after taking the center. Publication priority for this exact statement is unestablished. [Leurgans–Ross–Abel](https://doi.org/10.1137/0614071) · [Bhaskara–Charikar–Vijayaraghavan, robust uniqueness](https://arxiv.org/abs/1304.8087) · [Maehara–Murota](https://www.keisu.t.u-tokyo.ac.jp/data/2009/METR09-53.pdf)

The certified projector replacement is a complexity improvement over the direct binomial-tail evaluation used in the earlier noisy channel proof. That construction uses a polynomial degree bound quadratic in the inverse rescaled gap. The rounding scheme above uses only logarithmically many matrix iterations in the inverse gap, and accommodates binary exponentially small separations. The claim is specific to that implementation comparison. There is no measured speed advantage here over optimized tensor solvers. The explicit center construction uses large linear operators, and the worst-case guaranteed noise tolerance is conservative. The proof does give a constructive broad class where stable recovery is possible from raw data without hidden frames.

The federated review included existing spectral projection and Davis–Kahan interfaces and commutant catalog entries. The proof reuses the common spectral partition idea from the earlier channel construction and the linear intertwiner perspective from the tensor-isomorphism work. All arguments here are informal. [Earlier noisy Choi recovery](https://github.com/Dugongue/MathProofs/blob/main/FourIsomorphismResearchBets/QUANTUM.md)

A [floating-point control](check_noise.py) ran six nonorthogonal cases with all individual slices singular and the coefficient rows (1,0), (0,1), (1,1). It tested block multiplicities (1,1,1) and (2,1,3). At added Frobenius noise 1e-7, the worst paired projector error was 8.68e-8. These examples use observed conditioning and do not test the conservative theorem threshold or compare production runtimes.
