# Noise-robust graph recovery from isospectral quantum channels

**Theorem.** The rational channel construction in the earlier isospectral proof has an inverse-polynomial gap for approximate equivalence under independent unitary changes of input and output bases. It retains both fixed spectra, strict positivity of the Choi states, linear invertibility, and entanglement breaking. With distance to depolarizing less than $1/n$, nonisomorphic $n$-vertex graphs give channel orbits separated by $\Omega(n^{-6})$ in normalized Choi operator norm and in diamond norm. Given a unitary pair with Choi error below the gap, rounding its entries recovers an actual graph isomorphism.

There is also a reconstruction algorithm. For explicit Gaussian-rational Hermitian input promised to be sufficiently close in operator norm to either locally rotated Choi template, a deterministic algorithm extracts its graph up to isomorphism in polynomial bit time. The allowed error is inverse polynomial. The two bases are unknown and no approximate transporter is supplied.

## 1. Templates and readout using only off-diagonal entries

Use the earlier marked matrix $K_G$ on $d=3n^2$ coordinates. Each vertex has three anchors, and each unordered vertex pair has six ports. The negative marker edges on an anchor triple have magnitudes $1000n,2000n,4000n$. The marks linking each port to the $+$ and $-$ anchors of its two endpoints have magnitudes $20+w_r,20-w_r$, where $w=(-5,-3,-1,1,3,5)$. The pair block adds $b_t b_t^{\mathsf T}$, where $b_0=(1,-1,-1,1,0,0)$, $b_1=(1,-1,0,0,-1,1)$, and $t$ is the graph edge bit. The remaining entries follow the earlier Laplacian construction. All entries are integers of magnitude at most $M=10^4 n$, diagonal entries are at least 80, and off-diagonal entries are at most one. [Original channel construction](https://github.com/Dugongue/MathProofs/blob/main/FurtherIsomorphismTransfers/QUANTUM.md)

The **off-diagonal** entries determine the graph and every simultaneous coordinate permutation of its encoding. Keep the entries with magnitudes exceeding $25$. These form exactly the marked anchor triangles. The three distinct edge weights identify the roles of the vertices in each triangle. Every remaining coordinate has marks of magnitudes between $15$ and $25$ to its endpoint anchors. These marks recover its unordered pair and its port index. The entry between ports 1 and 3 of that pair equals $-1$ for $b_0$ and $0$ for $b_1$, so it recovers the edge bit. Conversely a permutation of graph vertices induces the marked coordinate permutation. This readout avoids the upper spectral block entirely.

Set $\tau=1/n$, $e=\tau/(4dM)$, and $s=\tau/(8d)$. Define

$$
 \rho_G=bI+\alpha\,\operatorname{diag}((K_G)_{ij})+s|\Omega\rangle\langle\Omega|,
 \qquad b=(1-s)/d^2,\quad \alpha=(1-s)e/d .
$$

This is the normalized Choi state of the earlier channel, with the parameter $\tau$ changed from $2^{-n}$ to $1/n$. The original bounds on positivity, norm distance, and separability hold for any $0<\tau\le1$. For example the diagonal classical part has entries at least $(1-s)(1-\tau/4)/d^2$, which exceeds $s/d$. Thus it contains the diagonal term of a separable isotropic state that absorbs the rank-one addition. The marker matrix is positive semidefinite and has row sums zero, so the identity mixture is linearly invertible. The earlier pairwise orthogonal reflections fix the marker and preserve both spectra for every common parameter choice. In their displayed bases the channels are self-adjoint, unital, and trace-preserving. The norm-distance bound to depolarizing remains strictly less than $\tau$. [Entanglement-breaking Choi criterion](https://arxiv.org/abs/quant-ph/0302031)

Write $D=\operatorname{span}\{|ii\rangle:1\le i\le d\}$. Its eigenvalues are at least $b+80\alpha$, since the added rank-one term is positive and supported there. Each $|ij\rangle$ with $i\ne j$ is an eigenvector with eigenvalue $b+\alpha(K_G)_{ij}\le b+\alpha$. Thus the high and low spectral intervals are separated by at least $79\alpha$.

## 2. A gap in operator norm, and rounding a near-transporter

We use the following elementary spectral-subspace estimate. Let $Q$ be an invariant orthogonal projector for a Hermitian matrix $A$, and $P$ one for a Hermitian matrix $B$. If $A$ on the range of $Q$ has spectrum at least $c+g$ and $B$ on the perpendicular complement of $P$ has spectrum at most $c$, then

$$
 \|(I-P)Q\|_{\rm op}\le\|A-B\|_{\rm op}/g .
$$

Indeed $X=(I-P)Q$, viewed between these two spaces, satisfies $B_{\rm low}X-XA_{\rm high}=(I-P)(B-A)Q$. Integrating the derivative of $e^{t(B_{\rm low}-cI)}Xe^{-t(A_{\rm high}-cI)}$ from zero to infinity proves the bound. The factors have norms at most one and $e^{-tg}$, respectively. This is the separated-spectrum form of the Davis–Kahan estimate. [Davis–Kahan](https://doi.org/10.1137/0707001)

Let $\delta=\|\rho_H-(U\otimes V)\rho_G(U\otimes V)^*\|_{\rm op}$. Write $r=\delta/(79\alpha)$. The high projector for the rotated template is the projector onto $(U\otimes V)D$. Apply the estimate with the target high space $D$. For every column $i$ it gives

$$
 \sum_a |U_{ai}|^2 |V_{ai}|^2\ge 1-r^2.
$$

Let $\pi(i)$ maximize the squared moduli of column $i$ of $U$. The maximum is at least $1-r^2$, since the squared moduli in the other matrix's column sum to one. The mass outside this maximizing row in the first column distribution is at most $r^2$. Therefore the probability in the same row for $V$ is at least $1-2r^2$. If $\delta<\alpha/2$, each maximum exceeds $1/2$, so the maximizing rows form a permutation by the unit row norms. They are also the unique maxima for $V$.

Now take $i\ne j$. The two vectors $(U\otimes V)|ij\rangle$ and $|\pi(i)\pi(j)\rangle$ are individual eigenvectors of the two matrices being compared. The absolute value of their overlap is at least $\sqrt{(1-r^2)(1-2r^2)}>1/2$. Taking their matrix element of the difference yields

$$
 \alpha\, |(K_G)_{ij}-(K_H)_{\pi(i)\pi(j)}|\,
 |\langle \pi(i)\pi(j)|(U\otimes V)|ij\rangle|\le\delta.
$$

By integrality, $\delta<\alpha/2$ forces equality of these two matrix entries for every $i\ne j$. The off-diagonal readout proves that $\pi$ encodes a graph isomorphism. Conversely, any graph isomorphism gives an exact channel isomorphism. Thus the orbit distance is zero on graph-isomorphic pairs and at least $\alpha/2$ otherwise. Here $\alpha=(1-s)/(360000\,n^6)$. The bound also applies in Choi Frobenius norm and to diamond distance, since evaluating the difference of the channels on the normalized maximally entangled state gives their Choi difference, whose trace norm dominates its operator norm.

The construction gives a deterministic polynomial-time reduction from GI to distinguishing orbit distance zero from at least $\alpha/2$. Under unknown basis changes and perturbations of each input by at most $\alpha/16$ in Choi operator norm, the corresponding yes and no distances are at most $\alpha/8$ and at least $3\alpha/8$. This follows from unitary invariance and the triangle inequality. Same-spectrum and self-adjointness claims concern the noiseless displayed templates. The argument compares data given by their explicit Choi matrices.

## 3. Deterministic reconstruction in unknown bases

Use the stronger noise promise
$$
 \|H-\rho^*\|_{\rm op}\le\nu,\qquad \nu=\frac{\alpha^2}{10^9d^6},
$$
where $\rho^*$ is a local-unitary transform of some $\rho_G$. The high space of $\rho^*$ is $S=\operatorname{span}\{x_i\otimes y_i\}$ for two unknown orthonormal bases. By the spectral gap and Weyl's inequality, the spectral projector of $H$ above $b+40\alpha$ has rank $d$. The subspace estimate in both directions bounds its distance from $P_S$ by $2\nu/(79\alpha-\nu)$. Compute a rational Hermitian approximation $\widetilde P$ to that projector within $\nu/(10\alpha)$ in operator norm. Thus $\|\widetilde P-P_S\|_{\rm op}\le\nu/\alpha$.

For each member $A$ of the Hermitian coordinate basis consisting of the diagonal units and the real and imaginary off-diagonal pairs, compute
$$
 \widetilde B(A)=\operatorname{Tr}_2((I\otimes A)\widetilde P).
$$
This is Hermitian by cyclicity within the traced factor. On the true high projector the result is $B(A)=\sum_i (y_i^*Ay_i)x_i x_i^*$. Each coordinate matrix has operator norm one. The operator norm of the error is at most $e=d\nu/\alpha$, by summing the $d$ diagonal blocks in the partial trace.

Individual $B(A)$ may have repeated eigenvalues. We use their entire family of spectral cuts. Put $h=1/(10d^2)$. For each $A$, compute the ordered eigenvalues of $\widetilde B(A)$, with multiplicity, to rational error at most $h/100$. Cut at the midpoint of each consecutive approximated gap exceeding $h$. Weyl's inequality shows that every cut is at spectral distance at least $h/3$ from both matrices. Between successive cuts the true eigenvalues have diameter at most $d(h+2h/100+2e)<1/d$. For every $i\ne j$, some coordinate matrix has $|y_i^*Ay_i-y_j^*Ay_j|\ge 1/d$: the difference of the two rank-one projections has Frobenius norm $\sqrt2$, and the coordinate basis is orthogonal with norms at least one. So the common refinement of all the true spectral partitions consists of the individual $x_i x_i^*$.

Use differences of two half-line projectors to compute the interval projectors for the observed cuts. Comparing each half-line projector with its true counterpart, the two-sided subspace estimate gives an error of at most $3e/h$, since the spectra on opposite sides of each cut are separated by at least $2h/3$. Thus each rational interval projector approximates its true counterpart to operator error at most
$$
 \eta=8e/h+\alpha/(10^6d^4),
$$
where the last term provides for rational evaluation. In the true basis all interval projectors commute. For an ordered product of at most $d^2$ approximate projectors, telescoping gives an error at most $d^2\eta(1+\eta)^{d^2}<2d^2\eta<\kappa$ from the corresponding true product, where $\kappa=\alpha/(10^5d)$.

Start with the identity and successively multiply every retained product by each spectral interval projector for the next coordinate matrix. Keep the product exactly when the real part of its trace exceeds $1/2$. The true product is an intersection projection of integral rank and the trace error is at most $d\kappa<1/4$. Hence this test keeps exactly the nonempty intersections, and there are at most $d$ retained products at each stage. The final $d$ products approximate the individual $x_i x_i^*$. Perform the symmetric procedure on the other factor to approximate the $y_i y_i^*$. No simultaneous diagonalization of the noisy matrices is required.

Pair the recovered endpoints by evaluating the real part of the trace of $\widetilde P$ against each product of recovered endpoint matrices. The exact template values are zero or one. In fact each approximate endpoint matrix has trace-norm error at most $d\kappa$, and each true endpoint matrix has trace norm one. A tensor product of the two approximate matrices has trace-norm error at most $3d\kappa$ and trace norm at most two. The trace evaluation error is consequently at most $2\nu/\alpha+3d\kappa<1/4$. Thus a threshold of $1/2$ gives the pairing. For every unmatched cell, evaluate the real part of the trace of $H$ against that tensor product. Its true value is $b+\alpha(K_G)_{ij}$, and the error is at most $2\nu+3d\kappa<\alpha/16$ because $\|\rho^*\|_{\rm op}\le1$. Rounding $(\text{value}-b)/\alpha$ recovers the exact off-diagonal entries. The readout in Section 1 gives an actual graph. The argument also applies to Hermitian perturbations that fail positivity.

For the bit bound, compute exact characteristic polynomials of Gaussian-rational Hermitian matrices, which have rational coefficients. Squarefree decomposition and certified real-root isolation give the required ordered brackets with multiplicities in polynomial bit time. To compute a spectral projector to the stated inverse-polynomial operator tolerance, rescale the known spectral interval to $[0,1]$ and replace its threshold step function by the binomial-tail polynomial
$$
 \sum_{j\ge \lceil Lt\rceil}\binom Lj x^j(1-x)^{L-j},
$$
where $t$ is the rescaled threshold. At spectral distance $\Delta$ from it and with $L\ge 2/\Delta$, the operator error is exponentially small in $L\Delta^2$, by binomial concentration at each eigenvalue. The lower bound on $L$ allows for rounding $Lt$. All spectral ranges have polynomial magnitude and all threshold gaps are inverse polynomial. Therefore polynomial degrees suffice. Exact evaluation on rational matrices has polynomial bit length, for instance by accounting for powers of a common denominator and the binomial coefficients. Products in the refinement have at most $d^2$ factors; their entry bit lengths are polynomial by the same denominator accounting. This proves the deterministic polynomial-bit-time claim. [Certified real-root refinement](https://arxiv.org/abs/1104.1362)

For two promised noisy inputs, extract the two graphs independently and compare them by GI. At Choi orbit-distance threshold $\alpha/4$, this gives a deterministic polynomial-time many-one reduction to GI on the explicit promise. The deterministic hardness direction already holds on the exact templates. The reconstruction noise tolerance $\nu$ is smaller than the geometric gap tolerance used in Section 2. The matrix inputs are given explicitly.

## Scope and prior work

This proof reuses the earlier exact channel templates and introduces two quantitative steps. The high subspace forces a common near-permutation, and comparison of individual low-space eigenvectors reads the discrete off-diagonal labels with one full unit of spectral resolution. For the reverse direction, the common spectral refinement of coordinate partial traces recovers stable bases without guessing the local unitaries. The literature includes approximate orbit distance under orthogonal and unitary actions and exact GI reductions to unitary isomorphism. Priority for the stated two-spectrum, noisy Choi formulation is unestablished. The proof is informal. [Chizewer–Everett–Mithal–Qiao](https://arxiv.org/abs/2603.27128) · [Classical-group tensor isomorphism](https://arxiv.org/abs/2306.03135)

The NumPy control [check_quantum_recovery.py](check_quantum_recovery.py) recovered all three tested graphs, of orders two and three, from dense independent local-unitary scramblings with added Hermitian noise of Frobenius norm $\alpha/1000$. It uses floating-point spectral projectors and verifies the decoded graph. The bit-time proof uses the rational projector algorithm above. The control measures neither a worst-case noise tolerance nor a runtime improvement.

Targeted federated searches found Choi inversion in PhysLean, partial trace definitions in the OpenAI matrix library, and Hermitian spectral projectors in the statistical learning and quantum sources. The proof uses these interfaces at the mathematical level.
