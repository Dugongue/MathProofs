# A single reference probe for an explicit finite unitary action

## GP-0976

Let a finite group $G$ of order $N$ be supplied by its multiplication table together with all matrices of a unitary representation $\rho:G\to U(d)$. An unknown operation applies $\rho(g)$ for one fixed $g$. Its operationally identifiable output is the coset $gK$, where $K=\{h\colon \rho(h)\text{ is scalar}\}$. There is a deterministic polynomial-bit construction of one ancillary-free input ray distinguishing all these cosets exactly if the matrices have Gaussian-rational entries. With a $d$-dimensional reference register, one probe also has a uniform inverse-polynomial pairwise fidelity gap for an arbitrary unitary representation of the finite group. Copies of this one probe give recovery with error probability at most $\eta$ in polynomial time, assuming polynomial-time preparation of the given dense matrices to requested precision. This specifies a chosen-input oracle model for the transporter.

### Exact ancillary-free construction

Let $v(t)=(1,t,\ldots,t^{d-1})^\mathsf T$ for an integer $t$. For each non-scalar $\rho(h)$, some coordinate of $v(t)\wedge\rho(h)v(t)$ is a nonzero polynomial of degree at most $2d-2$. Otherwise every $v(t)$ for real $t$ is an eigenvector. The matrix has only finitely many eigenvalues, so one eigenspace would contain infinitely many $v(t)$. Any $d$ of those with distinct $t$ form a Vandermonde basis, which would force a scalar matrix.

The union over non-scalar matrices has at most $2(d-1)N$ bad parameters. Test the integers from zero through $2(d-1)N$ by exact arithmetic, and use the first passing vector. Its unnormalized coordinates have polynomial bit length. Comparing two transformed rays reduces to the scalar criterion for their relative element. On an exact numerical ray from the group orbit, all cosets can be distinguished by enumeration and exact proportionality tests. When the representation has only scalar matrices, $K=G$ and every probe suffices.

### Uniform gap with a reference register

Use the maximally entangled unit vector $\Phi=d^{-1/2}\sum_{i=1}^d e_i\otimes e_i$. The inner product of the two output states for $g$ and $h$ is $d^{-1}\operatorname{tr}(\rho(g^{-1}h))$. If $gK\ne hK$ and the relative group element has order $m\le N$, the matrix has two distinct eigenvalues $\lambda_i,\lambda_j$ among the $m$-th roots of unity. In particular $|\lambda_i-\lambda_j|\ge 2\sin(\pi/m)\ge4/N$. The identity
$$
1-\left|d^{-1}\sum_i\lambda_i\right|^2
=d^{-2}\sum_{i<j}|\lambda_i-\lambda_j|^2
$$
proves a squared-fidelity gap of at least $16/(d^2N^2)$. The bound concerns distinct cosets, for which $d,N\ge2$.

To use it, for each distinct coset prepare the corresponding candidate probe output and perform independent swap tests against fresh copies of the unknown output. On the correct candidate an ideal test always accepts. On an incorrect candidate it rejects with probability at least $8/(d^2N^2)$. With $O(d^2N^2\log(N/\eta))$ copies per candidate, the union bound gives the desired error probability. Polynomial-precision implementation preserves this conclusion, for example by budgeting total trace-norm error at most $\eta/2$ over the polynomial number of preparations and tests and using $\eta/2$ in the ideal bound. The exhaustive comparison gives polynomial time in the explicit group and representation sizes. Testing scalar matrices and computing their cosets can be done by exact table arithmetic when matrix entries are supplied exactly. For approximate representations with a promise of a genuine finite-group action, normalized trace comparisons distinguish scalar from nonscalar relative matrices using the same gap.

A scalar multiplies every pure output by a phase, also with a reference register. Thus the projective kernel is the exact identification obstruction, while one probe is sufficient to resolve the entire quotient. The reference-state identity is standard in unitary discrimination. The finite-order bound supplies a uniform quantitative gap, and the Vandermonde argument gives the deterministic ancillary-free construction. [Quantum state isomorphism for groups](https://arxiv.org/abs/2605.12615) · [Unitary discrimination with entanglement](https://wordpress.qubit.it/wp-content/uploads/publications-dariano/entangl_meas.pdf)
