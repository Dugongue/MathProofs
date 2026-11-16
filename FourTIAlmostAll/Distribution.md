# Short-column mixing for a crossed inverse contraction

This is an informal proof over $\mathbb F_2$. The random model is a uniform balanced 4-tensor conditioned on invertibility of its $12\mid 34$ flattening. Write its flattening as $F=(T_{aj,kl})$, let $S=F^{-T}$, and use $T_{aj}$ and $S_{aj}$ also for the matrices in indices $k,l$. Define a block matrix $C$ on modes 2 and 3 and a covariant $E$ on mode 3 by
$$
 C_{j,s}=\sum_a T_{aj}S_{as}^{\mathsf T},\qquad E=\operatorname{Tr}_2(C^2).
$$
Here $\operatorname{Tr}_2$ is partial trace over the mode-2 blocks. The identities follow from contraction of a tensor and its dual, so $E$ changes by conjugation on mode 3 under ordinary tensor isomorphism. Relabeling gives an operator on any chosen mode, using the same invertible flattening with its sides exchanged as needed. The scalar trace is fixed: $\operatorname{tr} E=\operatorname{tr} C^2=(\operatorname{tr}C)^2=n^2\bmod 2$.

**Theorem.** For every fixed subspace $W\le \mathbb F_2^n$ of dimension at most $m_0=\lfloor 10^{-5} n\rfloor$, the law of $E|_W:W\to\mathbb F_2^n$ has total variation distance $O(2^{-n^2/120})$ from uniform. The bound is uniform over $W$. In addition, for irreducible polynomials $f$ of degree $d\le m_0/2$, the random quantity
$$
 \sum_{f\colon \deg f\le m_0/2,\; m_f(E)\ge 2} d\, m_f(E)^2
$$
is $o(\log n)$ in probability, where $m_f(E)$ is the exponent of $f$ in the characteristic polynomial. Both statements concern the operator above rather than a family of operators with independently chosen or sampled entries. The repeated-primary conclusion persists after conditioning on invertibility of all three splitting flattenings, since that conditioning has probability bounded below. The quantitative total variation claim is for conditioning on the one chosen flattening only.

## From a shear to a quadratic form

Take disjoint sets $\mathcal A,\mathcal B$ of mode-1 labels of sizes $a=b=\lfloor n/5\rfloor$. Fix a mode-2 label $s_0$ and a disjoint set $J$ of $k$ other labels. Starting with an independent uniform invertible $F_0$, draw $X$ with independent uniform allowed entries $X_{(h,r),(\ell,s_0)}$ for $h\in\mathcal A,\ell\in\mathcal B,r\in J$, and all other entries zero. Then $X^2=0$, so $F=(I+X)F_0$ is uniform invertible and $S=(I+X^{\mathsf T})S_0$ with $S_0=F_0^{-T}$.

Changes to the $T$ factors in $C_{j,s}$ occur at first index $a\in\mathcal A$ and only when $j\in J$. Changes to the $S$ factors occur at first index $a\in\mathcal B$ and only when $s=s_0$. The block-matrix increment $D=C-C_0$ is therefore linear in $X$, with support in block rows $J$ and block column $s_0$. Set $U_\ell=T^0_{\ell,s_0}$ and $V_{h,t}=(S^0_{h,t})^{\mathsf T}$. In the $J\times J$ principal block,
$$
 D_{r,s}=\sum_{h,\ell} X_{(h,r),(\ell,s_0)}\,U_\ell V_{h,s}.
$$
The variables in distinct rows $r\in J$ are independent. Also $D_{s_0,s_0}=\sum_{r\in J}\sum_{h,\ell}X_{(h,r),(\ell,s_0)}U_\ell V_{h,r}$, and $D_{s_0,r}=0$ for $r\in J$. Every product $U_\ell V_{h,s}$ is traceless by the dual row pairing and $h\ne\ell$. In the partial trace of $D^2$ only the $J\times J$ principal block and $D_{s_0,s_0}$ contribute.

For a phase $P\in M_n(\mathbb F_2)$, $\operatorname{tr}(P E)$ has degree at most two in the shear variables. Set $r_P=\operatorname{rank}\operatorname{ad}_P$, where $\operatorname{ad}_P(M)=PM-MP$, and let $r'_P$ be the rank of the alternating form
$$
 B_P(A,B)=\operatorname{tr}((PA-AP)B)
$$
on the traceless matrices. The trace pairing on $M_n$ is perfect, so $r_P-2\le r'_P\le r_P$. Write $Q_P$ for the traceless space modulo the radical of this alternating form. If $P$ is nonscalar, there is $v$ with $Pv$ linearly independent of $v$. Restrict $\operatorname{ad}_P$ to rank-one matrices $vf$ as the covector $f$ varies and project the output modulo matrices whose image is in the line $\mathbb F_2 v$. The induced map $f\mapsto (Pv)f$ in that quotient is injective, hence $r_P\ge n$. If $P$ has rank at most $m$, left and right multiplication each have rank at most $nm$ as maps of the matrix space, so $r'_P\le 2nm$.

## Surjectivity for a row of shear variables

Suppose $k r'_P\le ab/2$. With probability
$$
 1-O(2^{k r'_P-ab}+2^{a k+b-n^2}+2^{b-n^2})
$$
over $F_0$, the map from the $ab$ variables in a row of the shear to the $k$ coordinates $D_{r,s}\bmod\operatorname{rad} B_P$ in $Q_P^k$ is surjective. The map has the same coefficients for all $r\in J$.

The selected rows $U_\ell$ are a uniform ordered independent list in the $n^2$-dimensional matrix space. Conditional on this list, the selected dual rows $V_{h,s}$ for $h\in\mathcal A,s\in J$ are a uniform ordered independent list in the common trace-orthogonal space $U^\perp$. Indeed, right multiplication of $F_0$ by an invertible map fixing its selected rows preserves the conditional distribution. On the annihilator of their span these invertible maps induce every invertible transformation. The dual rows are required to lie in that annihilator because their original row labels are distinct from the selected labels. To compare with independent sampling, first draw the $U_\ell$ independently and uniformly and then, given $U$, draw the $V_{h,s}$ independently and uniformly in $U^\perp$. The independent-list conditioning alters event probabilities by at most $O(2^{b-n^2}+2^{a k+b-n^2})$ by the sequential rank test.

A fixed nonzero dual label on $Q_P^k$ is represented by $Z_s\in M_n(\mathbb F_2)$ for $s\in J$ via the trace pairing. For at least one $s$ we can choose a nonscalar representative $Z=Z_s$, because the annihilator of the traceless space consists exactly of scalar matrices. Failure at that label imposes, for every $h,\ell$, the constraints
$$
 \sum_{s\in J}\operatorname{tr}(Z_s U_\ell V_{h,s})=0 .
$$
Given $U$, the $b$ constraints for each $h$ have rank at least the dimension of the span of $ZU_\ell$ modulo $\operatorname{span}\{U_\ell\}$, by projecting their coefficient vectors to the selected $s$-coordinate. Write this rank lower bound as $b-\delta$. To bound the deficiency, choose a column $u$ and a row $v$ such that $v u=0$ and $vZu=1$, possible since $Z$ is nonscalar. For independent uniform $U_\ell$, expose their columns modulo $\mathbb F_2 u$. Now each row $vU_\ell$ is fixed, while the rows $vZU_\ell$ are uniform and mutually independent. Their span modulo $\operatorname{span}\{vU_\ell\}$ is a lower bound on the dimension of the span of $ZU_\ell$ modulo the span of the $U_\ell$. The row quotient has dimension at least $n-b$. The probability that a uniform linear map from a $b$-dimensional space to an $N$-dimensional space has kernel of dimension at least $j$ is at most $4\cdot 2^{-j(N-b+j)}$, by a union bound over its $j$-dimensional subspaces using the Gaussian binomial coefficient. It follows that $\Pr(\delta\ge j)\le 4\cdot 2^{-j(n-2b+j)}$.

The $a$ groups of dual rows indexed by $h$ are conditionally independent in the approximation. The probability that all the constraints for this fixed label hold is therefore bounded by
$$
 2^{-ab}\mathbb E[2^{a\delta}]
 \le 2^{-ab}\left(1+4\sum_{j\ge1} 2^{-j(n-2b-a+j)}\right)=O(2^{-ab}).
$$
A union bound over the fewer than $2^{k r'_P}$ nonzero labels, and the cost of reverting to independent lists, gives the surjectivity claim.

## Fourier estimate

On the surjectivity event the $J\times J$ block coordinates jointly span $Q_P^{k\times k}$. The bilinear form of the quadratic shear phase from this principal block is
$$
 (D,D')\ \longmapsto\ \sum_{r,s\in J} B_P(D_{r,s},D'_{s,r}).
$$
This pairs each coordinate with its transpose-index coordinate through the nondegenerate form on $Q_P$, so it has rank $k^2 r'_P$ after pullback along the surjection. The contribution from $D_{s_0,s_0}^2$ has rank at most $r'_P$, by tracelessness and the expression $B_P(D_{s_0,s_0},D'_{s_0,s_0})$ for its bilinear form. The full form has rank at least $(k^2-1)r'_P$. Over $\mathbb F_2$, differencing a quadratic phase of polarized rank $s$ bounds its absolute mean by $2^{-s/2}$, including any linear terms. Consequently
$$
 \big|\mathbb E (-1)^{\operatorname{tr}(PE)}\big|
 \le O(2^{k r'_P-ab}+2^{a k+b-n^2}+2^{b-n^2})
       +2^{-(k^2-1)r'_P/2}.
$$

For a nonzero phase of rank at most $m_0$, $P$ is nonscalar and $r'_P\le 2 n m_0$. Take $k=\lfloor ab/(2r'_P)\rfloor$. For all sufficiently large $n$, $4\le k\le n-1$, using $n-2\le r'_P\le 2 n m_0$ and $ab\ge n^2/36$. The first three terms have exponent at most $-n^2/72$, for sufficiently large $n$. Also $(k^2-1)r'_P\ge (ab)^2/(32 r'_P)\ge n^3/(82944 m_0)$, which is more than sufficient for an $O(2^{-n^2/100})$ bound on the entire absolute mean. Every nontrivial character of the restriction to a fixed $W$ arises from a nonzero phase of rank at most $\dim W$: the linear functional is a sum of evaluations $\ell_i(Ew_i)$ on a basis of $W$, represented by $\sum_i w_i\ell_i$. Parseval and Cauchy–Schwarz bound its total variation distance from uniform by one half the square root of the sum of squared nontrivial Fourier coefficients. There are $2^{n\dim W}-1$ such coefficients. This gives the claimed $O(2^{-n^2/120})$ bound.

## Extension to all low-commutator phases

The estimate for the shear applies directly to every nonscalar $P$ with $r_P=\operatorname{rank}\operatorname{ad}_P\le 10^{-5}n^2$, regardless of its rank as a matrix. Indeed $n-2\le r'_P\le r_P$ and the same choice $k=\lfloor ab/(2r'_P)\rfloor$ gives the same $O(2^{-n^2/100})$ bound. One can then sum the squared Fourier coefficients over the whole low-commutator range.

Over the algebraic closure, let $g$ be the greatest geometric multiplicity of an eigenvalue of $P$. Write $c_{\lambda,j}$ for the $j$-th column length of the Jordan partition for eigenvalue $\lambda$. The centralizer of $P$ has dimension $\sum_{\lambda,j} c_{\lambda,j}^2$, since each pair of Jordan blocks of the same eigenvalue contributes the minimum of their sizes and pairs at distinct eigenvalues contribute zero. Every column length is at most $g$, and their sum is $n$, so $n^2-r_P\le gn$. Consequently $g\ge n-r_P/n > n/2$. This uniquely large eigenspace is sent to itself under Frobenius, and hence its eigenvalue $\lambda$ is in $\mathbb F_2$. It follows that $\operatorname{rank}(P-\lambda I)\le r_P/n$. The number of $n$-by-$n$ matrices over $\mathbb F_2$ of rank at most $D$ is at most $2^{2nD}$, because every such matrix factors as an $n$-by-$D$ matrix times a $D$-by-$n$ matrix. Thus the nonzero low-commutator range has at most $2^{1+2\cdot 10^{-5}n^2}$ phases and their squared Fourier coefficients sum to $2^{-\Omega(n^2)}$.

For the trace hyperplane, the scalar phases $0,I$ coincide with those of the uniform law there. Accordingly, an exponentially small contribution of the high-commutator phases to the sum of squared Fourier coefficients would give exponential total variation mixing for the entire operator on that hyperplane. The argument above proves the low-commutator contribution.

## Consequences for repeated small-degree factors

For an irreducible $f$ of degree $d$ and $j\ge2$, write $k=dj\le m_0$. If $m_f(E)\ge j$, then $E$ has an invariant $k$-dimensional subspace on which its characteristic polynomial is $f^j$. This follows by the elementary-divisor decomposition, taking a subchain of the $f$-power filtration of each cyclic summand until their lengths total $j$. For fixed $W$ of dimension $k$, the restriction law agrees up to $O(2^{-n^2/120})$ in total variation with that of a uniform linear map $W\to\mathbb F_2^n$. The number of operators on $W$ with characteristic polynomial $f^j$ is
$$
 |\mathrm{GL}_k(2)|\,\frac{2^{-dj}}{\prod_{i=1}^j(1-2^{-di})}.
$$
One way to see the formula is to sum inverse centralizer orders over the partitions of $j$. An $f$-primary module with partition $\lambda$ has the same automorphism order as the corresponding nilpotent module of type $\lambda$ over $\mathbb F_{2^d}$, by the filtrations of the cyclic summands. The sum of the inverse centralizer orders equals the number $2^{d(j^2-j)}$ of nilpotent $j$-by-$j$ matrices over $\mathbb F_{2^d}$ divided by $|\mathrm{GL}_j(2^d)|$. This is also the uniform-matrix primary count used in the existing fixed-field proof.

Sum over $W$ using the Gaussian binomial coefficient. The expected number of such subspaces from the uniform main term is at most $4\cdot 2^{-dj}$: the identity ${n\brack k}_2 |\mathrm{GL}_k(2)|=\prod_{i=0}^{k-1}(2^n-2^i)$ cancels the denominator $2^{nk}$ from the uniform law, up to a factor at most one, and $\prod_{i\ge1}(1-2^{-i})>1/4$. The accumulated error is $2^{-\Omega(n^2)}$ since there are at most $4\cdot 2^{nk}$ subspaces and $k\le m_0$. Thus
$$
 \Pr[m_f(E)\ge j]\le 4\cdot 2^{-dj}+2^{-\Omega(n^2)}.
$$
The truncated weighted tail $\sum_f\sum_{2\le j\le m_0/d}2dj\,1_{\{m_f(E)\ge j\}}$ has bounded expectation. Indeed there are at most $2^d$ polynomials of degree $d$, the exponential terms sum to $O(1)$, and summing the displayed errors preserves exponential decay. For $d\le m_0/2$, set $j_d=\lfloor m_0/d\rfloor\ge2$. If $m_f(E)d>m_0$ then $m_f(E)\ge j_d$, and $d(j_d-1)\ge m_0/3$. A union bound over these $d$ and $f$ shows that the probability of any such overflow is $2^{-\Omega(n)}$. On the event of no overflow the truncated sum dominates the theorem's repeated-primary weight for factors of degree at most $m_0/2$. The weight divided by $\log n$ therefore tends to zero in probability by Markov's inequality. If all three balanced cuts are required to be invertible, asymptotic independence of their invertibility bounds the additional conditioning probability below, preserving this conclusion.

## Low phases over every fixed finite field

Fix a finite field $K$ of order $q$, and fix a nontrivial additive character $\chi:K\to\mathbb C^\times$. The flattening and covariant above now use $K$. For any $P\in M_n(K)$, write
$$
 L_P(M)=PM+MP,\qquad r_P=\operatorname{rank}_K L_P.
$$
The polar form of $\operatorname{tr}(PE)$ is computed with $B_P(A,B)=\operatorname{tr}((PA+AP)B)$. In characteristic two the plus sign is the commutator. In odd characteristic this is a symmetric bilinear form. Let $r'_P$ be its rank on the traceless subspace. Perfectness of the matrix trace pairing again gives $r_P-2\le r'_P\le r_P$. If $P$ is nonscalar the same $u,Pu$ projection proof gives $r_P\ge n$. In odd characteristic any nonzero scalar has $r_P=n^2$, while in characteristic two scalars have $r_P=0$. Hence $r_P\ge n$ throughout the nonzero-polar-rank range.

There is one common full shear space for the estimates. Reserve a mode-2 label $s_0$. Partition the mode-1 labels into three sets containing disjoint high and low sets, each of size $a=b=\lfloor n/5\rfloor$. Allow the shear to add arbitrary high-from-low rows of the flattening with these mode-1 labels, with all mode-2 row and column labels initially permitted. All such matrices $X$ have square zero. Restrict to high target labels indexed by $J$ in mode 2 and low source labels indexed by $s_0$ to make the low-phase shear. High phases can use a different subspace of the same full shear space, in particular high targets at $s_0$ and low sources outside $s_0$, including smaller mode-1 subsets. Both the full shear and these restrictions leave every dual row with high mode-1 label unchanged.

For the low-phase restriction $F=(I+X)F_0$, we now have $S=(I-X^{\mathsf T})S_0$. The $J\times J$ increment is the same $\sum_{h,\ell} X_{(h,r),(\ell,s_0)} U_\ell V_{h,s}$ as before. The single diagonal correction at $s_0$ gets a minus sign. Its square gives the same polar estimate, and the support and trace-orthogonality arguments are unchanged. The rank and dual-label argument uses the same field-linear trace pairing. For $n\times n$ matrix variables $U_\ell$, one can still choose $v u=0,\ v Z u=1$ for every nonscalar $Z$, by scaling a linear functional after choosing $u,Zu$ independent. Conditional exposure of all columns modulo $K u$ still leaves all $v ZU_\ell$ independently uniform in $K^n$. The kernel-rank deficiency count by Gaussian binomial coefficients over $k$ gives
$$
 \Pr(\delta\ge j)\le 4 q^{-j(n-2b+j)},\quad
 \Pr(\text{a fixed nonzero dual label annihilates the row map})
 \le q^{-ab}\Big(1+4\sum_{j\ge1}q^{-j(n-2b-a+j)}\Big).
$$
The two independent-list costs become $O(q^{a k+b-n^2}+q^{b-n^2})$, where $k=|J|$ denotes the number of shear row groups. Summing dual labels gives row-map failure probability $O(q^{k r'_P-ab}+q^{a k+b-n^2}+q^{b-n^2})$. Its surviving quadratic polar rank is still at least $(k^2-1)r'_P$. For an additive quadratic phase, squaring its mean and differencing kills every direction outside the radical of the polar form. This uses the fact that any nonzero field-linear functional is surjective and hence has zero mean after applying $\chi$. The absolute phase mean is at most $q^{-(k^2-1)r'_P/2}$ on the surjectivity event.

In particular, for $0<r_P\le 10^{-6}n^2$, choose $k=\lfloor ab/(2r'_P)\rfloor$. Eventually $4\le k\le n-1$, and the same estimates prove the bias bound $O(q^{-n^2/100})$. The bound also holds conditional on any event $G$ of probability at least $1/2$ depending only on dual rows in the high mode-1 set. Every such $G$ is preserved under each shear, so the distribution of $F=(I+X)F_0$ conditional on $G$ remains uniform on that event for any allowed shear. The $F_0$-bad-set probability in the Fourier bound is inflated by at most the factor $1/\Pr(G)$, and the pointwise quadratic bound on good $F_0$ is unaffected. This lets the low-phase estimate apply under the same conditioning as the high-phase estimate.

The count of low phases uses intertwiners between $P$ and $-P$. Over an algebraic closure write $c_{\lambda,j}$ for the $j$-th column lengths of the Jordan partitions for $P$, zero for absent eigenvalues. The kernel dimension of $L_P$ equals $\sum_{\lambda,j} c_{\lambda,j}c_{-\lambda,j}$, by counting homomorphisms of Jordan blocks. This sum is at most $\sum_{\lambda,j}c_{\lambda,j}^2$ by $2xy\le x^2+y^2$. The latter is at most $ng$, where $g$ is the greatest geometric eigenvalue multiplicity. Thus $g\ge n-r_P/n>n/2$. The unique eigenvalue with that geometric multiplicity lies in the base field, since the $q$-Frobenius must preserve it. Then $\operatorname{rank}(P-\lambda I)\le r_P/n$. Counting matrices of rank at most $\lfloor 10^{-6} n\rfloor$ by rank factorization and allowing $q$ choices of $\lambda$ bounds the number of phases in the designated range by $q^{1+2\cdot 10^{-6}n^2}$. Their squared Fourier coefficients therefore sum to $q^{-\Omega(n^2)}$, even conditional on the dual-row event $G$ above.

For characteristic two the phases with $r_P=0$ are precisely the scalars and match the uniform law on the affine trace hyperplane $\operatorname{tr}E=(n^2)^2$ in $K$. For odd characteristic $r_P=0$ holds only for the zero phase, which matches the uniform law on all matrices. The remaining high-phase estimate is a separate part of the full distribution theorem.

## Stronger spectral tail once full marginal mixing is available

A stronger recognition rate is available by using the dimension of each actual commutant algebra, instead of bounding it by the square of the whole primary multiplicity. This result is an independent finite-field enumeration lemma. Let $A$ be a uniform matrix over a fixed $\mathbb F_q$, with or without conditioning on a prescribed trace. Write $\lambda_f$ for its $f$-primary partition, $e_f=\deg f$, and
$$
 D_{\mathrm{comm}}(A)=\sum_{f\colon |\lambda_f|\ge2}e_f \sum_j(\lambda'_{f,j})^2.
$$
Then $\mathbb E q^{s D_{\mathrm{comm}}(A)}$ is bounded uniformly in $n$ for every fixed $0<s<1/2$.

For a finite set of distinct irreducibles $f$ and prescribed nonempty types $\lambda_f$, count a subspace on which the restriction has precisely the direct sum of those types. The actual primary spaces witness such a subspace whenever the full matrix has exactly the prescribed types on those primaries. For the uniform matrix law the normalized frame count bounds the probability by the reciprocal automorphism order of that direct sum, which is the product of the reciprocal orders for its primaries. Conditioning on trace costs at most the single factor $q$. To make the bound explicit, for $Q=q^{e_f}$, $\lambda=\lambda_f$, and $S(\lambda)=\sum_j(\lambda'_j)^2$,
$$
 |\operatorname{Aut}_f(\lambda)|=Q^{S(\lambda)}\prod_{d\colon m_d(\lambda)>0}\prod_{i=1}^{m_d(\lambda)}(1-Q^{-i})
 \ge Q^{S(\lambda)}4^{-\sqrt{2|\lambda|}} .
$$
Here $m_d(\lambda)$ counts blocks of size $d$. The commutant dimension $S(\lambda)$ over the coefficient field follows by counting homomorphisms of cyclic summands. The semisimple quotient of its commutant is the product of the matrix algebras acting on the multiplicity space at each different block size. For the invertibility count, one can instead look at the induced map modulo the radical generator on the full nilpotent module. It is block triangular by sizes, because a homomorphism from a shorter cyclic block into a longer one maps into that longer block's radical. The equal-size diagonal blocks vary independently. Surjectivity on the entire module is equivalent to surjectivity modulo the radical generator, by lifting repeatedly until that nilpotent generator vanishes. Thus the fraction of units is exactly the product in the display. There are at most $\sqrt{2|\lambda|}$ distinct positive block sizes, since their sum is bounded by $|\lambda|$.

Expand $q^{sD_{\mathrm{comm}}}$ as the product over $f$ of $1$ plus a term supported on $|\lambda_f|\ge2$, and bound each joint expectation by the frame count above. The result is at most
$$
 q\prod_f\left(1+\sum_{\lambda:\,|\lambda|\ge2}4^{\sqrt{2|\lambda|}}q^{-(1-s)e_f S(\lambda)}\right).
$$
The product is uniformly bounded. There are at most $q^e$ monic irreducibles of each degree $e$, $S(\lambda)\ge|\lambda|$, and the number of partitions of $m$ is $\exp(O(\sqrt m))$. The last bound follows directly from the Euler product evaluated at $x=e^{-1/\sqrt m}$: its logarithm is $\sum_{j\ge1}(j(e^{j/\sqrt m}-1))^{-1}\le\sqrt m\sum_{j\ge1}j^{-2}$, and coefficient extraction using positivity costs $x^{-m}=e^{\sqrt m}$. For $m\ge2$, the exponent $((1-s)m-1)e$ grows at least linearly in $em$, since $s<1/2$. This proves convergence even after the subexponential factors in $m$.

Consequently a commutant enumeration cut off at $D_{\mathrm{comm}}\le K\log_q n$ has rejection probability $O(n^{-sK})$ for a uniform trace-conditioned marginal. If the crossed inverse covariants satisfy full marginal mixing up to $q^{-\Omega(n)}$, the rejection probability in that branch remains $O(n^{-sK})$ and a union bound handles the four modes. For a desired inverse polynomial loss choose $K$ to be a sufficiently large fixed constant. The cap can be checked by linear algebra on each repeated primary block and the enumeration still costs at most $q^{\sum_i D_{\mathrm{comm}}(E_i)}$.

For the singular-cut branch of the previous fixed-field algorithm, the same stronger cutoff gives inverse polynomial rejection after increasing its constants. The original flattening corank and the rank defects of random nonzero selected kernel forms are at most $K_0\sqrt{\log_q n}$, with error $O(n^{-M})$ for any prescribed fixed $M$ if $K_0$ is sufficiently large. This uses the usual rank count, and the sampled form from each uniform kernel is a uniform nonzero matrix. These caps retain the kernel enumeration inequality $q^c\le n$. The original projected-law comparison is exponential uniformly in those caps, since the deficient-side projection still loses at least $2n-O(\sqrt{\log n})$ coordinates. The original Fourier estimate is also exponential uniformly, since it uses lower bounds $n-O(\sqrt{\log n})$ on the live mode dimensions and upper bounds $O(\sqrt{\log n})$ on the two trace-constraining codimensions.

The dimension of the commutant enumeration for the enlarged operator can be charged to the actual repeated commutant dimension of the live operator. Its invariant flag has graded operators $0,A_0,0$, with outside pieces of dimension $u$ each. Nonzero primaries retain their live partitions, since primary decomposition preserves exact sequences and kills both outside pieces on those primaries. For the zero primary, let $\alpha_j$ and $\beta_j$ be the $j$-th column lengths of the live and enlarged partitions. On an invariant submodule $U$ of a nilpotent module $V$, column $j$ is $\dim(N^{j-1}U\cap\ker N|_U)$, which is at most the ambient column. The same inequality holds for quotients by applying it to the dual. Therefore $\alpha_j\le\beta_j$ and $\sum_j(\beta_j-\alpha_j)=2u$. It follows that
$$
  \sum_j \beta_j^2\le \left(\sqrt{\sum_j\alpha_j^2}+2u\right)^2
      \le 2\sum_j\alpha_j^2+8u^2.
$$
Since a multiplicity-one zero primary contributes at most one to the full commutant dimension, the enlarged repeated budget is at most $2 D_{\mathrm{comm}}(A_0)+8u^2+2$. A sufficiently large fixed multiple of $\log_q n$ thus covers the singular branch with probability $1-O(n^{-M})$. Only the enumeration cutoff is changed. The comparison treats the entire enlarged operator exactly.

## Recovering an explicit isomorphism on typical accepted inputs

The decision argument uses signed field-unit image membership. It can also recover a witness when the kernel of that field-unit map has exponent dividing $q-1$. This condition is typical for the tensor family in question. Indeed, the stabilizer of a uniform $n^4$-entry tensor in $\mathrm{GL}_n(q)^4$ consists of scalar tuples with product one except with probability $q^{-\Omega(n^3)}$. If a candidate tuple has a nonscalar component $g$, choose $v$ with $gv$ outside its line and restrict the tensor action minus identity to $\mathbb F_qv\otimes\bigotimes_{j\ne i}V_j$. Project the output modulo the line of $v$ in mode $i$. The induced map from the other three modes is injective, so the fixed subspace has codimension at least $n^3$. A scalar tuple with product different from one fixes only the zero tensor. A union bound over at most $q^{4n^2}$ tuples proves the claim. It transfers to the invertible- or singular-cut random model by conditioning on each event of probability bounded below, or can be combined directly with their joint unconditional estimates.

For invertible cuts, every element of the relevant unit-map kernel stabilizes the original tensor, so it is killed by $q-1$ on this event. For the enlarged singular branch, a kernel element restricts to scalar maps on the full original supports in the two primal and two dual factors. Its $(q-1)$-st power hence fixes those supports pointwise. On an enlarged primal $E$, if this power is $g$, then $g-I$ maps $E$ into the annihilator of the embedded dual support, a subspace of the embedded primal support, on which $g-I$ vanishes. Thus $(g-I)^2=0$. The same holds on the other enlarged primal. Such matrices have order a power of the characteristic. They still belong to a field-unit torus whose order is prime to the characteristic, hence $g=I$ in each enlarged factor. This proves the same exponent statement there.

Write the homomorphism in abstract logarithmic coordinates as $\Phi:\prod_j\mathbb Z/m_j\to\prod_s\mathbb Z/m_s$ with matrix $A_{sj}$, where the $m_j$ are local unit-field orders and the $m_s$ are target cell field orders. The dual character map has integral entries $B_{js}=m_j A_{sj}/m_s$, by the divisibility defining the embeddings and signs. The character $(q-1)e_j$ at each unit coordinate kills $\ker\Phi$ on the good event. Finite abelian group duality gives $(\ker\Phi)^\perp=\operatorname{im}\Phi^*$, so integer Smith form solves $Bv=(q-1)e_j\bmod (m_i)_i$. This solution can also be checked computationally for each $j$, independently of the random-tensor stabilizer proof. If the cell values $y_s$ belong to the image of a unit tuple $x_j$, the solution says
$$
 x_j^{q-1}=\prod_s y_s^{v_s}
$$
in hypothetical compatible multiplicative generators. That hypothetical equality can be evaluated without forming a common large field. Gcd-split the finite field orders into pairwise coprime atoms. CRT power project each cell contribution into its atom-power subgroups. For one atom choose an available field of maximal atom exponent among contributing cells and the unit field, and transport all the projections to this field via compatible common subfields. The relevant group order for each transport divides the gcd of its source and target field orders, hence the element belongs to the common subfield of gcd degree. Multiply those contributions, and transport the result for that atom to the unit field. This is possible because the product represents the atom-primary part of $x_j^{q-1}$. Multiply over atoms to recover the power in the unit field.

For fixed $q$, find an arbitrary root $\widetilde x_j$ of $Z^{q-1}-x_j^{q-1}$ in the unit field by fixed-characteristic finite-field factoring. The true unit differs from $\widetilde x_j$ by an element of $\mathbb F_q^\times$. After applying $\widetilde x$ to the cell values, the residual equations are scalar equations over $\mathbb F_q^\times$, with signs inherited from primal or dual occurrences. Use a finite table of base-field discrete logs and Smith form modulo $q-1$, permissible since the base field is fixed. Verify the recovered isomorphism on the original input. One may safely abstain on a positive case if the checked dual-map equations fail for all matching branches. On typical inputs the exponent proof ensures they succeed on every matching branch.

## Scope and reuse

The short-column estimate controls repeated factors of degrees up to $m_0/2$. The [full single-operator mixing argument](SingleAnchor.md) covers higher degrees and is sufficient for the [complete recognition theorem](FullCoverage.md).

The uniform matrix counting and limiting simultaneous-invertibility statements used here are also in [Fixed-field ordinary 4-tensor isomorphism, sections 4 and 6](https://github.com/Dugongue/MathProofs/blob/main/FixedFieldOrdinaryFourTI/PROOF.md). For finite-field matrix enumeration via primary partitions, see [Kent Morrison, Eigenvalues of Random Matrices over Finite Fields](https://aimath.org/~morrison/Research/ERMFF.pdf).
