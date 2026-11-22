# The exact cancellation dimension for finite étale tensor products

Fix a finite field $k$ and a nonzero finite étale $k$-algebra $C=\prod_j k_{m_j}$, where $k_d$ is the degree-$d$ extension of $k$. Consider $T_A(x,y,z)=\operatorname{Tr}_{A/k}(xyz)$ with the usual three independent invertible linear changes of basis. For $M=\{m_j\}$ define
$$
 D(M)=\tfrac12\min_{H}\prod_{p\in H}2p ,
$$
where $H$ ranges over sets of primes containing at least one prime divisor of every member of $M$. Take the minimum of the empty family of choices to be infinity.

**Theorem.** For every $n<D(M)$, tensoring by $T_C$ reflects ordinary tensor isomorphism on all $n$-dimensional finite étale trace tensors over $k$. For each integer $n\ge D(M)$ there are two distinct isomorphism classes with isomorphic products. The same threshold works for symmetric equivalence by a single common basis change, and for a polynomial $\prod_i(C_i\otimes A^{\otimes i})$ in the algebra $A$, using the union of all field-factor degrees of nonzero coefficients of positive exponent. Here the outer product is the direct product of algebras, and at least one positive exponent has a nonzero coefficient.

For example, if the marker factor degrees are $6,10,15$, cancellation holds through dimension 11. In dimension 12 take $A=k_6\times k^6$ and $B=k_2^3\times k_3^2$. The same pair works for marker degrees 2 and 3. A marker with a degree-one factor cancels in every dimension.

## From tensors to signed cycles

The trace pairing is perfect for every finite separable algebra, and algebra isomorphisms preserve it. An independent-leg equivalence thus amounts to three invertible linear maps with $h(xy)=f(x)g(y)$ (use the dual inverse on the output leg). Both $u=f(1)$ and $v=g(1)$ are units, since multiplication by either is surjective. Substituting 1 gives $h(x)=f(x)v=ug(x)$. Hence $x\mapsto (uv)^{-1}h(x)$ is a unital algebra isomorphism. Conversely the same algebra isomorphism on all three legs preserves the trace form. Under tensor product the trace of a pure tensor is the product of the traces, as one sees in a tensor-product basis.

A finite étale algebra over a finite field is classified by the Frobenius permutation of its embeddings into an algebraic closure. A field factor of degree $d$ contributes a cycle of length $d$, and tensor products of algebras give Cartesian products of Frobenius sets. [Stacks Project, Lemma 58.2.2](https://stacks.math.columbia.edu/tag/03QR)

Write $e_d$ for a single $d$-cycle. The finitely supported signed cycle difference $x=\sum x_de_d$ has integer coefficients. Its mass norm is $\|x\|=\sum d|x_d|$. Raising a permutation to the $m$-th power induces the additive map $R_m(e_d)=g e_{d/g}$, $g=\gcd(d,m)$. The number of points fixed by the $a$-th power of a permutation with cycle counts $c_d$ is $\sum_{d\mid a}d\,c_d$. These integer marks determine all cycle counts by triangular inversion. Marks multiply under Cartesian product. The marker has positive mark at $a$ exactly when some $m_j\mid a$. Therefore equality of the products is equivalent to $R_m x=0$ for every $m\in M$, since the marks of the powered permutation are the original marks on multiples of $m$. For the polynomial extension, each mark of the output is a polynomial in the input mark with nonnegative integer coefficients. It is strictly increasing on the nonnegative integers precisely when some positive-exponent coefficient has a positive mark. This gives the very same joint kernel for the union of the active markers.

## The sharp lower bound

Let $F(M)$ denote the minimum product in the display, before division by 2, and $F(\varnothing)=1$. Every nonzero integral vector in the joint kernel has mass norm at least $F(M)$. Induct on the number of distinct primes occurring in $M$. A marker 1 makes the kernel zero, and for empty $M$ the lower bound is the integrality of the mass norm.

Choose a prime $p$ in $M$. Let $M_0$ be the markers coprime to $p$ and $M_1$ the family obtained by stripping all $p$-powers from every marker. Group $x$ into slices $x_t(e)=x_{p^te}$ for $p\nmid e$. For an avoiding marker, restriction acts within each slice. Consequently $R_m x_t=0$ for every $m\in M_0$. Set $y=\sum_t p^t x_t$, a vector supported on $p$-free lengths. If $m=p^b m'$, collapsing after $R_m$ gives $R_{m'}y$. On $e_{p^te}$ both operations give $p^t g\,e_{e/g}$, where $g=\gcd(e,m')$, since $\min(t,b)+(t-b)_+=t$.

If $y\ne 0$, induction and the triangle inequality give $\|x\|\ge\|y\|\ge F(M_1)$. If $y=0$, let $t$ be the largest nonzero slice index. Then $t\ge1$, and the weighted norm of all other slices combined is at least $p^t\|x_t\|$, since their weighted sum equals $-p^t x_t$. Therefore
$$
\|x\|\ge2p^t\|x_t\|\ge2p F(M_0).
$$
A prime hitting set either omits $p$, giving optimum $F(M_1)$, or includes it, giving optimum $2p F(M_0)$. Thus the smaller of the branch bounds is exactly $F(M)$. This applies to arbitrary lengths on either side of the isomorphism test, including lengths with higher prime powers or extraneous primes.

## Equality

Multiplication of virtual cycles uses $e_d e_s=\gcd(d,s)e_{\operatorname{lcm}(d,s)}$. Given a minimizing prime hitting set $H$, form
$$
 z=\prod_{p\in H}(e_p-p e_1).
$$
Each restriction $R_m$ respects Cartesian multiplication and kills at least one factor. In the expansion, each subset $J\subseteq H$ produces a distinct length $\prod_{p\in J}p$ and coefficient of magnitude $\prod_{p\in H\setminus J}p$. The norm is exactly $\prod_{p\in H}2p$. Because $M\ne\varnothing$, every kernel vector has signed mass zero (restriction preserves signed mass). Its positive and negative parts therefore have equal degree, half its norm. These two parts attain equality. Adding common fixed points realizes every larger degree.

An equivalent matrix consequence holds over any field. Permutation matrices are similar precisely when their cycle types agree. Indeed $\dim\ker(P^s-I)=\sum_d c_d\gcd(s,d)$ because coordinates are constant around each cycle of the $s$-th power. Expanding $\gcd(s,d)=\sum_{h\mid s,\,h\mid d}\varphi(h)$ and using inversion in $s$ recovers $\sum_{h\mid d}c_d$ for each $h$; descending in $h$ then gives each $c_h$. Thus the same first dimension describes failure of cancellation of Kronecker products with a fixed permutation matrix, among permutation matrices under unrestricted similarity.

## Prior work and verification

Naquin and Gadouleau proved the fixed-point criterion for cancellative finite dynamical systems. Their Lemma 33 already gives alternating witnesses and credits earlier work. Porreca and Rolland extend the injectivity criterion to polynomial operations and exhibit simultaneous collisions. The upper-bound mechanism thus has direct precedent. The proposed refinement here is the *optimal minimum common input degree*, including its lower bound for overlapping composite lengths. A targeted literature search did not establish priority for that refinement. [Naquin and Gadouleau](https://arxiv.org/abs/2210.11270) · [Porreca and Rolland, §3.3 and Lemma 12](https://arxiv.org/html/2604.04065v1)

The general theorem has the mathematical proof above. The companion Lean file covers the arithmetic identity and local mass comparison in the induction. The Python control computes the products of actual cycle types and checks all partitions in its stated finite range.
