# Generic orbit recovery and modular spanning degree

The results below are informal proofs. For a finite group acting on $V$, $\beta_{\rm field}$ is the minimum degree of polynomial invariants generating $K(V)^G$, and $D_{\rm span}$ is the minimum degree of polynomials spanning $K(V)$ over $K(V)^G$.

## Algebraic and unitary moments distinguish different complex vectors

Edidin and Katz ask in Remark II.7 whether algebraic and unitary invariants have the same separating power on complex vectors of real finite-group representations. Both strict directions occur. The unitary cutoff can be smaller by an arbitrarily large amount on a coordinate stratum. The reverse difference is bounded by two degrees, and that bound is attained. The strata in the examples below are specified explicitly. [Edidin and Katz, §II and Remark II.7](https://arxiv.org/html/2503.00009#S2).

Use the paper's tensors with one conjugated slot in the unitary version:
$$
T_d(x)=\sum_{g\in G}(gx)^{\otimes d},\qquad
M_d(x)=\sum_{g\in G}(gx)^{\otimes(d-1)}\otimes\overline{gx}.
$$

### Sharp reverse direction

Let $C_2$ act on its real sign line and complexify. The second algebraic tensor is $2z^2$, which determines the orbit $\{z,-z\}$. The first and third unitary tensors vanish, and the second tensor is $2|z|^2$. Thus unitary tensors through degree three do not separate nonzero points of the same magnitude. The fourth tensor is $2z^2|z|^2$, so the two least cutoffs on the nonzero stratum are two and four.

For any finite group preserving a Hermitian inner product, the contraction of one ordinary slot and the conjugated slot of $M_{d+2}$ is $\|x\|^2 T_d(x)$. The trace of $M_2$ gives $|G|\|x\|^2$. Consequently, on nonzero vectors, algebraic tensors through degree $d$ can be read from unitary tensors through degree $d+2$. The norm identifies the zero vector separately. This proves the uniform bound in the reverse direction, with the sign action giving equality.

### An unbounded difference favoring the unitary moments

Fix $k\ge3$ and put $n=2^k-1$. Let $C_n$ act on the real direct sum of rotation planes of weights $2^0,2^1,\ldots,2^{k-1}$. Its complexification has both the positive weights $2^i$ and their negatives. They are all distinct: opposite weights could coincide only if a sum of two powers of two equalled the $k$-digit binary integer $2^k-1$, which is impossible for $k\ge3$.

Take the stratum on which the positive-weight coordinates $x_i$ are all nonzero and all negative-weight coordinates vanish. The second unitary tensor gives all $|x_i|^2$. The third gives all $x_i^2\overline{x_{i+1}}$, with cyclic indices, because $2\cdot2^i=2^{i+1}\bmod n$. If two points agree in these entries, let $\tau_i$ be their coordinate ratios. Then $|\tau_i|=1$ and the third tensor gives $\tau_{i+1}=\tau_i^2$. Hence $\tau_0^{2^k-1}=1$ and $\tau_i=\tau_0^{2^i}$. This is precisely the action of a group element, so the unitary cutoff is three. Degrees one and two give only magnitudes on this stratum and cannot separate its finite orbits.

On the algebraic side, the nonconstant invariant monomials on this stratum correspond to nonnegative vectors $(a_0,\ldots,a_{k-1})$ with $\sum_i a_i2^i=0\bmod n$. Whenever $a_i\ge2$, replace two copies of $2^i$ by one copy of $2^{i+1}$, wrapping the index cyclically. This preserves the weight modulo $n$ and strictly decreases the degree. Starting from a nonzero vector, the process never produces an empty sum. At termination the digits are zero or one, so the only possible positive zero-sum is the sum with every digit one. Thus the least positive degree is $k$ and the only invariant monomial of degree $k$ on the stratum is $\prod_i x_i$. That monomial cannot separate all finite orbits on the stratum.

At degree $k+1$ we also have the exponent vectors $\mathbf 1+2e_i-e_{i+1}$. Their differences with $\mathbf 1$ are $2e_i-e_{i+1}$. These differences generate the full zero-sum lattice, since their quotient group has generators $e_i=2^i e_0$ and single cyclic relation $(2^k-1)e_0=0$. Equivalently, equality of these monomials forces the corresponding coordinate ratios to satisfy $\tau_{i+1}=\tau_i^2$ and $\tau_0^n=1$. Therefore the algebraic cutoff on this stratum is $k+1$.

## A closed formula for the modular cyclic spanning degree

Let $K$ have characteristic $p$ and let a generator of $C_{p^r}$ act faithfully on $V$. Let $s$ be its largest Jordan-block size, so $p^{r-1}<s\le p^r$. Then
$$
D_{\rm span}(C_{p^r},V)
=
\max_{0\le j<r}\left\lceil
\frac{p^{r-j}-1}{\left\lfloor (s-1)/p^j\right\rfloor}
\right\rceil.
$$
For a nonfaithful action use the actual order of the matrix and the same formula on the effective quotient. For the trivial action $D_{\rm span}=0$. This gives deterministic polynomial bit complexity over a finite field when the generator matrix and the group order in binary are supplied. It is a closed-form modular answer to the spanning-degree question. [Blum-Smith, Garcia, Hidalgo and Rodriguez, Question 5.11](https://arxiv.org/html/2303.05626v6#S5.SS2) · [Blum-Smith and Derksen, general spanning-degree theory](https://arxiv.org/html/2506.05650v4#S4).

### Proof

Write $L=K(V)$ and $F=L^G$. The Galois evaluation map $L\otimes_F L\to \prod_{g\in G}L$ given by $u\otimes v\mapsto(u\,g(v))_g$ identifies the $F$-rank of a set of polynomials with the $L$-rank of their orbit evaluation vectors. Write the generator as $I+N$ in Jordan coordinates on $V^*$. At group exponent $t$,
$$
(I+N)^t=\sum_{\ell<s}\binom{t}{\ell}N^\ell.
$$
The largest block shows that the degree-at-most-one evaluations span all the functions $\binom{t}{\ell}$ for $\ell<s$ over $L$. Indeed, as one traverses the block the successive coordinate evaluations are lower triangular combinations of these functions with the same nonzero generic first coordinate on the diagonal. Smaller blocks add no new functions.

Write $t=\sum_{\mu=0}^{r-1}t_\mu p^\mu$ and write the digits of $\ell$ as $\ell_\mu$. Lucas's congruence gives
$$
\binom{t}{\ell}=\prod_{\mu=0}^{r-1}\binom{t_\mu}{\ell_\mu}
\quad\text{in }K .
$$
The right hand side has leading digit monomial $\prod_\mu t_\mu^{\ell_\mu}$ with nonzero coefficient, and all other exponent vectors are componentwise smaller. The set $\ell<s$ is closed under decreasing individual digits. Hence the span of the binomial functions is exactly the span of the digit monomials with weighted exponent $\sum_\mu \ell_\mu p^\mu<s$.

Let $\alpha$ range over that downward-closed set of exponent vectors. Products of $d$ such monomials, allowing the constant monomial, span the evaluations of polynomials of degree at most $d$. In the function algebra on $\mathbb F_p^r$, reduce each product using $t_\mu^p=t_\mu$. Reduced monomials with digit exponents from zero to $p-1$ form an $L$-basis. Including the top monomial with exponents all $p-1$ suffices to include the other basis vectors, since exponents can be decreased in each factor. More precisely, to obtain any reduced exponent $\beta_\mu$ by a product one needs total unreduced exponent at least $\beta_\mu$ in that coordinate. By downward closure one can decrease exponents in the factors so that their sum equals $\beta_\mu$ exactly. Thus full rank is equivalent to expressing the all-$(p-1)$ vector as an exact sum of $d$ allowed digit vectors.

This is a packing problem with $p-1$ items of each size $1,p,\ldots,p^{r-1}$ and $d$ bins of capacity $s-1$. For every $j$, the items of size at least $p^j$ consume exactly $p^{r-j}-1$ slots in units of size $p^j$. These items fit only if
$$
p^{r-j}-1\ \le\ d\left\lfloor (s-1)/p^j\right\rfloor.
$$
The conditions suffice. Place items in decreasing order of size. Before placing those of size $p^j$, all previously occupied capacity is a multiple of $p^j$ in every bin. The sum of the remaining integer slot counts is therefore at least the number of items of size $p^j$ by the displayed condition. Distribute those items among the remaining slots and continue. This gives the formula.

The largest Jordan block size is the first power of the generator minus the identity that vanishes, and can be found by matrix powering or successive kernels. The remaining operations use at most logarithmically many integer powers and ratios in the group order. This establishes the claimed bit complexity.


### Deterministic extension to cyclic groups of mixed order

For $C_{p^r m}$ in characteristic $p$, with $\gcd(p,m)=1$, the same method gives a finite directed graph whose distances determine $D_{\rm span}$. Work over a splitting field for the $m$-part. For each occurring character $\chi$ of that part, let $s_\chi$ be the maximum Jordan-block size for the $p$-part on its weight space. The degree-one evaluations span the functions
$$
\chi(u)\prod_\mu t_\mu^{\alpha_\mu},
\qquad \sum_\mu \alpha_\mu p^\mu<s_\chi .
$$
Here the group element has coordinates $u\in C_m$ and $t\in C_{p^r}$. This follows from the same triangular block argument, applied within a weight space.

Use a graph with vertices $(\psi,\beta)$, where $\psi$ is a character of $C_m$ and each $\beta_\mu$ is between zero and $p-1$. Start from $(1,0)$. For each displayed degree-one monomial, include the transition
$$
(\psi,\beta)\ \longmapsto\
(\psi\chi,\,\min(p-1,\beta+\alpha)),
$$
where the minimum is taken in each digit. Saturation only records whether each digit sum is sufficiently large. For any sequence of factors yielding a given saturated exponent, one can decrease the individual digit exponents to sum exactly to that exponent, staying within each factor's allowed set and keeping all the characters unchanged. Conversely, any exact digit sum can be obtained by the corresponding transitions. For each character the set of reachable digit exponents is downward closed. Thus an exponent occurring after reduction by $t_\mu^p=t_\mu$ also occurs in this graph at the same or a smaller number of steps: the unreduced exponent is at least the reduced one in every digit, and one can decrease it exactly. The character times digit monomials form a basis of the full function algebra on the group. The maximum of the shortest distances to all vertices is therefore exactly $D_{\rm span}$.

The graph has $m p^r$ vertices and at most $m p^r$ degree-one types. This gives a deterministic algorithm polynomial in the group order and the sizes of the supplied block and character data. For $r=0$ this reduces to ordinary shortest paths in the directed Cayley graph of the character group.

## The spanning degree in a succinct encoding is a covering-radius problem

Given a full-row-rank binary parity-check matrix $H$ of size $r\times m$, let $G=(C_2)^r$ act over $\mathbb Q$ on $m$ coordinates by giving coordinate $j$ the sign character specified by the $j$-th column $H_j$. This faithful action is specified by only $r$ diagonal sign matrices. Then
$$
D_{\rm span}(G,V)=\max_{s\in\mathbb F_2^r}\ \min_{e\in\mathbb F_2^m,\ He=s}|e|
=\rho(\ker H),
$$
where $|e|$ is Hamming weight and $\rho$ is covering radius. The equality gives polynomial-time reductions both ways between computing the spanning degree for succinct faithful diagonal sign modules and computing the covering radius of binary linear codes.

Indeed a monomial with exponent vector $\alpha$ has character $H(\alpha\bmod2)$, and any given parity vector occurs at minimum degree equal to its Hamming weight. For the rational function field over its fixed field, each character space is one-dimensional: the ratio of any two nonzero eigenvectors of the same character is invariant. All characters occur, since the weights generate the character group. The eigenspaces are independent and exhaust the field, which has dimension $2^r$ over its fixed field. Therefore the spanning degree is the maximum of the first degrees in which the characters occur. For any word $w$ with syndrome $s$, the words $e$ satisfying $He=s$ are exactly the coset of $\ker H$ containing $w$. Its lightest word gives the distance of $w$ to the code. This proves the displayed equality. Conversely, from the diagonal generator matrices one reads the same parity-check matrix. Row reduction handles any redundant generating characters. The reductions use the succinct encoding; an explicit list of all group elements has a different input size. [Blum-Smith and Derksen, Proposition 4.1 on characters and the spanning degree](https://arxiv.org/html/2506.05650v4#S4.SS1) · [McLoughlin, the computational covering-radius problem](https://doi.org/10.1109/TIT.1984.1056978). In particular, deciding whether the spanning degree is at most a given integer is $\Pi_2^{\rm P}$-complete in the succinct encoding. Hardness follows from binary linear covering radius, and the syndrome formulation gives the universal–existential certificate. [Guruswami, Micciancio and Regev, Section 5.3](https://cseweb.ucsd.edu/~daniele/papers/CoveringRadius.pdf).

## Replacing the high-degree norm in modular cyclic field generators

Reimers and Sezer give field generators for the $n$-dimensional indecomposable $C_p$-module, with all except a degree-$p$ norm of degree at most three. For $n\ge2$ and $p>3(n-1)$, one can replace that norm by a single explicit transfer of degree $\lceil(2p-1)/(n-1)\rceil$. In particular, for $n\ge4$ this replacement has degree smaller than $p$. In the same range one has the bounds
$$
\left\lceil\frac p{n-1}\right\rceil
\ \le\ \beta_{\rm field}\
\le\left\lceil\frac{2p-1}{n-1}\right\rceil.
$$
This answers the degree-reduction question in this range, with explicit dependence on the block size. [Reimers and Sezer, Theorem 3 and the paragraph following its proof](https://arxiv.org/html/2505.20895#S3).

Use coordinates $x_1,\ldots,x_n$ of an indecomposable Jordan block, so the generator acts by $I+N$, with $N x_j=x_{j-1}$ and $N x_1=0$. Extend it to the additive group by
$$
\rho(a)=\sum_{j=0}^{n-1}\binom aj N^j.
$$
The denominators are invertible since $j<p$. The binomial identity gives $\rho(a+b)=\rho(a)\rho(b)$ and $\rho(1)=I+N$. On the rational field, $t=x_2/x_1$ transforms by $t\mapsto t+a$. Applying $\rho(-t)$ to the vector of coordinate variables gives the rational additive-group invariant coordinates. Reconstruction using $\rho(t)$ shows that the full rational field is $E(t)$, where $E$ is the additive-group invariant field. In this description the $C_p$-invariant field is $E(t^p-t)$.

Every polynomial of total degree $d$ has orbit polynomial in the parameter $a$ of degree at most $d(n-1)$. An invariant of degree $d$ for $C_p$ whose orbit-polynomial degree is less than $p$ is also invariant under the additive group, since the orbit polynomial minus its value at zero vanishes at all $p$ field elements. Thus the degree-three-or-less generators of Reimers and Sezer belong to $E$ for $p>3(n-1)$. They generate $E$ as a field. Indeed by their theorem adjoining the norm $x_1^p(t^p-t)$ to them generates the $C_p$ invariant field, and the additive group acts on this extra variable by the nonconstant translation $x_1^p(a^p-a)$. Its invariant subfield over the other generators is exactly the field generated by those generators. The same polynomial root argument proves the displayed lower bound.

Put $k=n-1$ and write $2p-1=Ak+B$ with $0\le B<k$. Let $P=x_n^A$ when $B=0$, and $P=x_n^A x_{B+1}$ when $B>0$. In $E[t]$ it has exact $t$-degree $2p-1$, since $x_i$ has $t$-degree $i-1$ with nonzero leading coefficient $x_1/(i-1)!$. Its transfer $\sum_{a\in\mathbb F_p}P(t+a)$ has $t$-degree exactly $p$. Indeed the first nonzero parameter sum in its binomial expansion has exponent $p-1$ and value $-1$, while the exponent-zero sum is zero. For the leading monomial of degree $2p-1$ the coefficient $\binom{2p-1}{p-1}$ is $1$ modulo $p$ by Lucas's congruence. Lower-degree monomials cannot contribute to degree $p$. The transfer is $C_p$-invariant, so it is linear with nonzero slope in $t^p-t$ over $E$. Thus it replaces the norm in the generating set, as claimed.
