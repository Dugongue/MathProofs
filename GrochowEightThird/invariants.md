# Four answers in invariant theory and Schurian intersection problems

## Published Problem 1.4

Maleki and Razafimahatratra ask whether all maximum intersecting families of a Gelfand pair are canonical when their Question 1.1 has an affirmative answer. Their intersecting families are the independent sets of the union of the eligible orbital graphs. Canonical families are independent orbits of conjugates of the specified Young subgroup. The answer is **no**, already in the ordinary Johnson scheme, with a full classification at the balanced boundary. The balance condition falls in line 1 of the published Table 1, and Section 5 treats Question 1.1 for that line. [Maleki and Razafimahatratra, AJC 89(3), pp. 415–418 and §5](https://ajc.maths.uq.edu.au/pdf/89/ajc_v89_p413.pdf#page=3).

### Counterexample and proof

Take $G=S_6$ and $H=S_3\times S_3$, with $G/H$ identified with the triples in $[6]$. This is a Gelfand pair by the multiplicity-free two-row decomposition of the permutation module on triples. Its second constituent in dominance order is $S^{(5,1)}$. A conjugate of the Young subgroup $S_5\times S_1$ fixes a point $i$ and has two orbits: the triples containing $i$ and those avoiding $i$.

The nontrivial orbitals are the pair relations of overlap sizes $0$, $1$, and $2$. For positive overlap, one can put $i$ in the intersection or outside the union by relabeling. Thus both point-stabilizer orbits contain an edge of every positive-overlap orbital. In the overlap-zero orbital, complements are adjacent and each of the two orbits is independent. The union of eligible orbitals is therefore exactly $KG(6,3)$, a disjoint union of ten edges.

For a vector $a=(a_1,\ldots,a_6)$ with $\sum_i a_i=0$, the function $f_a(T)=\sum_{i\in T}a_i$ lies in the standard constituent, and complementing $T$ negates $f_a$. The least eigenvalue of a matching is $-1$, so this constituent affords the least eigenvalue of the eligible orbital. Both premises in Question 1.1 are therefore met.

Let $\mathcal F$ consist of the triples containing at least two points of $\{1,2,3\}$. Exactly one member of every complementary pair belongs to $\mathcal F$, since the corresponding two intersection sizes sum to three. It has the maximum size 10. Its intersection is empty: $\{1,2,3\}$ excludes every outside point, and for each inside point we can use the other two inside points and one outside point. Its union is all of $[6]$, since each outside point belongs to a triple with two inside points. Thus $\mathcal F$ is neither an orbit of triples containing a fixed point nor an orbit of triples avoiding one. This disproves canonical uniqueness.

### Sharp general classification for the standard constituent

Let $(S_n,H)$ be a Gelfand pair in which $S^{(n-1,1)}$ occurs. The natural permutation representation splits into the trivial and standard representations. Frobenius reciprocity therefore gives exactly two $H$-orbits on $[n]$. Let $U$ be one of least size $k$, and send $gH$ to $gU$. Each fiber has size $m=[S_k\times S_{n-k}:H]$. Fixing a point $i$ gives precisely two orbits on $S_n/H$, according as $i$ belongs to $gU$ or its complement. For the smaller, containing-point orbit, a nontrivial orbital is eligible exactly when its two underlying $k$-sets are disjoint. Indeed, equality or positive intersection lets one relabel a shared point to $i$, while disjointness precludes the two vertices from both containing $i$.

The union of eligible orbitals is therefore the independent-fiber blow-up of $KG(n,k)$ with fiber size $m$. Its adjacency matrix is $A(KG(n,k))\otimes J_m$. Consequently its least eigenvalue is $-m\binom{n-k-1}{k-1}$ and is afforded by the standard constituent. This spectral assertion describes the union graph. Question 1.1(b) concerns the existence of a suitable individual orbital.

Every maximum independent set of the union graph fills each fiber it meets, since any unfilled fiber could be completed without creating edges. Its support on the underlying $k$-sets is a maximum independent set of $KG(n,k)$. By the strict Erdős–Ko–Rado theorem, when $n>2k$ all such maximum families are exactly the full inverse images of point stars. When $n=2k$, the supports are exactly the transversals of the complementary pairs. The balanced classification includes $2^{\binom{2k}{k}/2}$ labeled maximum families, with precisely $4k$ canonical ones for $k\ge2$. Canonical ones are the point stars and point antistars, which are distinct in this range. For $k=2$ these eight exhaust the possibilities; for every $k\ge3$ most maximum families are noncanonical. [Erdős, Ko and Rado, *Intersection theorems for systems of finite sets*](https://doi.org/10.1093/qmath/12.1.313).

**Verification:** self-contained informal proof of the counterexample, with the standard Johnson decomposition and strict Erdős–Ko–Rado theorem used for the extension.

## Fixed-support extremizers for the polynomial generation degree

**Published Question 5.4.** Let $p$ be an odd prime, let the field $K$ have characteristic different from $p$, and let $m\ge1$ count the distinct nontrivial characters of a $C_p$-representation $V$ after base change. Write $h=\lceil m/2\rceil$. For each fixed $m$ and every sufficiently large $p$, the arithmetic upper bound
$$
\beta_{\mathrm{field}}(C_p,V)\ \le\ \left\lceil\frac ph\right\rceil
$$
holds for polynomial invariants generating $K(V)^{C_p}$ as a field. Equality holds exactly for the following supports, up to scaling all characters by a unit modulo $p$: $\{\pm1,\ldots,\pm h\}$ for even $m$, and any single deletion from that set for odd $m$. Trivial and duplicate summands are allowed. This answers both parity cases of Question 5.4. The earlier cyclic-invariants result in this project gives the upper bound of Conjecture 5.1 across all prime-order supports. The new assertion here is the classification of equality and the strict bound for every other support when $p$ is sufficiently large at fixed $m$. [Blum-Smith, Garcia, Hidalgo and Rodriguez, Question 5.4](https://arxiv.org/html/2303.05626v6#S5.SS1).

The 2026 geometry-of-numbers result classifies large-$p$ extremizers for generation by rational functions and obtains the polynomial degree bound under dual-pair closure. Its short-basis argument supplies the starting point for the following nonnegative rounding construction. [Blum-Smith, Crane, Guzman, Menenses and Song-Hurewitz, Proposition 2.16, Lemma 3.4, Lemma 3.7 and Theorem 3.9](https://arxiv.org/html/2604.18876v1#S3).

### Nonnegative lattice generation

Use the base-change and multiplicity lemmas of the original paper to work with distinct nonzero coordinate weights $a_1,\ldots,a_m\in\mathbb F_p$. Put
$$
L=\left\{x\in\mathbb Z^m\mid\sum_i a_i x_i=0\pmod p\right\}.
$$
The polynomial generation degree equals the least $d$ for which nonnegative elements of $L$ with $\ell_1$ norm at most $d$ generate $L$ as an abelian group. Indeed, an invariant monomial has its exponent in $L$, and allowing field operations on such monomials makes the additive group of their exponents the relevant lattice. [Blum-Smith, Garcia, Hidalgo and Rodriguez, §2](https://arxiv.org/html/2303.05626v6#S2).

The case $m=1$ has one generator of degree $p$, so assume $m\ge2$. By the short-basis lemma, $L$ has a basis $b_1,\ldots,b_m$ such that $|\det(b_1,\ldots,b_m)|=p$ and $\|b_i\|_1\le (m-1)\sqrt{m!p}$ for $i<m$. Define the linear functional
$$
D(z)=\det(b_1,\ldots,b_{m-1},z)
$$
and let $M$ be the greatest absolute coordinate coefficient of $D$. If necessary negate $D$, so its coefficient at some $j$ is $M>0$. The map $D:L\to p\mathbb Z$ is onto and its kernel in $L$ has basis $b_1,\ldots,b_{m-1}$.

Let $R=1+\sum_{i<m}\|b_i\|_1$, take $u=(2R,\ldots,2R)$, and put $T=D(u)$. Then $|T|\le 2mRM$. Every $x$ with $D(x)=q p$ is in the affine real span of the lattice points in that level. Subtracting the fractional parts of its coordinates in the kernel basis gives a point $v$ of $L$ in the same level and at $\ell_1$ distance at most $R-1$ from $x$.

If $T\le p$, use
$$
x=u+\frac{p-T}{M}e_j .
$$
It lies in level $p$, with every coordinate at least $2R$, and $\|x\|_1\le p/M+4mR$. Round it to $v$. All the points $v,v+b_1,\ldots,v+b_{m-1}$ are nonnegative, and they generate $L$: their differences generate the kernel and $v$ maps to $p$.

If $T>p$, take $q=\lceil T/p\rceil$ and use the two real points
$$
x_s=u+\frac{s p-T}{M}e_j,\qquad s=q,q+1 .
$$
Both have coordinates at least $2R$. Their added $j$-coordinate is at most $2p/M$, and $p/M<2mR$ in this case. Thus both norms are at most $p/M+4mR$. Round them to $v_q,v_{q+1}$. Use $v_q,v_{q+1},v_q+b_1,\ldots,v_q+b_{m-1}$. These are nonnegative, and $v_{q+1}-v_q$ maps to $p$, while the other differences generate the kernel.

In either case the nonnegative generators have degrees at most
$$
\frac{p}{M}+(4m+2)\left(1+(m-1)^2\sqrt{m!p}\right).
$$

### Sharp support classification

If at least one coordinate coefficient of $D$ is nonzero modulo $p$, then $D$ and the original weight functional have the same kernel over $\mathbb F_p$ and therefore differ there by a nonzero scalar. Its $m$ coordinate coefficients are distinct and nonzero modulo $p$. If all coefficients vanish modulo $p$, then $M\ge p$. Consequently $M\ge h$. For $p>2h$, the only case $M=h$ has exactly the classifications in the theorem: $m$ distinct nonzero integers inside $[-h,h]$ exhaust that set except zero when $m$ is even, and omit one nonzero integer when $m$ is odd. Proposition 2.16 gives equality for these supports. [Blum-Smith et al., Proposition 2.16](https://arxiv.org/html/2604.18876v1#S2).

In all other cases $M\ge h+1$. For sufficiently large $p$ depending only on $m$, the displayed degree bound is strictly below $p/h$, since the saving $p/h-p/(h+1)=p/(h(h+1))$ exceeds the error term. This proves both the upper bound and the exact extremal classification.

## Quadratic transcendence bases for finite-group invariant fields

**Published Question 5.14.** For any finite group $G$, field $K$ of characteristic coprime to $|G|$, and finite-dimensional $G$-representation $V$, the following are equivalent.

- The degree-at-most-two invariants contain a transcendence basis of $K(V)^G$ over $K$.
- Over an algebraic closure, every irreducible constituent of $V$ is one-dimensional and its character has order dividing two.

Thus the answer to Question 5.14 is affirmative. The theorem characterizes when $\gamma_{\mathrm{field}}(G,V)\le2$. [Blum-Smith, Garcia, Hidalgo and Rodriguez, Lemma 2.1 and Question 5.14](https://arxiv.org/html/2303.05626v6#S5.SS2).

### Proof

Degree-bounded invariant spaces commute with field extension, and the transcendence degree of the field they generate is unchanged by algebraic extension of scalars. We can therefore assume $K$ algebraically closed. Maschke's theorem gives an isotypic decomposition. The field $K(V)^G$ has transcendence degree $\dim V$ because $K(V)$ is finite over it. If every irreducible constituent is a character of order at most two, the squares of eigen-coordinates are invariant and algebraically independent, proving sufficiency.

For the converse choose an irreducible constituent $W$ outside the stated class. We construct a nontrivial multiplicative-group action on $V$ fixing every invariant polynomial of degree at most two. The invariant field of this action has transcendence degree at most $\dim V-1$: each action below has a diagonal basis with a coordinate of weight $1$ or $-1$, and after inverting that coordinate all other coordinates can be rescaled by its suitable powers to have weight zero. Degree-at-most-two invariants therefore have insufficient transcendence degree.

For any direct-sum decomposition into irreducibles, an invariant homogeneous quadratic polynomial is the sum of its single-summand quadratic terms and its cross terms, each invariant by restriction. The cross terms are invariant bilinear pairings. Schur's lemma permits a nonzero pairing only between dual types. If $W$ is not self-dual, its invariant single-summand quadratics vanish. In characteristic different from two this follows by polarization. In characteristic two the polar form also vanishes, so a quadratic would be the square of a linear form. Over an algebraically closed field this form would be invariant by injectivity of squaring, while $W$ is nontrivial. We can now scale the $W$-isotypic part by $t$ and the $W^*$-isotypic part by $t^{-1}$, fixing all other parts. This preserves the cross terms, the single-summand terms and the invariant linear forms.

It remains to handle self-dual $W$ of dimension at least two. Identify all copies of $W$ with a fixed model. By Schur's lemma the space of invariant bilinear forms on the model is one-dimensional, spanned by a nondegenerate form $B$. In characteristic different from two, $B$ is symmetric or alternating by transposition. A symmetric nondegenerate form of dimension at least two over an algebraically closed field has a hyperbolic pair. An alternating nondegenerate form has a symplectic pair. Rescale that pair by $t,t^{-1}$ and fix its $B$-orthogonal complement. In either case this preserves $B$ and any invariant quadratic on the model, since polarization identifies those quadratics with the invariant symmetric bilinear forms.

In characteristic two, $B$ is symmetric by transposition and is alternating because $B(w,w)$ is the square of a linear form. The linear form would be invariant and must vanish on nontrivial $W$. The polar map on invariant quadratics on $W$ is injective by the same squares argument and its image lies in the line spanned by $B$. If a nonzero invariant quadratic $q$ exists, scale it so its polar form is $B$. Choose a nonzero $u$ with $q(u)=0$, choose $v$ with $B(u,v)=1$, and replace $v$ by $v-q(v)u$. This gives a hyperbolic pair for $q$. Reciprocal rescaling of that pair preserves both $q$ and $B$. If there is no invariant quadratic, rescale a symplectic pair for $B$.

In all self-dual cases apply the same rescaling to every copy of $W$, fixing the other irreducibles. It preserves all cross terms by Schur's lemma, all invariant single-summand quadratics by construction, and all invariant linear forms. This proves the converse.

**Verification:** the fixed-support and quadratic-transcendence results have informal proofs. The fixed-support proof uses the cited short-basis lemma and known equality examples.

## The improved transcendence-degree bound for prime cyclic actions

**Published Question 5.15.** Let $p$ be odd prime and assume the characteristic differs from $p$. If a representation of $C_p$ has $m\ge2$ distinct nontrivial characters over an algebraic closure, then
$$
\gamma_{\mathrm{field}}(C_p,V)\ \ge\ \left\lceil p^{1/m}+1\right\rceil .
$$
The answer is affirmative for every such representation. [Blum-Smith, Garcia, Hidalgo and Rodriguez, Question 5.15](https://arxiv.org/html/2303.05626v6#S5.SS2).

### Proof

By the lattice and base-change reductions, $\gamma_{\mathrm{field}}$ is the least $d$ for which the nonnegative zero-sum exponent vectors of total degree at most $d$ have rank $m$. Write the distinct nonzero weights as $a_1,\ldots,a_m\in\mathbb F_p$. Suppose $d-1<p^{1/m}$ and let $a=d-1$. For $d$ at most two, the only possible nonzero vectors are $e_i+e_j$ for inverse pairs of weights. The pairs are disjoint, so their rank is less than $m$. Hence assume $a\ge2$.

If $m$ linearly independent short exponent vectors existed, form an integer square matrix with those rows. Its determinant is nonzero and divisible by $p$, since the nonzero weight column lies in its kernel modulo $p$. Also $d=a+1\le a^2\le a^m<p$. Each row represents a nonzero relation, so it cannot be supported on a single coordinate. Every row has all entries at most $a$.

A row containing $a$ is necessarily $a e_i+e_j$ with $i\ne j$. Read it as an arrow $i\to j$. Each $i$ has at most one outgoing arrow: the other weight must equal $-a a_i$, and the weights are distinct. There are no directed cycles. A cycle of length $\ell$ would imply $p\mid((-a)^\ell-1)$. For $\ell<m$, its nonzero absolute value is at most $a^{m-1}+1\le a^m<p$. For $\ell=m$ even the absolute value is $a^m-1<p$. For $\ell=m$ odd, the only multiple of $p$ that $a^m+1$ could equal is $p$ itself, and $a^m+1$ is composite because $a+1$ is a proper divisor.

Let $k$ be the number of arrows. Order the $k$ pivot columns and the corresponding rows so that within the pivot set arrows go forward, and place the other columns last. The leading pivot block is upper triangular with diagonal $a$, so its determinant is $a^k$. The Schur complement expresses each column variable with an outgoing arrow in terms of its unique terminal variable. For an arrow $i\to j$, the eliminated variable satisfies $x_i=-x_j/a$. Thus a coefficient on a terminal variable is unchanged, and a coefficient on any other variable contributes to its terminal variable with magnitude at most $1/a$ times that coefficient.

In a remaining row every coefficient is at most $a-1$ and the total is at most $a+1$. Let $s$ be its total on terminal variables. Its Euclidean norm in the Schur complement is at most the Euclidean norm of its terminal part plus $(a+1-s)/a$. This quantity is at most $a$ in all three cases below.

- If $s\le a-1$, use the estimate $s+(a+1-s)/a\le a-1+2/a\le a$.
- If $s=a$, the norm of the terminal part is at most $\sqrt{(a-1)^2+1}\le a-1+1/a$. Adding $1/a$ gives at most $a$.
- If $s=a+1$ and $a\ge3$, the maximum possible square norm is $(a-1)^2+4\le a^2$. If $s=a+1$ and $a=2$, all three units lie in separate coordinates and the norm is $\sqrt3\le a$.

Here the maxima for fixed mass follow by moving mass into the largest coordinate until it reaches the cap and repeating. Hadamard's determinant inequality bounds the absolute determinant of the Schur complement by $a^{m-k}$. The original determinant therefore has absolute value at most $a^m<p$, contrary to divisibility by $p$. This rules out rank $m$ whenever $d-1<p^{1/m}$ and proves the bound.

**Verification:** informal proof using the published reduction from transcendence degree to rank of exponent vectors.
