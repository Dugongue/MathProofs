# An explicit depth bound for finite-group membership from algebraic-group growth

**Theorem.** In the Cayley-table model, subgroup membership for arbitrary finite groups of order $N$ has logspace-uniform circuits of polynomial size and depth
$$
O\!\left(
 \frac{(\log N)(\log\log\log N)^{5/2}}{\sqrt{\log\log N}}
 \right).
$$
Iterated logarithms may be bounded below by $2$. The circuits decide membership for generated subgroups with arbitrary composition factors. On a positive input they can also output a bounded-width straight-line program of length $N^{o(1)}$ for the target. The same size, depth, and witness bounds hold for each fixed efficiently compressible pseudovariety of finite semigroups.

This gives an explicit saving over the earlier $o(\log N)$ depth bound in the unrestricted setting of Stober–Thumm–Weiß Question 39(2). The proof uses restriction of scalars in the pivot argument for twisted classical groups and transfers the resulting diameter bound to bounded-width programs. Polylogarithmic program length, and hence the $O(\log\log N)$ depth bound from that route, remains open in general. [Question 39](https://arxiv.org/html/2601.04747v2#S12) · [Earlier bounded-width construction](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/group-membership.md)

## 1. Quantitative classical diameter bound

For every finite simple classical group $T$ of untwisted rank $r\ge9$ over $\mathbb F_q$, there are absolute $C,C'>0$ such that when $\log q\ge \exp(Cr^2\log(r+2))$,
$$
\log\operatorname{diam}(T)
\le \exp(C'r^2\log(r+2))(1+\log\log|T|).
\tag{1}
$$
Diameter denotes the worst symmetric Cayley diameter. Use a connected almost simple algebraic group $G\leq\mathrm{SL}_{M}$ over $\mathbb F_q$ and a subgroup $\Gamma$ of index at most two in $G(\mathbb F_q)$, perfect and with central quotient $T$. For types $A,{}^2A,C$, use the special linear, special unitary, and symplectic groups. For orthogonal groups take the connected special orthogonal algebraic group of the defining quadratic form, with $\Gamma=\Omega$. In even characteristic the odd-dimensional simple classical groups are covered by the symplectic case. The natural representations, with restriction from $\mathbb F_{q^2}$ to $\mathbb F_q$ for the unitary case, have $M=O(r)$, $\delta=\dim(G)=\Theta(r^2)$, and
$$
\Delta=\deg(G)\le \exp(O(r^2\log(r+2))),\qquad
c_0q^\delta\le|\Gamma|\le C_0q^\delta
\tag{2}
$$
for absolute positive $c_0,C_0$.

For the unitary degree bound, work in $\mathbb F_q$ coordinates on each entry of $\mathbb F_{q^2}$. Conjugation is linear. Hermitian-form preservation gives quadratic equations and determinant one gives equations of degree $r+1$. Over the algebraic closure the quadratic extension splits, and the equations solve one factor as the inverse transpose of the other, up to the defining form. Thus the algebraic group is of type $A_r$. Orthogonal form preservation gives quadratic equations, and we take the identity component. Bézout bounds the degree of the varieties and their components because there are $O(r^2)$ coordinates. The order estimates follow from the classical order formulas and the uniform bounds on products of factors $1\pm q^{-i}$. The unitary restriction is the same algebraic device used in the finite-unitary tensor-isomorphism comparison. [Classical groups and restriction of scalars, §§2.4 and 6.1 of Bajpai–Dona–Helfgott](https://arxiv.org/html/2308.09197) · [Finite-unitary tensor comparison](https://github.com/Dugongue/MathProofs/blob/main/MathProofsCrossovers/PROOF.md)

Lift any generating set of $T$ to $\Gamma$. The generated subgroup $H$ satisfies $\Gamma=HZ(\Gamma)$, so $H$ is normal with abelian quotient. Perfection gives $H=\Gamma$. We may therefore prove (1) for $\Gamma$. Fix a symmetric generating set $A$ of $\Gamma$ containing the identity.

The absolute almost simplicity of the connected orthogonal group follows from the central isogeny from the spin group of type $B_r$ or $D_r$ over the algebraic closure. This uses the definition by connected normal algebraic subgroups in §2.2 of Bajpai–Dona–Helfgott. Their Remark 2.8(v) discusses the different issue of simplicity of the finite group of rational points modulo its center. This distinction is what lets us estimate in $G$ while counting elements of $\Gamma$.

### Dimension estimates for the index-at-most-two subgroup

We use the geometric counting part of Bajpai–Dona–Helfgott Proposition 4.4, with a different proof of bounded-degree escape. Let $U,V$ be irreducible subvarieties of the algebraic group over the algebraic closure, with $\dim U<\delta$ and $\dim V>0$. Right-translate $V$ so that it contains the identity, preserving the dimensions of $UgV$ for the same $g$. The stabilizer $S=\{s:Us=U\}$ is a proper closed algebraic subgroup, since $S=\bigcap_{u\in U}u^{-1}U$ on geometric points. If every conjugate of $V$ lay in $S$, then the positive-dimensional $V$ would lie in the normal core of $S$, contrary to absolute almost simplicity. Thus there exist $g_0\in G$, $v\in V$, and $u\in U$ with $u g_0v g_0^{-1}\notin U$. Choose a hypersurface of degree at most $\deg U$ containing $U$ and omitting this point, using their Lemma 2.6. If $F$ defines the hypersurface, then
$$
F(u g v g^{-1})=0
$$
has degree at most $(1+\iota)\deg U$ in $g$, where $\iota\le M-1$ is the degree of inversion. Its vanishing locus $W$ does not contain $G$. For $g\notin W$, the closure of $UgVg^{-1}$ contains $U$ and a point outside $U$. Since this closure is irreducible, its dimension is larger. This argument uses only geometric points and bypasses separability of the product map.

We bound degrees simultaneously across the dimension-estimate induction. Start from varieties of degree at most $D_0=\exp(O(r^2\log(r+2)))$, sufficient for the tori and conjugacy classes used below. Each lower-dimensional variety in the induction of Theorem 4.5 has degree at most $(2\delta)^\delta D^{\delta+1}$ if the current variety has degree $D$, by (4.3) and the proof of Theorem 4.5. Iterate this upper bound for at most $\delta$ steps to get $D_{\max}$ with $\log D_{\max}=\exp(O(r^2\log(r+2)))$. Inside any individual call to Proposition 4.4, the degrees of intermediate closures $U=\overline{Vg_1V\cdots g_jV}$ are at most $(D_{\max}\delta)^{\delta^2}$ by the degree bound for images, since $j+1\le\delta$. Every separating hypersurface therefore has degree at most $D_{\rm esc}=(1+\iota)(D_{\max}\delta)^{\delta^2}$. Bézout and Proposition 2.10 give
$$
|\Gamma\cap W(\overline{\mathbb F}_q)|
\le\Delta D_{\rm esc}q^{\delta-1}<|\Gamma|,
$$
by (2) and the hypothesis on $\log q$. Proposition 2.15 with $\langle A\rangle=\Gamma$ supplies the separating elements in $A^{k_*}$ for $k_*=2\max(2,D_{\rm esc})^{M^2}$, so $\log k_*=\exp(O(r^2\log(r+2)))$. The rest of Proposition 4.4 uses only strict geometric dimension increase and counts of points in fibers and exceptional loci, with radius $\ell m+(\ell-1)k_*$. The induction in their Theorem 4.5 gives
$$
|A^m\cap V|
\le C_1|A^{C_2(m)}|^{\dim(V)/\delta},\quad
C_1=(2\delta\deg V)^{\delta^{\dim V}},\quad
C_2(m)=\delta(m+k_*).
\tag{3}
$$
The radius $C_2(m)$ dominates $\ell m+(\ell-1)k_*$ in every induction call because $\ell\le\delta$. The inequalities for $C_1$ in Theorem 4.5 remain the same. [Hypersurface separation, Lemma 2.6](https://arxiv.org/html/2308.09197#S2.SS1) · [Dimension estimates and escape](https://arxiv.org/html/2308.09197#S4)

### A regular element and a family of tori

Take $W$ to be the discriminant hypersurface in the natural representation. In the unitary case take the discriminant on one projection of the split quadratic algebra over the algebraic closure. The projection is linear, so $\deg(W)=O(r^2)$. There are diagonal elements with distinct eigenvalues over the algebraic closure. For an even-dimensional orthogonal group one can also exclude the eigenvalues $\pm1$ by adjoining their vanishing loci to $W$. Thus $G\not\subseteq W$. A point outside $W$ has a maximal torus as its centralizer and belongs to a unique maximal torus, as follows by diagonalizing in a natural eigenbasis. The property is invariant under conjugation. In the unitary case the two projections are related by inverse transpose and give the same condition.

The point bound and (2) give $\Gamma\not\subseteq W$. Escape produces an element in $A^{k_0}\setminus W$, with $k_0=\exp(O(r^2\log(r+2)))$. If a maximal torus $D$ contains such an element $g$, then $D$ is the centralizer of $g$. Centralizing a fixed matrix is a linear matrix equation, so $\deg(D)\le\Delta$ and $\deg(D\cap W)\le\Delta\deg(W)$. Also $\dim(D\cap W)\le r-1$. The closure of the conjugacy class of $g$ has dimension $\delta-r$ and degree at most $\Delta M^\delta$, by the image degree bound for $x\mapsto xgx^{-1}$. In (3) for these varieties one can use a common constant $C_1\le\exp(\exp(O(r^2\log(r+2))))$.

The number of $\Gamma$-conjugates of such a torus defined over $\mathbb F_q$ is at least $q^{\delta-r}/C_D$ for $C_D=\exp(O(r^2\log(r+2)))$. Indeed $N_\Gamma(D)/(D\cap\Gamma)$ embeds in the Weyl group, of order $\exp(O(r\log(r+2)))$. The point bound gives $|D(\mathbb F_q)|\le\Delta q^r$ and (2) bounds the order of $\Gamma$. [Degree and torus bounds in the pivot argument](https://arxiv.org/html/2308.09197#S5)

### Pivot and iteration

For a positive radius $m$, put $u=|A^m|$, $t=|A^{2m}|$, and $v=|A^{K(m)}|$. Use $k=\max(k_0,2m)$ and take an increasing integer affine function $K(m)$ large enough to dominate $2m$ and $C_2(k+2+2m)$, with $\log(K(m)/m)\le\exp(O(r^2\log(r+2)))$. The bound on $k_*$ gives such a function. Call a torus involved if it contains a point of $A^k\setminus W$. The dependence of $k$ on $m$ is important since an uninvolved torus then has $A^{2m}\cap D\subseteq W$. At least one torus is involved. Either an involved torus $D$ is taken by a generator $a$ to an uninvolved torus $D'=aDa^{-1}$, or some involved torus has all its $\Gamma$-conjugates involved. This follows by following words in $A$ through the conjugacy class of an involved torus.

In the first case, conjugate a point in $D\cap(A^k\setminus W)$ by $a$ to obtain $g'$. The map $y\mapsto yg'y^{-1}$ on $A^m$ has image of size at most $C_1v^{1-r/\delta}$ by (3). A fiber has size at most $|A^{2m}\cap D'\cap W|\le C_1v^{(r-1)/\delta}$, since two elements in the fiber differ by a point of $A^{2m}\cap D'$. Hence $u\le C_1^2v^{1-1/\delta}$.

In the second case the same class map, for an involved element in each torus $D'$, has a fiber of at least average size. Thus $|A^{2m}\cap D'|\ge u/(C_1v^{1-r/\delta})$. The points of this intersection in $W$ number at most $C_1v^{(r-1)/\delta}$. If this bound is at least half the lower bound, we obtain $u\le 2C_1^2v^{1-1/\delta}$. Otherwise sum the points outside $W$ over the conjugate tori. These sets are disjoint by uniqueness of the torus, so
$$
t\,v^{1-r/\delta}\ge \frac{u q^{\delta-r}}{2C_1 C_D}.
\tag{4}
$$

The least nontrivial complex representation degree of $\Gamma$ is at least $c_1 q^{r/2}$ by Landazuri–Seitz. An irreducible representation of the perfect central cover has scalar central action, and its induced projective representation of $T$ is nontrivial whenever the original representation is nontrivial. Thus the projective bound suffices. Nikolov–Pyber's quasirandom product lemma gives either $A^{6m}=\Gamma$ or $t\le C_3 q^{\delta-r/6}$ for an absolute $C_3$. In the latter case put $\alpha=(\delta-r)/(\delta-r/6)$. Then $q^{\delta-r}\ge(t/C_3)^\alpha$, and (4), together with $t\le v$, gives
$$
u\le (2C_1C_D C_3^\alpha)v^{1-r/\delta}t^{1-\alpha}
\le (2C_1C_D C_3^\alpha)v^{1-\eta},\qquad
\eta=\frac{r(\delta-r)}{6\delta(\delta-r/6)}.
$$
We have $\eta=\Omega(1/\delta)$. Combining the cases gives $u\le C_4v^{1-\eta_0}$ unless $A^{6m}=\Gamma$, where $\eta_0=\min(1/\delta,\eta)$ and $C_4=\exp(\exp(O(r^2\log(r+2))))$. [Quasirandom product lemma](https://arxiv.org/abs/math/0703343) · [Landazuri–Seitz representation bounds](https://deepblue.lib.umich.edu/bitstream/handle/2027.42/22240/0000676.pdf)

Start at $m_0=\lceil C_4^{2/\eta_0}\rceil$. Unless already equal to $\Gamma$, this ball has at least $m_0$ points because consecutive balls strictly increase until they reach the group. Iterating $m_{j+1}=K(m_j)$ increases the ball size by a power of at least $1+\eta_0/2$ per step until $A^{6m_j}=\Gamma$. This takes $O(\delta\log\log|\Gamma|)$ steps. Both $\log m_0$ and the increment of log radius per step are at most $\exp(O(r^2\log(r+2)))$. After increasing the absolute diameter constant $C'$ and projecting to $T$, we obtain (1).

## 2. Balancing ranks

Put $L=\max(2,\lceil\log_2(N+2)\rceil)$ and $b=\max(2,\log L)$. The bound of Halasi–Maróti–Pyber–Qiao gives for classical $T$ of order at most $N$
$$
\log\operatorname{diam}(T)
\le O\bigl(r\log q\,(\log(r+2))^2\bigr)
\le O\bigl(L(\log(r+2))^2/r\bigr),
\tag{5}
$$
using $\log|T|=\Theta(r^2\log q)$. Set $r_0=\lfloor c\sqrt{b/\log(b+2)}\rfloor$ for a sufficiently small absolute $c>0$. For $r>r_0$, the right side of (5) is at most $O(L(\log(b+2))^{5/2}/\sqrt b)$, using monotonicity of $(\log(r+2))^2/r$ once $r$ is large. For $9\le r\le r_0$, the choice of $c$ bounds both $\exp(Cr^2\log(r+2))$ and $\exp(C'r^2\log(r+2))$ by $L^{1/4}$ for large $L$. In the large-field case (1) then gives log diameter $O(L^{1/4}(1+\log L))$. For a smaller field, $\log q<L^{1/4}$ and the first expression in (5) gives $O(r(\log(r+2))^2L^{1/4})$. Both bounds are $O(\sqrt L)$ for large $L$. The bounded-rank diameter theorem covers ranks up to eight. Alternating factors have $\log\operatorname{diam}(A_m)=O((\log m)^4\log\log(m+2))$ by Helfgott–Seress, with $m=O(L)$. Sporadic factors contribute a constant. Consequently all nonabelian simple factors of any subgroup of order at most $N$ have log diameter at most
$$
B_*=O\!\left(L(\log(b+2))^{5/2}/\sqrt b\right).
\tag{6}
$$
[Diameter estimates and conventions, Eberhard–Maini–Sabatini–Tracey equations (1.1)–(1.2)](https://arxiv.org/html/2604.15303#S1)

For a finite group $H$, set $\theta(H)=\max(1,\max_T\log\operatorname{diam}(T)/\log\mu(T))$, with $T$ ranging over its nonabelian composition factors and $\mu(T)$ the least faithful permutation degree. For classical groups (5) and $\mu(T)\gg q^{r/2}$ give $\theta(T)=O((\log(r+2))^2)$. A faithful permutation action of a simple group supplies a nontrivial irreducible constituent of dimension at most the permutation degree, giving the needed lower bound on $\mu(T)$. Alternating groups use $\mu(A_m)=m$ and Helfgott–Seress. Fixed-rank Lie-type groups use the bounded-rank diameter theorem and the corresponding representation lower bounds. Therefore $\theta(H)\log L$ is polylogarithmic in $L$ and absorbed by (6).

## 3. From diameter to programs and circuits

The earlier bounded-register construction gives, for each finite group $H=\langle X\rangle$ of order at most $N$, programs of width eight and length $O(L^{26+5\theta(H)}D)$, where $D$ is the largest diameter of a nonabelian composition factor, or $1$. In brief, the short socle word of Eberhard–Maini–Sabatini–Tracey lifts to $H$. Its normal closure has generators of signed length $O(L^{18+5\theta(H)})$ and its radical-free quotient is a product of simple factors of diameter $O(L^4D)$. Schreier generators of the radical then have controlled signed length. Apply the bounded-width solvable-group program theorem to these generators, evaluating each load with two scratch registers. The extension correction after solving the quotient adds one saved register. Repeating across nonsolvable stages adds the lengths while retaining bounded width. The solvable stage uses the same program theorem with no dependence on the exponent. [Short-normal-word construction](https://arxiv.org/html/2604.15303#S5) · [Solvable compression](https://arxiv.org/html/2601.04747v2#S8.SS2) · [Full register proof](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/group-membership.md)

The logarithm of the program length is $O(B_*)$. Use a configuration graph on the eight registers, with each register empty or holding a table element. There are $O((N+1)^8)$ configurations, and the adjacency relation is computed by constant-depth circuits for a load, multiplication or idle step. Signed alphabet loads use inverses read by table comparisons. Repeated Boolean matrix squaring to the log-length bound tests reachability from the empty configuration. Every accepted element is generated, and the program bound proves completeness. The number of squarings is logspace-computable. Compute integer ceilings for $L$, $b$, and $c'=\log(b+2)$, then round $\sqrt{L^2(c')^5/b}$ upward by integer comparisons and multiply by a sufficiently large fixed constant. Register and layer indices take $O(\log N)$ bits. The resulting depth is $O(B_*)$ with polynomial size. The circuit takes the table and generator mask as input and needs no composition series.

Theorem 31 of Stober–Thumm–Weiß requires multiplication-only programs for groups. For nonempty generating sets, replacing each inverse load by exponentiation to the element's order minus one and each identity load by a generator raised to its order gives such programs. For an identity generator, use that generator itself as its own inverse. Repeated squaring costs $O(\log N)$ operations and two scratch registers per replaced load. Hence the group log-length bound remains $O(B_*)$. Theorem 31 transfers it to each efficiently compressible pseudovariety of finite semigroups, with constant width increase and an additive $O(\log N)$ length overhead. The same configuration simulation, using only the supplied generator loads and multiplication, gives the semigroup conclusion. [Theorem 31 and Question 39](https://arxiv.org/html/2601.04747v2)

### Extracting a program in the same depth

During Boolean squaring, for every reachable configuration pair record the lexicographically least successful intermediate configuration. For each possible middle vertex, testing success and suppressing it if any earlier vertex succeeds takes constant depth. At the end similarly select a target configuration containing the requested element. Starting with this configuration and the empty configuration, expand the stored midpoint choices in parallel down the recursion tree. A table lookup for a pair of given configuration indices has constant depth and polynomial size by comparing to every stored pair and selecting the matching entry. Expanding a level takes constant depth and there are $O(B_*)$ levels. The resulting elementary edges encode the successive SLP instructions, with the least valid operation selected locally if multiple instructions realize an edge. Idle steps can be recorded as padding. There are only $2^{O(B_*)}=N^{o(1)}$ tree nodes, so extraction still has polynomial size. All the node and pair indices fit in logspace. A negative input is flagged by the same reachability test. This argument covers both the group and the semigroup configuration graphs.

## Scope and provenance

The new argument makes the explicit product-growth proof work for twisted classical groups and index-at-most-two rational-points subgroups, and balances the resulting quantitative bound with the high-rank diameter estimate. The algebraic realization of the twists, the dimensional estimates and the pivot method are due to Bajpai–Dona–Helfgott. The earlier project construction already gives a uniform $o(\log N)$ depth bound. This result supplies an explicit rate and covers every finite group. The proof is informal, and publication priority for the resulting bound is unestablished.
