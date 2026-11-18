# Exact and parity antichain counting in rank-three geometric lattices

**Theorem.** Counting the antichains of an explicitly presented rank-three geometric lattice is #P-complete under polynomial-time metric reductions. Testing oddness is ⊕P-complete under polynomial-time many-one reductions, even if each line has at most three points. Both hardness statements hold when a rational projective-plane representation is supplied. The same constructions can instead supply representations over prime fields of polynomial cardinality, with the prime part of the output. The bounds concern explicit inputs and are informal.

This strengthens a sharp height-four hardness result for finite lattices to geometric lattices. It concerns antichains of the lattice of flats, rather than bases of the matroid. It also gives a structured class within the broader restricted counting question posed by Amarilli. The separate case of distributive lattices remains outside this proof. A targeted search did not identify the precise geometric-lattice result, and publication priority remains unverified. [Amarilli’s restricted counting question](https://a3nm.net/work/research/questions/#complexity-of-counting-antichains-in-restricted-poset-classes)

## The counting formula

A simple rank-three matroid obtained from distinct projective points has one bottom flat, its points, its lines determined by pairs of points, and the whole set. A line is represented in the lattice by the subset of input points on it. The point-line incidence gives every comparability other than those involving the extremes. This is an explicitly presentable geometric lattice of height four. At rank at most two the lattice has height at most three and its number of antichains is immediate.

For a point subset $T$, write $\ell(T)$ for the number of lines all of whose points are in $T$. An antichain avoiding top and bottom determines a set of chosen point flats. If $T$ is its complementary point set, exactly the $\ell(T)$ lines contained in $T$ can be freely chosen. Therefore the count, minus two for the two singleton extremal antichains, is
$$
Z=\sum_T2^{\ell(T)}.
$$
Membership in #P and in ⊕P for the corresponding parity language follows by guessing one subset of lattice elements and testing the antichain condition. From rational point coordinates one can enumerate the lines by examining every pair and testing collinearity.

## Parity with all line lengths at most three

Take a simple graph $G=(V,E)$ with at least three vertices. For every nonedge $uv$ add a dummy point $d_{uv}$. Declare $\{u,v,d_{uv}\}$ a three-point line, and add a two-point line at each pair not already covered. Every pair occurs on exactly one line. The following gives a rational representation, so no geometric existence assumption is needed.

Place the vertices at points $(x_i,x_i^2)$ with distinct positive integers $x_i$. No three such points are collinear. In succession place each $d_{uv}$ on the line through $u,v$, avoiding its intersections with all other lines determined by pairs of already placed points. Also avoid the previously placed points themselves. The joining line of $u,v$ contains only those two points until the dummy for it is placed, because all original vertices were present in each earlier avoidance step. There are polynomially many forbidden locations, so an integer affine parameter along the line can be found by a polynomial search. Each point uses original endpoint coordinates for its parametrization, keeping coordinate magnitude polynomial. Thus the declared triples and the remaining pairs are exactly the represented lines.

Modulo two, the count is the number of point subsets $T$ containing no full line. If $T$ contains no dummy, these are exactly the independent sets of $G$. If $d_{uv}\in T$, then no other dummy can belong to $T$, and no original vertex other than $u,v$ can belong to $T$, since each of those pairs would be a full two-point line. The triple prevents both endpoints from being present. Thus the other subsets are exactly $\{d_{uv}\}$, $\{d_{uv},u\}$, and $\{d_{uv},v\}$ for each nonedge. Writing $\bar m$ for the number of nonedges, the parity is therefore
$$
\#\operatorname{IS}(G)+3\bar m\pmod2.
$$
Before building the configuration, add one universal vertex to $G$ if $\bar m$ is odd. This preserves the number of nonedges and changes the independent-set count by exactly one, because the only new independent set is the singleton of the added vertex. The lattice parity now equals the original graph parity. The finitely many graph inputs below size three can be treated directly. Valiant gives the required parity hardness even on a restricted planar graph class. [Valiant, *Accidental Algorithms*](https://people.seas.harvard.edu/~valiant/focs06.pdf)

## Exact counting with one lattice query

### Realizing the points and the adjustable lines

Again take a simple graph $G=(V,E)$, with $n\ge3$ original vertices. Place its vertices at $(x_i,x_i^2)$ with $x_i=(2n+1)i^2+i$ for $1\le i\le n$. The slope of the line through $i,j$ is $x_i+x_j$. These slopes are all distinct for unordered pairs. Indeed, the sum modulo $2n+1$ recovers $i+j$, and then the original equality recovers $i^2+j^2$, which determines the unordered pair.

For each nonedge place a point $d_{uv}$ at infinity in the direction of the line through $u,v$. Let $D$ be the set of these dummy points and let $N=n+|D|$. All dummies are on the line at infinity. Add a block $U$ of $t$ further points at infinity, in distinct directions different from every original pair slope. The points of $D\cup U$ constitute one line, and every $U$–original pair is on a two-point line. Other lines among the old points are the triples consisting of a nonedge pair and its dummy, and the remaining ordinary pair lines.

Then add a second block $W$ of $s$ points on the affine horizontal line $y=-1$. Choose each point at a distinct integer horizontal coordinate, avoiding intersections with all lines determined by pairs of points from $V\cup D\cup U$. None of those points lies on $y=-1$ and its direction is absent from $D\cup U$. Thus each pair joining $W$ to $V\cup D\cup U$ gives a two-point line, and all $W$ points give one common line. With polynomial block sizes there are polynomially many positions to test, and the full projective coordinates of the constructed points have polynomial magnitude.

### Recovering the weighted subset-size counts from the final block

Let $A=V\cup D\cup U$ have $M=N+t$ points before adding $W$. Write
$$
Q_t(X)=\sum_{T\subseteq A}2^{\ell_A(T)}X^{|T|},
$$
with $\ell_A$ counting full lines in the configuration on $A$. When a fixed old subset of size $k$ is combined with $j$ selected points of $W$, there are $kj$ new full cross lines. The new line on $W$ is full precisely when $j=s$. Summing over the new points multiplies the old weight by
$$
B_k=(1+2^k)^s+2^{ks}.
$$
Hence a single antichain count in the final lattice, minus two, is
$$
\sum_{k=0}^M[X^k]Q_t(X)\,B_k.
$$
The coefficients have total at most $2^{M+\binom M2}$, since there are at most $\binom M2$ lines. Successive bases satisfy $B_{k+1}/B_k\ge(3/2)^s/2$. Taking $s=4(M+\binom M2+3)$ makes this ratio larger than the total coefficient bound. Starting at the largest base, floor-divide by that base and subtract its recovered term. All smaller terms have total less than the divisor, so the coefficient is exact. Repeating recovers $Q_t(X)$ with polynomially many integer operations on polynomial-length numbers.

### Eliminating every dummy using one selected block size

For $T\subseteq V\cup D$ let $a=|T\cap V|$ and let $L_*(T)$ count full old lines apart from the line at infinity. Define
$$
P_a(X)=\sum_{\substack{T\subseteq V\cup D\\|T\cap V|=a}}
2^{L_*(T)}X^{|T|},\qquad
R_a(X)=\sum_{\substack{T\subseteq V\cup D\\|T\cap V|=a\\D\subseteq T}}
2^{L_*(T)}X^{|T|}.
$$
Both have degree at most $N$. Each selected point of $U$ creates $a$ full cross lines. The infinity line contributes one additional full line precisely when all dummies and all $U$ points are selected. Thus, for $t\ge2$,
$$
Q_t(X)=\sum_{a=0}^n P_a(X)(1+2^aX)^t
+\sum_{a=0}^n R_a(X)(2^aX)^t.
$$
Put $d=(n+1)(N+1)$. At $t\ge d$, the second sum has zero coefficients at degrees $0,\dots,d-1$. The first $d$ coefficients give a square linear system for the $(n+1)(N+1)$ coefficients of the polynomials $P_a(X)$. With rows $k$ and columns $(a,h)$ its entries are
$$
A_{k,(a,h)}(t)=
\begin{cases}
\binom{t}{k-h}(2^a)^{k-h},&k\ge h,\\
0,&k<h,
\end{cases}
\quad 0\le k<d,\ \ 0\le h\le N.
$$
Its determinant is a nonzero polynomial in $t$. To see this, scale row $k$ by $t^{-k}$ and column $(a,h)$ by $t^h$ and let $t$ tend to infinity. The limiting entry is $(2^a)^{k-h}/(k-h)!$ for $k\ge h$. Multiply row $k$ by $k!$ to recognize the transpose of the evaluation matrix for derivatives of orders $0,\ldots,N$ at the distinct points $2^a$. It is invertible, since a polynomial of degree less than $d$ vanishing with multiplicity $N+1$ at all those points must be zero.

The unscaled determinant has degree at most $d(d-1)$. In advance of any oracle query one can scan $d(d-1)+1$ consecutive integers starting at $d$, compute the determinants exactly, and choose one with nonzero determinant. All trial values have polynomial magnitude, all matrix entries have polynomial bit lengths, and exact elimination is polynomial-time. Use just this $t$ in the point construction. The one recovered $Q_t(X)$ determines all $P_a(X)$.

The coefficient $[X^a]P_a(X)$ restricts to subsets of the original vertices, since $|T|=a$ allows no dummy. For such a subset the full lines are exactly the original graph edges whose two endpoints lie in it. A nonedge line requires its dummy and therefore does not contribute. Summing those coefficients gives
$$
\sum_{T\subseteq V}2^{|E(G[T])|}.
$$
This equals $\#\operatorname{IS}(S(G))$ for the graph $S(G)$ formed by subdividing every edge once. To see this, let $T$ consist of the original vertices *omitted* by an independent set and observe that each subdivision vertex is free precisely when both original endpoints are omitted.

### The hardness source under a single-query reduction

For clarity, $\#\operatorname{IS}(S(G))$ is #P-hard under a single-query reduction, even though all its graphs are bipartite. Use the separated-weight graph construction in the companion height-four lattice proof. For an arbitrary source graph $F$ with $n_0$ vertices and $m_0$ edges, put $t_2=9(n_0+2)$, $t_1=4(m_0t_2+n_0+2)$. Replace each edge of $F$ by $t_2$ internally disjoint length-two paths to form part of $G$, and add $t_1\deg_F(v)$ private leaves to each original vertex. In $S(G)$, the edge paths have endpoint weights $(5,3,2)$ and the leaf paths have root weights $(3,2)$. Conditional on the original spins, group by the number $c$ of original edges of type $11$ and the total degree $k$ of chosen original vertices. At fixed $k$, increasing $c$ by one changes the integer base by the ratio $(10/9)^{t_2}>2^{n_0+2}$. Increasing $k$ by one decreases the leaf factor by $(3/2)^{t_1}$, larger than the maximal edge-factor variation $(5/2)^{m_0t_2}$ times $2^{n_0+2}$. Therefore the same greedy exact decoding recovers all grouped counts from a single value and the sum over $c=0$ is $\#\operatorname{IS}(F)$.

To see that total independent-set counting can itself be used with one query from #SAT, give each Boolean variable two adjacent choice vertices and each clause a clique of choices for its first true literal. Connect each clause-choice vertex to the variable-choice vertices inconsistent with that literal being true and all earlier clause literals being false. An independent set taking one vertex from each variable and clause block corresponds bijectively to a satisfying assignment. If the graph has $L$ vertices, attach $L+1$ leaves to each vertex. Each independent set of size $j$ in the preattachment graph then produces $(2^{L+1})^{L-j}$ sets of the enlarged graph. Its total independent-set count yields every size coefficient by extracting a digit in base $2^{L+1}$. These transformations compose with the one lattice query above, proving metric #P-hardness.

## Finite-field realizations

Use homogeneous integer coordinates for both constructions. All entries have polynomial magnitude, including those chosen by finite avoidance. Take a prime greater than the largest absolute nonzero $3\times3$ determinant of the point coordinate columns and greater than the largest absolute nonzero coordinate. It has polynomial magnitude and can be found by elementary trial division and Bertrand’s postulate. Reduction modulo this prime preserves exactly the collinear triples and point ranks. Distinct point pairs remain distinct because every independent pair extends to an independent triple in the rank-three configuration. The resulting represented lattice is the same one.
