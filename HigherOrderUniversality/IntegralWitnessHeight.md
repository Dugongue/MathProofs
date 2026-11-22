# Exponential integral isomorphism witnesses on triangulated six-manifolds

Let $n\ge 1$ and $M=3^n$. There are two polynomial-bit-size triangulated oriented closed simply connected stably parallelizable smooth six-manifolds with torsion-free homology, $b_2=3$ and $b_3=0$, which are orientation-preservingly diffeomorphic, and have the following properties.

1. The minimum bit length of an explicit degree-two cohomology matrix over all degree-one maps is $\Theta(3^n)$ in the displayed integral bases. This holds in either direction. The same minimum applies to oriented diffeomorphisms and oriented homotopy equivalences separately. The bases are supplied by explicit simplicial cycles of size polynomial in $n$.
2. Any simplicial representative of a degree-one map from a subdivision of either input triangulation to a subdivision of the other has at least $\exp(\Omega(3^n))$ source two-simplices.
3. Their rational cup isometry has a matrix of bit length $O(n)$ in the same bases. Their rational homotopy types coincide, and actual nonzero-degree maps exist in both directions.

This quantifies the output issue for ordinary explicit integral isomorphism search. It applies to genuine triangulations in addition to the two ternary cubic tables. It leaves decision complexity and compressed witness representations open. The companion integral tensor construction supplies the triangulations in polynomial time. [Framed realization and classification](https://github.com/Dugongue/MathProofs/blob/f98f6bdf13cb7ba606f020ef0ea07512028cc9d1/ManinGrochowCrossovers/IntegralTensorManifolds.md) · [Rational mapping criterion](https://github.com/Dugongue/MathProofs/blob/f98f6bdf13cb7ba606f020ef0ea07512028cc9d1/ManinGrochowCrossovers/RationalTensorMaps.md)

## Two binary norm lattices

Work in the field $K=\mathbb Q(\sqrt2)$ and maximal order $S=\mathbb Z[\sqrt2]$. Use norm $\mathrm N(a+b\sqrt2)=a^2-2b^2$. Consider these rank-two lattices and corresponding norm polynomials in their indicated bases:

$$
O=\mathbb Z+M\mathbb Z\sqrt2,\quad Q_O(x,y)=x^2-2M^2y^2,
\qquad
I=M\mathbb Z+\mathbb Z\sqrt2,\quad Q_I(x,y)=M^2x^2-2y^2.
$$

Let $\eta=1+\sqrt2$, the fundamental unit of $S$, with norm $-1$, and $\epsilon=\eta^2=3+2\sqrt2$, of norm $1$. For completeness, every unit of $S$ is $\pm\eta^j$. After multiplying by a sign and a power of $\eta$, reduce a unit's positive real value to $[1,\eta)$. If $u=a+b\sqrt2$ lies there, then $|\bar u|=1/u$, so $b=(u-\bar u)/(2\sqrt2)$ is an integer in $[0,1)$. The upper bound follows since $u+1/u<\eta+1/\eta=2\sqrt2$. Therefore $b=0$, $u=1$, proving the assertion. For a background reference on Pell units and the explicit-output distinction see [Lenstra, Solving the Pell equation](https://web.math.ucsb.edu/~agboola/teaching/2017/%25spring/115B/lenstra-pell.pdf).

The projective order of $\epsilon$ in $(S/MS)^{\times}/(\mathbb Z/M\mathbb Z)^{\times}$ is $2\cdot3^{n-1}$. Modulo 3, $\epsilon$ is purely irrational and its square $17+12\sqrt2$ is a scalar unit. An odd power is consequently not scalar modulo 3. For $r>0$, the coefficient of $\sqrt2$ in $(17+12\sqrt2)^r$ has 3-adic valuation $1+v_3(r)$. To verify this, write $u=A+B\sqrt2$ with $3\nmid A$, $3\mid B$. In a power $u^s$ for $3\nmid s$, the first irrational binomial term is $sA^{s-1}B\sqrt2$, and the other irrational terms are all divisible by $B^3$. Thus the valuation is unchanged. Cubing has irrational coefficient $B(3A^2+2B^2)$ and raises it by exactly one. The real component remains a unit mod 3 under all these powers. This proves the asserted valuation and projective order. Since the projective order of $\eta^2$ is even, the projective order of $\eta$ is $4\cdot3^{n-1}$.

Write $k=3^{n-1}$. The element $\epsilon^k=A+B\sqrt2$ has $3\nmid B$ because $k$ is odd and its square is scalar modulo $M$. The square's irrational coefficient is $2AB$, so $M\mid A$. It follows that $\epsilon^k O=I$: modulo $MS$, these two lattices both reduce to the line spanned by $\sqrt2$, and both contain $MS$. An explicit norm-one isometry $O\to I$ given by multiplication by $\epsilon^k$ has matrix
$$
P=\begin{pmatrix}A/M&2B\\B&MA\end{pmatrix}
$$
in the displayed bases. Its determinant equals $A^2-2B^2=1$. Its entries have $O(3^n)$ bits.

Conversely, any integral lattice isomorphism $T:O\to I$ satisfying $\mathrm N(Tx)=d\,\mathrm N(x)$ for $d\in\{1,-1\}$ extends to a rational norm similitude on $K$. Put $u=T(1)\in I$. Then $\mathrm N(u)=d$, so $u$ is an $S$-unit. The similitude $u^{-1}T$ fixes $1$ and preserves norm. By polarization with $1$ it also preserves trace, so it maps $\sqrt2$ to $\sqrt2$ or $-\sqrt2$. It is identity or quadratic conjugation. Since conjugation preserves $O$, it follows that $uO=I$. Writing $u=\pm\eta^j$, equality of the lines modulo $M$ gives
$$
j\equiv 2k\pmod{4k}.
$$
In particular $j$ is even, so no anti-isometry is possible, and $u=\pm\epsilon^r$ with $|r|\ge k$. Its irrational coordinate, namely the second coefficient of the first column of $T$, has magnitude $(\epsilon^{|r|}-\epsilon^{-|r|})/(2\sqrt2)$. Thus its bit length is $\Omega(3^n)$. The same lower bound holds in the reverse direction because inversion of a unimodular matrix of fixed size changes bit lengths by at most a constant factor and additive constant.

## Passing to actual six-manifolds

Use the diagonal cup cubics $6tQ_O(x,y)$ and $6tQ_I(x,y)$. The companion binary-coefficient construction realizes these cubics directly by framed surgery on primitive sparse relations: its input step needs that every diagonal coefficient is divisible by 6, as holds here. This gives a triangulation of size polynomial in $n$ for each, with the indicated cohomology coordinates. An integral isometry of their oriented cup cubics must preserve the linear factor $t$ up to scalar, since the binary quadratic $a x^2+bxy+c y^2$ of each norm form has no rational linear factor. The induced scalar on $t$ is $1$ or $-1$: the coordinate form $t$ is primitive and a unimodular change of basis preserves primitivity. Restriction to $t=0$ after canceling $t$ gives a binary norm isometry or anti-isometry. This transfers the integral lower bound. The displayed isometry $P$ of the norm lattices extends by the identity on the $t$-axis, attaining $O(3^n)$ bits.

A degree-one map gives a split injection in integral cohomology by integral Poincaré duality and transfer. Equal finite ranks and torsion-free cohomology make this an isomorphism. It must preserve the oriented cup cubic, yielding the lower bound for every degree-one map. The marked version of the Wall–Jupp theorem realizes the indicated oriented cup isometry by an orientation-preserving diffeomorphism. Indeed it extends by the inverse dual in degree four and the identity in top degree to a ring isomorphism, and the relevant characteristic classes vanish by stable parallelizability. This attains the bound separately for the map classes in the theorem. [Wall](https://doi.org/10.1007/BF01389738) · [Jupp](https://doi.org/10.1017/S0305004100076854) · [Marked formulation, Ning Theorem 3.1](https://arxiv.org/html/2505.09550v1#S3.Thmtheorem1)

Over $\mathbb Q$, the diagonal map $(x,y)\mapsto(x/M,My)$ is an isometry from $Q_O$ to $Q_I$; together with $t\mapsto t$ it supplies the small rational cup witness. The rational mapping criterion for simply connected six-manifolds with equal Betti numbers gives the claims about rational homotopy and nonzero-degree maps. [Rational mapping criterion](https://github.com/Dugongue/MathProofs/blob/f98f6bdf13cb7ba606f020ef0ea07512028cc9d1/ManinGrochowCrossovers/RationalTensorMaps.md)

## Simplicial witness size

The framed construction can keep one unused parallel factor sphere for each of its three original coordinates. Include these spheres in the marked disjoint coordinate spheres and require that no tube endpoint belongs to them. Their normal charts then avoid the surgery, and the triangulation may refine along them by the same fixed-dimensional rational subdivisions. The primitive relations on the auxiliary coordinates leave the three original coordinate spheres as an integral basis of $H_2$. Thus each of the displayed dual basis cycles is a sum of polynomially many original oriented triangles with coefficients $\pm1$.

For either input triangulation, choose rational 2-cocycles representing the three displayed dual cohomology basis elements by imposing the cocycle equations and prescribed evaluations on the three displayed cycles. These are solvable rational linear systems of polynomial dimensions with bounded integer entries. A basic solution obtained by a nonsingular full-rank minor, setting free coordinates to zero, has all coefficients of magnitude at most $\exp(\operatorname{poly}(n))$ by the determinant bound. This may be done in polynomial bit time.

Suppose the target is subdivided. Assign each new vertex to any original vertex in its smallest containing original simplex. This gives a simplicial map from the subdivision to the original target and is homotopic to the identity of the target realization because each point and its image lie in a common original simplex. Composing with it preserves the degree. On the source subdivision each of the original cycles subdivides to a chain with at most the total number $N$ of source two-simplices, counted with coefficients $\pm1$. A simplicial map sends each oriented simplex to a single oriented simplex or to zero. Consequently every matrix coefficient in degree-two cohomology has magnitude at most $N\exp(\operatorname{poly}(n))$ by the evaluation formula. The lower bound from the norm calculation is $\exp(\Omega(3^n))$ for at least one coefficient, so $N\ge \exp(\Omega(3^n))$.

## Status and relation to the Grochow questions

This is an explicit separation of the smallest integral and rational transporter sizes on a realizable family. It combines the fixed-dimensional rational comparison with the polynomial-bit integral triangulation construction. Grochow–Qiao ask about the relationship between their classes over different fields, and Part V identifies integral tensor isomorphism with several arithmetic orbit problems. The output-size theorem concerns the explicit integral search version and its geometric realization. [Grochow–Qiao, Open Question 10.6](https://arxiv.org/html/1907.00309#S10.SS2) · [Part V](https://arxiv.org/abs/2611.00735)
