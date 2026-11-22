# Exact side thresholds for joint prime tests of rational tensor isomorphism

Let $A,B$ be finite étale $\mathbb Q$-algebras of the same positive dimension $n$, all of whose field factors are abelian over $\mathbb Q$. Compare their ordinary multiplication tensors (three independent changes of basis). For a set $S$ of good primes define one integer
$$
M_A(S)=\sum_{E\text{ a factor of }A}[E: \mathbb Q]\,{\bf1}\{\text{every }p\in S\text{ splits completely in }E\}.
$$
Include repeated field factors with multiplicity. A singleton answer counts degree-one points of the unmarked reduction. Higher joint counts require the primes to split in the **same rational factor**. Independent unmarked modular black boxes need not supply that information.

**Sharp theorem.** For $k\ge0$, let $b_k=\prod_{i=0}^k(1+2^i)$. For $n<b_k$, equality of all joint counts of order at most $k$ implies rational tensor isomorphism. Already on multiquadratic splitting fields, for every $n\ge b_k$ there are nonisomorphic examples of side $n$ with equal counts at every such set of good primes. For the sufficient direction one only needs primes $p\le C\log^2(2D)$, avoiding $D$, where $D$ is the absolute product of the discriminants of any two full orders in the inputs and $C$ is absolute and effective. Dirichlet GRH supplies the bound on prime size. The combinatorial threshold and the examples are unconditional.

| Number of primes in a joint query | Last side where this order always suffices | First side admitting a collision |
|---:|---:|---:|
| 0 | 1 | 2 |
| 1 | 5 | 6 |
| 2 | 29 | 30 |
| 3 | 269 | 270 |
| 4 | 4,589 | 4,590 |

More precisely, fix any finite abelian Galois splitting field $K/\mathbb Q$ and write $G=\operatorname{Gal}(K/\mathbb Q)$. Put $r_p=\dim_{\mathbb F_p}(G_p/pG_p)$, where $G_p$ is the Sylow $p$-subgroup. Among products split by $K$ the first collision has side
$$
\min_{p: r_p>k}\frac p2\prod_{i=0}^k(1+p^i).
$$
If this set is empty, the counts decide every side. This is a statement about algebras split by $K$ and permits smaller splitting fields. For example an elementary abelian cubic splitting group of rank at least three first permits a two-prime collision at side $120$, while binary rank three permits one at $30$.

## Restrict to the first subgroup that detects a difference

Write $X=\operatorname{Hom}_{\mathbb Q\text{-alg}}(A,\overline{\mathbb Q})$ and similarly $Y$. The $G$-sets of embeddings have size $n$. A field $K^U$ contributes the orbit $G/U$. These orbits determine the factors and the algebra. For completeness, an invertible tensor transporter $R(xy)=P(x)Q(y)$ induces an algebra isomorphism: $a=P(1)$ and $b=Q(1)$ are units by invertibility of their multiplication maps; then $a^{-1}R(x)b^{-1}$ is a unital algebra isomorphism. Conversely use the same algebra isomorphism three times.

For any subgroup $V$, let $m(V)=|X^V|-|Y^V|$. For Frobenius elements of the primes of $S$ the mark at the subgroup they generate is precisely $M_A(S)-M_B(S)$. This uses that $G$ is abelian, so every point of a transitive orbit is fixed together or none is. First work with arbitrary group elements as probes. If the two $G$-sets differ, some mark differs by triangularity of the orbit marks. Choose an inclusion-minimal subgroup $H$ with $t=m(H)\ne0$. If all tuples of length at most $k$ agree, $H$ needs at least $k+1$ generators. Equal total degree gives $H\ne1$.

Restrict both sets to $H$. Write $a_U$ for the signed difference of multiplicities of $H/U$. For $V\le H$ the marks obey $m(V)=\sum_{U\ge V}[H:U]a_U$. All proper marks vanish by minimality. Finite-poset Möbius inversion therefore gives
$$
[H:U]a_U=t\,\mu(U,H).
$$
The sum of the positive orbit sizes in this difference is half its weighted absolute sum, since the total signed size is zero. It is at most $n$, even if common restricted orbits cancel. This mark formula is the abelian case of the classical primitive idempotent formula of Gluck and Yoshida. [Burnside-ring formulas](https://www.lamfa.u-picardie.fr/bouc/burnamscorr.pdf)

Select $p$ so the Sylow $p$-subgroup $P$ of $H$ has generator rank $s>k$. Such a $p$ exists by the decomposition theorem for finite abelian groups, and $r_p(G)\ge s$ because $P[p]\subseteq G_p[p]$. In $H$ an index-$p$ subgroup has Möbius value $-1$, so $p\mid t$. For subgroups $U$ containing $pP$ and the prime-to-$p$ part of $H$, the interval above $U$ is a subspace lattice. At codimension $j$ its Möbius value is $(-1)^jp^{\binom j2}$. Indeed the Gaussian binomial product identity
$$
\sum_{j=0}^s {s\brack j}_p p^{\binom j2}z^j=\prod_{i=0}^{s-1}(1+p^i z)
$$
follows by induction from the Gaussian binomial recurrence obtained by intersecting subspaces with a fixed hyperplane. Specializing at $z=-1$ gives the zero-sum recurrence characterizing these Möbius values. Specializing at $z=1$ sums their magnitudes. Thus
$$
n\ \ge\ \frac{|t|}{2}\sum_{U\le H}|\mu(U,H)|\ \ge\ \frac p2\prod_{i=0}^{s-1}(1+p^i).
$$
This gives the proposed sufficient dimension range for fixed $K$ and, by $p\ge2$, the universal bound.

## Extremizers

Choose a quotient $E$ of $G$ isomorphic to $(C_p)^{k+1}$ for a minimizing $p$. For each subgroup $U\le E$ take the signed number of orbits $E/U$ to be $a_U=p\mu(U,E)/[E:U]$. These are integers. At codimension $j$ the exponent of $p$ in the magnitude is $1+\binom j2-j=(j-1)(j-2)/2\ge0$. Put the positive orbits on one side and the negative ones on the other. Inversion gives top mark $p$ and zero marks at every proper subgroup, including the trivial one. Each side has degree $(p/2)\prod_{i=0}^k(1+p^i)$. Inflate these sets to $G$ and replace each orbit by its fixed field inside $K$. Every $k$-generated subgroup has proper image in $E$. Its marks therefore agree. The two algebras remain different. Adjoin the same rational factors on each side to realize every larger degree. For the universal minimum choose any multiquadratic field generated by square roots of $k+1$ different primes. For $k=0$ the data are dimension alone, and the same construction compares a quadratic field with two rational factors.

In side 30 take any triquadratic field $K$. Compare two rational factors and its seven quartic subfields with its seven quadratic subfields and two copies of $K$. Two-prime answers always agree. Three primes whose Frobenius elements form a basis give counts $2$ and $0$. In particular the two-prime equality is compatible with **every** choice of two primes, however large.

## Why small primes suffice

If a mark differs on a subgroup generated by at most $k$ elements, take its generators. Replace them one at a time, retaining a nonzero difference. Fixing all coordinates except the current coordinate selects, on each side, just the original field-factor occurrences split by all fixed elements. The remaining section $h$ is an integral difference of abelian permutation characters. Write $h=\sum a_\chi\chi$, $M=\sum |a_\chi|^2$, $L=\sum|a_\chi|$, $W=\sum |a_\chi|\log q_\chi$ for primitive conductors $q_\chi$. Each transitive abelian permutation character contains its quotient characters once. The conductor–discriminant formula thus gives $W\le\log D$, also after selecting factors. A nonzero section has $M\ge1$, $L\le M$ by integrality, and $L^2\le(1+W/\log3)M$ by Cauchy–Schwarz.

For a fixed nonnegative smooth weight supported in $(1/2,1)$ with integral $I>0$, the smoothed explicit formula under Dirichlet GRH gives
$$
\sum_{p\nmid D}\eta(p)\log p\,w(p/x)
={\bf1}_{\eta=1}Ix+O_w(\sqrt x\log(2q_\eta)+\log(2D)).
$$
Indeed the zero terms have size $O_w(\sqrt x\log(2q_\eta))$ by rapid Mellin decay and the unit-interval zero count. Removing higher prime powers costs $O_w(\sqrt x)$ by Chebyshev, and excluded primes cost $O_w(\log(2D))$. Use Kronecker–Weber to read characters as Dirichlet characters at the good primes. Expanding $|h|^2$ and using $q_{\chi\bar\psi}\le q_\chi q_\psi$ shows the corresponding weighted prime sum equals $IxM$ with error at most
$$
O_w\!\left(\sqrt x(L^2+LW)+L^2\log(2D)\right).
$$
Taking $x=C\log^2(2D)$ makes the sum positive for a fixed effective $C$. There is a prime in this range preserving the discrepancy. Iterate on the coordinates. Repeats can be dropped because fixing a point twice gives the same condition. This is the section argument from the earlier joint-count theorem; replacing a group element by a word in prime generators would not justify this conclusion. [Weighted prime estimates](https://doi.org/10.1090/S0025-5718-96-00763-6) · [Verified Dirichlet hypothesis](https://math.mit.edu/~drew/grh/)

## Recovering the algebra from a raw tensor

The statement also applies to raw rational tensors in arbitrary bases that become diagonal of full side over the algebraic closure, with abelian splitting field for their diagonal summands. The multiplication algebra can be recovered deterministically in polynomial bit time. Regard the input as a bilinear map $T:U\times V\to W$ on three spaces of dimension $n$. Over a splitting field its left-contraction determinant is a nonzero constant times a product of $n$ nonzero linear forms. Each form is nonzero as a polynomial on the rational moment curve $(1,t,\ldots,t^{n-1})$. Their product has at most $n(n-1)$ roots there. Test successive integers starting at zero to find a left regular element $u_0$ with invertible $L(v)=T(u_0,v)$. The same argument finds $v_0$ with invertible $R(u)=T(u,v_0)$. Put
$$
x*y=T(R^{-1}x,L^{-1}y).
$$
The unit is $T(u_0,v_0)$. In diagonal coordinates this multiplication is coordinatewise multiplication divided coordinatewise by the corresponding nonzero entries of that unit, and hence becomes the split algebra. The identity above is a rational tensor isotopy, so the resulting algebra is independent up to isomorphism of the choices. Conversely any rational finite étale algebra yields a raw geometrically diagonal tensor this way. The searches use polynomially many rational determinant tests on polynomial-bit entries. Rational basis inversion, denominator clearing, trace discriminants, and Hermite normal form also have polynomial bit cost. For example, with a rational basis $w_i$ one obtains an order as the span over the integers of the unit and the $c w_i$ for a common denominator $c$ of the multiplication table. Rational étale decomposition then recovers the field factors for evaluating the separate joint queries. This does not impose any bound on the degree of the compositum. [Algorithms for rational algebras](https://arxiv.org/abs/1509.08843)

For the side-30 example take $K=\mathbb Q(\sqrt2,\sqrt3,\sqrt5)$. The quadratic-character signs of $7,11,13$ in this basis, with a nonsquare represented by one, are $011,100,101$. They span binary rank three. These three primes give the first pair of different counts in the increasing lexicographic search through good primes below 100.

## Comparison and verification

The previous generator-rank theorem bounded the required order by $\lfloor\log_2 n\rfloor$ and exhibited rank-sharp pairs without optimizing dimension. Here the worst-case order is exactly the smallest $k$ with $n<b_k$, asymptotic to $\sqrt{2\log_2 n}$. The known side-six example is the $k=1$ case; the minimal dimension at **every** order and the fixed-splitting-field formula supply the extension. Webster studies the related single-element notion of linearly equivalent permutation sets. The proposed ranking is as an extension of the existing local–global diagonal-tensor entry. Literature priority for this version remains open. [Earlier joint counts](https://github.com/Dugongue/MathProofs/blob/main/RiemannGrochowTransfers/JointPrimeCounts.md) · [Webster](https://arxiv.org/abs/math/0610205)

The general proof is written mathematics. The Lean companion treats the explicitly displayed subgroup incidence table of $(C_2)^3$ and arbitrary nonnegative orbit multiplicities. It has separate statements for the lower bound of 30 and for the pair attaining it. The arithmetic identification and the general finite-group theorem are outside that formalization.
