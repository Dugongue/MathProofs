# New results on mapping degrees, boundary extension, and persistence

The main results are written proofs. We use the classical integer Diophantine representation theorem, topological realization and obstruction theory, and the previously developed extension and persistence arguments where indicated. All priority judgments are provisional. [Earlier MathProof results for Manin](https://github.com/Dugongue/MathProofs/blob/51ba97e579d31bf86ba528ca5a99a61752c48934/ManinTop20/ManinNewProofs.md)

## 1. A halting-complete mapping degree set for fixed six-manifolds

**Theorem.** Fix $k\ge2$. Every computably enumerable subset $A$ of the positive integers that is upward closed under divisibility and contains every integer divisible by a prime $k$-th power is realized as the exact degree set
$$
D(M,(S^2)^3)=\{0\}\cup \{\pm a:a\in A\}
$$
for a closed oriented simply connected smooth six-manifold $M$ with torsion-free homology. In particular, every cofinite divisibility-upward subset occurs. One fixed pair has a many-one complete degree set even though all residue classes occur modulo every integer and every degree occurs after localization at any prime or rationally.

### Homogeneous gates with integral decoding

Call a positive integer $k$-free if every prime valuation is less than $k$. Take a polynomial gate system over the integers recognizing $A$ at an input $T$. Use DPRM and, if the chosen representation has nonnegative witnesses, use sums of four squares. Homogenize the gates to quadrics using a coordinate $V$ and let $U$ be the homogeneous input coordinate. When division is integral the decoded input is $U/V$. Impose also
$$
U^2=VZ,\qquad U^{k+1}=V^k C,\qquad a^k=V^{k-1}s_a
$$
for each original gate coordinate $a$, including the input. Compile the higher-power equations into homogeneous quadrics by computing both sides with multiplication gates relative to $V$. This preserves the equations wherever $V\ne0$. Denote all resulting quadrics by $q_j(x)=0$.

Any nonzero $U$ makes $V\ne0$. Suppose further that $|U|$ is $k$-free. The second equation gives $k v_p(V)\le(k+1)v_p(U)$, so $v_p(V)\le v_p(U)<k$ for every prime $p$. The third gives $k v_p(a)\ge(k-1)v_p(V)$ for $a\ne0$, hence $v_p(a)\ge v_p(V)$; divisibility is automatic when $a=0$. Thus all the original gates decode integrally and $U/V$ lies in $A$. By upward closure $|U|$ lies in $A$. A non-$k$-free $|U|$ already lies in $A$ by assumption. Conversely every $U\in A$ has witnesses with $V=1$, since the auxiliary powers can then be evaluated over the integers. The absolute nonzero $U$ values are exactly $A$.

### Realize the square-zero locus of a six-manifold

Introduce separate coordinates $y_j$, a coordinate $z$, and two coordinates $b,c$. Put $K=288$. Add a dummy zero quadric if necessary so that $y_1$ exists. On the full free integer lattice specify a symmetric trilinear form $\mu$ by its diagonal cubic
$$
\mu(v,v,v)
=K\left(\sum_j y_j q_j(x)+z\left(\sum_j y_j^2+z^2\right)\right)
+3z^2y_1+6Ubc .
$$
Here $U$ is one coordinate of $x$, and all variables in the cubic denote coordinates of a cohomology class. Integral polarization of the $K$-multiple has every trilinear coefficient divisible by 48, since the diagonal coefficients are divided only by 1, 3 or 6. The $3z^2y_1$ term has coefficient 1 on the relevant trilinear entries, as does the $6Ubc$ term.

Specify $w_2=e_z\bmod2$, where $e_z$ is the $z$ basis vector in degree two. Specify the Pontryagin functional by $p_1(v)=3y_1(v)$ and take third Betti number zero and smooth obstruction zero. For an integral vector $w=e_z+2v$, the $K$ part vanishes modulo 48 and the $Ubc$ term is divisible by 48. The difference of the remaining diagonal cubic and the Pontryagin functional is $24 z(v)(z(v)+1)y_1(v)$, a multiple of 48. This is the smooth Jupp admissibility congruence. Thus the data are realized by a simply connected smooth closed six-manifold with torsion-free homology, and it is nonspin. [Jupp’s classification and realization](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/classification-of-certain-6manifolds/EFFEA60DC78627B37915377D232680A4) · [Explicit admissibility congruence](https://archive.mpim-bonn.mpg.de/id/eprint/3317/1/preprint_1994_46.pdf)

By integral Poincaré duality a class $v$ has cup square zero exactly when every first derivative of the diagonal cubic vanishes at $v$. Its derivative in $z$ is $K(\sum y_j^2+3z^2)+6zy_1$, which is positive definite in $(y,z)$, by $|6zy_1|\le3(z^2+y_1^2)$. Hence the square-zero locus has $y=z=0$. The $y_j$ derivatives now impose precisely the $q_j(x)$, and the $U,b,c$ derivatives impose $bc=Uc=Ub=0$. These conditions also suffice. Consequently each square-zero class occupies at most one of the three coordinates $U,b,c$.

For these nonspin six-manifolds every integral square-zero class is the pullback of the degree-two generator by a map to $S^2$. This is Li–Pan–Wu, Proposition 4.4, applied in the torsion-free case. A map to $(S^2)^3$ is therefore specified for degree purposes by any three square-zero classes, and its degree is their triple pairing. The terms of $\mu$ involving $y$ or $z$ disappear. The remaining pairing is the polarization of $6Ubc$. It vanishes unless the three classes occupy three different axes among $U,b,c$, and in that case it is the product of their selected coordinates. Conversely one can use any admissible $U$ class and arbitrary integral multiples of the two pure $b,c$ axes. Thus
$$
D(M,(S^2)^3)=\{0\}\ \cup\
\bigcup_{\substack{q_j(x)=0\ \mathrm{over}\ \mathbb Z\\ U(x)\ne0}}
U(x)\mathbb Z .
$$
Upward closure and the characterization of the possible $U$ values now give the exact degree set. [Li–Pan–Wu, Proposition 4.4](https://arxiv.org/html/2410.16055#S4.SS1)

For any computably enumerable set $E$ of positive primes take $k=2$ and let $A$ consist of multiples of prime squares and multiples of members of $E$. The positive primes in the degree set are exactly $E$. For $E$ the primes indexed by the halting set, prime enumeration is a many-one reduction, and simplicial approximation gives enumerability. For any modulus choose a prime coprime to that modulus. Its square multiples run through every residue. For localization at $\ell$, choose $p\ne\ell$ and realize degree $p^2$. On one sphere factor of the localized target a map can multiply the degree by any fraction in $\mathbb Z_{(\ell)}$, using localized inverses of degree maps with unit degree for denominators. Composition gives every local degree, and the same argument works rationally. The construction complements the realization results of Neofytidis–Wang–Wang and the recursive-enumerability obstruction of Löh–Uschold. [Realising sets of integers as mapping degree sets](https://arxiv.org/abs/2109.13790) · [Löh–Uschold, Appendix A](https://loeh.app.uni-regensburg.de/preprints/l2_comp.pdf#page=29)

### An exact gap with fixed homology and a supplied map

For each fixed integer $K\ge2$, there is an effective family of sources, with the same integral homology groups, for which the spectrum is $\mathbb Z$ if a specified machine halts and $\{0\}\cup\{d:|d|\ge K\}$ otherwise. The family comes with a map of degree $K$. To see this, take the uniform enumerable predicate that accepts $T\ge K$ automatically and accepts $1\le T<K$ if the machine halts. Pick $k$ with $2^k\ge K$. A fixed universal predicate pins the machine index by a constant gate, so the numbers of variables and equations stay fixed. The cubic construction has fixed second Betti number, third Betti number zero, and torsion-free homology.

To compute a source, enumerate oriented smooth triangulations with positive certificates of simple connectivity. Require torsion-free homology with the prescribed ranks, and dovetail integral lattice identifications of the degree-two cubic. Test the nonspin condition by $Sq^2:H^4(M;\mathbb F_2)\to H^6(M;\mathbb F_2)$ and Wu’s formula. The Jupp realization ensures termination. The cubic and the nonspin condition alone suffice for the degree calculation, so every accepted triangulation has the required spectrum. Enumerating simplicial maps finds the promised degree-$K$ map. This specializes the degree decision problem to a fixed simply connected target with a gap between positive degrees and known integral maps. [Effective manifold enumeration](https://arxiv.org/abs/1812.09413) · [Earlier undecidability of nonzero degree with varying inputs](https://arxiv.org/abs/1908.02824)

## 2. An undecidable gap in the minimum positive degree to complex projective space

**Theorem.** Fix an integer $K>1$ divisible by 1536. From a machine index one can compute a finite triangulation of a closed simply connected smoothable eight-manifold $M$, and a map of degree $K$ to the fixed target $\mathbb{CP}^4$. The minimum positive degree of a map $M\to\mathbb{CP}^4$ is 1 when the machine halts and $K$ otherwise. Thus every fixed-factor approximation of that minimum is undecidable on the stated input family, allowing $K$ to depend on the factor. Degree-one existence is halting-complete for this fixed target, even with explicit localized degree-one witnesses at every prime and rationally.

### An integer quartic with an exact gap

Use a fixed universal integer gate system with the input machine index pinned by one constant equation. In its polynomial representation, multiply the predicate polynomial by $(2u-1)(3v-1)$ using fresh variables before compiling the quadratic gates. Both factors are nonzero on integers, and a witness is available after inverting 2 or 3 by setting the corresponding variable to its reciprocal. Homogenize the resulting system by $x_0$ into quadrics. For each original witness coordinate include a chain of squaring gates, homogenized in the same way, requiring its normalized value to have an $E$-th power represented by a normalized coordinate. Choose $E$ a power of two with $2^E>K^{1/4}$. Write $Q_i$ for all the resulting quadrics, and take a new independent coordinate $z$. Form
$$
P=x_0^4+K\left(\sum_i Q_i^2+z^4\right).
$$
It always assumes $K$, at $z=1$ and all other coordinates zero. When the machine halts it assumes 1 with $x_0=1$, all gates satisfied, and $z=0$. If the machine does not halt, a positive value below $K$ would require all penalties zero and $0<|x_0|\le K^{1/4}$. Every normalized coordinate has reduced denominator dividing $|x_0|$. A normalized original witness with a denominator at least 2 would give an $E$-th power denominator at least $2^E$, which the squaring gates forbid. Thus all original witnesses would be integers, a contradiction. The minimum positive quartic value is exactly the asserted gap.

### Realize its values as degrees

Put $h=2x_0$. After replacing $x_0=h/2$, multiplying the quartic penalty by 16 clears denominators. Polarization gives
$$
24 z_1z_2z_3z_4
=\sum_{I\subseteq\{1,2,3,4\}}(-1)^{4-|I|}
\left(\sum_{i\in I} z_i\right)^4.
$$
This works with repeated variables. Because $K$ is a multiple of $4\cdot24\cdot16$, one obtains an integral expression
$$
P=x_0^4+4\sum_j c_j\,\ell_j(2x_0,x_1,\ldots,z)^4
$$
with integer linear forms $\ell_j$ and integer $c_j$.

Start with a connected sum of one copy of $\mathbb{CP}^4$, copies of $S^2\times S^6$ for all other data coordinates, and one $S^2\times\mathbb{CP}^3$ per term. In each latter summand denote the two degree-two coordinates by $a_j,b_j$. Its fourth power contribution is $4a_jb_j^3$. Impose the two linear relations on these coordinates
$$
a_j=c_j\ell_j,\qquad b_j=\ell_j
$$
by surgery on the dual integer 2-cycles. Each attaching cycle is represented by a smooth embedded sphere, using the Hurewicz isomorphism and general position. The finitely many spheres can be chosen disjointly. Their oriented normal bundles are trivial, because the second Stiefel–Whitney class pairs to zero on each cycle. In fact all summands other than $\mathbb{CP}^4$ are spin and every coefficient of its dual 2-cycle in these relations is even. An oriented rank-six bundle on $S^2$ is classified by its second Stiefel–Whitney class. Thus the indicated framed surgeries are available.

The surgery trace from the original manifold uses index-three handles, and from the surgered side it uses index-six handles. Hence integral $H^2$ of the result identifies with precisely the sublattice of the original $H^2$ given by the linear relations. Fourth powers evaluate equally on the two boundary fundamental classes of the trace. Thus the new quartic is exactly $P$ in the original data coordinates. Removing the spheres has codimension six and the new handles preserve simple connectivity. Every class in this integral $H^2$ is realized by a map to $\mathbb{CP}^4$, since the classifying map to $\mathbb{CP}^{\infty}$ can be made cellular from an eight-dimensional domain. The degrees are therefore exactly the values of $P$.

For effectivity, one can enumerate finite oriented smooth triangulations in dimension eight, together with positive certificates of simple connectivity, using differentiable triangulation enumeration. Compute their integral degree-two cup quartics. Dovetail integer basis identifications of those lattices with the prescribed lattice. The surgery proves existence, so the search terminates. Every accepted triangulation has the required degree set by the cellular argument. Finally enumerate simplicial maps until a map of degree $K$ is found. Degree-one existence is enumerable, and the reduction gives hardness. For a factor-$c$ guarantee choose $K>c^2$ so that even symmetric factor intervals for the two answers are disjoint. [Manin–Weinberger, effective manifold enumeration](https://arxiv.org/abs/1812.09413) · [Manin on degree and geometry](https://doi.org/10.1017/fmp.2023.33)

For each $q=2,3$, the explicit gate witness gives $P=1$ over $\mathbb Z[1/q]$. Let $\alpha$ be the resulting degree-two class and choose $r\ge0$ so that $q^r\alpha$ is integral. Realize that integral class by a genuine map to $\mathbb{CP}^4$ by the cellular argument. There is also a self-map of $\mathbb{CP}^4$ multiplying its degree-two generator by $q^r$, by the same argument. That map is an equivalence after inverting $q$, since it induces an isomorphism on homology over $\mathbb Z[1/q]$ for these simply connected spaces. Its localized inverse, composed with the genuine map, realizes $\alpha$ and has localized degree 1. Both genuine maps can be found by enumeration of representatives with the specified pullbacks. Thus every prime has a supplied finite description of a localized degree-one map, uniformly in the input.

## 3. One spherical boundary at the first unstable dimension

**Theorem.** For every even $n\ge2$ and every computably enumerable set $E$ of positive squarefree integers, there is a fixed $(n-1)$-connected finite pair $(X,S^{2n-1})$ with $\dim X=2n$, such that for positive squarefree $q$ the class $q[\iota_n,\iota_n]$ extends to $X\to S^n$ exactly when $q\in E$. The pair can be chosen so that every instance extends after localization at each prime. This gives halting completeness on a fixed pair with a single spherical boundary, at the first dimension beyond the known algorithmic range.

Use a fixed integer polynomial gate system for $E$, homogenized to quadratic gates using $U$ and with homogeneous input $T$. Before compilation replace the predicate polynomial by its product with $(2u-1)(3v-1)$. This preserves the integral predicate and gives an explicit witness after inverting either denominator, by setting the appropriate scalar to its reciprocal. Adjoin $T^2=UZ$ and make $UT=q$ the only nonhomogeneous equation. If a prime divides $U$, the square equation forces it to divide $T$, contradicting squarefreeness of $q=UT$. Thus $U=\pm1$, and $T/U=q$. Every original arithmetic gate therefore decodes integrally. Conversely a solution at $q$ gives a solution with $U=1$.

Take a wedge of one $n$-sphere per variable and one boundary $(2n-1)$-sphere. Attach $2n$-cells along the sums of Whitehead brackets of variable spheres specified by the homogeneous quadrics. Repeated variables use self-brackets. For the final cell attach along the boundary generator minus the bracket for $UT$. Every assignment of integers is realized by sphere degree maps, and naturality and bilinearity make each attaching image an integer multiple of $[\iota_n,\iota_n]$. Its infinite order for even $n$ proves both directions with no torsion cancellation. Over the prime-local target use $U=1,T=q,Z=q^2$ and the explicit localized witness, now using classes in $\pi_n(S^n_{(\ell)})=\mathbb Z_{(\ell)}$. The same nullity calculation applies. The suspended Whitehead square vanishes. Take $E$ to be the images of halting indices under the prime enumeration to get completeness. The stable-range algorithm of Čadek et al. applies through dimension $2n-1$. Their quadratic reduction and the later single-sphere restriction supply precedents. The fixed pair with a single varying sphere class at the sharp dimension is the additional restriction here. [Stable range and Whitehead arithmetic](https://arxiv.org/abs/1302.2370) · [Earlier single-sphere restriction](https://arxiv.org/abs/2008.00492)

### Sharp ambient dimension for extending a complex line subbundle

For every $m\ge1$, a fixed pair $(X,S^{2m+1})$ of dimension $2m+2$ has a halting-complete boundary line-subbundle extension problem in the trivial bundle $\mathbb C^{m+1}$. All the prescribed lines on the boundary are abstractly trivial. All extend after passing to ambient $\mathbb C^{m+2}$. In dimensions at most $2m+1$, an abstract extension of the boundary line always suffices for extension in ambient $\mathbb C^{m+1}$.

Use the same gate system, multiplying each homogenized quadratic by $U^{m-1}$, and use the reader $U^m T=q$. This forces $U\ne0$, so all old equations still hold. Squarefreeness forces $U=\pm1$, using the square equation if $m=1$ and using $U^m\mid q$ if $m\ge2$. Dehomogenizing gives $T/U=\pm q$. The gate predicate recognizes only positive inputs, so existence is exactly membership of $q$ in $E$, and $U=1$ gives the converse.

Use the target $\mathbb{CP}^m$. Each monomial of degree $m+1$ is represented by the top attaching class of the fat wedge of $m+1$ copies of $S^2$, with each factor identified with the corresponding variable sphere. Give separate copies of the fat wedge to separate monomials, gluing only along the wedge of their indicated factors using the fold map when a variable repeats. The fat wedge has dimension $2m$. Maps on it with specified degrees on the factors exist, and are unique up to homotopy relative to the factor maps, by the connectivity through dimension $2m$ of the homotopy fiber of $\mathbb{CP}^m\to\mathbb{CP}^\infty$. The fiber is $S^{2m+1}$, from the scalar circle action on the unit sphere in $\mathbb C^{m+1}$.

To compute the top attaching obstruction, the resulting line class on the full product is $\sum_i d_i a_i$ for factor degrees $d_i$, where $a_i^2=0$. The obstruction to lifting to $\mathbb{CP}^m$ is the Euler class of the sum of $m+1$ copies of the line, up to the choice of orientation sign. Its top evaluation is $(m+1)!\prod_i d_i$. This is the image of the attaching class in $\pi_{2m+1}(\mathbb{CP}^m)\cong\mathbb Z$ using the homotopy fiber generator. Hence all monomials have the same nonzero coefficient times their degree product. Add one final cell per homogeneous equation by summing these attaching classes with the polynomial coefficients. For the reader, subtract its attaching class from the boundary sphere generator and send that sphere to $q(m+1)!$ times the consistent generator. The higher-factor and final-cell construction has dimension exactly $2m+2$, and yields the claimed predicate.

Maps to $\mathbb{CP}^m$ specify actual complex line subspaces in the fixed ambient trivial bundle. On the boundary sphere $H^2=0$, so the line is abstractly trivial. Its map becomes null after the inclusion in $\mathbb{CP}^{m+1}$, since $\pi_{2m+1}$ of that space is zero. A nullhomotopic boundary map extends over any cofibration by homotopy extension from a constant map. For the claimed low-dimensional assertion, an abstract line extension supplies the classifying map into $\mathbb{CP}^{\infty}$ with the specified boundary up to homotopy. Extend the lift into $\mathbb{CP}^m$ relative to the boundary. The fiber $S^{2m+1}$ has no obstruction until dimension $2m+2$. This proves the sharp threshold. [Manin’s projective-space Whitehead setup](https://arxiv.org/html/2007.10632#S8)


## 4. Based and free persistence on nilmanifolds

**Theorem.** Let $Y$ be a compact nilmanifold with a length metric from a left-invariant Riemannian metric on its simply connected nilpotent covering group. For based loops, in every homological degree, a class at Lipschitz level $L$ that eventually vanishes already vanishes at $C(L+1)$. The same bound holds for free loops on every compact class-two nilmanifold. For a fixed compact Engel nilmanifold the free-loop bound is sharply $C(L+1)^{4/3}$. On a fixed seven-dimensional class-three nilmanifold it is sharply $C(L+1)^{5/3}$. In particular the free-loop assertion of Block–Manin–Weinberger Question 1.4 has a negative answer, while the based-loop assertion holds. Classes in every degree zero through three in the Engel example and zero through five in the seven-dimensional example attain the respective sharp exponents. [Block–Manin–Weinberger, Question 1.4](https://arxiv.org/html/2505.16907v2#S1.SS3)

### Canonical paths and starting points of lifts

Write the nilmanifold as $\Gamma\backslash G$. In any simply connected nilpotent $G$ there is a continuous choice of paths $P_g$ from the identity to $g$ of speed at most $C(d(e,g)+1)$. One construction uses exponential coordinates adapted to the lower central series. Assign a coordinate in $\mathfrak g_j/\mathfrak g_{j+1}$ weight $j$. These layer-$j$ coordinates at distance $D$ are $O((D+1)^j)$, by integrating the left-invariant velocity equations in increasing order of weight. Indeed the coordinate differential in layer $j$ is a sum of velocity times polynomials in lower coordinates of total weight at most $j-1$. For the other direction start with exponentials of weight-one vectors. In layer $j$ express the remaining coordinates in a fixed basis of iterated brackets mod the next layer. An iterated group commutator realizes a coefficient $\lambda$ on that bracket modulo the next layer when each argument is scaled by $|\lambda|^{1/j}$ and one is also multiplied by $\operatorname{sgn} \lambda$. This follows from the lowest-weight term of the Baker–Campbell–Hausdorff formula. Correct each subsequent layer in order. The weighted polynomial bounds on products and the finitely many layers keep all speeds at most a constant times the weighted coordinate gauge $\sum_j |\log(g)_j|^{1/j}+1$. Use a fixed time interval for each exponential segment. The signed-root choices are continuous, including at zero. This proves both the path bound and the gauge bounds used below.

A free loop $\eta$ lifts to a path $x(s)$ with $x(1)=\gamma x(0)$ for a deck element $\gamma$. Deform the lifted path to the canonical path
$$
s\longmapsto x(0)P_{x(0)^{-1}\gamma x(0)}(s).
$$
For the deformation retain the prefix $x|_{[0,t]}$ on the first half of the time interval and put the canonical left-translated path from $x(t)$ to $x(1)$ on the second half. At the endpoint there may be a constant half interval, which is removed by reparametrization. Start with the preceding reparametrization in reverse to match the original parametrization. The prefix costs at most $2L$ and the suffix endpoints have distance at most $L$ when $\eta$ has Lipschitz constant at most $L$. Thus the whole deformation stays at level $C(L+1)$. It is continuous in the uniform topology and equivariant under deck changes of lifts. For based loops the starting point can be fixed in the universal cover on each component. The deformation gives a contraction of each component to its canonical loop with this control, which proves the based assertion in every degree.

Fix a representative $\gamma$ of the free conjugacy class. The starting point of a lift using exactly this deck element is well-defined in $C_\Gamma(\gamma)\backslash G$. Evaluation there and the canonical-path construction are inverse in one direction and homotopy inverse in the other as above. The Lipschitz bounds on a loop bound the displacement $x^{-1}\gamma x$. The displacement gives the base of a bundle with fiber $C_\Gamma(\gamma)\backslash C_G(\gamma)$, pulled back from the centralizer bundle over the conjugacy orbit. For an affine orbit in log coordinates, or the explicitly parametrized parabola below, the orbit is a contractible smooth submanifold and the bundle has a global product trivialization. For the affine case the Lie orbit has full rank in the affine space since its dimension is the rank of the adjoint derivative, giving the usual centralizer quotient topology. A section can also be chosen directly in the class-two coordinates.

In class two, writing $a=\log\gamma$ and $b=\log x$, the displacement has log $a+[a,b]$. All allowed starts at level $L$ have displacement lying in a fixed weighted coordinate box with side bounds $C_j(L+1)^j$. Its intersection with this affine orbit is convex. If a cycle starts in that box and eventually fills, project the base coordinates of the starting points of the filling to the convex intersection, leaving the fiber coordinates fixed. Retain only components with boundary, so the relevant intersection is nonempty. This fixes the original starts. The canonical loops of the resulting filling have speed $C(L+1)$, and the canonicalization homotopy on the original cycle supplies the needed collar. This proves the class-two result uniformly over components. The same argument applies whenever all log-conjugacy orbits of a nilpotent group are affine.

### The Engel lower bound and the sharp upper bound

Let $G=\mathbb R\ltimes\mathbb R^3$ with multiplication
$$
(t,u)(s,v)=(t+s,u+\exp(tA)v),
\qquad AY=Z,\quad AZ=2W,\quad AW=0.
$$
The basis $Y,Z,W$ is integral and both $\exp(A)$ and its inverse preserve the lattice, so $\Gamma=\mathbb Z\ltimes\mathbb Z^3$ is a cocompact lattice. Fix $Y_{\mathrm E}=\Gamma\backslash G$. In coordinates $(t,y,z,w)$ the gauge is comparable at large scale to $|t|+|y|+|z|^{1/2}+|w|^{1/3}$. This also follows directly by integrating the velocity equations $(\dot t,\dot y,\dot z,\dot w)=(a,b,c+tb,d+2tc+t^2b)$, and using the canonical commutator paths for the converse.

Take $\gamma_n=(0,Y-n^2W)$. At start coordinate $t$ its conjugate displacement has coordinates
$$
(0,Y-tZ+(t^2-n^2)W).
$$
Canonical loops at $t=\pm n$ therefore have Lipschitz constants $O(\sqrt n)$. They lie in one free-loop component, as the start varies continuously in the $t$-coordinate. In any homotopy their lifts have the same fixed deck multiplier by continuity. The centralizer of $\gamma_n$ consists exactly of the elements with $t=0$, so the two end starts have the same indicated $t$-coordinates for every lift using $\gamma_n$. A slice of any path of starts between them has $t=0$, whose displacement forces Lipschitz constant at least $c n^{2/3}$ for all large $n$. The difference of the endpoint classes in $H_0$ gives the stated lower bound and unbounded log-length.

For the upper bound consider any $\gamma=(a,u)$. If $a\ne0$, the conjugate displacement has form
$$
(a,\exp(-tA)(u+(\exp(aA)-I)v)).
$$
Since the image of $\exp(aA)-I$ is $\langle Z,W\rangle$, the orbit at fixed $a$ is affine in these coordinates. If $a=0$ and the $Y$-coordinate $y$ of $u$ vanishes, the orbit is also affine. In the remaining case, its variable coordinates are
$$
z(t)=z-yt,\qquad w(t)=w-2zt+yt^2 .
$$
Let $R=L+1$. Starts of low loops satisfy $|z(t)|\le C R^2$ and $|w(t)|\le C R^3$. Since $y$ is a nonzero integer, any two such starts have $|t_1-t_2|\le2C R^2/|y|$. On their segment the quadratic value differs from its linear interpolation by at most $|y|(t_1-t_2)^2/4$. The interval spanned by all low starts thus has $|z(t)|\le C R^2$ and $|w(t)|\le C'R^4$ throughout. In this case the centralizer is precisely the normal abelian subgroup $t=0$ and the base is the real $t$ line, with an explicit product splitting. Project the starts of a filling onto the interval and use the canonical paths. Their speed is $O(R^{4/3})$. This proves the uniform upper bound in every degree and its exponent is sharp by the preceding examples.

For $\gamma_n$ the start space is $T^3\times\mathbb R$. Canonical loops give maps of $T^3$ at both $t=\pm n$ with the same $O(\sqrt n)$ bound for every start in the torus. The difference of the two images of any nonzero class in $H_i(T^3)$ cannot die below $c n^{2/3}$, since its image in $T^3\times(\mathbb R\setminus\{0\})$ is the nonzero pair of opposite classes. The canonical family along the segment gives a prism that kills the difference at $C n^{2/3}$. This proves the higher homology assertion, with independent classes of rank $\binom3i$. Riley’s null-homotopy estimate discussed by Block–Manin–Weinberger concerns contractions of nullhomotopic loops. The Engel classes here lie in nontrivial free components. [Riley, §2.6](https://math.uchicago.edu/~shmuel/lg-readings/Riley%2C%20CRM%20notes%20Dehn%20functions%20etc.pdf)

### A sharp $5/3$ bound on a seven-dimensional nilmanifold

Let $U=P=Q=\mathbb R^2$ and $V=P\oplus Q\oplus\mathbb RW$, and use
$$
J=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M_p=p_1I+p_2J.
$$
For $u\in U$ let $A(u)p=M_pu\in Q$, $A(u)q=2u^{\mathsf T}Sq\,W$, and $A(u)W=0$. The operators $A(u)$ commute since $SM_p$ is symmetric. Their cubes vanish and $I+A(u)+A(u)^2/2$ preserves the integer lattice bijectively when $u$ is integral. Use the group $G=U\ltimes V$ with product $(u,v)(a,b)=(u+a,v+e^{A(u)}b)$ and the cocompact lattice $\Gamma=\mathbb Z^2\ltimes\mathbb Z^5$. The second and third lower central layers are $Q\oplus\mathbb RW$ and $\mathbb RW$. The exponential map sends the Lie algebra coordinates $(u,v)$ to $(u,(I+A(u)/2+A(u)^2/6)v)$ in group coordinates. This triangular change and its inverse preserve the weighted gauge bounds, so $\max\{|u|,|p|,|q|^{1/2},|w|^{1/3}\}$ controls distance and canonical path speed up to the fixed constants above.

For $\gamma=(a,b)$, its conjugate by $x=(u,v)$ in the form $x^{-1}\gamma x$ equals
$$
(a,e^{-A(u)}b+(e^{A(a)}-I)e^{-A(u)}v).
$$
If $a\ne0$, the image of $e^{A(a)}-I$ equals $\operatorname{im} A(a)$ and contains $W$. The $w$ coordinate is unrestricted and the $q$ coordinate ranges over an affine subspace, so the whole orbit is affine. Otherwise write $b=(p,q_0,w_0)$. The moving coordinates are
$$
q=q_0-M_pu,\qquad w=w_0-2u^{\mathsf T}Sq_0+u^{\mathsf T}SM_pu .
$$
When $p_1\ne0$ this is a quadratic graph over $Q$ with quadratic matrix $SM_p^{-1}$. From $M_p^{-1}=p_1^{-1}I-p_2p_1^{-2}J$, its norm is at most $C(1+|p_2|)$. If $p_1=0$ and $p_2\ne0$, then $q_2=(q_0)_2$ and $q_1=(q_0)_1-p_2u_2$. When $(q_0)_2\ne0$ the coefficient of $u_1$ in $w$ is nonzero and the orbit is affine. Otherwise $w$ is a quadratic graph over $q_1$ with coefficient $1/p_2$. The remaining case $p=0$ is affine.

At level $L$, put $R=L+1$. The low starts obey $|p|,|a|\le C R$, $|q|\le C R^2$, $|w|\le C R^3$. Use the convex intersection with this box for affine orbits. For a graph $w=f(q)$, take the convex hull of the projection of the intersection to its variable $q$ coordinates and lift the hull by $f$. For $q=\sum_i\theta_iq_i$ the deviation of $f(q)$ from $\sum_i\theta_i f(q_i)$ has absolute value at most $\sum_i\theta_i\|D\||q_i-q|^2$, where $D$ is the quadratic matrix. Here $\|D\|\le C R$, so throughout the enlarged graph $|w|\le C R^5$. Projection in these orbit charts, with the fiber coordinate in the product centralizer bundle fixed, fixes the low starts and controls their fillings at gauge $C R^{5/3}$. As above, canonical paths and the canonicalization homotopy turn these fillings into loop fillings at that level.

For the lower bound take a lattice element with $a=0$, $p=(1,n)$, $q_0=0$, $w_0=n^5$. Choose $u_\pm$ by $M_pu_\pm=\pm n^2e_2$. At those starts $w=0$ and $q=\mp n^2e_2$, so the canonical loops have Lipschitz constant $O(n)$. When $q_2=0$, necessarily $u_2=0$ and $w=n^5$, requiring level at least $c n^{5/3}$. On the intervening line $u=su_+$ with $|s|\le1$, $w=(1-s^2)n^5$, so the upper path has the matching growth. The centralizer has $u=0$, hence the start space is $T^5\times\mathbb R^2$. The difference of a class in $H_i(T^5)$ on the two endpoint tori maps to opposite nonzero components in the complement of $q_2=0$. It is killed by the canonical prism over the segment, which gives independent classes of rank $\binom5i$ realizing the exponent in all degrees $0\le i\le5$.

## 5. Relative persistence with a prescribed boundary

**Theorem.** Fix a finite simplicial pair $(X,A)$, a finite parameter pair $(Z,B)$ whose every component of $Z$ meets $B$, and a closed simply connected two-stage manifold target $Y$. A family of maps on $X$ with prescribed common Lipschitz restriction $g:A\to Y$, whose $B$-slices have Lipschitz constant at most $L$, can be changed relative to both $B\times X$ and $Z\times A$ to a family of slices of Lipschitz constant at most $C(L+1)^{4/3}$. For scalable $Y$ the bound is $C(L+1)$. The constant can be taken uniform over $g$ and over finite parameter complexes of bounded dimension. In particular these estimates bound the cutoff for deaths of finite singular cycles in every relative mapping space, in every component.

Use the paired whole-boundary thickening from the earlier paper to reduce to a smooth compact $M$ with $A=\partial M$. The Lipschitz maps of pairs with their section and retraction transfer families and restrictions with fixed constants. Approximate $g$ by a smooth $g'$ in a target tubular neighborhood, with a Lipschitz homotopy of cost $O(L+1)$ from $g$ to $g'$. This is possible by local convolution and interpolation followed by the tubular retraction, since the $B$ slices bound $\operatorname{Lip}(g)$. Attach the homotopy in a fixed spatial collar to transfer all maps to the new restriction, and attach the reversed homotopy to transfer back after the proof. The composite collar is a backtracking path. Shortening its traversed interval contracts it relative to the outside boundary, and the collar compression is homotopic to the identity by fixed Lipschitz precompositions. Thus this change costs only fixed factors at the controlled stages. For smooth $g'$, compress an inner spatial collar to the boundary. Sample and smooth the $X$ slices relative to that collar, and interpolate in the parameter variables as in the absolute proof. This preserves the restriction exactly and creates only a low-cost homotopy on $B$.

Work with the product-collared double of $M$. The Hodge contraction $K$ and harmonic projection $P=\alpha\pi$ preserve the forms odd under the reflection. A form vanishing tangentially on $\partial M$ extends to such an odd form by reflection. Its differential is the reflected derivative in the weak sense, because the tangential trace vanishes. The contraction and projection satisfy $dK+Kd=1-P$ and $K^2=PK=KP=0$ on this relative complex. They have the same supremum bounds as the closed-double operators. The identity $dK=1-P-Kd$ gives bounded derivatives when the input and its weak derivative are bounded. Hence the forms used here are valid flat forms for shadowing. The projection represents relative real cohomology, by the relative de Rham identification with the odd part on the double.

On each parameter component take the model $\phi_0$ of one reference slice on $B$, constant with respect to $Z$. Subtract this model on the closed generators before normalization. The difference vanishes on $Z\times\partial M$, and its horizontal relative cohomology class is constant and zero at the reference slice. Thus after subtracting $d(\tau K(\phi(v)-\phi_0(v)))$ on the closed stage and integrating its differential on the second stage, the horizontal closed-stage values are exactly the reference values everywhere. The estimates on $B$ during this homotopy are those of the absolute argument, since the reference is itself a low-Lipschitz slice.

On the second stage subtract $dK(\phi(w)-\phi_0(w))$ to leave horizontal forms $\phi_0(w)+\alpha u_w(z)$. The difference on each slice is closed, because the closed-stage horizontal values already coincide. The parameter-one-degree equation from the absolute proof is now $d_Zu=J\xi$ in relative cohomology. Multiplication uses the module action of absolute cohomology on relative cohomology, evaluated at the reference closed-stage classes. The proof is the same coefficient calculation in each product: exactly one factor has parameter degree one. Since $u$ vanishes at the reference, it lies in $\operatorname{im}J$. Cut it off to $u'=\chi u$ with $\chi=1$ near $B$ and supported where the boundary bounds still hold. Lift $u'-u$ linearly through $J$ to relative closed forms, and add their exact parameter homotopy to the closed stage. Integrating on the second stage and normalizing it again gives the desired $u'$. Every added form is relative to the spatial boundary, and all horizontal estimates equal the absolute estimates. In particular there is no bound needed on the norm of the right inverse of $J$.

Attach the external parameter collar on $B$ using these homotopies, constant along the spatial boundary. Stretch the parameter and apply relative shadowing with both the outer parameter boundary and the spatial boundary as fixed subcomplex. Their prescribed maps have the required Lipschitz bound, since stretching affects parameter derivatives and the spatial restriction is constant in the parameter. This gives an actual family with the required polynomial or linear rate. Shorten the external collar using a pair equivalence relative to its outside copy of $B$ and reinsert the original smoothing and boundary homotopies. These operations affect the parameter only, or have the controlled spatial factor already described. This proves the relative family statement. The finite singular-chain parameter construction then gives the homology assertion. [Relative shadowing](https://arxiv.org/html/2505.16907v2#S6.SS2) · [Absolute proof and whole-boundary thickening](https://github.com/Dugongue/MathProofs/blob/51ba97e579d31bf86ba528ca5a99a61752c48934/ManinTop20/ManinNewProofs.md)

### Linear persistence on rationally null components

For an arbitrary closed simply connected two-stage target, the absolute bound improves to $C(L+1)$ on every component whose maps are rationally nullhomotopic, with the same constant across those components. Work after thickening, smoothing, and adding the parameter collar as in the absolute argument. Write $\phi$ for the resulting model on $Z\times M$. For a generator $v$ of the closed stage, its horizontal cohomology vanishes. Extend in an auxiliary parameter $t$ by
$$
\Phi(v)=P\phi(v)+d(t^{|v|}K\phi(v)).
$$
Here $K$ is the horizontal contraction with its product sign convention, so $dK+Kd=1-P$ on the family. This agrees with $\phi(v)$ at $t=1$. Its horizontal value is exactly $t^{|v|}\phi(v)_{\mathrm{hor}}$.

For a second-stage generator $w$, extend initially by $\Phi_0(w)=\phi(w)+\int_1^t\iota_{\partial_s}\Phi(dw)\,ds$. This solves the differential equation. If $b=|w|+1$, each term contributing to the $t$-derivative of the horizontal value has a factor $t^{b-1}$, by the total degree of $dw$. Thus the horizontal value is $t^b\phi(w)_{\mathrm{hor}}+(1-t^b)\eta_w$, with $\eta_w$ the horizontal value at $t=0$. Each $\eta_w$ is exact on its slice. Indeed, the slice at $t=0$ is rationally null and has all closed-stage values zero. In an algebraic nullhomotopy, normalize the closed-stage values to have zero horizontal part by subtracting the differential of their horizontal $K$-primitives. Those corrections vanish on the endpoints. Every term of $dw$ is decomposable, so its image along the normalized homotopy vanishes because at least two factors have the homotopy differential. It follows that the second-stage endpoint classes agree, and the null endpoint gives zero. Replace $\Phi_0(w)$ by $\Phi_0(w)-d((1-t^b)K\eta_w)$, using the smooth family of horizontal primitives. Its horizontal value is then exactly $t^b\phi(w)_{\mathrm{hor}}$.

Choose $t=t(z)$ between 0 and 1, equal to 1 near the fixed parameter boundary and supported where the original horizontal images obey the low-slice bounds. The graph pullback is algebraically homotopic to the original model relative to the boundary by interpolating between $t(z)$ and 1. Each horizontal image is now bounded by $C(L+1)$ to the power of its generator degree. Stretch the parameter to control the other coefficients and apply ordinary relative shadowing. This proves the stated linear cutoff for these components, without requiring scalable shadowing.

## 6. Computing the true minimum Lipschitz extension value

**Theorem.** Give a rational finite simplicial pair $(X,A)\subset\mathbb R^s$ the extrinsic Euclidean metric and give the unit sphere in $\mathbb R^m$ its Euclidean chordal metric. Given an exact semialgebraic boundary map $f$, its minimum extension Lipschitz constant $\mu(f)$, with value $\infty$ if no Lipschitz extension exists, is uniformly computable as a compactified real $\mu/(1+\mu)$. For each rational $B\ge0$, the predicate $\mu\le B$ is co-computably enumerable. Yet for one fixed pair and one effective family of boundary maps the finite-envelope function
$$
M(N)=\max\bigl(\{0\}\cup\{\mu(f_n):n\le N,\ \mu(f_n)<\infty\}\bigr)
$$
has exactly the Turing degree of the halting set as a real-valued function. Thus even true optimal extension cost has an exact distinction between one compactified value and the maximum over the extendable instances.

For a finite effective $\delta$-net $D\subset X$, test whether there are points $y_d$ on the sphere satisfying the $B$-Lipschitz inequalities for all pairs in $D$, and between $D$ and all points of $A$ with their specified $f$-values. Include the inequalities within $A$. The test is an exact sentence in the theory of real closed fields with algebraic coefficients. A true extension of constant at most $B$ gives a feasible solution. Conversely a feasible solution extends into the ambient Euclidean space by Kirszbraun’s theorem. On $X$ that extension lies within $B\delta$ of the sphere. If $B\delta<1$, radial projection returns a sphere map of Lipschitz constant at most $B/(1-B\delta)$ while preserving $f$. The projection bound follows from
$$
\|x/\|x\|-y/\|y\|\|^2
\le \frac{\|x-y\|^2}{\|x\|\|y\|}.
$$

At a fixed cutoff $K$, choose one net with $\delta$ small enough that the bound differs from $B$ by at most a specified error for all $B\le K$. Check a fine grid of candidate budgets on $[0,K]$. Rejections give lower bounds and acceptances give upper bounds up to this error. This gives $\min(K,\mu)$ to arbitrary additive precision. Taking $K$ large enough computes the compactified value to arbitrary precision even when $\mu=\infty$. For a fixed $B$ use all nets of a computable sequence with $\delta\to0$. If they are all feasible, compactness gives an actual $B$-Lipschitz extension by the corrected maps and Arzelà–Ascoli. Thus rejection on some net semi-decides $\mu>B$.

Use the fixed even-sphere pair of Theorem 3 with index map $j\mapsto p_j$ and semialgebraic representatives for $p_j[\iota_d,\iota_d]$ in a fixed even sphere dimension $d$. A fixed piecewise linear representative for the Whitehead square and piecewise linear degree maps suffice after a fixed semialgebraic identification with the round sphere. Every extension class on the finite pair admits a Lipschitz extension with the exact prescribed Lipschitz boundary, by relative approximation and the neighborhood correction of the earlier Lipschitz theorem. Thus finite values occur exactly at halting indices. A halting oracle selects the finite terms and the compactified computation obtains each actual value to arbitrary accuracy. Conversely, one coarse approximation to $M(n)$ gives an integer $B>M(n)$. A single finite-net test at this $B$ and sufficiently small $\delta$ is feasible exactly when $f_n$ extends, since feasibility implies a true extension and on a yes instance the minimum is below $B$. This proves both reductions. [Earlier extension growth theorem](https://github.com/Dugongue/MathProofs/blob/51ba97e579d31bf86ba528ca5a99a61752c48934/ManinTop20/ManinNewProofs.md#1-when-lipschitz-extension-bounds-are-computable)


## Verification

The six main sections give written proofs. Priority for the precise results is provisional. Lean 4.33.0 independently kernel-checked the integer normalization in the one-sphere argument with the standard axiom set. [Checked source](SquarefreeNormalization.lean)
