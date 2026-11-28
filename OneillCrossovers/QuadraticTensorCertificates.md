# Arithmetic tensor-isomorphism obstructions at tunable proof degree

This combines the Top 30 tensor-isomorphism proof-complexity program with the quadratic nonvanishing and short prime-interval releases. The degree calculation below is independent of those releases. The distributional statements are conditional on the indicated preprints. [Quadratic nonvanishing](https://charlesponeill.com/maths-releases/chowla-nonvanishing/chowla-nonvanishing.pdf) and [primes between consecutive powers](https://charlesponeill.com/maths-releases/legendre/legendre.pdf).

## Exact degree over finite fields

Let $\mathbb F_p$ be a finite field of cardinality $p\ge3$, here allowing $p$ to be a prime power. In the ordinary tensor-isomorphism system with cubic action equations, inverse axioms, and the equations $x^p-x$ for each variable, the minimum Polynomial Calculus degree for distinguishing a split étale algebra from any nonsplit commutative étale algebra of the same dimension is exactly $p+1$. For any nonisomorphic commutative étale pair of the same dimension the degree is at least $p+1$. Their multiplication tensors are geometrically isomorphic, so neither case has a refutation with the action and inverse equations alone.

For the lower bound, work over the algebraic closure. Choose three change-of-basis matrices $P^A_j$ and $P^B_j$ for each multiplication tensor, taking the diagonal tensor to the tensor of algebra $A$ or $B$. For each permutation $\Pi$ and two independent diagonal scalings with entries $u_i,v_i$, the three maps

$$
P^B_1\Pi D_u (P^A_1)^{-1},\quad
P^B_2\Pi D_v (P^A_2)^{-1},\quad
P^B_3\Pi D_{(uv)^{-1}} (P^A_3)^{-1}
$$

and their inverses give geometric solutions. The Laurent weights of the variable entries, in the $i$th two-dimensional torus block, are
$ (1,0),(0,1),(-1,-1),(-1,0),(0,-1),(1,1)$,
one for each of the six matrix types. Each is an exposed vertex of the convex hull of all weights in all blocks. A linear functional attaining $1$ at that vertex alone is obtained from a supporting functional in block $i$, extended by zero on other blocks. Hence the character of weight $p$ times that vertex cannot occur after substituting any polynomial of degree less than $p$.

Consider a constant combination of the field axioms and a polynomial vanishing on all those families. If the combination has degree less than $p$, its coefficient at each such character vanishes for every $\Pi$. For a forward matrix, the coefficient at the character corresponding to block $i$ is a pairing of the matrix of field-axiom coefficients with the $p$th powers of column $\Pi(i)$ of $P^B_j$ and row $i$ of $(P^A_j)^{-1}$. The analogous inverse formula switches source and target. As $i,\Pi(i)$ vary, the column and row ranges are bases. Their Frobenius powers remain bases. Every field-axiom coefficient must therefore vanish.

Induct through any derivation of degree at most $p$. Each line is a polynomial vanishing on these families plus a constant combination of field axioms. Linear rules preserve this form. To multiply a nonzero line by a variable its degree must be below $p$, so the preceding argument makes its field-axiom combination zero. Multiplication then preserves vanishing. The constant $1$ cannot be derived.

For the upper bound when the source is split, use split coordinates on the target over a finite splitting field. Let the idempotents of the target be ordered so Frobenius permutes them by $\sigma$, and let $A$ be the inverse output action written with these idempotents as its columns in the target basis. Each row $(a_i)_i$ of $A$ contracts the target diagonal multiplication tensor to $\operatorname{diag}(a_i)$. The same contraction applied to the source action is a rank-one matrix. Substituting the rank-one entries into each two-by-two minor derives $a_i a_j=0$ for $i\ne j$ at degree at most four. The contraction uses one inverse variable, so also stays within degree four.

Since $a_i$ is obtained by multiplying the base-field inverse output matrix by the column of the $i$th idempotent, the base-field equations give $a_i^p-a_{\sigma(i)}=0$ in degree $p$. Choose a moved index $i$. Multiply by $a_{\sigma(i)}$ and eliminate $a_i^p a_{\sigma(i)}$ using $a_i a_{\sigma(i)}=0$. This gives $a_{\sigma(i)}^2=0$ by degree $p+1$. Repeated multiplication and the field equation at $\sigma(i)$ give $a_{\sigma^2(i)}=0$. The argument holds for every row, making one column of $A$ zero and contradicting its inverse identity. This remains within degree $p+1$ when $p=3$. Descend the refutation to $\mathbb F_p$ by expanding each line in a splitting-field basis containing $1$ and replaying the coefficient derivations. Scalar linear combinations become base-field linear combinations, variable multiplication commutes with coefficient expansion, and degrees do not increase.

## Distribution by local tags

Now take a quadratic number field of fundamental discriminant $D$. At an odd unramified prime the reduction of its integral multiplication tensor is equivalent to the split tensor exactly when $\chi_D(p)=1$. Inertia gives the nonsquare case above. One way to see that an isotopy cannot identify the field and split algebras is that the split algebra has two nonzero elements with product zero and a field has none. Isotopy preserves this property because all three maps are invertible. A ramified reduction is the dual-number algebra, which remains distinct from the split algebra after base change. In fact, in a unital associative commutative algebra an isotopy to another such algebra normalizes to an algebra isomorphism. If $R(xy)=P(x)Q(y)$, then $P(1),Q(1)$ are units because multiplication by them is a bijective linear map. Therefore $R(x)/(P(1)Q(1))$ is a multiplicative unital linear isomorphism.

Fix any one of the six sign and 2-adic classes in the nonvanishing paper. On each shell $X<|D|\le2X$, prescribe the local splitting type at every odd prime up to $z(X)=o(\log X)$. These tags can vary with $X$. Theorem 2 gives a nonempty family for sufficiently large $X$ and a proportion at least $0.9453419890-o(1)$ of fields in that family with nonvanishing central quadratic $L$-value. The same proportion has $\zeta_{\mathbb Q(\sqrt D)}(1/2)\ne0$, since $\zeta(1/2)$ is nonzero by the alternating eta series.

The prime-interval release supplies a prime in each of its specified consecutive $11/5$-power windows. For a growing window below $z(X)$, prescribe inertia at one such prime $p$ and choose the other tags freely. Every tensor in the family then has exact modular refutation degree $p+1$ at that prime, and the same uniform nonvanishing bound holds inside this family.
