# Factoring and determinant-one transporters of finite-field multiplication tensors

Let $F=\mathbb F_q$ be given by an explicit finite-field presentation. For bilinear maps $T,S$, a transporter is a triple $(P,Q,R)$ of invertible linear maps with $S(Px,Qy)=R(T(x,y))$. A determinant-one transporter has determinant $1$ in each given mode basis. A multiplication isotope is any bilinear map obtained from multiplication in a nonzero algebra by three independently chosen invertible linear maps. These are instances of the three-tensor action used by Grochow and Qiao. [Grochow–Qiao, On the complexity of isomorphism problems for tensors, groups, and polynomials I](https://par.nsf.gov/servlets/purl/10494304)

**Theorem.** The following hold under deterministic polynomial-time search reductions, with $\log q$ included in the input size.

1. Finding a determinant-one transporter of semisimple associative multiplication isotopes, or deciding that none exists, reduces to univariate polynomial factoring over finite fields. The same upper bound applies to ordinary transporters. Under the GRH used by Evdokimov's factoring algorithm the resulting deterministic bound is $L^{O(\log L)}$, for $L$ the full input length in bits.
2. Finding either kind of transporter is factoring-hard even on guaranteed-YES pairs of multiplication tables of algebras split as products of copies of $F$. The conversion from a completely split squarefree polynomial to such a pair is a single oracle call.
3. When a reference ordinary transporter is supplied, finding a determinant-one transporter is still factoring-hard under polynomial-time Turing reductions. The source can be restricted to a split commutative algebra or the explicitly presented algebra $M_2(\mathbb F_p)$, with $p$ prime, and every oracle call is a YES instance. On the single explicitly presented block $M_d(F)$, with a reference transporter, the sharper equivalence is to extracting $d$-th roots in $F^\times$. In particular this single-block case has a deterministic polynomial-time algorithm over prime fields under the ERH in Adleman–Manders–Miller.

The reductions in all three statements are unconditional. GRH and ERH enter through the cited algorithms for the arithmetic subproblems. A finite-field factoring oracle takes an explicitly presented field and a univariate polynomial and returns its full factorization. The lower bounds concern witness production. For example, on the explicit matrix block with a reference transporter, existence is tested by a power computation.

## Multiplication transporters

For unital associative algebras $A,B$, suppose $(P,Q,R)$ is a transporter of their multiplications and put $a=P(1_A)$, $b=Q(1_A)$. Substituting the identity gives $R(x)=P(x)b=aQ(x)$. Since $P,Q,R$ are bijections, multiplication by $a$ on the left and by $b$ on the right is bijective. In a finite-dimensional unital algebra these conditions make $a,b$ units. For example a right inverse $c$ to $a$ satisfies $a(ca-1)=0$, so injectivity of left multiplication by $a$ gives $ca=1$. Now

$$
\phi(x)=a^{-1}R(x)b^{-1}
$$

is a unital algebra isomorphism. Indeed, $P(x)=a\phi(x)$ and $Q(y)=\phi(y)b$, which turn the transporter identity into $\phi(xy)=\phi(x)\phi(y)$. Conversely, any unital algebra isomorphism and any two units of the target give the transporter $(L_a\phi,R_b\phi,L_aR_b\phi)$, where $L_a(z)=az$ and $R_b(z)=zb$. In particular,

$$
\det \phi = \frac{\det P\,\det Q}{\det R}.
$$

## Factoring from guaranteed-YES queries

Let $f\in F[X]$ be monic, squarefree, and completely split, of positive degree $m$. Compute $A=F[X]/(f)$ in its power basis and $B=F^m$ in its coordinate basis. If the distinct roots are $r_1,\ldots,r_m$, evaluation gives an algebra isomorphism $\psi:A\to B$ whose determinant $w$ is a Vandermonde. Although the roots are unavailable, $w^2=\operatorname{disc}(f)\in F^\times$ is computable by a resultant. Let $\alpha$ be a diagonal linear map on $B\times B$ with determinant $\operatorname{disc}(f)^{-1}$. On the target use the multiplication

$$
y\star z=\alpha\bigl(\alpha^{-1}(y)\,\alpha^{-1}(z)\bigr).
$$

The source is multiplication in $A\times A$. The algebra isomorphism $\alpha\circ(\psi\oplus\psi)$ has determinant $1$, so the query is guaranteed YES even in characteristic two. From any returned transporter obtain $\phi$ by the formula above. Applying $\alpha^{-1}$ to $\phi((X\bmod f,X\bmod f))$ gives the list of roots, each twice. The doubling makes the required change of basis computable directly from the discriminant.

The standard deterministic polynomial-time reduction from general finite-field factoring to proper splitting of squarefree completely split polynomials over prime fields now gives the claimed factoring-hardness. [Gao, abstract and §1](https://www.math.clemson.edu/~sgao/papers/FacPoly.pdf)

## A known witness on a single split matrix block

Let $A=M_d(F)$ in its standard basis, and suppose $\gamma=(P_0,Q_0,R_0)$ is a reference ordinary transporter from the given source to the given target. Every transporter equals $\gamma$ composed with a source self-transporter. Every $F$-algebra automorphism of $M_d(F)$ is inner, with determinant one because the left and right multiplication determinants cancel. Left multiplication by $a$ applies $a$ to each column, and right multiplication by $b$ applies $b$ to each row. Thus the determinant triples of self-transporters are exactly

$$
\bigl(u^d,v^d,(uv)^d\bigr), \qquad u,v\in F^\times .
$$

For a determinant-one transporter, write $x=(\det P_0)^{-1}$, $y=(\det Q_0)^{-1}$, and $z=(\det R_0)^{-1}$. First require $z=xy$. Then find $u^d=x$ and $v^d=y$, and use the matrices $\operatorname{diag}(u,1,\ldots,1)$ and $\operatorname{diag}(v,1,\ldots,1)$ for the correcting units. Existence of a $d$-th root of $x\in F^\times$ is equivalent to $x^{(q-1)/\gcd(d,q-1)}=1$.

Conversely, given a nonzero $x$ promised to be a $d$-th power, let $L$ be a known diagonal linear map on the $d^2$-dimensional vector space $A$ with determinant $x^{-1}$. Use $T(u,v)=uv$ and $S(u,v)=L((L^{-1}u)v)$, with reference transporter $(L,I,L)$. Given a determinant-one transporter $(P,Q,R)$, the element $a=L^{-1}P(1)$ is the left unit in its relative self-transporter. Therefore $(\det a)^d=x$. Deterministic extraction in time polynomial in $d$ and $\log p$ over $\mathbb F_p$ follows from the ERH bound with the exponent $d$ counted by its value, as permitted by the tensor dimension. [Adleman–Manders–Miller, Theorem IV](https://www.cs.cmu.edu/~glmiller/Publications/AMM77.pdf)

## Factoring with a known witness

It suffices to find a proper factor of a monic squarefree completely split polynomial $f\in\mathbb F_p[X]$ of degree $m>1$. Apply the procedure recursively. When $p=2$, direct evaluation at both elements suffices. Write $A=\mathbb F_p[X]/(f)$ and $x=X\bmod f$.

For odd $m$, conjugate the multiplication of $A$ in all three modes by a known linear map $\alpha$ with determinant $-1$. Supply the reference transporter $(\alpha,\alpha,\alpha)$. A transposition of two field factors of $A\simeq\mathbb F_p^m$ has determinant $-1$, so composing $\alpha$ with such a transposition gives a determinant-one algebra isomorphism and the query is guaranteed YES. On receiving a determinant-one transporter, compose its three maps on the left by $\alpha^{-1}$. The relative self-transporter has all three determinants $-1$, so its associated algebra automorphism $\phi$ has determinant $-1$. This is an odd permutation of the field factors. It has an even cycle because its sign is negative, and an odd cycle because the total number of points is odd. Let $h$ be the least common multiple of the positive odd integers at most $m$. The fixed points of $\phi^h$ are precisely the points on odd cycles. The coordinates of $x$ are distinct, so the gcd of $f$ with a polynomial representative of $\phi^h(x)-x$ is a proper factor. Both $h$ and the representation of the linear map $\phi^h$ can be computed in polynomial time.

For even $m$, use the known-witness $M_2(\mathbb F_p)$ queries to take square roots. Write $p-1=2^s t$ with $t$ odd. Starting at $-1$, repeated square roots construct a generator $\zeta$ of order $2^s$. In fact, every square root of an element of order $2^j$ for $1\le j<s$ has order $2^{j+1}$, and such roots exist. There are at most $s-1$ guaranteed-YES queries. The following gives the proper factor using only $\zeta$ and arithmetic, and is the even-degree tournament argument for factoring. [Gao, §§2.4 and 3](https://www.math.clemson.edu/~sgao/papers/FacPoly.pdf)

Compute in the algebra $A\otimes_{\mathbb F_p}A$, identified in unknown coordinates with functions of ordered pairs of roots. Put $z=x\otimes 1-1\otimes x$, $u=z^{p-1}$, and $b=(z+1-u)^t$. Thus $u$ masks the off-diagonal pairs and $b$ lies componentwise in the subgroup generated by $\zeta$. Compute the highest bit of the exponent of $b$ relative to $\zeta$ without splitting the algebra. Starting with the current $b$, for $j=0,\ldots,s-1$ let

$$
c_j=\frac{1-b^{2^{s-j-1}}}{2}, \qquad
b\ \longleftarrow\ b\bigl(1-c_j+c_j\zeta^{-2^j}\bigr).
$$

In each coordinate the current exponent is divisible by $2^j$, and $c_j$ reads its $j$-th bit and the update removes it. Off the diagonal, reversing an ordered pair negates $z$. Since $t$ is odd, this adds $2^{s-1}$ to the original exponent modulo $2^s$, toggling the highest bit. Hence $u c_{s-1}$ records a tournament on the $m$ roots. Apply the identity on the first factor and the algebra trace on the second. The resulting element of $A$ has as its coordinates the outdegrees, which cannot all be equal since their average $(m-1)/2$ is not integral. As $m\le p$, the integer degrees $0,\ldots,m-1$ remain distinct in $\mathbb F_p$. Scan these values and take the gcd of $f$ with a polynomial representative of the resulting element minus that value. At least one such gcd is a proper factor. Computing the trace by multiplication matrices and performing the displayed powers uses polynomially many field operations on algebras of dimension at most $m^2$.

## Constructive upper bound

One can recover a multiplication table from a raw multiplication isotope before factoring. In the equal-dimensional case compute by linear equations the adjoint algebra consisting of pairs $(X,Y)$ with $T(Xu,v)=T(u,Yv)$. The first projection uses the opposite of ordinary composition, the second uses ordinary composition. In hidden multiplication coordinates these projections are the right and left regular representations, since substituting a unit gives $X(u)=ua$ and $Y(v)=av$ for a common $a$. Compare the regular module of each projected algebra with its action on the corresponding tensor input. Use the opposite algebra as needed so this is a left module comparison. The image of the algebra identity under a module isomorphism is a cyclic vector, which corresponds to a unit in the hidden coordinates. Constructive module isomorphism takes deterministic polynomial time. [Brooksbank–Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Let the cyclic vectors be $\alpha,\beta$ and let $J=T(-,\beta)$ and $L=T(\alpha,-)$. The maps $J,L$ are invertible on the promised locus. The product $x\star y=T(J^{-1}x,L^{-1}y)$ is a unital associative multiplication. In fact, if $T(Pu,Qv)=R(uv)$, $\alpha=P(a)$ and $\beta=Q(b)$, the map $z\mapsto R(zab)$ identifies the original multiplication with $\star$. Thus $(J,L,I)$ is an explicit normalization. The algorithm can reject unequal dimensions, failed module comparisons or singular slices, and it can check the unit, associativity and vanishing Jacobson radical on the normalized table. Successful checks exhibit precisely a semisimple multiplication isotope.

Use finite-algebra decomposition and explicit matrix presentation over finite fields to write each normalized algebra as a product $\prod_i M_{d_i}(E_i)$, and match blocks by the pair $(d_i,[E_i:F])$. The procedures of Rónyai are deterministic polynomial time with a univariate factoring oracle. They can be applied after restriction to the prime field $\mathbb F_p$. The explicit presentations also give the embeddings of $F$ into the block centers, by mapping scalar multiples of the algebra identity. To identify two matched centers, factor the absolute irreducible presentation polynomial of one center over the other and take a root, giving an $\mathbb F_p$-isomorphism. Postcompose with a power of $p$-Frobenius in the target so that the isomorphism respects the two embeddings of $F$. The embeddings differ by such a power, and at most $[F : \mathbb F_p]$ powers need testing on a generator of $F$. The corrected map extends entrywise to the matrix block. [Rónyai, Computing the structure of finite algebras](https://doi.org/10.1016/S0747-7171(08)80017-X) · [Rónyai, explicit isomorphism algorithm, Theorem 5.1](https://www.cs.uoregon.edu/Reports/TR-1985-012.pdf)

If there is a type match, this gives a reference transporter by composing an algebra isomorphism with the two normalizations. It remains to construct a correcting self-transporter on the source. Write $e_i=[E_i:F]$ and $g=\gcd(q-1,d_1,\ldots,d_\ell)$. On a block the determinant of multiplication by a unit on either side is $N_{E_i/F}(\det_{E_i}a)^{d_i}$. Thus each unit determinant can range over $C=(F^\times)^g$. Automorphisms can permute equal-type blocks, with a transposition contributing the sign $(-1)^{e_i d_i^2}$. Within a block, entrywise $q$-Frobenius contributes $(-1)^{(e_i-1)d_i^2}$ by the normal-basis theorem, while inner automorphisms have determinant one. These operations exhaust the possibilities by Skolem–Noether. Let $D$ be the subgroup generated by the displayed signs. The full determinant image of self-transporters is therefore

$$
\bigl\{(u r,v r,u v r):u,v\in C,\ r\in D\bigr\}.
$$

For a required triple $(x,y,z)$, take $r=xy/z$. Membership is exactly $r\in D$ and $x/r,y/r\in C$. Use the identity automorphism for $r=1$ and an elementary Frobenius or block swap of negative determinant for $r=-1$. To realize a given $u\in C$ by a unit, factor $X^g-u$ and take a root $w$. Compute Bézout coefficients $c_i$ with $\sum_i c_i d_i\equiv g\pmod{q-1}$. On block $i$ choose $t_i$ of norm $w^{c_i}$ and use the diagonal matrix $\operatorname{diag}(t_i,1,\ldots,1)$. The product of block determinants is $u$. Apply this independently to $x/r$ and $y/r$, then conjugate the correcting maps by the source normalization.

Here is a norm-inversion procedure with bounded-degree factoring calls. Given $E/F$ of degree $e$ and $u_0\in F^\times$, put $K=(q^e-1)/(q-1)$ and let $K_1$ be the largest divisor of $K$ supported on the primes dividing $q-1$. Since $K\equiv e\pmod{q-1}$, those primes all divide $e$, so their list and valuations are obtained by trial division of $e$ and exact division of $K$. Choose $t$ inverse to $K/K_1$ modulo $q-1$ (if $q=2$, return $1$). By cyclicity, $u_0^t$ is a $K_1$-th power in $E^\times$. Undo the prime factors of $K_1$ one at a time by factoring $X^\ell-v$ over $E$ and taking any root. At a step with remaining exponent $\ell h$, if $v=a^{\ell h}$, every $\ell$-th root differs from $a^h$ by an $\ell$-th root of unity. Because $\ell h$ divides $|E^\times|$, those roots of unity are all $h$-th powers. Thus every answer preserves the induction. The final element $b$ has $b^{K_1}=u_0^t$, hence norm $b^K=u_0$. Each factoring degree is at most $e$ and the number of calls is at most $\log_2 K$. All larger auxiliary degrees and representations in the constructive upper bound are polynomial in the input dimensions.

Evdokimov's general conditional bound for degree $n$ is $n^{O(\log n)}(\log q)^{O(1)}$. Guo obtains smaller exponents for certain Galois groups of characteristic-zero lifts. The displayed theorem uses the classical general bound. [Guo, §1.1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2020.42)

Finite arithmetic checks covered 244,543 discriminant identities, 150,852 even-degree tournament instances, 184,023 odd permutations, and 765 norm targets. The reductions and bit complexity are established by the written proofs and remain unformalized.
