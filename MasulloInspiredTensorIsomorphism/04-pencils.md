# Counting special-linear transporters of binary matrix pencils

Let $U=k^u$, $V=k^v$ for $k=\mathbb F_q$, and let $P=(A,B)$ and $Q=(C,D)$ be pairs of maps $U\to V$. For $H=(h_{ij})\in\operatorname{GL}_2(k)$ write $H P=(h_{11}A+h_{12}B,h_{21}A+h_{22}B)$. A transporter is a triple $(S,T,H)$ with $S\in\operatorname{GL}(U)$ and $T\in\operatorname{GL}(V)$ such that $Q_iS=T(HP)_i$ for both slices. This is the three-mode action on $V\otimes U^*\otimes k^2$. Passage to the usual action on the second mode inverts its determinant and preserves the determinant-one condition.

**Theorem.** For every pair of binary pencils over $k$, including rectangular, singular, and linearly dependent pencils, one can count all transporters in $\operatorname{SL}(U)\times\operatorname{SL}(V)\times\operatorname{SL}_2(k)$ and produce one if the count is nonzero. The algorithm is deterministic and polynomial in the matrix dimensions and $q$, hence polynomial-time at every fixed field. It also computes the exact number of strict transporters with any prescribed pair of nonzero determinants, with the slice change fixed.

The count is obtained by an explicit multiplicative formula for one kernel and an additive sum over the slice changes. The method uses the classical Kronecker decomposition, the standard radical description of a finite direct sum of indecomposables, and constructive module isomorphism. [Kronecker decomposition over arbitrary fields, Murota §5.1.3](https://kzmurota.fpark.tmu.ac.jp/mybooks/KronFormProofEng.pdf) · [Brooksbank–Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

## The strict stabilizer and its determinant image

Regard $P$ as a representation of the quiver with two arrows from the source to the target. Its endomorphism algebra $E$ consists of pairs $(X,Y)$ satisfying $YA=AX$ and $YB=BX$. Composition is componentwise. Its units are exactly the strict stabilizer of $P$.

Write the rational Kronecker decomposition as a direct sum of $m_i$ copies of each distinct indecomposable type $M_i$. The two integers $(a_i,b_i)$ and the residue degree $d_i$ for a type are as follows.

| Type | $(a_i,b_i)$ | $d_i$ |
| --- | --- | --- |
| Column or row minimal index $r$ | $(r+1,r)$ or $(r,r+1)$, according to the block's source and target dimensions | $1$ |
| Finite elementary divisor $f^e$, with $f$ monic irreducible | $(e,e)$ | $\deg f$ |
| Infinite elementary divisor of size $e$ | $(e,e)$ | $1$ |

With $J=\operatorname{rad} E$, the Krull–Schmidt radical formula gives
$$
E/J\cong\prod_i \operatorname{Mat}_{m_i}(\mathbb F_{q^{d_i}}).
$$
In this formula the maps on equal-type blocks are reduced modulo the radical of their local endomorphism algebra. Maps between distinct types vanish in the quotient. One way to see the formula is to use the idempotents projecting onto the individual indecomposable summands. Each is primitive because its corner algebra is local by the Fitting lemma. In the semisimple quotient, two such primitive idempotents belong to the same matrix component exactly when their indecomposable summands are isomorphic. Indeed, equivalence in the quotient lifts to a pair of maps whose composites are identities modulo the local radicals. Those composites are units, so the summands are isomorphic. The converse follows by reducing mutually inverse isomorphisms. The division algebra of a corner in each component is the residue of that local endomorphism algebra.

For a singular block the local endomorphism algebra is $k$. For the maps $k^r\to k^{r+1}$ sending the $j$th basis vector to the $j$th and $(j+1)$st basis vectors, respectively, the endomorphism relations force every interior pair of shifted columns to coincide on their overlap. In the source matrix this gives $X_{i,j+1}=X_{i-1,j}$ for $2\le i\le r$, $1\le j<r$, together with $X_{1,j+1}=0$ and $X_{r,j}=0$. These equations make $X$ scalar, and then both arrow images force the same scalar on the target. At $r=0$ one vertex is one-dimensional and the other is zero. Transposition gives the other singular block. For a finite regular block of $A+tB$ the maps are minus multiplication by $t$ and the identity on $k[t]/(f^e)$, in that order. Commuting with multiplication by $t$ is equivalent to multiplication by an element of that ring. Thus the residue is $k[t]/(f)$. The infinite block has the identity in the first slot and minus multiplication by $t$ on $k[t]/(t^e)$ in the second.

Every element of $1+J$ acts unipotently at each vertex, because $J$ is nilpotent. This kernel of $E^\times\to(E/J)^\times$ has order $q^j$, where
$$
j=\dim_k E-\sum_i m_i^2 d_i.
$$
The map on units is surjective since inverses lift modulo a nilpotent ideal. Consequently both vertex determinants factor through the quotient on units.

In the $i$th component let $Z_i\in\operatorname{GL}_{m_i}(\mathbb F_{q^{d_i}})$ and put $z_i=N_{\mathbb F_{q^{d_i}}/k}(\det Z_i)$. The contribution to the two determinants is $(z_i^{a_i},z_i^{b_i})$. For a singular component the action at each vertex consists of $a_i$ or $b_i$ copies of the multiplicity-space transformation. For a regular component each vertex of the block has the $f$-adic filtration with $e$ successive quotients, each isomorphic to $\mathbb F_{q^{d_i}}^{m_i}$. Lift $Z_i$ entrywise to the local ring. It is invertible there and acts by $Z_i$ on every quotient. The determinant of $Z_i$ viewed over $k$ is the norm of its determinant over its field of definition, as follows after extending scalars and taking the product over all field embeddings. An infinite block uses the same argument with the $t$-adic filtration. Acting as the identity on all other components proves the asserted contributions. All $z_i\in k^\times$ are attainable by finite-field norm surjectivity and by choosing a diagonal $Z_i$.

Define
$$
D_P=\left\{\prod_i(z_i^{a_i},z_i^{b_i}):z_i\in k^\times\right\},
\qquad
K_P=\frac{q^j \prod_i \left|\operatorname{GL}_{m_i}(\mathbb F_{q^{d_i}})\right|}{|D_P|}.
$$
Thus $D_P$ is the strict stabilizer's exact determinant image, and every fiber above a pair in $D_P$ has cardinality $K_P$. The multivariate generating object here is just a subgroup of $(k^\times)^2$. It retains correlations between vertex determinants, which can be lost by computing the two projections separately.

## Counting and finding transporters

For a fixed $H$ find one strict transporter $(S_0,T_0)$ from $HP$ to $Q$, or certify its absence. The endomorphism algebras of $HP$ and $P$ are literally the same because $H$ is invertible on the two arrows. When a transporter exists all strict transporters are precisely $(S_0X,T_0Y)$ for $(X,Y)\in E^\times$. For the prescribed determinants $(s,t)$ the count is therefore $K_P$ if
$$
(s/\det S_0,\ t/\det T_0)\in D_P,
$$
and zero otherwise. For the full special-linear count sum this test at $(s,t)=(1,1)$ over all $H\in\operatorname{SL}_2(k)$. The cases in the sum are disjoint because each full transporter has a specific third matrix, even if two choices of $H$ produce identical slice pairs.

Here are the computational details.

1. Compute an ordinary strict transporter by applying constructive module isomorphism to $U\oplus V$. The three marked operators are the projector onto $U$ and the two operators with only the lower-left block nonzero, given by the two arrows. Commutation with the projector forces the isomorphism to be block diagonal. The two other intertwining equations are then exactly the pencil equations. This also constructs coordinates for a Kronecker model once its block types are known.
2. To recover the types, find the normal rank $r_0$ of $A+tB$ and one nonzero minor of that order by exact elimination over $k(t)$. Rational elimination has polynomial bit cost here using fraction-free elimination, since all minors have degree at most $r_0$. In the rank-zero case use the empty minor $1$. Every prime $f$ of a finite elementary divisor divides that minor, so factor its determinant. For each such $f$ and each $s=1,\ldots,r_0+1$ compute the kernel dimension over $k$ for multiplication by the pencil over $k[t]/(f^s)$. Dividing by $\deg f$ gives
   $$ (u-r_0)s+\sum_{\ell=1}^{r_0}\min(s,e_\ell), $$
   where the $e_\ell$ are the $f$-valuations of the nonzero Smith invariant factors. The formula follows by evaluating each Smith diagonal entry in the quotient. Differences after subtracting $(u-r_0)s$ recover the positive valuations with multiplicities. Each valuation is at most $r_0$ by the degree bound on the chosen minor. Use the same calculation for the reversed pencil $B+tA$ at $f=t$ to recover infinite blocks. For the right singular indices, compute $h_s$, the dimension over $k$ of the polynomial kernel vectors of degree at most $s$. This is a linear coefficient system. In Kronecker form each right singular block of index $r$ contributes $\max(0,s-r+1)$, because its kernel is freely generated by the alternating monomial column of degree $r$. The other blocks contribute zero. Thus the second differences of $h_s$, with $h_{-1}=h_{-2}=0$, give the multiplicities. Stop at $s=\max(u,v)$, an upper bound on all minimal indices. Transposition recovers the left indices.
3. Compute $\dim E$ by solving its two linear endomorphism equations. To compute $D_P$, start with the identity and multiply by the set $\{(z^{a_i},z^{b_i}):z\in k^\times\}$ for each type, keeping a predecessor for each reachable pair. The table has at most $(q-1)^2$ entries. For a requested pair recover the $z_i$ and lift them. To lift a prescribed $z_i$, use $Z_i=\operatorname{diag}(y_i,1,\ldots,1)$ with $N(y_i)=z_i$, then use the block coordinates from step 1. The next paragraph gives the norm step in time polynomial in $q$ and $d_i$.

For $K=\mathbb F_{q^d}$ let $N=(q^d-1)/(q-1)$, so the norm is the $N$th power. Factor the integer $q-1$ by trial division and find a generator of $k^\times$ by enumeration. For each prime $\ell\mid q-1$, obtain from this generator an element of order $\ell^{v_\ell(q-1)}$. Find an $\ell$th root in $K$ repeatedly, $v_\ell(N)$ times. At each step a root exists by cyclicity and has order exactly $\ell$ times the current order. The final element has order $\ell^{v_\ell(q^d-1)}$, so its norm has order $\ell^{v_\ell(q-1)}$. Multiply the final elements over the distinct primes and enumerate the first $q-1$ powers of their product. Its norm generates $k^\times$, so one of those powers yields any requested norm. If $q=2$, take $y_i=1$.

Each root extraction in this construction only needs a deterministic algorithm for a split squarefree binomial of degree $\ell\le q-1$ over $K$. It is split because one root exists and all the $\ell$th roots of unity lie in $k$. For any such split polynomial, pick a $k$-basis $c_1,\ldots,c_d$ of $K$. Two distinct roots differ in at least one value $\operatorname{Tr}_{K/k}(c_jx)$ by nondegeneracy of the finite-field trace pairing. For each $j$ and each $b\in k$, split the current factors by taking gcds with $\operatorname{Tr}_{K/k}(c_jx)-b$, using the polynomial $\sum_{h=0}^{d-1}(c_jx)^{q^h}$ reduced modulo the polynomial being split. Compute that polynomial by repeated modular $q$th powering. The gcds give each trace-value partition, and their common refinement consists of linear factors. This costs polynomially many field operations in $d$, $q$, and the degree of the binomial, even when $|K|$ is exponential in $d$.

All finite-field operations use the input field representation and polynomial quotient representations of its extensions. Base-field polynomial factoring in step 2 is deterministic in time polynomial in $q$ and input degree, for example by Berlekamp's algorithm with enumeration of the $q$ constants to split. The ordinary transporter computations use polynomially many base-field operations and there are $q(q^2-1)$ slice matrices of determinant one. The counts have bit length polynomial in the original dimensions and $\log q$, since they count subsets of three general linear groups. Multiplying out the standard finite general linear group orders and summing the tested fibers therefore satisfies the claimed bound. A recovered transporter can be checked by two matrix equations and three determinants.

## Two examples where the joint test matters

Take the direct sum of one singular block of source and target dimensions $(1,2)$ and its transpose of dimensions $(2,1)$. The determinant image consists of $(xy^2,x^2y)$ with $x,y\in k^\times$. Each individual determinant ranges over all $k^\times$. The joint image has index $\gcd(3,q-1)$, since the exponent matrix has Smith diagonal $(1,3)$. In particular over $\mathbb F_7$ there are strict GL transporters whose two determinants cannot be simultaneously corrected, although each can be corrected on its own.

For a full three-mode example over $\mathbb F_5$, let $P=(I_2,J_2)$ with $J_2$ a nilpotent Jordan block of size two, and put $Q=(E,EJ_2)$ for $E=\operatorname{diag}(2,1)$. These pencils are GL-isomorphic by left multiplication. Their homogeneous determinant forms are $x^2$ and $2x^2$. Vertex transformations of determinant one preserve the determinant form, and a slice change sends $x^2$ to the square of a nonzero linear form. Over $\mathbb F_5$ this cannot equal $2x^2$. Thus the full SL transporter count is zero.

## Connection to the manuscript

Masullo's §1.3.3 and §1.8.1 filter a global object through stages designed to make the local terms tractable. In the finite result, the nilpotent radical contributes the explicit common factor $q^j$ and contributes trivial determinant labels. The residual components carry the whole determinant image, and finite products and coset sums give the full count. This proof uses finite algebra and is independent of the manuscript's analytic claims. Its scope is the binary slice format in the Grochow–Qiao tensor isomorphism framework. [Masullo, The Music of the Primes](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=38) · [Grochow–Qiao, Tensor Isomorphism-Completeness](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2021.31) · [Grochow–Qiao, Counting-to-Decision](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.16)

The regular block norm calculation also occurs in the project's rational pencil work. The finite-field result here includes singular block contributions to both determinant coordinates and gives exact fiber sizes with witness recovery. [Earlier rational binary-pencil proof](https://github.com/Dugongue/MathProofs/blob/main/FourIsomorphismResearchBets/PENCILS.md)
