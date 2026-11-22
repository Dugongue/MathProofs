# Arithmetic profiles of ordinary tensor isomorphism

Let $K$ be a field. For an $n$-dimensional unital associative $K$-algebra $A$, write $T_A$ for its multiplication tensor in $A^*\otimes A^*\otimes A$. Isomorphism of these tensors uses all three independent general linear groups. For extensions $E/K$ the arithmetic profile of a pair records where $T_A$ and $T_B$ are isomorphic. All the theorems below concern ordinary tensors over these extensions.

## 1. Exact tensor witnesses and entry degrees

**Lemma 1.** For two unital associative algebras of the same finite dimension, there is a natural bijection, for every field extension $E/K$,
$$
 \operatorname{Iso}_{\rm TI}(T_A,T_B)(E)
 \simeq (B_E^\times)^2\times \operatorname{Iso}_{E\text{-}{\rm alg}}(A_E,B_E).
$$
The same formula is an isomorphism of functors on commutative $K$-algebras.

*Proof.* An ordinary TI witness is an invertible triple $(P,Q,R)$ such that $R(ab)=P(a)Q(b)$. Put $u=P(1)$ and $v=Q(1)$. The equalities $R(a)=P(a)v=uQ(a)$ make left multiplication by $u$ and right multiplication by $v$ invertible. Thus $u,v\in B_E^\times$. For example, invertible left multiplication gives a right inverse, which is also a left inverse by injectivity. Now $\phi(a)=u^{-1}R(a)v^{-1}$ is unital, invertible and multiplicative, using $u^{-1}P(a)=\phi(a)=Q(a)v^{-1}$. The inverse sends $(u,v,\phi)$ to the maps $a\mapsto u\phi(a)$, $a\mapsto\phi(a)v$, and $a\mapsto u\phi(a)v$. The formulas commute with base change, and the proof uses the same invertible maps over an arbitrary commutative $K$-algebra. $\square$

In particular, for finite étale $A,B$ of dimension $n$, the witnesses form $n!$ geometric components, each a copy of $(\mathbb G_m)^{2n}$. Each component is indexed by an algebra isomorphism between two split products of $n$ fields. If $L/K$ is a common finite Galois splitting field, let $X,Y$ be the sets of geometric factors with their $G=\operatorname{Gal}(L/K)$-action. The Galois action on components is the natural action on the set $\operatorname{Bij}(X,Y)$. The bijections of Lemma 1 retain the transport of the finite algebra witnesses.

**Corollary 2.** The least extension degree admitting a tensor isomorphism equals the smallest $G$-orbit size in $\operatorname{Bij}(X,Y)$, and in particular is at most $n!$. The upper bound is attained over $\mathbb Q$ in every dimension.

*Proof.* For an extension $E/K$, choose the relative embedding in a common overfield and let $H_E=\operatorname{Gal}(LE/E)$ viewed inside $G$. A witness exists exactly when $H_E$ fixes a bijection. If its stabilizer in $G$ is $J$, then $[E:K]\ge[G:H_E]\ge[G:J]$, and $E=L^J$ attains the latter degree. For sharpness let $A$ be a degree $n$ number field with normal closure of group $S_n$, and let $B=\mathbb Q^n$. Every bijection from the natural $S_n$-set to the trivial set has trivial stabilizer. For $n\ge3$, such a field is given by a monic polynomial having, modulo three distinct sufficiently large primes, squarefree factor degrees $(n),(n-1,1),(2,1,\ldots,1)$. Irreducibility makes the group transitive. The $(n-1)$-cycle makes it doubly transitive, and conjugating a transposition then gives all transpositions. CRT combines the three coefficient prescriptions. Dimensions one and two are immediate. $\square$

## 2. Classification over a Galois extension

**Theorem 3.** Given a finite Galois extension $L/K$, the extension profiles of pairs of equal-dimensional finite étale multiplication tensors split by $L$ are exactly the nonempty conjugacy-invariant downward-closed families $\mathcal C$ of subgroups of $G=\operatorname{Gal}(L/K)$. For every such $\mathcal C$, one pair realizes
$$
 T_A\simeq_E T_B\quad\Longleftrightarrow\quad H_E\in\mathcal C
$$
for every field extension $E/K$.

*Proof.* A finite $G$-set $X$ corresponds to the étale algebra $\prod_{G/S\ {\rm orbit\ of}\ X}L^S$. Selecting another representative for an orbit gives an isomorphic factor. Over $E$, scalar extension corresponds to restriction of the action to $H_E$, since the primitive idempotents give these actions after extending to $LE$. For any $X,Y$, the family $\{H:X|_H\simeq Y|_H\}$ is conjugacy invariant and downward closed, and contains the trivial subgroup when the dimensions agree.

For the converse, let $v(H)=0$ on $\mathcal C$ and $v(H)=1$ elsewhere. In the Burnside ring, the mark of a virtual $G$-set at $H$ is its signed number of $H$-fixed points. Marks are injective and exhaust the rational vectors on conjugacy classes of subgroups, since their matrix on the orbit basis $[G/S]$ is triangular with diagonal entries $[N_G(S):S]$. Choose an integral virtual set $a$ whose marks are a positive integer multiple of $v$, and write $a=[X]-[Y]$ by separating positive and negative orbit coefficients. The mark at the trivial subgroup vanishes, so $|X|=|Y|$. For $a=0$, take equal singleton sets. Restriction of $a$ to $H$ is zero exactly when every subgroup of $H$ has zero mark. By downward closure this is equivalent to $H\in\mathcal C$. Vanishing in the Burnside ring of $H$ is equality of the actual orbit multiplicities, and Lemma 1 now gives the asserted ordinary tensor profile. $\square$

Here is an explicit dimension bound from the classical mark inversion. Let $\mu$ be the Möbius function of the subgroup poset, and put $y(S)=\sum_{S\le H}\mu(S,H)v(H)$. The coefficient of $[G/S]$ in the rational preimage of $v$ is $y(S)/[N_G(S):S]$. Indeed, $m_U([G/S])$ is $[N_G(S):S]$ times the number of conjugates of $S$ containing $U$. Multiply the rational coefficients by $|G|$, which makes them integral. The two sets then both have size
$$
 \frac{|G|}{2}\sum_{S\le G}|y(S)|
$$
when the profile is proper. The factor $1/2$ uses the zero total dimension of the virtual set. Every finite table here is effective from $G$ and the allowed subgroup classes. The mark calculation is classical. [Gluck–Yoshida idempotents in Yoshida](https://www.math.sci.hokudai.ac.jp/hmj/page/19-3/pdf/HMJ_19_3_1990_509-574.pdf) · [Burnside marks in Bouc](https://www.lamfa.u-picardie.fr/bouc/burnamscorr.pdf)

**Corollary 4.** Suppose $G=(C_p)^r$ for $r\ge1$. For the profile accepting every proper subgroup and rejecting $G$, the minimum side length of an étale multiplication tensor pair split by $L$ is
$$
 p\prod_{j=1}^{r-1}(1+p^j).
$$

*Proof.* Since every proper subgroup must have mark zero, the mark at $G$, say $h\ne0$, determines the entire virtual difference. For $S$ of codimension $s$, the orbit coefficient is $h(-1)^s p^{s(s-1)/2}/p^s$ by subspace-lattice inversion. The coefficients at hyperplanes force $p\mid h$, and $h=p$ gives integer coefficients in every codimension. The least equal cardinality is half the absolute mass of that primitive virtual difference, since adding any common orbit only increases size. The absolute mass is $p\sum_{S\le G}p^{s(s-1)/2}$. The subspace recurrence for Gaussian binomial coefficients gives $\sum_s {r\brack s}_p p^{s(s-1)/2}t^s=\prod_{j=0}^{r-1}(1+p^jt)$. At $t=-1$ this identity gives the stated Möbius coefficients by the defining recursion, and at $t=1$ it evaluates the mass. $\square$

## 3. Prescribed bounded-degree tests with every local test positive

**Theorem 5.** Let $K$ be a number field, $D\ge1$, and $K_1,\ldots,K_a$ any finite list of finite extensions of $K$. There are two equal-dimensional finite étale $K$-algebras $A,B$ such that their ordinary multiplication tensors are isomorphic over every completion of $K$, and for every $[E:K]\le D$,
$$
 T_A\simeq_E T_B
 \quad\Longleftrightarrow\quad
 \text{some }K_i\text{ admits a }K\text{-embedding in }E .
$$
The construction allows the list to be empty.

*Proof.* Let $L/K$ be finite Galois containing copies of the $K_i$, inside a fixed algebraic closure of $\mathbb Q$. Pick $r$ with $2^{r-1}>D$, and rational primes $\pi_j$ unramified in $L/\mathbb Q$, all congruent to $1\bmod8$, satisfying $\pi_j\equiv1\bmod\pi_i$ for $i<j$. Dirichlet's theorem gives each choice. Quadratic reciprocity makes each prime a square modulo each of the others. Put $M=\mathbb Q(\sqrt{\pi_1},\ldots,\sqrt{\pi_r})$. The $\pi_j$ are independent mod squares over $L$ by valuations at primes above $\pi_j$. Consequently $G'=\operatorname{Gal}(LM/K)\simeq\operatorname{Gal}(L/K)\times(C_2)^r$.

At the place $2$ all $\pi_j$ are already local squares, and all are positive at the real place. At a prime $\pi_j$, the other $\pi_i$ are local squares by Hensel's lemma. All remaining finite primes are unramified and have cyclic decomposition group, of order at most two in this elementary abelian group. Thus every decomposition subgroup $D_v\le G'$ over a place $v$ of $K$ has projection of order at most two to $(C_2)^r$. Base change of the local $\mathbb Q$-extension to $K_v$ preserves this upper bound. In particular $[G':D_v]\ge 2^{r-1}>D$.

Apply Theorem 3 over $LM/K$ with the downward family generated, up to conjugacy, by all the $D_v$ and all $\operatorname{Gal}(LM/K_i)$. It contains each $D_v$, so all completions are positive. For a probe of degree at most $D$, its subgroup $H_E$ has index at most $D$ in $G'$, so it cannot lie in any conjugate of $D_v$. It lies in a conjugate of $\operatorname{Gal}(LM/K_i)$ precisely when the corresponding conjugate of $K_i$ is contained in $E$. This is equivalent to the stated embedding test. $\square$

In particular, for every integer $d\ge2$, there is a pair locally isomorphic everywhere and with least global extension degree exactly $d$. Use $D=d$ and one degree-$d$ extension, which can be given by an Eisenstein polynomial over $K$. For quadratic probes, this also has a full converse. If the test at $K$ is negative, only finitely many quadratic fields can be positive, since any quadratic field outside a common splitting field $L$ has $H_E=G$. All finite sets of positive quadratic probes occur, with all local tests positive, by Theorem 5. If the test at $K$ is positive, every quadratic probe is positive by scalar extension. Over a number field this classification is effective for computable families of these étale tensors when the output consists of the base decision and the finite positive list in the negative-base case. Splitting fields and their subgroup actions determine that list, and Theorem 5 constructs a pair from it. The unrestricted integral-point profiles on quadratics can be arbitrary c.e. subsets, so the ordinary étale-tensor profiles obey a strictly smaller universality law.

## 4. Sharp dimension for locally isomorphic étale tensors

This section records a calibration example already known in the portfolio. The earlier result covers both size-six Gassmann types for geometrically diagonal tensors. The rigidity through size five and the Klein four relation are established group-theoretic results. [Earlier side-six tensor classification](https://github.com/Dugongue/MathProofs/blob/5e2ab397cd7bcaaec1a54642f5e62c0558a8e77d/DickeAndIsomorphismMethods/GEOMETRY.md) · [Lin–Shinder–Zimmermann, Corollary 2.6 and Example 2.7](https://content.algebraicgeometry.nl/2023-6/2023-6-024.pdf).

**Theorem 6.** The minimum possible side length for a pair of finite étale multiplication tensors over a number field that are locally isomorphic everywhere and globally nonisomorphic is six. This is also their common tensor rank over an algebraic closure.

*Proof of attainment.* Take $L=\mathbb Q(\sqrt{17},\sqrt{89})$. Both primes are $1\bmod8$, and $89\equiv4\bmod17$ makes the mutual quadratic symbols positive. The argument of Theorem 5 shows that every local decomposition group has order at most two. If $G=(C_2)^2$ and $S_1,S_2,S_3$ are its three order-two subgroups, the Burnside relation
$$
 [G/1]+2[G/G]-[G/S_1]-[G/S_2]-[G/S_3]
$$
vanishes on every proper subgroup and has nonzero mark at $G$. Thus use $A=L\times\mathbb Q\times\mathbb Q$ and $B=L^{S_1}\times L^{S_2}\times L^{S_3}$, both of dimension six. The exact global test over $E$ is $E\cap L\ne\mathbb Q$. Over $\mathbb Q$, taking integral bases of the maximal orders gives tensors with integer coefficients that are also isomorphic over every $\mathbb Z_\ell$, because an algebra isomorphism over $\mathbb Q_\ell$ preserves the integral closures of $\mathbb Z_\ell$. Over an algebraic closure, an $n$-dimensional étale multiplication tensor is the diagonal sum of $n$ pure tensors, and its flattening has rank $n$. The underlying Klein four relation is classical. [Webster, small linearly equivalent $G$-sets](https://arxiv.org/html/math/0610205#S3)

*Proof of minimality.* Choose a common Galois splitting field and associated sets $X,Y$. Chebotarev implies equality of their element fixed-point counts, since every conjugacy class occurs as an unramified Frobenius and local isomorphism gives isomorphic actions of its decomposition group. The common kernel can be removed because $g$ lies in the kernel exactly when it fixes all points. Thus both actions may be taken faithful. Burnside's orbit-counting lemma applies to every subgroup, so that subgroup has the same number of orbits in $X$ and $Y$.

First suppose $X,Y$ are transitive of equal cardinality $2\le n\le5$. Let $H$ be a point stabilizer in $X$. It has at least two orbits in $X$. If it fixes no point of $Y$, it has at most $\lfloor n/2\rfloor$ orbits in $Y$. This leaves $n=4$ or $5$, with exactly two orbits. The two $H$-orbits in $X$ have sizes $1,n-1$. For $n=4$ the two orbits in $Y$ are $2,2$, making $H$ a subgroup of $S_2\times S_2$ despite having order divisible by $3$. For $n=5$ the two orbits in $Y$ are $2,3$, giving $H\le S_2\times S_3$ with order divisible by both $4$ and $3$. Thus $H=S_2\times S_3$, which has an element of order $6$ and cannot act faithfully on the four remaining points of $X$. In all cases $H$ fixes a point of $Y$, and the equal-degree transitive actions are isomorphic. The degree-one case is automatic.

For intransitive sets of size at most five, the number of orbits rules out different orbit-size partitions except $3+1$ versus $2+2$, $3+1+1$ versus $2+2+1$, and $4+1$ versus $3+2$. The first two would give a faithful action of a group of order divisible by three on a product of two-point and singleton orbits. In the last case the common faithful group has order divisible by $4$ and $3$ and injects into $S_2\times S_3$, so it is $S_2\times S_3$. It cannot inject into $S_4$. If the same partition occurs, cancel common singleton orbits. Repeated orbits of size two are distinguished as a multiset by their nontrivial quadratic characters, using independence of complex irreducible characters. In the case $3+2$, the reduced permutation representation of a transitive degree-three orbit has no nontrivial quadratic summand, since the transitive image is $C_3$ or $S_3$. The quadratic character therefore identifies the two-point orbit and leaves equivalent transitive degree-three actions. All other equal partitions reduce to transitive actions or these two-point cases. Hence no distinction of the required kind exists below six. $\square$

## 5. Exactly when extension of scalars reflects isomorphism

**Theorem 7.** Scalar extension along $E/K$ reflects isomorphism of all finite étale multiplication tensors exactly when $K$ is separably algebraically closed in $E$. For reflection of all ordinary three-tensors, a necessary condition over any field is that $K$ be algebraically closed in $E$.

*Proof.* If $K$ is separably algebraically closed in $E$, then for every finite Galois $L/K$, one has $E\cap L=K$ and $H_E=G$. Theorem 3 gives reflection for every pair of finite étale multiplication tensors. Conversely, if $E$ contains a proper finite separable subextension $K'/K$, use its Galois closure $L$ and the family of subgroups contained in conjugates of $\operatorname{Gal}(L/K')$. Theorem 3 gives a pair that coalesces over $E$ but is nonisomorphic at $K$.

Suppose there is a new algebraic element in $E$ but no new separably algebraic element. In characteristic $p>0$, one then obtains $\beta\in E\setminus K$ with $\beta^p=a\in K$, by successively taking powers of a purely inseparable element. The $K$-algebras $K[X]/(X^p-a)$ and $K[X]/(X^p)$ are respectively a field and a nonreduced algebra. Over $E$ they are isomorphic by translation of $X$. Their ordinary multiplication tensors therefore coalesce by Lemma 1. $\square$

For finite base fields the condition in Theorem 7 is also sufficient for all ordinary three-tensors. See [Finite-field tensor profiles](FiniteFieldProfiles.md) for the proof through the connected component and Lang's theorem. For general bases even a regular extension can make ordinary tensors coalesce. In fact, over $\mathbb Q$ take the Hamilton quaternion division algebra and ${\rm Mat}_2(\mathbb Q)$. Over $E=\mathbb Q(C)$, where $C$ is the smooth projective conic $u^2+v^2+z^2=0$, the matrices
$$
 i\longmapsto\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
 j\longmapsto\begin{pmatrix}u/z&v/z\\v/z&-u/z\end{pmatrix}
$$
anticommute and both square to $-1$. They give a splitting isomorphism, since $1,i,j,ij$ map to linearly independent matrices. The conic is geometrically integral, so $\mathbb Q$ is algebraically closed in $E$. The algebras, and therefore their multiplication tensors by Lemma 1, are nonisomorphic at $\mathbb Q$.

**Theorem 8.** Suppose $|K|\ge8$. The extension profiles of geometrically isomorphic ordinary three-tensor pairs are exactly the point-existence profiles of torsors under affine group schemes of finite type over $K$. In particular $E/K$ reflects all ordinary three-tensor isomorphism exactly when
$$
 H^1_{\rm fppf}(K,G)\longrightarrow H^1_{\rm fppf}(E,G_E)
$$
is injective for every affine group scheme $G$ of finite type over $K$.

*Proof.* The scheme of ordinary TI witnesses between two geometrically isomorphic tensors is a torsor under the stabilizer of the source tensor, a closed subgroup scheme of a product of general linear groups. It trivializes after any field extension giving a witness. A closed point of this nonempty finite-type scheme has finite residue degree over $K$, so this trivialization can be witnessed on an fppf cover.

For the converse let $P$ be a torsor under $G$. Milne realizes $G$ as the automorphism group scheme of a finite-dimensional, possibly nonassociative, $K$-algebra $A$. Descend the algebra structure along $P$ to get its twist $B$. Sending $p$ to the isomorphism $a\mapsto[p,a]$ identifies $P$ with the right $G$-torsor $\operatorname{Iso}_{\rm alg}(A,B)$. This is checked after a faithfully flat trivialization, where both torsors and the indicated map are the same. Use the field-independent Futorny–Grochow–Sergeichuk reduction for the single bilinear operation defining these algebras. Applying it over $K$ yields one fixed pair of ordinary three-tensors whose isomorphism over every extension $F/K$ is equivalent to $A_F\simeq B_F$, since the reduction uses the same block constructions after scalar extension. This realizes the profile of $P$. [Milne, group schemes as automorphism groups of algebras](https://arxiv.org/abs/2012.05708) · [Futorny–Grochow–Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, field independence in Example 10.7](https://arxiv.org/html/1907.00309#S10.SS2)

Hence reflection for all tensors is equivalent to a trivial kernel for every such $H^1$ restriction. This is equivalent to injectivity for every group, since if two torsors acquire the same class over $E$, their equivariant isomorphism scheme is a torsor under the inner form of $G$ obtained from the source torsor. It has an $E$-point and has a $K$-point exactly when the original classes agree. $\square$

These give extension-by-extension answers to the scalar-extension aspect of Grochow and Qiao's across-fields question (Open Question 10.6 in the combined preprint). The broader question concerns reductions between decision problems over different fields. [Grochow–Qiao, Open Question 10.6 and Example 10.7](https://arxiv.org/html/1907.00309#S10.SS2)

## 6. Relation to the proof-complexity questions

Question 7.1 of Galesi, Grochow, Pitassi and She asks for the rank-dependent polynomial-calculus degree of tensor isomorphism, including whether there is a polynomial bound without the finite-field equations. Their Question 7.3 asks for PC complexity of matrix conjugacy and congruence. The locally isomorphic but globally nonisomorphic pairs above isolate one arithmetic aspect of the interpretation of Question 7.1. The usual polynomial equations for ordinary TI with the matrix-inverse equations have a solution over the algebraic closure for every equal-dimensional étale pair. Every arithmetic negative in Theorems 3 and 5 therefore has no PC refutation in that equation system, even when all completion tests are positive. The constructions give exact extension behavior for this class of arithmetic negatives. Degree bounds for geometrically inconsistent systems, and the matrix PC bounds of Question 7.3, remain outside these results. [Galesi–Grochow–Pitassi–She, §7](https://drops.dagstuhl.de/storage/00lipics/lipics-vol264-ccc2023/LIPIcs.CCC.2023.4/LIPIcs.CCC.2023.4.pdf#page=35)

Grochow and Qiao's algebra-isomorphism and TI reductions provide the broader context. Here the normalization of an actual ordinary multiplication-tensor witness supplies a direct construction and keeps the full dependence on field extension. The use of marks and their inversion is classical. This note applies it to exact ordinary TI profiles, including prescribed finite arithmetic tests with local positivity and the stated sharp dimension bounds. The proofs are manuscript proofs. [Grochow–Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110)
