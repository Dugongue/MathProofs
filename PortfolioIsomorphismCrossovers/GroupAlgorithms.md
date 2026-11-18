# Counting epimorphisms from elementary-abelian Sylow towers

**Theorem.** Let $G$ be a finite group admitting a normal Sylow tower all of whose factors are elementary abelian, and let $D\unlhd G$. Given the Cayley tables of $G$ and any finite group $H$, and the elements of $D$, one can decide whether a surjection $G\to H$ with kernel contained in $D$ exists, construct one if it does, and count all such surjections exactly, in deterministic polynomial bit time. The bound allows an unbounded number of layers and no bound on the multiplicities of simple modules.

More strongly, in deterministic polynomial time we produce a weighted list of at most $|G|$ representatives of quotient maps $G/N\to G/D$ with $N\unlhd G$, $N\le D$. Every eligible kernel belongs to exactly one represented block. All quotient maps within that block are isomorphic over $G/D$. The weight gives the number of kernels in the block. Distinct blocks may represent the same relative isomorphism type.

The same conclusion holds if $G$ has a normal abelian Sylow subgroup $P$ of arbitrary exponent, the given $D$ contains $P$, and $G/P$ has an elementary-abelian Sylow tower. Thus the unmarked algorithm allows an arbitrary abelian first layer.

This gives the elementary-abelian Sylow-tower case of Grochow–Srivastava–Thakkar’s Open Question 3(4), and an exact counting result for their Open Question 2 on these classes. The case $D=G$ gives the unmarked algorithm. The classes are recognized from raw tables, and the target need not come with a tower. This is an informal proof. [Original questions](https://arxiv.org/html/2609.07429v1#S7)

## 1. A normal kernel at one layer

If $G\ne1$, take a normal elementary abelian Sylow $p$-subgroup $P$ and a Hall complement $K$, so $G=P\rtimes K$. Write $P$ additively and $K$ multiplicatively. Let $N\unlhd G$ and let $U=N\cap P$. Because $N/U$ and $P/U$ are normal in $G/U$ and have trivial intersection, they commute there. For $(x,k)\in N$, this means $k$ acts trivially on $P/U$. The order $m$ of $k$ is prime to $p$. Taking the $m$-th power in $G/U$ gives $(m(x+U),1)$. This lies in the trivial intersection of $P/U$ with $N/U$, so $x\in U$ and $(0,k)\in N$. It follows that

$$
N=U\rtimes W,\qquad W=N\cap K,\qquad
W\unlhd K,\quad W\le \ker(K\to\operatorname{Aut}(P/U)).
$$

Conversely, any $K$-submodule $U\le P$ and normal subgroup $W\unlhd K$ satisfying that kernel constraint define the kernel of the natural quotient homomorphism $P\rtimes K\to (P/U)\rtimes(K/W)$. Thus such pairs parametrize all normal kernels. The additional constraint $N\le D$ is equivalent to $U\le P\cap D$ and $W\le K\cap D$.

All operations here are polynomial in the table length. To recognize a normal Sylow subgroup, collect the elements of $p$-power order, test the subgroup property, and check the Sylow order. In the promised group some such subgroup exists. Picking any normal Sylow subgroup preserves the tower condition in the quotient. In fact the image of the original tower under quotient by that Sylow subgroup has one trivial factor, and all other factors survive unchanged since their orders are prime to $p$. Repeating also recognizes the input promise. To construct $K$, form the quotient $Q=G/P$, select a representative $s(x)$ for each $x\in Q$, and read the cocycle $f(x,y)=s(x)s(y)s(xy)^{-1}\in P$. Set $g(x)=|Q|^{-1}\sum_{z\in Q} f(x,z)$ in $P$. Summing the cocycle relation over $z$ gives

$$
f(x,y)=g(x)+xg(y)-g(xy).
$$

Hence $s'(x)=-g(x)s(x)$, with the minus sign in the additive coordinate of $P$, is a homomorphic section. Its image is $K$.

## 2. Count every bounded kernel with one branch per multiplicity vector

Put $P_0=P\cap D$, and take its isotypic decomposition as a $K$-module

$$
P_0=\bigoplus_{i=1}^a S_i^{m_i},
\qquad
q_i=\big|\operatorname{End}_{\mathbb F_p K}(S_i)\big|,
$$

where the simple $S_i$ are pairwise nonisomorphic. Maschke’s theorem applies because $p$ does not divide $|K|$. Use any $K$-module complement of $P_0$ in $P$. For a dimension vector $0\le u_i\le m_i$, choose $U_{\mathbf u}\le P_0$ to be the direct sum of the first $u_i$ copies of each $S_i$. The number of $K$-submodules $U\le P_0$ of that type is

$$
b_{\mathbf u}=\prod_{i=1}^a {m_i\brack u_i}_{q_i}.
$$

Indeed, on the $i$-th isotypic summand the functor $\operatorname{Hom}_K(S_i,-)$ identifies submodules with subspaces of a right vector space of dimension $m_i$ over the endomorphism division ring. This division ring is finite and is a field. The same identification shows that an automorphism of $P_0$ as $K$-module takes any $U$ of this type to $U_{\mathbf u}$. Extend it by the identity to the chosen complement in $P$, then to $P\rtimes K$ by fixing $K$ pointwise. It acts trivially on $G/D$, because it changes each element of $P$ only by an element of $P_0$. In particular, replacing $U$ by $U_{\mathbf u}$ preserves the quotient together with its map to $G/D$; it also preserves the subset of $K$ that acts trivially on $P/U$.

The decomposition is elementary to compute within polynomial table time. Compute a basis of $P$ and coordinates for all elements by building successive spans. To find a simple submodule in a current submodule, enumerate its nonzero vectors and compute their cyclic $K$-spans. A span of least positive dimension is simple, since any of its proper nonzero submodules would give a smaller cyclic span. An invariant complement can be found by solving for a $K$-equivariant projection onto this simple summand that is the identity on the summand. Maschke guarantees consistency. Iterate. The $K$-intertwiner spaces between summands and the endomorphism-ring sizes follow by solving linear equations.

## 3. Pass the remaining constraint through the complement

For a chosen $U_{\mathbf u}$, set

$$
D_{\mathbf u}=(K\cap D)\cap\ker(K\to\operatorname{Aut}(P/U_{\mathbf u})).
$$

This subgroup is normal in $K$. Recurse on $(K,D_{\mathbf u})$. The base case $G=1$ emits one quotient record of weight one. A recursive record $K/W_j\to K/D_{\mathbf u}$ of weight $b_j$ induces the record

$$
(P/U_{\mathbf u})\rtimes (K/W_j)\ \longrightarrow\ G/D
$$

of weight $b_{\mathbf u} b_j$. On $P/U_{\mathbf u}$ the map is the original quotient to $G/D$, and on $K/W_j$ it is the map induced from $K\to G/D$. Both the action on $P/U_{\mathbf u}$ and the latter map factor through $K/D_{\mathbf u}$. Therefore any relative isomorphism of two complement quotients over $K/D_{\mathbf u}$ extends by the identity on $P/U_{\mathbf u}$ to a relative isomorphism over $G/D$.

The proof of coverage and weights is by induction. For a given actual $U$ of a fixed type, the eligible $W$'s are exactly the same eligible normal subgroups of $K$ as for $U_{\mathbf u}$. Changing $U$ to $U_{\mathbf u}$ fixes $K$, so none of these $W$'s is changed by that replacement. Use the unique recursive block containing $W$. The uniqueness of $U=N\cap P$ and $W=N\cap K$ proves that the blocks partition the eligible original kernels. Each resulting record has a known representative kernel, namely $U_{\mathbf u}\rtimes W_j$, with the displayed weight.

## 4. Decision, search and counting

There are at most

$$
\prod_i (m_i+1)\ \le\ 2^{\sum_i m_i}\ \le\ |P|
$$

branches at this layer. Choose the underlying sequence of Sylow complements deterministically from the group alone, independent of the marked subgroups. At depth $r$, the product of the preceding branch upper bounds is the product of the orders of the preceding Sylow factors, at most $|G|$. Thus there are at most $|G|$ leaves and $(1+\log_2 |G|)|G|$ total nodes. All tables and auxiliary systems have polynomial size. The Gaussian binomial coefficients can be computed by their integer recurrence. Even an unrestricted count of subgroups of $G$ has polynomial bit length, since a subgroup has a generating list of length at most $\log_2|G|$. Thus the arithmetic on weights costs polynomial bit time.

Any quotient of an elementary-abelian Sylow tower is in the same class. The images of a Sylow tower form a normal series with elementary abelian factors, and the primes remain distinct. So if the arbitrary target $H$ fails the tower recognition, return zero. Otherwise test each represented quotient for isomorphism to $H$ by Babai–Qiao’s polynomial-time Cayley-table isomorphism and transporter-coset algorithm. The algorithm and its coset output are also stated as Proposition 1.1 in Skresanov’s recent account. A representative isomorphism composed with the quotient map gives an actual surjection. Sum the weights of the matching records to count kernels. Every matching kernel contributes exactly $|\operatorname{Aut}(H)|$ epimorphisms, and that group order is computable from the coset algorithm’s permutation generators using a stabilizer chain. [Babai–Qiao](https://people.cs.uchicago.edu/~laci/papers/stacs12.pdf) · [Skresanov, Proposition 1.1](https://arxiv.org/html/2605.26748v1)

## 5. An abelian first layer of arbitrary exponent

Now assume that $G=P\rtimes K$ with $P$ an abelian Sylow $p$-subgroup, $P\le D$, and $K$ an elementary-abelian Sylow-tower group. One can find an appropriate $P$ by trying the finitely many primes dividing $|G|$ and applying the same table recognition in the quotient. The cocycle calculation of Section 1 constructs the complement because multiplication by $|K|$ is invertible on every finite abelian $p$-group. The same normal-kernel proof yields $N=U\rtimes W$, since multiplication by $m$ is invertible on $P/U$ for $m$ prime to $p$.

The appropriate branches are now the $K$-module isomorphism types of $P/U$, weighted by the number of kernels $U$ realizing each type. For two such kernels of the same quotient type, choose any $K$-linear isomorphism between the quotients and extend it to the respective semidirect products by fixing $K$. The map to $G/D$ ignores the $P$ coordinate, since $P\le D$. Thus the previous argument applies to every branch once we can enumerate the $K$-module quotient types and count their kernels.

### Computing a decomposition into homocyclic lifts of simple modules

Write the underlying additive group as $\bigoplus_t A_t$, where $A_t$ is homocyclic of exponent $p^t$. Such bases are computable from the group table by standard abelian-group algorithms. The quotient of $\operatorname{End}(P)$ by its Jacobson radical $J$ is the product $\prod_t\operatorname{End}(A_t/pA_t)$, with quotient map reducing the diagonal blocks modulo $p$. [Skresanov, Proposition 3.7](https://arxiv.org/html/2605.26748v1)

For a coordinate projection $e_t$ onto $A_t$, average $k e_t k^{-1}$ over $K$, using the inverse of $|K|$ modulo the exponent of $P$. The result commutes with $K$ and reduces to the same central idempotent as $e_t$ modulo $J$. Correct it to an idempotent $f_t$ by iterating the integer polynomial $x\mapsto 3x^2-2x^3$. This changes $x$ by a multiple of $x^2-x$, and the new idempotence error is a multiple of $(x^2-x)^2$. It therefore terminates because $J$ is nilpotent. A descending chain of nonzero radical powers has length at most $\log_2|\operatorname{End}(P)|+1$, since equality would persist and contradict nilpotence. Each iteration uses ordinary endomorphism operations on group elements.

The element $f_te_t+(1-f_t)(1-e_t)$ reduces to $1$ modulo $J$ and intertwines $e_t$ and $f_t$. It is a unit, so $\operatorname{im} f_t$ has the same additive group type as $A_t$. Also $\sum_t f_t e_t$ reduces to $1$ modulo $J$, so it is invertible. Its restriction to each $A_t$ has image in $\operatorname{im}f_t$, is injective, and hence is onto by equal sizes. Consequently the $K$-invariant homocyclic groups $\operatorname{im}f_t$ give a direct sum decomposition of $P$.

In a homocyclic component of exponent $p^t$, decompose the module modulo $p$ into simple modules by Maschke. Lift each equivariant coordinate projection to an ordinary matrix modulo $p^t$, average it over $K$, then use the same idempotent correction in the ideal of matrices divisible by $p$. The idempotent images are free over $\mathbb Z/p^t\mathbb Z$ and reduce to their designated simple summands. Their bases taken together reduce to a basis modulo $p$, hence form a basis of the whole component. This gives a $K$-module decomposition into summands $S_{i,t}$, each free over $\mathbb Z/p^t\mathbb Z$, where $i$ labels the simple isomorphism type of its reduction modulo $p$. An isomorphism between reductions of two lifts of the same length lifts to an isomorphism of the lifts. First lift its matrix, then average over $K$, which retains the prescribed equivariant matrix modulo $p$. The averaged map is invertible since its reduction is invertible. The same argument identifies shorter truncations with the lifts of the corresponding smaller length.

These multiplicities are unique. The characteristic subquotient

$$
P[p^t]/\big(P[p^{t-1}]+pP[p^{t+1}]\big)
$$

is a semisimple $\mathbb F_p K$-module that detects exactly the reductions of the length-$t$ summands. Every operation described, including simple decomposition and isomorphism of simple constituents, runs in polynomial table time by the methods of Section 2 on the individual reductions. The homocyclic groups and their subquotients have size at most $|P|$. Endomorphisms of $P$ are determined by at most $\log_2|P|$ generator images, so the idempotent iterations have a polynomial bound.

### Listing and counting all kernel types

Let the source lengths for simple type $i$ be $s_{i,1}\ge s_{i,2}\ge\cdots$. The possible quotient types are exactly those obtained by choosing a truncation length $t_{i,j}$ between $0$ and $s_{i,j}$ for each summand, sorting within each $i$, and discarding zero lengths. Each such choice gives a representative quotient and a projection. The number of choices before removing duplicates is at most $\prod_{i,j}(s_{i,j}+1)\le |P|$.

To see exhaustiveness and compute weights, fix a target lift sum $B$ with sorted positive lengths $t_{i,1}\ge\cdots\ge t_{i,b_i}$ in type $i$. The image $L$ of

$$
\operatorname{Hom}_K(P,B)\longrightarrow
\operatorname{Hom}_{\mathbb F_p K}(P/pP,B/pB)
$$

is described entry by entry. A row of length $t$ may use source columns of the same simple type with length $s\ge t$. All other entries are zero, because nonisomorphic residue simples have zero intertwiner space, and maps from a shorter summand into a longer one land in $p$ times the latter. Every permitted entry lifts: lift any residue intertwiner to an additive map between the underlying free summands of the two lengths, then average over $K$. Accordingly each permitted entry is arbitrary in the finite field of size $q_i=|\operatorname{End}_K(S_i)|$, after choosing identifications of the residue copies. Their choices are independent by the direct sum decomposition.

Write $a_i(t)=\#\{j:s_{i,j}\ge t\}$. A map onto $B$ is equivalent to a surjection modulo $p$, since $B=\operatorname{im} f+pB$ implies $B=\operatorname{im} f+p^eB=\operatorname{im} f$ by iteration. Counting independent rows of type $i$ in descending length order gives

$$
\prod_{j=1}^{b_i} \big(q_i^{a_i(t_{i,j})}-q_i^{j-1}\big)
$$

if all $a_i(t_{i,j})\ge j$, and zero otherwise. The formula follows because the preceding rows lie in the nested coordinate subspace available to the next row. The condition $a_i(t_{i,j})\ge j$ is exactly $s_{i,j}\ge t_{i,j}$ for every $j\le b_i$, proving that the truncation list includes every quotient type.

All residue maps in $L$ have the same number of lifts, namely $|\operatorname{Hom}_K(P,B)|/|L|$. The two cardinalities are computable exactly. The above description determines $|L|$. To compute the homomorphism count, introduce the cyclic coordinates of the image of every cyclic generator, impose its order relation, and impose intertwining with the explicit $K$-action. These are linear congruences on a product of explicit finite cyclic groups. Smith normal form computes the order of the kernel of the resulting linear map in polynomial bit time. Multiplying the residue surjection count by the number of lifts gives $\#\operatorname{Epi}_K(P,B)$. Applying the same calculation with source $B$ gives $\#\operatorname{Aut}_K(B)$. Therefore the required number of distinct kernels giving quotient type $B$ is

$$
\frac{\#\operatorname{Epi}_K(P,B)}{\#\operatorname{Aut}_K(B)}.
$$

Use this number as the branch weight and a truncation projection as representative. The remaining recursion is exactly the elementary-abelian theorem on $K,D_{\mathbf u}$. The first branch bound is $|P|$, preserving the bound $|G|$ on leaves. Recognize an abelian Sylow tower in $H$ by allowing any abelian normal Sylow at each recognition step. The output groups have abelian Sylow towers, so the same Babai–Qiao coset algorithm gives decision, search, and exact epimorphism counts.

## Scope and provenance

Grochow–Srivastava–Thakkar’s earlier cases include specific two-layer coprime families and constraints on abelian chief multiplicity. A tower can have arbitrarily many active layers and arbitrary elementary abelian multiplicities. The quotient record here controls how choices at a lower layer act on a previously selected upper quotient, and the weighted blocks account for every eligible kernel. The approach combines the MathProofs marked quotient-kernel enumeration for Fitting-free targets with relative automorphism orbits of submodules and the finite-ring principle of reducing a lift to tractable residue data. It is independent of the recent proposed polynomial-time algorithm for general Cayley-table group isomorphism and its finite-ring applications. The marked recursion uses Maschke’s splitting at the elementary abelian layers. The general case of arbitrary abelian Sylow towers and the tame-tower clause remain open here. Publication priority has not been established. [Group epimorphism baseline](https://arxiv.org/html/2609.07429v1) · [Previous MathProofs kernel enumeration](https://github.com/Dugongue/MathProofs/blob/main/GrochowGroupFrontier/CayleyEpimorphism.md) · [Recent finite-ring applications](https://arxiv.org/abs/2611.18084)

An exact finite control enumerated every normal subgroup of the order-150 group $\mathbb F_5^2\rtimes S_3$, where $S_3$ acts through its sign. It checked the predicted weights for all 17 normal-subgroup constraints and compared six epimorphism counts with direct enumeration of images of generating elements. A second control checked the block-triangular lifting counts against all ten subgroups of $C_9\times C_3$, covering all five quotient types. All those subgroups are invariant for the coprime inversion action. A third control used the order-three companion action of $X^2+X+1$ on $C_4^2\oplus C_2^2$. With Schur field $\mathbb F_4$, all counts agree across the 12 invariant kernels and five quotient types.
