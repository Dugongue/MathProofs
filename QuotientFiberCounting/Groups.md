# Epimorphism testing for Abelian Sylow towers with projective layers

Informal proof. Grochow, Srivastava, and Thakkar ask in Open Question 3(4) whether Group Epimorphism for two Abelian Sylow tower groups is in polynomial time on complete Cayley tables. The result below gives a new polynomial-time case with no bound on the number of primes, Sylow exponents, generator ranks, or ranks of the actions on lower layers. The unrestricted question remains open. [Original Question 3(4)](https://arxiv.org/html/2609.07429v1#S7)

## 1. The target promise and algorithm

Let a Sylow tower be written as nested split extensions $H_i=B_i\rtimes H_{i+1}$, where $B_i$ is a normal abelian Sylow $p_i$-subgroup and the primes are distinct. The conjugation action of a chosen complement defines the structure of $B_i$ as a module. The complement is determined up to conjugation and therefore up to the induced module isomorphism needed here.

For a coprime module $B_i$, split it into homocyclic indecomposable lifts of simple $\mathbb F_{p_i}H_{i+1}$-modules. For each simple type separately, choose one exponent and call a summand exceptional if it has a different exponent. The theorem assumes a choice with at most $s$ exceptional summands per simple type at each target layer, for a constant $s$. In particular every target with homocyclic Sylow subgroups passes with $s=0$. The case $s=0$ also allows different simple types of the same Sylow subgroup to occur at different exponents. Multiplicities at the chosen exponent are unrestricted.

**Theorem.** Given both Cayley tables, there is a deterministic polynomial-time decision and search algorithm on this class. The target promise may instead be stated for a source tower order whose restriction to primes dividing $|H|$ is a valid target order with the indicated bound. The algorithm recognizes and tests all such orders. For a specified compatible order with per-layer bounds $s_i$, the work is at most
$$
(|G|+|H|)^{O(1)}\prod_i |A_i|^{O(s_i)},
$$
where $A_i$ are the source Sylow layers. There is no rank or exponent restriction on the marked action quotients. There is also a deterministic polynomial-time exact count and corresponding witness algorithm on the same class. Section 4 gives the additional counting argument.

## 2. A local orbit lemma for the retained quotient marks

Work at prime $p$, with a $p'$-group $K$ acting on a finite abelian $p$-group $B$. Let $C$ be another such $K$-module, and seek representatives of the surjections $B\twoheadrightarrow C$ up to precomposition by $K$-module automorphisms of $B$.

First suppose all simple constituents of $B$ modulo $p$ have one isomorphism type. Split $B=P\oplus E$, where $P$ comprises its summands of the chosen exponent $p^a$, and $E$ comprises all exceptional summands. Take the coefficient ring $R=(\mathbb Z/p^a\mathbb Z)[K]$ for $P$. The module $P$ is projective over $R$. Indeed it is free as a module over $\mathbb Z/p^a\mathbb Z$. Given a lift problem against a surjective $R$-map, lift first over the scalar ring and average the lift over $K$. The order of $K$ is a unit, so the averaged lift is equivariant.

**Projective cover fact.** If $P$ is this projective module, any two equivariant surjections $\alpha,\beta:P\to D$ are related by an automorphism $u$ with $\beta u=\alpha$. Their maps on reduction modulo $p$ are surjections of semisimple modules. Their kernels on that reduction have the same isomorphism type by cancellation in a semisimple module, so an automorphism $g$ of $P/pP$ takes one reduced surjection to the other. The map
$$
P\longrightarrow D\times_{D/pD}(P/pP),\qquad x\longmapsto(\beta(x),\bar x)
$$
is surjective. To lift a pair, choose an element with the required reduction and correct its image by an element of $pP$, using $\beta(pP)=pD$. Lift the map $x\mapsto(\alpha(x),g\bar x)$ through this surjection by projectivity. The resulting endomorphism $u$ lifts $g$, so its image generates $P$ modulo $pP$. Iterating through the powers of $p$ shows its image is all of $P$. Finiteness makes it an automorphism. This proves the fact.

Now fix $\chi:E\to C$. Put $C_0=C[p^a]$, $U=\chi(E)$, $V=C_0\cap U$, and $U_0=\chi(E[p^a])$. Every map from $P$ has image in $C_0$. A surjection $\psi:B\to C$ with this restriction therefore requires $C_0+U=C$ and a surjection $\bar\mu:P\to C/U$. Conversely these conditions give surjective marks, since projectivity lifts $\bar\mu$ to $\mu:P\to C_0$. For every map $\lambda:P\to V/U_0$, choose a lift $\tilde\lambda:P\to V$ by projectivity. Retain the mark
$$
f_\lambda(p_0,e)=\mu(p_0)+\tilde\lambda(p_0)+\chi(e).
$$

Any desired $\psi$ is in the orbit of one of these marks. Use the projective cover fact to align the quotient maps on $P$ by an automorphism of $P$, leaving $E$ unchanged. The aligned map on $P$ differs from $\mu$ by a map into $V$. Its residue modulo $U_0$ is one of the enumerated $\lambda$. The remaining discrepancy into $U_0$ lifts through $\chi:E[p^a]\twoheadrightarrow U_0$ by projectivity. The resulting block shear $(p_0,e)\mapsto (p_0,e+v(p_0))$ absorbs the discrepancy. This proves orbit coverage and includes the earlier case where every exceptional summand has smaller exponent, since then $U=U_0$ and $\lambda$ is zero.

For several simple types, decompose $B$ and $C$ into their isotypic summands. Every composition factor of a homocyclic lift is its residue simple type, as is seen on the successive $p$-multiples. Homomorphisms across different types vanish by their composition factors. Hence the problems in the types are independent. Write $C_\nu,P_\nu,E_\nu$ for the components of type $\nu$, and let $s_\nu$ count the exceptional $E_\nu$-summands. Each homocyclic simple summand is generated as a $K$-module by a single lift of a nonzero residue element. Its orbit spans modulo $p$ by simplicity, and iteration through powers of $p$ gives additive generation. Consequently the number of $\chi$-choices is bounded by $\prod_\nu |C_\nu|^{s_\nu}$. The subquotient $V/U_0$ of $\chi(E_\nu)$ is annihilated by $p^a$. Its additive generator rank is at most $s_\nu\dim_{\mathbb F_p}S_\nu$, since an additive subgroup or quotient of an abelian $p$-group has no larger generator rank. Thus $|V/U_0|\le p^{a s_\nu\dim_{\mathbb F_p}S_\nu}$. With one module generator per homocyclic summand of $P_\nu$, this bounds the number of $\lambda$-choices by $|P_\nu|^{s_\nu}$. In total the mark list has at most
$$
\prod_\nu (|C_\nu||P_\nu|)^{s_\nu}\le (|C||B|)^{\max_\nu s_\nu}
$$
entries. Types absent from $B$ require the corresponding $C_\nu$ to vanish. All statements include zero summands.

The representatives can be constructed in time polynomial in the explicit group tables per attempted $\chi$. Scan the possible images of the cyclic module generators and use word propagation on their $K$-orbit. For each $\chi$, test and construct an equivariant epimorphism $P\to C/U$ by the existing algorithm for fixed marked module quotients, with trivial mark. List $\lambda$ by its possible generator images, and construct $\mu$ and $\tilde\lambda$ by additive linear congruences. The earlier algorithm uses partition-matroid and linear-matroid intersection on the choices of residue maps. It is polynomial in the explicit tables and applies with arbitrary coprime $K$-action. The coprime module decomposition and polynomial quotient lists are those already established by the earlier proof. [Coprime module decomposition and listing](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md) · [Fixed marked module lift and earlier action-rank algorithm](https://github.com/Dugongue/MathProofs/blob/main/SylowTowerActionRanks/PROOF.md)

## 3. Combining the marked quotients along the tower

The precise held datum at one recursive stage is a quotient map from $G'=A\rtimes K$ to $G'/D$, where $D\unlhd G'$ bounds the kernel of a sought epimorphism. One can start with $D=G$. Every normal kernel $N$ has form $U\rtimes W$ with $U\le A$ invariant, $W\unlhd K$, and $W$ acting trivially on $A/U$. In fact $A/U$ and $N/U$ commute in $G'/U$ by normality and trivial intersection. If $(a,k)\in N/U$, then $k$ acts trivially on $A/U$, and taking the element to the order of $k$ kills the complement coordinate. Its additive coordinate must vanish by coprimality. This gives the decomposition and its converse.

Let $C=A/(A\cap D)$, with map $\rho:A\to C$. Enumerate the at most $|A|$ coprime module quotient types $B$ of $A$, by truncating its homocyclic simple summands. Retain only those of the additive Sylow type required by the corresponding target quotient in the chosen order. If the prime is absent in the target, the required type is zero. Exclude those for which no exponent choice gives at most $s_i$ exceptional summands in every simple type at that layer. This exclusion is sound under the promise. For a successful quotient the acting complement $K$ acts through a surjection onto the target complement, so pulling back its modules preserves simple types, isomorphism relations and exponents. Each successful $B$ obeys the target's bound.

For each remaining $B$, use Section 2 to construct mark representatives $\psi:B\twoheadrightarrow C$. For each representative, decide whether an equivariant epimorphism $f:A\to B$ with $\psi f=\rho$ exists and construct one if so. Use the fixed marked module test cited above. Replacing a mark by its orbit representative preserves feasibility, since the tested $f$ can be postcomposed by the corresponding automorphism of $B$. Retain one witness $f$ for each feasible representative.

Define
$$
D'=(K\cap D)\cap\ker(K\to\operatorname{Aut}(B)).
$$
Recurse in $K$ with this upper bound on the complement kernel. Every permitted $W$ lies in $D'$, and the action of $K$ on $B$ as well as its existing map to $G'/D$ both factor through $K/D'$. Therefore an isomorphism of recursive quotients over $K/D'$ gives an isomorphism of the reconstructed semidirect products over $G'/D$, without affecting the marked map of $B$. This proves that one representative at each stage still suffices, inductively, to represent every prospective kernel needed for the decision. The kernel of the action of $K$ on $B$ depends on its module isomorphism class, so choosing a new $f$ over the same mark cannot change $D'$. Induction reconstructs all needed quotient representatives and their explicit maps from $G$. At the root compare the resulting quotient to $H$ by the polynomial-time isomorphism algorithm for Abelian Sylow towers, with its isomorphism output. A positive test yields an actual epimorphism. [Babai–Qiao](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.453) · [Coset version, Proposition 1.1](https://arxiv.org/html/2605.26748v1#S1)

At one stage the number of tested branches is bounded by $|A|\cdot(|A||C|)^{s_i}\le |A|^{1+2s_i}$. Thus the product over the layers is at most $|G|\prod_i |A_i|^{2s_i}$. Finding a splitting, computing a coprime module decomposition, and testing each candidate use polynomial table time. One can try all orders of the distinct primes of $|G|$, since their number of permutations is at most $|G|$. For each order, use the raw tables to find normal abelian Sylow subgroups and compute complements by the ordinary coprime cocycle-averaging argument. Inspect the target's induced tower using the same order, skipping absent primes. If a putative target prime occurs without a source prime, divisibility already rules out an epimorphism. Recognition of the module condition uses the same homocyclic decomposition. Since complements of the relevant abelian normal Hall groups are conjugate, the order-specific test is independent of the choice of complement. This proves the theorem's polynomial bound on the promised inputs.

## 4. Exact counts on the same class

The same promise also gives polynomial-time exact counting. This requires a count for the local marked epimorphisms $f:A\to B$, and a weight for each orbit of marks $\psi:B\to C$. All epimorphisms and automorphisms here respect the acting group $K$.

### Counting with one fixed mark

Work one simple type at a time. Decompose the corresponding part of $A$ into $k$ homocyclic simple summands $S_j$. In $B=P\oplus E$ let $P$ have exponent $p^a$ and let $E/pE$ have multiplicity $s$ of the residue simple $S$, where $s$ is the number of exceptional summands. Let $\mathbb D=\operatorname{End}_{\mathbb F_pK}(S)$, a finite field. After identifying the source simple reductions with $S$, the residues of maps on individual summands are columns over $\mathbb D$.

Enumerate the entire residue matrix into $E/pE$, with $s$ rows and $k$ columns. It has $|\mathbb D|^{sk}$ possibilities. If it is not surjective discard it. For each selected matrix, use additive congruences to impose on each $S_j$ both $\psi f_j=\rho|_{S_j}$ and its selected residue into $E/pE$. These are independent affine systems. Discard the selection if any system has no solution. Use linear congruences and their projections to compute, for each possible residue into $P/pP$, the number of completions of the corresponding per-summand system. Concretely this number is the common cardinality of the kernel of projection from the homogeneous solution group to the $P$-residue. It is computed once per system by imposing zero $P$-residue, without listing all possible residues.

For a source summand $S_j$ of exponent $p^{t_j}$, the variations of its $P$-residue form the column space $U_{t_j}$ corresponding to the image of
$$
Z[p^{t_j}],\qquad Z=\ker\psi\cap(P\oplus pE),
$$
in $P/pP$. Indeed every residue map into that image lifts as a module map through $Z[p^{t_j}]$ by projectivity of the source summand over $(\mathbb Z/p^{t_j}\mathbb Z)[K]$. These column spaces increase with $t_j$; they may be zero. Thus the $P$-residues are independent affine columns with nested spaces of variation.

For the chosen surjective $E$-residue map, let $W$ be its kernel on the multiplicity space $\mathbb D^k$. The combined map is onto exactly when the $P$-residue restricted to $W$ is onto. Filter the ambient $\mathbb D^k$ by the spans of the source coordinates of lengths at most $t$ and give $W$ the induced filtration. An adapted basis of $W$ extends to one of the ambient filtered space, by successively extending bases of the nested subspaces. It follows that restriction to $W$ of the allowed variations gives every map still respecting the induced filtration and the spaces $U_t$; extend such a map by zero on the new basis vectors. The cardinality of each restriction fiber is the ratio of the product of the ambient column-space sizes to the product of the induced column-space sizes on $W$.

For completeness, the exact number of spanning tuples of affine columns with nested variation spaces is found by tracking only their current rank. Order the adapted basis columns in nondecreasing $t$. For the current column $v+U_t$, the projection of the span of the preceding chosen columns modulo $U_t$ is the fixed span of their offsets, since every preceding variation belongs to $U_t$. Let its dimension be $j$. If the next offset projects outside this span, all $|U_t|$ choices increase the rank. If the offset projects inside the span and the current rank is $r$, exactly $|\mathbb D|^{r-j}$ choices lie in the current span and leave the rank unchanged; all other choices increase it. These transition weights give an exact rank dynamic program. Retain the count for the full target rank. Multiply by the uniform restriction-fiber count and all per-summand counts. Sum over the $E$-residue matrices, then multiply over the simple types. Surjectivity on the head is equivalent to surjectivity on the finite abelian $p$-group.

The number of $E$-residue matrices over all types is at most $|A|^{s_i}$, since $|\mathbb D|\le |S|$ and every source summand contains at least $|S|$ elements. The endomorphism field is computed by linear equations in the simple representation, and arithmetic in it uses the additive basis and composition of its matrices. Its cardinality is at most the table size, so explicitly finding field coordinates is also feasible. The other operations and the bit length of the counts have polynomial cost. This proves the marked-count bound per quotient test.

### Counting mark orbits and full maps

Fix $\chi$ and retain the definitions of $C_0,U,V,U_0$ and $\bar\mu$ from Section 2. For each epimorphism $\alpha:P\to C/U$, conceptually pick an automorphism aligning it to $\bar\mu$; the algorithm never lists these automorphisms. Normalize a mark with quotient map $\alpha$ by this automorphism. For each residual $\lambda:P\to V/U_0$, the number of normalized maps $P\to C_0$ with that residual is $|\operatorname{Hom}_K(P,U_0)|$, by projectivity. Thus each enumerated pair $(\chi,\lambda)$ stands for a disjoint bin of size
$$
\#\operatorname{Epi}_K(P,C/U)\cdot|\operatorname{Hom}_K(P,U_0)|.
$$
Every mark in its bin is in the orbit of the produced representative. The first factor uses the existing unmarked coprime-module count and the second uses additive congruences. Multiply independent bin sizes across the simple types.

Merge mark representatives that are isomorphic over $C$, by the fixed marked module test with source and target both $B$. An onto endomorphism of $B$ is an automorphism, so this tests exactly the required orbit equality. For a merged orbit $\mathcal O$ with representative $\psi$, its cardinality is the sum of the sizes of its represented bins. The number of distinct $K$-invariant kernels $U\le A\cap D$ whose marked quotient belongs to that orbit is
$$
\frac{|\mathcal O|\cdot\#\{f:A\twoheadrightarrow B \mid \psi f=\rho\}}
     {|\operatorname{Aut}_K(B)|}.
$$
To see this, each epimorphism $A\to B$ whose kernel lies in $A\cap D$ determines its mark uniquely. All marks in the same orbit have equal fiber counts by a change of basis in $B$. Each kernel has $|\operatorname{Aut}_K(B)|$ quotient identifications, all with marks in this orbit. The denominator is the earlier unmarked count for $B\to B$. This gives an integer branch weight, with no duplication across distinct quotient types and merged mark orbits.

As in Section 3, the permitted complement kernels and all downstream acceptance tests depend only on the marked relative quotient, so the local and recursive kernel counts multiply. Distinct local kernels $U$ and complement kernels $W$ give distinct full kernels $U\rtimes W$. Count the kernels whose quotient is isomorphic to $H$, then multiply by $|\operatorname{Aut}(H)|$. The transporter-coset algorithm for Abelian Sylow towers produces automorphism generators, and their group order is computable in polynomial time by the standard permutation group algorithms. The same induction handles different valid tower orders by choosing one that satisfies the promise before counting, since each such order yields the full count. A positive branch still supplies the actual map. Polynomial time follows on the same class, though counting uses more local tests than decision. [Unmarked coprime counts](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md) · [Isomorphism cosets](https://arxiv.org/html/2605.26748v1#S1)

## 5. Unbounded-action examples and exact scope

Take the groups
$$
G_r=\mathbb F_3^r\rtimes (\mathbb Z/8\mathbb Z)^r,\qquad H_r=\mathbb F_3^r\rtimes (\mathbb Z/4\mathbb Z)^r.
$$
An element of either complement inverts coordinate $i$ if and only if its $i$-th coordinate is odd. The normal Sylow $3$-subgroup comes first in the tower, as the Sylow $2$-subgroup is not normal. The non-elementary source layer has an action quotient of binary rank $r$. Thus the prior bound from action ranks does not give polynomial table time uniformly on these examples. Both target layers are homocyclic and the new theorem applies with $s=0$. For another family, use the same sign actions of complements $(\mathbb Z/8)\times C_2^r$ and $(\mathbb Z/4)\times C_2^r$ on $\mathbb F_3^{r+1}$. The marked action rank grows, and the target has $r$ shorter summands relative to its maximum exponent. The present theorem applies by taking exponent two as the chosen exponent and keeping the single longer summand as exceptional.

This argument does not reduce arbitrary nonhomocyclic targets to the projective case. In particular the existing two-prime family built from binary code containment may have unbounded numbers of summands of both exponents in one simple type. Since its tables have size $2^{O(r)}$ for code length $r$, a polynomial-time algorithm for this family would give a deterministic $2^{O(r)}$-time code containment algorithm. NP-completeness of the compact code problem neither supplies nor rules out that running time. The present contribution is the exact compression of all chosen-exponent summand marks with compatible exceptional restrictions, and the resulting unbounded-action algorithms. The fixed-mark orbit lemma and the overall proof are informal. Publication priority for the specific application was not established by the source search. [Original scope](https://arxiv.org/html/2609.07429v1#S7) · [Earlier code correspondence](https://github.com/Dugongue/MathProofs/blob/main/SylowTowerActionRanks/PROOF.md)
