# Graph and quantum symmetry results

The arguments below are written proofs. The cited results are used at their stated scope. GP-0952, GP-0954, and GP-0955 concern different parts of the questions in Baptista–Coutinho–Godsil–Schmidt §5. The proof of GP-0952 provides the convex-geometric input for the two counterexamples.

## GP-0952 — A polyhedral quantum fractional automorphism set is classical

Let $u=(u_{ij})$ be the universal magic unitary of a finite graph $G$, and let $K=QP(G)=\{(\phi(u_{ij})): \phi \text{ a state}\}$. This is a compact convex set by weak-* compactness of the state space. Then
$$
 K\text{ is a polytope}\quad\Longleftrightarrow\quad
 K=\operatorname{conv}\{P_g:g\in\operatorname{Aut}(G)\}.
$$
More generally, every vertex with a full-dimensional normal cone in the state-evaluation set of a finite list of projections is a 0/1 point.

Indeed, if $K$ is a polytope and $v$ is a vertex, choose a real coefficient vector $c$ in the open set of vectors that uniquely maximize at $v$. This set is open in the ambient real space because there are only finitely many other vertices and all defining inequalities are strict. Write $a_c=\sum_{ij}c_{ij}u_{ij}$ and $h(c)=c\cdot v$. Every state has evaluation of $a_c$ at most $h(c)$, so $h(c)1-a_c$ is positive. Let $\phi$ lift $v$, with GNS unit vector $\xi$. Since its vector expectation on this positive element is zero, $a_c\xi=h(c)\xi$ in the GNS representation. For every individual coordinate $ij$ choose a nonzero sufficiently small real $\epsilon$ so $c+\epsilon e_{ij}$ is still in the same open set. The same equation for the perturbed coefficients, subtracted from the first, gives $u_{ij}\xi=v_{ij}\xi$. The eigenvalues of a projection belong to $\{0,1\}$. A 0/1 doubly stochastic matrix is a permutation matrix, and each evaluation commutes with the adjacency matrix. Thus every vertex of $K$ is a classical automorphism. All classical automorphism matrices lie in $K$ via characters, so the equivalence follows.

Take an asymmetric graph with quantum symmetry, as exhibited by van Dobben de Bruyn, Roberson, and Schmidt. Some off-diagonal universal entry is a nonzero projection. A state is nonzero on that projection, because states separate positive elements. Hence $K$ strictly contains the classical singleton and is nonpolyhedral. [Question in §5](https://arxiv.org/html/2606.13928v1#S5) · [Asymmetric quantum-symmetric graphs, Theorem A](https://doi.org/10.1112/plms.70098)

## GP-0955 and GP-0954 — Quantum isomorphism preserves neither polyhedrality nor the affine type

There are connected finite ordinary graphs $U,V$ that are quantum-isomorphic, with $QP(U)$ polyhedral and $QP(V)$ nonpolyhedral. In particular, quantum isomorphism does not induce a bijective affine map on these sets, including any bijection coming from a linear correspondence on their containing commutants.

First take connected, nonisomorphic, quantum-isomorphic graphs $X,Y$ with classical quantum automorphism algebras. Start with the uncolored magic-square pair of Roberson–Schmidt Corollary 6.11. To ensure connectedness, give all vertices one color and apply Theorem D of van Dobben de Bruyn–Roberson–Schmidt. It makes the graphs connected and preserves both isomorphism relations and quantum automorphism groups. Let $A=X\sqcup X$ and $B=X\sqcup Y$. If $w$ is a magic isomorphism from $Y$ to $X$, then $\operatorname{diag}(I,w)$ is a magic isomorphism from $B$ to $A$. [Uncolored magic-square pair, Corollary 6.11](https://doi.org/10.1112/jlms.12664) · [Connected decoloring, Theorem D](https://doi.org/10.1112/plms.70098)

For $A$, denote the two components by $C_1,C_2$, each of order $n$, and let $u$ be its universal magic unitary. The entries of $D=(I+A_A)^{n-1}$ are positive exactly within components. If $u$ commutes with $D$, multiplying the $x,y'$ entry of this relation on the left by $u_{xy}$ and on the right by $u_{x'y'}$ gives
$$
 (D_{yy'}-D_{xx'})u_{xy}u_{x'y'}=0.
$$
Hence, for each $j$, the projection $p_{x,j}=\sum_{y\in C_j}u_{xy}$ is constant on a source component: for $x,x'$ in that component, the two products $p_{x,j}(1-p_{x',j})$ and $p_{x',j}(1-p_{x,j})$ vanish. Denote the constant by $p_{ij}$. Row sums are $1$, and summing columns within $C_j$ and dividing by $n$ proves the same for column sums. Therefore the four entries are $p,1-p,1-p,p$ in their natural order. Every $u_{xy}$ is supported by the projection of its block, so $p$ commutes with every entry. The same argument applied to column partial sums, or to $u^{\mathsf T}$, shows that the column margin of each block equals the corresponding $p_{ij}$. Indeed the column partial sums are constant within each target component, and the row and column constants are equal by summing the block in the two ways.

On the $p$-corner each diagonal block is a magic automorphism of $X$, with unit $p$. The off-diagonal blocks give the same statement on the $1-p$-corner. Every state splits into these two corners with scalar weights $\phi(p)$, $1-\phi(p)$, omitting a corner of weight zero. The quantum automorphism algebra of $X$ is classical, so each active block has scalar evaluation a convex combination of ordinary automorphism matrices. Within either corner, choose the two corresponding ordinary automorphisms independently according to these two finite combinations. The expected matrix is exactly the corner evaluation, and each choice is an ordinary automorphism of $A$. Thus $QP(A)$ equals the classical convex hull.

On $B$, the magic matrix with off-diagonal blocks $w,w^{\mathsf T}$ and zero diagonal blocks is an automorphism. Evaluating at any state yields off-diagonal block mass, whereas every ordinary automorphism of $B$ preserves each component by nonisomorphism and connectedness. By GP-0952, $QP(B)$ is nonpolyhedral. For connected examples, take the cones $U,V$ on $A,B$ by adjoining one universal vertex to each. Extending the magic isomorphism by the fixed added vertex preserves quantum isomorphism, since a magic matrix fixes the constant vector and its transpose does too. In each cone the new vertex has unique maximum degree. A magic automorphism preserves the degree vector by adjacency commutation and row sums, so its entries between vertices of different degrees vanish by row orthogonality. The new vertex is fixed, and restricting to the original vertices identifies the state-evaluation sets affinely with $QP(A),QP(B)$. Affine bijections preserve polyhedrality. [The two questions](https://arxiv.org/html/2606.13928v1#S5)

## GP-0956 — The complete directed hypergraph has the classical symmetric group

For a finite set $V$, put $E=\mathcal P(V)\times\mathcal P(V)$. Let $s(S,T)=S$, $r(S,T)=T$, and let $I_s,I_r$ be the vertex-by-edge incidence matrices. Write $u,v$ for the universal vertex and edge magic unitaries in Faroß's definition. They satisfy $uI_s=I_sv$ and $uI_r=I_rv$. Summing the vertex coordinates of the first equation gives
$$
 |s(f)|1 = \sum_e |s(e)|v_{ef}.
$$
Multiplication by a column projection $v_{ef}$ shows $v_{ef}=0$ unless the source sizes agree. Similarly the range sizes agree. Thus the edge matrix restricts to a magic matrix on the edges $e_{ik}=(\{i\},\{k\})$. For a fixed column $e_{jl}$, the incidence equations become
$$
 u_{ij}=\sum_b v_{e_{ib},e_{jl}},\qquad
 u_{kl}=\sum_a v_{e_{ak},e_{jl}}.
$$
Both are sums of pairwise orthogonal projections from that column. They commute for arbitrary $i,j,k,l$, using the availability of all singleton/singleton edge pairs, including $e_{jj}$. The hypergraph has no multi-edges, so the vertex entries generate the entire quantum automorphism algebra by Corollary 3.17. They therefore generate a commutative algebra. Every permutation of $V$ extends uniquely to the ordered subset pairs and yields a character. Characters give exactly these permutations by the defining relations, so the compact quantum group is $S_V$. Its inclusion in $S_V^+$ is strict exactly for $ |V|\ge4$, by the standard classification of when the quantum symmetric group is classical. [Faroß, Corollary 3.17 and Question 6.1](https://doi.org/10.4153/S2976859426100046) · [Wang's quantum permutation groups](https://doi.org/10.1007/s002200050385)

## GP-0957 — Every Faroß hypergraph symmetry group is a Banica graph symmetry group

Given a finite directed hypergraph on vertex set $V$ and edge set $E$, make a simple vertex-colored graph on the disjoint union $V\sqcup E\sqcup E_s\sqcup E_r$. Put $V,E,E_s,E_r$ in four distinct colors. Join the copy of each $e\in E$ to its copies $e_s,e_r$ by two identity matchings. Join $x\in V$ to $e_s$ iff $x\in s(e)$, and to $e_r$ iff $x\in r(e)$. Empty color classes may be omitted.

The universal color-preserving magic unitary is block diagonal. Commutation with the two identity-matching adjacency blocks forces the three edge-indexed magic blocks to coincide, say with $v$. The incidence blocks then give exactly $u I_s=I_s v$ and $u I_r=I_r v$ for the vertex block $u$. The transpose blocks give equivalent equations, since magic matrices are orthogonal with transpose the inverse. All other adjacency blocks are zero. This is an isomorphism of universal C*-algebras and preserves the coproduct since it identifies the fundamental blocks and their entries. Thus the colored graph has exactly the given hypergraph quantum automorphism group.

Apply the polynomial-time vertex decoloring theorem of van Dobben de Bruyn, Roberson, and Schmidt to obtain a connected uncolored simple graph with the same Banica quantum automorphism group. Before decoloring, the construction has $ |V|+3|E|$ vertices and is polynomial in the incidence input. This settles the Banica realization alternative in the catalogue. [Hypergraph definition and open question](https://doi.org/10.4153/S2976859426100046) · [Decoloring, Theorem D](https://doi.org/10.1112/plms.70098)

## GP-0950 — Unlabeled affine seed orbits can all coincide

The minimum is one seed when the affine space is the two-point line, and no number of seeds suffices at any other positive dimension and field order. The zero-dimensional space admits only the trivial faithful action. On the two-point line there are exactly two affine subgroups, distinguished by an orbit of size one or two. In every other positive dimension and field order, the translation group and the full affine group are faithful, transitive, and have different orders because the linear group is nontrivial. Both return the entire affine space at every seed.

The obstruction can also be made with equal group orders and free orbits. For every finite field $F$, the translational action of its additive vector group on $F^3$ and the action
$$
 L_{a,b,c}(x,y,z)=(x+a,y+b,z+c+a y),\qquad(a,b,c)\in F^3
$$
are faithful regular affine actions. The latter family is a group, since
$$
 L_{a,b,c} L_{a',b',c'}=L_{a+a',b+b',c+c'+a b'} .
$$
The map from parameters to the image of any fixed point is bijective: solve uniquely for $a,b$ from the first two output coordinates and for $c$ from the third. Hence both actions give the whole affine space for every seed, including labeled seed locations and arbitrarily many adaptive seed choices. The former is abelian, and $L_{1,0,0}$ and $L_{0,1,0}$ do not commute, since the two products have different third parameters. Thus no finite seed bound resolves the unrestricted recovery question, even when the field is given and the dimension is fixed at three. The equal-order obstruction extends to every fixed dimension $d\ge3$ by adjoining full independent translation coordinates. This is a finite-field counterpart to the ambiguity of unlabeled observations studied in the real setting. [Orbit recovery questions](https://arxiv.org/html/2411.17434#S4) · [Earlier real one-orbit portfolio result](https://github.com/Dugongue/MathProofs/blob/b0947ecc8675432a7292628b99e945b7d50b216e/GrochowOrbitAndGroupAdvances/ambiguity.md)

## GP-0865 — Dense adjacency-oracle queries have quadratic worst-case complexity

Allow arbitrary preprocessing of the prior graph, and let an exact membership algorithm query individual entries of the new labeled adjacency matrix. Put $M=\binom n2$. Deterministic algorithms need $M$ queries in the worst case. Bounded-error randomized algorithms with error $\epsilon<1/2$ and worst-case budget $t$ need $t\ge(1-2\epsilon)M$.

Take the entire preprocessing data for the fixed prior $K_n$. For a fixed string of random coins, run the query algorithm with the all-one off-diagonal oracle. It inspects at most $t$ distinct unordered pairs before halting. If a uniformly random unordered pair $e$ is deleted, the execution on $K_n-e$ follows the all-one branch unless $e$ belongs to that inspected set. Coupling the two oracle runs with the same coins, the probability that their outputs differ is at most $t/M$. The probability of accepting $K_n$ is at least $1-\epsilon$ and that of accepting the random $K_n-e$ is at most $\epsilon$. The acceptance probability difference is at most the coupled differing-output probability, proving the bound. Query every unordered pair to recover the query graph and compare with its preprocessed prior by computing its canonical form; the query count is $M$, independently of the time bound for that comparison. The lower bound deals with adjacency-access query cost and worst-case dense inputs. [Isomorphic-prior model motivating the target](https://arxiv.org/abs/2609.37979)

## Status correction: GP-0968

Classical compactness is an effectively checkable criterion for $QP(A)=S(A)$. The inclusion $P(A)\subseteq QP(A)\subseteq S(A)$ gives one direction, and the published Theorem 16 gives the converse. Enumerate rational vertices of the fractional automorphism polytope and check that they are permutation matrices. This is a previously available resolution. [Baptista–Coutinho–Godsil–Schmidt, Theorem 16](https://arxiv.org/html/2606.13928v1#S3.SS5)

## GP-0927 — A polynomial-time cycle index for bilinear-forms graphs

Let $H_q(d,e)$ be the graph on $d\times e$ matrices over $\mathbb F_q$, with adjacency when the difference has rank one. Let $N=q^{de}$ be the graph order. If $\min(d,e)\ge 2$, the full automorphism cycle index, listed as cycle signatures with integer multiplicities, can be produced deterministically in $N^{O(1)}$ bit time. This includes arbitrary extension fields and arbitrary aspect ratios. If one permits one-row or one-column matrices, the corresponding complete graphs instead have a superpolynomial number of output signatures. [Graph family and full automorphism group](https://api.research-repository.uwa.edu.au/ws/portalfiles/portal/184280004/1908.11110v2.pdf) · [General matrix isometry description, §2](https://arxiv.org/abs/2211.00298)

### Recovering the parameters

On a promised raw graph, compute its diameter $d$ after assuming $d\le e$. At distance two the number $c_2$ of common neighbors is $q(q+1)$. For a direct count, translate the pair so its difference is the standard rank-two matrix with a leading identity block. If the sum of two rank-one matrices has rank two, their column lines and row lines span exactly the column space and row space of the sum. Thus each common neighbor can be treated as a $2\times2$ matrix $a b^{\mathsf T}$ with $a,b\in\mathbb F_q^2$ nonzero and $\operatorname{rk}(I-a b^{\mathsf T})=1$. This is equivalent to $b^{\mathsf T}a=1$. There are $(q^2-1)q$ choices of $(a,b)$ and precisely $q-1$ scalar copies of each rank-one matrix, so the formula follows. Recover $q$ from $c_2$ and then $e$ from $N=q^{de}$. Field arithmetic can be constructed in time polynomial in $q$ by searching for an irreducible polynomial over the prime field.

### Group structure and the square case

By the fundamental theorem of the geometry of matrices, the full automorphism group consists of the maps
$$
 X\longmapsto T+A X^\sigma B^{-1},
 \quad A\in\operatorname{GL}_d(q),\; B\in\operatorname{GL}_e(q),\;
 \sigma\in\operatorname{Aut}(\mathbb F_q),
$$
and the transpose coset when $d=e$. Here $T$ ranges over all matrices. A pair of row and column matrices gives the same action precisely up to a common nonzero scalar after $T$ and $\sigma$ are fixed. For $d=e$, $|\operatorname{GL}_d(q)|^2\le q^{2d^2}=N^2$, so simply enumerate maps of both forms, walk their permutations on all $N$ vertices, tally signatures, and divide by the common multiplicity $q-1$. The transpose is distinct from the two-sided subgroup for $d=e\ge 2$: it interchanges the two types of rank-one maximal linear subspaces that the two-sided transformations preserve.

### Frobenius cosets and their norms

Suppose $d<e$ and write $q=p^f$. For every divisor $h$ of $f$, put $q_0=p^{f/h}$ and choose as representative field automorphism the $q_0$-power Frobenius $\sigma$, of order $h$. There are $\varphi(h)$ field automorphisms of order $h$, and their affine cosets have identical cycle signature distributions. In fact, any generator of $\langle\sigma\rangle$ is $\sigma^a$ for a unit class $a$ modulo $h$. Choose an integer in that class coprime to the order of the full graph automorphism group, by avoiding zero modulo each prime divisor of that order outside $h$. Raising a group element to this integer bijects the two cosets, with inverse a power map modulo the group order. It preserves the cycle lengths of every permutation.

For fixed $\sigma$, group the pairs $(A,B)$ by their independent $\sigma$-twisted conjugacy classes. The Shintani correspondence for general linear groups identifies the classes of $\operatorname{GL}_d(q)$ with conjugacy classes in $\operatorname{GL}_d(q_0)$, and similarly for the other dimension. For an ordinary representative $A_0$ of the corresponding class, the norm $A\sigma(A)\cdots\sigma^{h-1}(A)$ is conjugate to $A_0$ over $\mathbb F_q$, and the twisted class has size $|\operatorname{GL}_d(q)|/|C_{\operatorname{GL}_d(q_0)}(A_0)|$. Use the corresponding rule for $B_0$. These statements are the norm and centralizer form of Shintani descent. [Shintani's original norm correspondence](https://www.jstage.jst.go.jp/article/jmath1948/28/2/28_2_396/_article)

For completeness, the twisted-class and centralizer counts follow directly from Lang's theorem. Write $F$ for the $q_0$-Frobenius on the general linear group over an algebraic closure. For $A$ fixed by $F^h$, choose $a$ with $A=a^{-1}F(a)$ and put $A_0=F^h(a)a^{-1}$. This is $F$-fixed since $F^{h+1}(a)=F^h(a)A$. The ordinary twisted norm of $A$ is $a^{-1}A_0a$. Changing the choice of $a$ conjugates $A_0$ by an $F$-fixed element. Every $F$-fixed $A_0$ is obtained, since Lang also lets one solve $F^h(a)a^{-1}=A_0$ and then $a^{-1}F(a)$ is $F^h$-fixed. If two choices give the same $A_0$, their quotient $a'^{-1}a$ is $F^h$-fixed and gives a twisted conjugacy between the two original matrices. Finally $x\mapsto axa^{-1}$ bijects the $F^h$-fixed twisted centralizer of $A$ with the $F$-fixed centralizer of $A_0$. For the forward direction use $xA=AF(x)$ to see $F(axa^{-1})=axa^{-1}$ and then $F^h(axa^{-1})=A_0(axa^{-1})A_0^{-1}$ to see commutation with $A_0$. The reverse follows from the same equations. Since ordinary conjugacy in the general linear group descends through field extensions by rational canonical form, the norm and its representative are already conjugate over $\mathbb F_q$.

### Computing each norm pair without constructing its preimages

For fixed norm representatives $A_0,B_0$, let $M$ be the $\mathbb F_{q_0}$-linear map $Y\mapsto A_0 Y B_0^{-1}$ on $\mathbb F_{q_0}^{d\times e}$. On $h$ copies of this space define the block cyclic map
$$
 (Y_0,\ldots,Y_{h-1})\longmapsto (M Y_{h-1},Y_0,\ldots,Y_{h-2}).
$$
This is similar over $\mathbb F_{q_0}$ to the semilinear original $X\mapsto A X^\sigma B^{-1}$, considered as an $\mathbb F_{q_0}$-linear map. To see it, extend scalars to an algebraic closure of $\mathbb F_{q_0}$. The separable extension of degree $h$ splits there into one factor per embedding and Frobenius permutes them cyclically. Thus the linear map has invertible links around a single cycle of $h$ blocks. Successive basis changes make the first $h-1$ links identities. The remaining link is their product around the cycle, the action of the two norm matrices, and is conjugate to $M$. Similarity after scalar extension implies similarity already over $\mathbb F_{q_0}$, since the dimensions of the kernels of powers of each base-field irreducible polynomial of the matrix determine its rational canonical form and are preserved under extension.

Conjugating the linear part by that similarity bijects the sets of all additive translations, preserving each affine permutation's cycle type. So for each norm pair enumerate all $N$ translations of the explicit block cyclic model, compute each type by a walk through its $N$ vertices, and multiply the resulting counts by the two twisted class sizes and $\varphi(h)$. Sum over all divisors and norm pairs, and finally divide by $q-1$ to account for the scalar duplicates.

### Cost and the degenerate case

One can list the rational canonical forms in dimension $j$ over $\mathbb F_{q_0}$ by enumerating ordered degree compositions of $j$ and lists of monic polynomials of those degrees with nonzero constants, retaining the divisibility chains. The number of candidates is at most $2^j q_0^j$. For each form, the centralizer order is the number of units in the endomorphism algebra of its $\mathbb F_{q_0}[x]$-module. If the $P$-primary part has $m_{P,i}$ cyclic blocks of length $i$ for irreducible $P$, the dimension of this endomorphism algebra is
$$
 D=\sum_P \deg(P)\sum_{i,j}m_{P,i}m_{P,j}\min(i,j),
$$
and its semisimple quotient is $\prod_{P,i}M_{m_{P,i}}(\mathbb F_{q_0^{\deg P}})$. Thus the order of its unit group is the product of the general linear orders of those factors times $q_0^{D-\sum_{P,i}\deg(P)m_{P,i}^2}$. The dimension formula follows by counting maps between two cyclic primary summands. The quotient formula follows from decomposing into indecomposable cyclic primary summands: the endomorphism ring of a summand of length $i$ has residue field $\mathbb F_{q_0}[x]/(P)$, and quotienting the full endomorphism ring by its radical kills maps between nonisomorphic indecomposable summands. Units lift through the nilpotent radical. Polynomial factoring by exhaustive monic trial divisors costs $q_0^{O(j)}$, already within the required bound. Since $d+e\le de$ for $d,e\ge2$, all work per divisor is bounded by $N^{O(1)}$. The number of divisors and the bit lengths of the counters are polynomial in $N$.

If $\min(d,e)=1$, every nonzero difference has rank one, so the graph is $K_N$. Its automorphism group has one cycle signature for each partition of $N$. Even restricting to partitions constructed from independently chosen distinct parts in $\{2,\ldots,\lfloor\sqrt N\rfloor\}$ and padding with parts of size one gives $2^{\Omega(\sqrt N)}$ signatures. Thus if the catalogue includes diameter one, no algorithm can give the stipulated list in polynomial time for all orders.

## Connections to existing portfolio proofs

The affine-orbit obstruction combines the same upper-unitriangular group multiplication used in earlier Heisenberg epimorphism work with the unlabeled observation map from orbit recovery. Affine pullback in the project’s Lean sources supplies the relevant coordinate transport model. The present counterexample is established by the coordinate argument above. [Heisenberg group multiplication and lifts](https://github.com/Dugongue/MathProofs/blob/b0947ecc8675432a7292628b99e945b7d50b216e/GenusTwoGroupEpimorphism/HEISENBERG.md) · [Orbit recovery](https://github.com/Dugongue/MathProofs/tree/b0947ecc8675432a7292628b99e945b7d50b216e/GrochowOrbitAndGroupAdvances)

The four-color incidence construction transports the two relations separately, while the existing incidence-design Lean module encodes a single classical incidence relation and proves uniqueness of its induced block permutation. GP-0956 derives commutativity of the vertex entries from the two relations before using classical incidence uniqueness. The new statements about quantum symmetry use the universal-algebra proofs above.

Bilinear-forms parameter recovery is compatible with the portfolio’s raw adjacency reconstruction and prime-field algorithms. The new counting argument replaces direct enumeration of a potentially large product of two general linear groups in the rectangular case with norm classes and additive translations. [Earlier bilinear-forms reconstruction and prime-field cycle index](https://github.com/Dugongue/MathProofs/blob/b0947ecc8675432a7292628b99e945b7d50b216e/GrochowGraphII/PROOF.md)
