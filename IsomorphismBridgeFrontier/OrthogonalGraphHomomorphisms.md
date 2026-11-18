# Orthogonal fingerprints for bounded-degree graph homomorphisms

Informal proofs. Homomorphism indistinguishability stays coRE-complete with planar, bipartite, subcubic probes of arbitrarily prescribed girth. Over positive rational weighted targets, ordinary subcubic probes can need exponentially many vertices. Both results use the same conversion between tensor contractions and graph homomorphisms. The general real weighted formulation below extends the subcubic unweighted characterization already proved by Maehara. [Cai–Young, the question following Corollary 6.6](https://arxiv.org/html/2509.10991v1#S6.SS1) · [Maehara, Lemma 13](https://arxiv.org/html/2610.09042v2#S3.SS1).

## 1. Exact orthogonal characterization

**Theorem 1.** Fix $d\ge2$. Let $A$ and $B$ be real symmetric adjacency or weight matrices, with unit vertex weights. For a simple graph $F$, put
$$
Z_A(F)=\sum_{\varphi:V(F)\to[N_A]}\prod_{uv\in E(F)}A_{\varphi(u),\varphi(v)}.
$$
Let $S_A=\operatorname{im} A$, $P_A$ be the Euclidean orthogonal projector onto $S_A$, and $M_k(A)=\sum_i(P_Ae_i)^{\otimes k}$. Then $Z_A(F)=Z_B(F)$ for every simple graph $F$ of maximum degree at most $d$ if and only if $N_A=N_B$ and a Euclidean isometry $U:S_A\to S_B$ satisfies
$$
UA|_{S_A}=B|_{S_B}U,\qquad U^{\otimes k}M_k(A)=M_k(B)\quad(1\le k\le d).
$$
For rational inputs and fixed $d$, the tuple $(A,M_1(A),\ldots,M_d(A))$ is computable in deterministic polynomial bit time in ambient coordinates. Comparison can equivalently be made under $\mathrm O(N_A,\mathbb R)$ after checking vertex counts.

Write $x_i=P_Ae_i$. The edge weight is $\langle x_i,A x_j\rangle=A_{ij}$. At a vertex of degree $k$, summing its image label gives $M_k(A)$. Hence $Z_A(F)$ is the contraction of the indicated vertex tensors with $A|_{S_A}$ on every edge, times $N_A$ for every isolated vertex. It is preserved by the stipulated isometry.

Conversely equality on one isolated vertex gives $N_A=N_B=N$. The first fundamental theorem for $\mathrm O(N)$ says that complete pairings of slots of copies of the entries of the tuple generate its polynomial invariants. These are diagrams whose vertices are copies of $A$ or of the $M_k(A)$. Self-wires and parallel wires are permitted. Invariants separate real orthogonal orbits because the group is compact, or one can apply the real orthogonal converse of the Holant theorem directly. [Ben Young, Theorems 2.11 and 4.3](https://arxiv.org/html/2409.06911).

Collapse each chain of $j$ consecutive $A$-vertices between moment slots. The resulting wire has operator $A^j$; when $j=0$, it can use $P_A$ because its incident legs lie in $S_A$. Pure $A$-components are traces $\operatorname{tr}(A^j)$ with $j\ge1$. Let $Q(t)$ be a common annihilating polynomial on the two nonzero spectral subspaces, with $Q(0)\ne0$. For rational inputs take the product of the nonzero-root parts of their characteristic polynomials. If both matrices vanish, the fingerprints are zero. For every $j\ge0$, $t^3$ is invertible modulo $Q(t)$, so there is a polynomial $q_j$ divisible by $t^3$ and congruent to $t^j$ modulo $Q(t)$. Then $q_0(A)=P_A$, and $q_j(A)=A^j$ for $j\ge1$, with the same $q_j$ for $B$.

Replace a power $A^\ell$ on a wire by a path of $\ell$ edges and sum over its fresh internal labels. A self-wire becomes a cycle based at its moment vertex. All powers in $q_j$ are at least three, so the resulting probes are simple, even for parallel wires or several self-wires. Original moment-vertex degrees stay at most $d$. A pure tag trace is a common combination of $\operatorname{tr}(A^\ell)$ for $\ell\ge3$, represented by simple cycles. Thus all diagrams agree on the two tuples. Orthogonal separation gives an ambient transporter, whose $A$-slot forces it to carry $S_A$ onto $S_B$. Conversely any isometry as in the theorem extends orthogonally across the kernels, which have the same dimension.

For the bit-time claim, find a rational column basis $C$ by Gaussian elimination. For positive rank, $P_A=C(C^{\mathsf T}C)^{-1}C^{\mathsf T}$, with polynomial bit lengths by determinant bounds. Rank zero gives $P_A=0$. Computing all $M_k$ uses polynomial bit time for fixed $d$.

At $d=3$ the fingerprint uses the Euclidean commutative algebra product $u*v=P_A(u\odot v)$, with $\odot$ denoting coordinatewise multiplication. Its cubic multiplication tensor is $M_3(A)$. The other tags are $A|_{S_A}$, $P_A{\bf 1}$, and the Euclidean metric $M_2(A)$. When $A$ is nonsingular the algebra is the coordinatewise algebra and its isometries are coordinate permutations.

**Algorithm with simple nonzero spectrum.** The comparison is in deterministic polynomial bit time if all nonzero eigenvalues of the first adjacency matrix are simple, with arbitrary multiplicity at zero. Compare characteristic polynomials and vertex counts. Compute each normalized eigenvector over the field obtained from its individual eigenvalue and the positive square root of its squared norm. Every intertwiner is diagonal with signs in the ordered eigenbases. A transformed moment coefficient uses at most $d$ eigenvalues, so the two inputs' corresponding coefficients can be compared in a common field of polynomial degree for fixed $d$. Exact algebraic arithmetic tests whether those coefficients agree, are negatives, or have different magnitudes. Reject a magnitude mismatch. Every nonzero coefficient gives one linear sign equation over $\mathbb F_2$, with a repeated eigenline occurring with its multiplicity modulo two. Gaussian elimination decides the combined equations. [Exact algebraic arithmetic in Chizewer et al., Appendix A](https://arxiv.org/html/2603.27128v1#A1).

## 2. Positive rational weighted targets encode orthogonal 3-TI

**Theorem 2.** Orthogonal isomorphism of rational three-tensors under three independent real orthogonal groups reduces in deterministic polynomial bit time to subcubic homomorphism indistinguishability of strictly positive rational positive semidefinite weight matrices, allowing nonzero diagonal weights.

For $T\in U_1\otimes U_2\otimes U_3$, let $C_T$ denote its equivariant injective image in the multidegree $(1,1,1)$ subspace of $\operatorname{Sym}^3(W)$, where $W=U_1\oplus U_2\oplus U_3$ is orthogonal. Decompose it into rational multiples of cubes monomial by monomial, by
$$
uvw=\frac1{48}\sum_{\epsilon\in\{\pm1\}^{3}}\epsilon_1\epsilon_2\epsilon_3(\epsilon_1u+\epsilon_2v+\epsilon_3w)^3.
$$
For a term $t v^3$, put $x=t/6$ and add rows $(x+1)v,(x-1)v,-xv,-xv$. Their first moment is zero, their third moment is $t v^3$, and their second moment is $(4x^2+2)vv^{\mathsf T}$. Across the eight directions for each monomial the covariance is diagonal, since all $|t|$ agree.

For the input pair choose three distinct positive integers $c_1,c_2,c_3$ greater than every current diagonal entry. Add pairs of opposite basis multiples to raise both second moments to $D=\operatorname{diag}(c_1I,c_2I,c_3I)$, preserving first and third moments. To express half a nonnegative rational deficit $a/b$ as a sum of rational squares, write $ab$ in binary, replace each odd power $2^{2j+1}$ by two copies of $(2^j)^2$, and divide all square roots by $b$. This gives polynomial bit lengths and a polynomial number of rows. Pad by zero rows to a common length $N$. Replace each row $v_i$ by $b_i=(H,v_i)$ with common rational $H>0$ large enough that all dot products are positive and $NH^2>\max c_i$. Output the Gram matrices $A_{ij}=\langle b_i,b_j\rangle$. Every step has deterministic polynomial bit time.

The latent moments of the two lists are
$$
\begin{aligned}
L_1&=NH e_0,\\
L_2&=NH^2e_0^{\otimes2}+D,\\
L_3(T)&=NH^3e_0^{\otimes3}
+H(e_0\otimes D+\text{the other two placements})+C_T .
\end{aligned}
$$
Subcubic probes contract these tensors with the Euclidean metric and contribute $N$ per isolated vertex. A transporter of the original tensors thus preserves probes. Conversely, to obtain any diagram contraction as a common linear combination of simple probes, replace each wire by a path, which contributes $L_2^j$ for $j$ internal degree-two vertices. Since $L_2$ is fixed and invertible, the identity is a polynomial combination of powers with $j\ge2$. Once again the graphs in the expansion are simple and subcubic. Orthogonal separation gives an exact moment transporter. It fixes $e_0$ by $L_1$ and preserves all three labelled $U_i$ by the distinct eigenvalues of $L_2$. The $C_T$-slot then yields the original transporter.

## 3. Exact exponential lower bound on probe size

**Theorem 3.** There are explicit pairs of strictly positive PSD rational matrices on $N=\Theta(m)$ vertices, with entries in one fixed finite alphabet, for which the least number of degree-three vertices in any distinguishing simple subcubic probe is exactly
$$
D_m=8(F_{m+2}-2)
$$
for $F_1=F_2=1$ and $m\ge2$. Thus every distinguishing probe has $2^{\Omega(N)}$ vertices, and one has $O(D_m)$ vertices.

Use the realified unit-magnitude tensor pair of the exact invariant-degree theorem. The three modes have side $2(6m-8)$, all nonzero entries have magnitude two, and at most six nonzero entries use any given mode coordinate. Their least separating invariant degree is $D_m$. A separating invariant of degree $D_m$ is a single contraction, with exactly one wire per mode per tensor copy. [Exact tensor invariant-degree theorem, Sections 1–3](https://github.com/Dugongue/MathProofs/blob/main/TopologyAndInvariantCrossovers/Spectral.md).

Use Theorem 2 with one constant choice of $c_1,c_2,c_3$ across the whole family. Each monomial adds a fixed diagonal covariance on each incident coordinate and each coordinate sees bounded incidence. All deficits take values in a fixed finite rational set. Thus only boundedly many rows per coordinate are needed and row entries lie in a fixed finite alphabet. Positive definiteness of $D$ ensures at least $\dim W$ rows, giving $N=\Theta(m)$. Row norms are bounded and one constant $H$ works, with $H^2>\max c_i$. The resulting dot products lie in one fixed positive rational alphabet.

For any probe with $s$ degree-three vertices, substituting the displayed moment formulas gives a polynomial in $T$ invariant under $\prod_i\mathrm O(U_i)$ of degree at most $s$, because only the $C_T$ term varies and it is linear. Separation degree proves equality whenever $s<D_m$.

For the upper bound take the degree-$D_m$ separating contraction and label each wire by its mode. At each trivalent vertex place $L_3(T)$, with the orthogonal projector onto the labelled $U_i$ on every wire. Constants with $e_0$ disappear, leaving the known separating contraction times a common nonzero normalization. Each labelled projector is a common linear combination of $L_2^j$ for $2\le j\le5$, by interpolation at the four distinct nonzero eigenvalues. Expanding each power via a path gives simple subcubic probes with exactly $D_m$ degree-three vertices and $O(D_m)$ total vertices. At least one term distinguishes.

## 4. Planar bipartite subcubic probes are coRE-complete

**Theorem 4.** Fix $g\ge3$. It is coRE-complete to determine whether two finite simple graphs have equal homomorphism counts from every finite simple planar bipartite graph of maximum degree three and girth at least $g$. This holds for 2-degenerate probes and for target graphs with nonsingular adjacency matrices whose nonzero eigenvalues, even across the pair, contain no distinct opposites. The complexity drops to deterministic polynomial time when the probe maximum degree is two.

This strengthens the undecidability for all planar probes of Mančinska and Roberson. We use their coRE-completeness theorem and their equivalence with commuting quantum isomorphism. In the magic-unitary formulation, two simple graphs of the same order are quantum isomorphic when a matrix $U=(u_{ai})$ of projections in a nonzero unital $C^*$-algebra satisfies $UA=BU$, with pairwise orthogonal projections summing to the identity on each row and column. [Mančinska–Roberson, main theorem and its coRE-completeness corollary](https://arxiv.org/abs/1910.06958) · [Atserias et al., quantum and non-signalling graph isomorphisms](https://arxiv.org/abs/1611.09837).

### Quantum-isomorphism-preserving preprocessing

First compare the numbers of isolated vertices and remove them. A quantum transporter preserves degrees: $UA=BU$ and $U{\bf1}={\bf1}$ imply $\sum_i u_{ai}\deg_A(i)=\deg_B(a){\bf1}$. Multiplying by $u_{ai}$ shows that entries between unequal degrees vanish. Restriction to nonisolated vertices, or adjoining an identity block for equal isolate counts, then preserves and reflects quantum isomorphism. Unequal input sizes, unequal isolate counts, and empty resulting cases can be handled by fixed yes/no instances of the output promise.

For each remaining graph form its corona by attaching one private leaf to every vertex. Its adjacency in core/leaf order is $\left[\begin{smallmatrix}A&I\\I&0\end{smallmatrix}\right]$. The original graph has minimum degree at least one, so core degrees are at least two and leaf degrees are one. A quantum transporter of coronas is block diagonal by degree preservation. Its two blocks are identical by intertwining the off-diagonal $I$ blocks, and this common block intertwines the original adjacencies. Conversely a quantum transporter lifts by duplication. The coronas have distinct closed neighborhoods: different core vertices have different private leaves, different leaves have different core neighbors, and a core and leaf have different degrees.

Replace each vertex of a corona $C$ by a 3-clique, with complete bipartite connections between adjacent cliques. In coordinates the new matrix is
$$
X=A_C\otimes J_3+ I\otimes(J_3-I_3).
$$
A magic unitary lifts by tensoring with $I_3$. Conversely, the closed-twin classes of this graph are exactly the 3-cliques: its closed adjacency is $(A_C+I)\otimes J_3$, and the rows of $A_C+I$ are distinct. Every quantum transporter of the blown-up graphs preserves the closed-twin relation. Indeed equality of closed neighborhoods is determined by the two degrees and the value of $(X+I)^2$ at the pair. For any scalar matrices $M,N$ satisfying $UM=NU$, left multiplication of the entry equation at $(a,j)$ by $u_{ai}$ and right multiplication by $u_{bj}$ gives
$$
 (M_{ij}-N_{ab})u_{ai}u_{bj}=0.
$$
Thus degree preservation and the equation with $M=(X+I)^2$ force $u_{ai}u_{bj}=0$ whenever the closed-twin relation differs between the two pairs. Summing over $i$ or $b$ gives $UE_C=E_{C'}U$ for the closed-twin masks $E_C,E_{C'}$, whose diagonal blocks are $J_3$. In particular sums $\sum_{i\in D} u_{ai}$ over a source class $D$ are independent of the target representative $a$ within a target class. They also equal the corresponding column sums within the target class for each fixed representative $i\in D$. Hence they give a quantum permutation matrix $V$ on the quotient classes. Subtract $E_C-I$ and $E_{C'}-I$ in the transporter equation. The remaining relation is $U(A_C\otimes J_3)=(A_{C'}\otimes J_3)U$. Restricting it to class-constant vectors and cancelling the scalar three gives $VA_C=A_{C'}V$. This proves reflection.

The spectrum of $X$ consists of $3\lambda+2$ for $\lambda\in\operatorname{Spec}(A_C)$ and $-1$ on the internal clique contrasts. Adjacency eigenvalues are algebraic integers. A zero shifted value would give $\lambda=-2/3$. An opposite pair of shifted values, even across different input graphs, would give $\lambda+\mu=-4/3$. The only possible collision with the opposite of the internal eigenvalue would give $\lambda=-1/3$. Each is impossible because a rational algebraic integer is an integer. The preprocessing is polynomial in the graph order and preserves the yes/no quantum-isomorphism answer.

### Replacing wide planar probes by long even subdivisions

For a pair $X,Y$ with the displayed spectral property, the squares of the distinct eigenvalues in their joint spectrum are all distinct and nonzero. For any even $L\ge \max(g,4)$, interpolation therefore expresses both $I$ and $X$ as common linear combinations of even powers $X^\ell$ with $\ell\ge L$. For example interpolate the function values $1/\lambda^L$ and $\lambda/\lambda^L$ at the points $\lambda^2$ and multiply by $X^L$. The same coefficients give $I$ and $Y$.

Take a planar embedding of any simple probe $F$. Replace a vertex of degree above three by a planar subcubic tree carrying equality tensors at its vertices, with the incident edges attached in the given cyclic order. Such a tree is obtained by repeatedly splitting off two consecutive ports and joining the new branch to the remainder, inside a small neighborhood of the vertex. Each inner tree edge uses the identity matrix. The original edges use $X$ or $Y$. The value is the original homomorphism count, since an identity tree forces one common label and gives it multiplicity one. Isolated vertices simply contribute the target order.

Now replace each edge label by its interpolation combination and expand multilinearly. A power $X^\ell$ is realized by a path of $\ell$ edges, with private new internal vertices. Every resulting graph is simple, planar, and subcubic. All original network vertices may be assigned the same bipartition color because every path has even length. Every cycle is made of whole subdivided edges and has length at least $L$. Every subgraph with an edge contains either some internal path vertex of degree at most two or only original vertices, which have no edges between them. Thus the graphs are 2-degenerate. Consequently equality on the specified small-degree class implies equality on every planar probe. The converse follows from inclusion of the probe classes. The reduction uses only the polynomial-size target preprocessing, since the symbolic expansion proves equivalence and need not be computed.

The coRE lower bound now follows from the planar quantum-isomorphism theorem. Inequivalence is recursively enumerable by enumerating the restricted finite probes. For degree two, every component is a path or an even cycle. Path counts are determined by finitely many consecutive terms of $\mathbf1^{\mathsf T}X^j\mathbf1$, by the characteristic-polynomial recurrence for $X$ and $Y$. Even-cycle counts above the girth cutoff use the corresponding trace recurrence for $X^2,Y^2$. Thus a polynomial number of exact integer matrix operations suffices.

The quantum reduction here relies on the published coRE-completeness theorem. The new statements are the simultaneous restrictions to bipartite, subcubic, arbitrarily fixed large girth 2-degenerate probes and the explicit simple-target spectral preprocessing. Nearby work treats either general planar probes or bounded-degree probes without the planarity restriction. Priority for this precise strengthening remains unestablished. [Mančinska–Roberson](https://arxiv.org/abs/1910.06958) · [Cai–Young, Corollary 39 in the proceedings](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2026.32) · [Neuen–Seppelt, sparse probes](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.75)
## Relation to prior work

Cai and Young give the complex orbit-closure formulation and ask for a sharper characterization. Maehara gives the projected-adjacency characterization at degree three for unweighted targets and uses path interpolation. Theorem 1 gives the uniform fixed-degree, real weighted version and is included as the construction framework. Theorem 2 reverses the moment map. Theorem 3 transfers the exact invariant-degree lower bound. Theorem 4 gives a quantum-isomorphism-preserving target construction with a spectral condition that makes the planar probe conversion bipartite. The unweighted polynomial-time decision question from Cai and Young remains open. Exact finite controls checked twelve common spectral identities on a pair of singular matrices, both signed cubic polarizations, and five corona/clique target fixtures with all twenty-five joint no-opposite-spectrum exclusions. The literature check did not establish publication priority for the new claims. [Cai–Young](https://arxiv.org/html/2509.10991v1#S6.SS1) · [Maehara](https://arxiv.org/html/2610.09042v2) · [Young](https://arxiv.org/html/2409.06911) · [Neuen–Seppelt, sparse probes](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.75).
