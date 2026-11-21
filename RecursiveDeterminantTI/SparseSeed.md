# A linear tensor arc with exponentially large necessary transporter poles

For each integer $m\ge1$, there are explicit concise ordinary three-tensors $T_m^+,T_m^-$ with coefficients in $\{0,1\}$ of equal format $N_m\times N_m\times N_m$, where $N_m\le55+306(m-1)$. Each tensor has $O(N_m)$ nonzero entries. Over every field there is one tensor $E_m$ supported in a single entry such that
$$
T_m^-+tE_m\ \in\ (\operatorname{GL}_{N_m})^3\cdot T_m^+
\qquad(t\ne0).
\tag{1}
$$
On the other hand, for any three invertible matrices over $k((t))$ realizing a degeneration from $T_m^+$ to $T_m^-$, let $p_i$ be the largest pole order of the entries of the $i$-th matrix, with $p_i=0$ for an integral matrix. Then
$$
p_1+p_2+p_3\ \ge\ 2^{m-1}/3,\qquad
\max_i p_i\ \ge\ 2^{m-1}/9.
\tag{2}
$$
The bounds apply to arbitrary independent changes of basis, including changes whose entries are infinite Laurent series. The construction also gives an upper bound $O(2^m)$ on the minimum sum of the three pole orders.

In particular, if polynomial matrices $P_i(t)$ in the three modes satisfy
$$
(P_1(t)\otimes P_2(t)\otimes P_3(t))T_m^+
    =t^r\bigl(T_m^-+tQ(t)\bigr)
\tag{3}
$$
with $Q(t)$ polynomial, then $r\ge2^{m-1}/3$. There is a presentation of this form with $r=O(2^m)$. Thus a linear polynomial orbit arc can require exponential order in a polynomial matrix presentation from this fixed source.

## A finite simplicial complex with doubled circulation

The underlying complex is a chain of triangulated Möbius bands and annuli. Start with an oriented three-edge circle $C_1$. A single block attaches a Möbius band whose core is the current circle $C_i$. Use the rectangular grid $[0,3]\times[-1,1]$ with integer coordinates in each axis, triangulate each unit square by the diagonal from its lower left to its upper right, and identify $(3,y)$ with $(0,-y)$. There are nine vertices, 21 edges and 12 faces. The core $y=0$ has three edges. The unique boundary circle has six edges. Orient the boundary so that the projection onto the core goes once around the core on each of its two three-edge halves.

Attach a triangulated annulus to that boundary, with the new boundary a three-edge circle $C_{i+1}$. Explicitly let $b_0,\ldots,b_5$ be the six old boundary vertices in the specified cyclic order and $a_0,a_1,a_2$ the three new ones. For $j=0,1,2$ use the faces
$$
[a_j,b_{2j},b_{2j+1}],\qquad
[a_j,b_{2j+1},b_{2j+2}],\qquad
[a_j,b_{2j+2},a_{j+1}],
$$
with subscripts read cyclically in their respective lists. These are the three triangular sectors of the strip, with each sector subdividing a pentagon bounded by two radial edges and the two boundary paths. Give $C_{i+1}$ the corresponding orientation. This block adds nine vertices, 30 edges and 21 faces to the complex. In its integral first homology, $[C_{i+1}]=2[C_i]$. The annulus identifies the two boundary classes, and the Möbius band retracts to its core with degree two on its boundary. Iterating gives $[C_m]=2^{m-1}[C_1]$. This doubling of homology classes with linearly many simplices is the Möbius-band construction used by Filakovský, Franek, Wagner and Zhechev. [Computing simplicial representatives of homotopy group elements, proof of Lemma 7](https://pmc.ncbi.nlm.nih.gov/articles/PMC6777513/)

Cone off $C_1$ with a new interior vertex and three faces. Take the barycentric subdivision of the entire capped complex, and designate one small face $\sigma$ of the cap given by a chain (cone vertex, spoke, cap triangle). Its closure is contained in the interior of the cap. Let $X$ denote the full subdivided complex and $X^-$ the same complex with the open face $\sigma$ omitted. The punctured cap is an annulus. The boundary of $\sigma$ is homologous to $C_1$ up to orientation. Each Möbius-plus-annulus block retracts to its input core, fixing that core, and the punctured cap retracts to its original outer boundary. Consequently $X^-$ is homotopy equivalent to $C_1$ and there is an integral simplicial 1-cocycle on $X^-$ with evaluation $-1$ on the boundary of $\sigma$, oriented by increasing barycentric ranks. Here each $C_i$ is identified with its subdivision, which has six edges.

Such a cocycle can be chosen with edge values bounded in absolute value by $O(2^m)$. Fix an integral cochain pattern of circulation one on an oriented subdivided core. In the single fixed-size block, choose a cocycle of circulation one on the input and hence two on the output. The difference between its restriction and the prescribed pattern on the input circle is a coboundary with integer vertex values, since the difference has circulation zero. The same holds on the output with twice the prescribed pattern. Extend the two vertex potentials to the block, possible because the two circles are disjoint, and subtract the coboundary. The resulting fixed block cocycle has the prescribed boundary values. Multiply that cocycle by $2^{i-1}$ in block $i$. Choose a fixed compatible cocycle on the punctured cap by the same adjustment on its outer circle. The pieces agree on their overlaps. Reverse the overall sign if necessary to obtain boundary evaluation $-1$ on $\sigma$.

Conversely every integral 1-cocycle $w$ on $X^-$ satisfies
$$
|w(C_m)|=2^{m-1}|w(C_1)|=2^{m-1}|w(\partial\sigma)|.
\tag{4}
$$
This follows by evaluating on the homologous cycles. If the circulation on the boundary of the omitted face is nonzero, some edge of $C_m$ has an absolute weight at least $2^{m-1}/6$.

## Two unital multiplication tensors

Order the vertices of $X$ first by the dimension of their simplex before subdivision, then by fixed labels. Every face of $X$ is a flag of simplex inclusions. Orient each edge from lower to higher vertex in this total order. Add an edge from each vertex to its successor in the total order if this was absent. Give every added edge zero products with other edges. The directed reachability order of this graph is the specified total order, so the graph has no nonidentity vertex permutation preserving its edges.

Take one basis vector $e_i$ for every vertex and one $p_{ij}$ for every edge $i\to j$, original or added. The $e_i$ are orthogonal idempotents with sum $e$. The edge $p_{ij}$ has left and right idempotents $e_i,e_j$, respectively. In the source law $\mu^+$ the only nonzero products of edge vectors are
$$
p_{ij}p_{jk}=p_{ik}
$$
for faces $(i,j,k)$ of $X$. For the target $\mu^-$ omit precisely the product belonging to $\sigma$. Every nonzero edge product uses barycentric ranks $0,1,2$, and its output has ranks $0,2$. Every product of three edges is therefore zero in either bracketing. Associativity with a vertex follows from the endpoints, so both laws are associative and unital.

In both algebras the ideal generated by commutators is exactly the span $J$ of the edge vectors. The quotient modulo the edges is commutative, and each edge is the commutator $[e_i,p_{ij}]$. The square $J^2$ is spanned by the output corners $p_{ik}$ of faces. The same corners occur as outputs in both laws. Indeed for a vertex $i$ of a pre-subdivision triangle $k$, there are two edge barycenters $j$ with $i<j<k$ in the subdivision poset. Omitting one of these two flags leaves the other. Thus $J,J^2$ have the same dimensions and the same based subspaces at both endpoints, and $J^3=0$. In the associated graded for this filtration, each off-diagonal corner is one-dimensional in exactly one of $J/J^2,J^2$.

The multiplication tensors are concise because the unit gives identity slices in both input modes and multiplication spans the output. Their entries are binary. Before subdivision the capped complex has $4+9(m-1)$ vertices, $6+30(m-1)$ edges and $3+21(m-1)$ faces. The subdivision has $13+60(m-1)$ vertices and $30+186(m-1)$ edges. The ordering adds at most $12+60(m-1)$ edges, giving the stated bound on $N_m$. Every idempotent contributes one nonzero entry, every edge contributes two unit-action entries, and each face contributes at most one further entry. This gives sparsity linear in $N_m$.

Choose the cocycle above and extend it by zero on the added edges. The diagonal algebra basis change $D(t)$ assigns $t^{w_{ij}}$ to $p_{ij}$ and one to every vertex. On a face $(i,j,k)$ the structure coefficient gains exponent $w_{ik}-w_{ij}-w_{jk}$. This is zero on the retained faces and one on the omitted face. The resulting ordinary tensor action uses $D(t)^{-\mathsf T}$ in both input dual modes and $D(t)$ in the output. This proves (1) and the $O(2^m)$ upper bound. It also produces a polynomial matrix presentation after clearing the entry poles in each mode separately.

## Reading arbitrary three-mode arcs on the associated graded

Put $R=k[[t]]$ and $K=k((t))$. Consider an arbitrary arc
$$
m(x,y)=C\,\mu^+(Ax,By)
$$
with $A,B,C$ invertible over $K$, integral law $m$ and reduction $\mu^-$. Thus the ordinary mode matrices are $A^{\mathsf T},B^{\mathsf T},C$, with pole orders $p_1,p_2,p_3$. Let
$$
R_e x=m(x,e),\qquad L_e y=m(e,y),\qquad u=m(e,e).
$$
Both slice maps reduce to the identity, and $u$ reduces to $e$. Choose a fixed functional $\ell$ with $\ell(e)=1$ and set $h=I+(u-e)\ell$. The matrix $h$ is integral and invertible over $R$, with $h(e)=u$. Normalize the law by
$$
\nu(x,y)=h^{-1}m(R_e^{-1}h x,L_e^{-1}h y).
$$
This is an integral law reducing to $\mu^-$. The unit moves back to $e$.

For the generic law write $a=Ae$, $b=Be$. The identities $R_e=C R_b A$ and $L_e=C L_a B$, with right and left multiplication in the source, show that $a,b$ are units. In a finite-dimensional unital algebra, bijective multiplication on one side gives a two-sided inverse, by applying its injectivity to the one-sided inverse identity. Substituting those identities into the normalized law gives the generic algebra isomorphism from the source to $\nu$
$$
H=h^{-1} C L_{ab}.
$$
Indeed the law before applying the change $h^{-1}$ is $C((C^{-1}x)(ab)^{-1}(C^{-1}y))$. The formula makes it isomorphic to $\mu^+$ by $x\mapsto C(abx)$. The associative and unital identities then hold over $R$, since they hold over $K$ and the modules are free. This is the unital multiplication-tensor normalization, used here with valuations on the original legs. [Bläser–Lysikov, unital multiplication tensor degenerations](https://arxiv.org/abs/1606.04253)

Use the commutator ideal $J_R$ of $\nu$, the image of the linear map $z\otimes x\otimes y\otimes w\mapsto z[x,y]w$. Its generic and special ranks are equal by the endpoint calculation. A unit minor and Gaussian elimination over $R$ make its image a free direct summand with the prescribed specialization. Apply the same argument to the multiplication of $J_R$ with itself to obtain $J_R^2$ as a direct summand. The cube is zero, since it is zero generically. Thus all three terms of the associated graded are free over $R$, and their fibers are the associated graded of the two displayed laws.

The quotient $\nu/J_R$ is isomorphic to $R^v$, where $v$ is the number of graph vertices. In detail, its special fiber is $k^v$. The primitive idempotents of this special fiber lift in the complete finite free commutative algebra. For a lift $x$ of an idempotent, $2x-1$ is a unit modulo $t$. The correction $x-(2x-1)^{-1}(x^2-x)$ squares the error. Iterate and pass to the limit, and proceed in the complementary factor for successive idempotents. Each lifted idempotent gives a rank-one direct summand because this is its special rank, and generates that summand by reduction modulo $t$. The same idempotents act on both positive graded pieces by left and right multiplication. These actions give free corner summands with the dimensions of the special corners. Choose integral graded corner generators reducing to the specified target edge vectors, and lift the graded bases to an integral basis of the original filtered module.

The generic isomorphism $H$ is filtered and induces a vertex permutation on degree zero. It preserves the union of the two positive-degree corner supports. This support includes all the ordering edges and is the same based directed graph in the two fibers. Its reachability order is total, so the permutation fixes every vertex. Hence $H$ acts by a nonzero scalar $\eta_{ij}$ on each indicated one-dimensional graded corner, in the chosen source and target bases. Write $w_{ij}=\operatorname{val}(\eta_{ij})$.

There is a bound on these scalars in terms of the original three matrix poles. Consider the two maps
$$
\widetilde B=B L_e^{-1}h=L_b H^{-1},\qquad
\widetilde C=h^{-1} C=H L_{(ab)^{-1}} .
\tag{5}
$$
The first goes from the normalized target to the source, and the second from the source to the normalized target. The extra multipliers in the expressions on the left are integral invertible matrices. Thus the entry poles are bounded by $p_2,p_3$, respectively. Both maps preserve the appropriate radical filtrations by their expressions on the right. In integral adapted bases the same pole bounds apply to all induced graded matrices, since each such coefficient is an entry of a diagonal block of the corresponding filtered matrix.

Write $\alpha_i,\beta_i$ for the valuations of the source vertex coordinates of $a,b$ in the quotient $K^v$. These coordinates are all nonzero because $a,b$ are units. Since $a=Ae$ and $b=Be$, one has $\alpha_i\ge-p_1$ and $\beta_i\ge-p_2$. In degree zero the $i$-th coefficient of $\widetilde C$ is $(a_i b_i)^{-1}$, so $\alpha_i+\beta_i\le p_3$. In any graded corner $(i,j)$, left multiplication by a unit acts by its residue at vertex $i$: the radical contribution raises the filtration degree. The two maps in (5) give, respectively,
$$
\beta_i-w_{ij}\ge-p_2,\qquad
w_{ij}-\alpha_i-\beta_i\ge-p_3 .
$$
Combining the inequalities gives
$$
|w_{ij}|\le p_1+p_2+p_3
\tag{6}
$$
on every edge. The proof used only the associated graded with integral frames. It allows poles in the off-diagonal components of the original maps and in $H$.

Finally let $c_{ijk}(t)$ be the structure coefficient of the normalized graded law on a face $(i,j,k)$ in the integral corner frames. It lies in $R$. Because the source coefficient is one, the generic algebra isomorphism gives
$$
c_{ijk}(t)=\eta_{ik}/(\eta_{ij}\eta_{jk}).
$$
At every retained face this coefficient has nonzero reduction. At $\sigma$ it is a nonzero element of $tR$. Thus the edge weights form an integer cocycle on $X^-$ and $|w(\partial\sigma)|=\operatorname{val}(c_\sigma)\ge1$. For the sharper constant, group the six signed edges of $C_m$ at the three original vertices. Each original vertex contributes a difference of two weights on edges with that same initial vertex. Both lie in $[\alpha_i+\beta_i-p_3,\beta_i+p_2]$, of length at most $p_1+p_2+p_3$. Thus $|w(C_m)|\le3(p_1+p_2+p_3)$. Equation (4) gives the stronger bound
$$
p_1+p_2+p_3\ \ge\ (2^{m-1}/3)\operatorname{val}(c_\sigma).
$$
Changing the integral corner generators scales the coefficient by units, so its valuation here is independent of the adapted generators. This proves (2). In particular a constant transporter is impossible and the degeneration is strict.

For (3), the target's full flattening ranks imply that all three polynomial mode matrices are generically invertible. Divide the first matrix by $t^r$. This gives a Laurent arc with pole sum at most $r$, proving the lower bound on the polynomial matrix presentation order.

## Exact feasibility of prescribed pole caps

In this family, a Laurent triple with prescribed nonnegative integer pole caps $p_1,p_2,p_3$ exists precisely when there are integers $w_{ij},\alpha_i,\beta_i$ with the face equations above, strict positive defect on $\sigma$, and
$$
\begin{aligned}
\alpha_i&\ge-p_1,&
\beta_i&\ge-p_2,&
\alpha_i+\beta_i&\le p_3,\\
\alpha_i+\beta_i-\beta_j-w_{ij}&\ge-p_1,&
\beta_i-w_{ij}&\ge-p_2,&
w_{ij}-\alpha_i-\beta_i&\ge-p_3.
\end{aligned}
$$
The vertex inequalities apply at every vertex and the second row applies on every edge. Necessity of the first inequality in the second row follows by also recording $\widetilde A=A R_e^{-1}h=L_{ab}R_{b^{-1}}H^{-1}$. Its graded coefficient has that valuation. The other inequalities were proved above.

For sufficiency let $H$ be diagonal of weight $w_{ij}$ on edges and zero weight on vertices. Let $a=\sum_i t^{\alpha_i}e_i$ and $b=\sum_i t^{\beta_i}e_i$ in the source algebra. Set $A=L_{ab}R_{b^{-1}}H^{-1}$, $B=L_bH^{-1}$ and $C=H L_{(ab)^{-1}}$. These maps are diagonal and the displayed constraints bound all their entry poles. Substituting them in $C\mu^+(Ax,By)$ gives $H\mu^+(H^{-1}x,H^{-1}y)$. Its regularity and endpoint follow from the face constraints. This proves that any feasible caps for arbitrary Laurent maps can be attained by diagonal Laurent maps. Clearing powers of $t$ separately in the three diagonal maps also shows that the least order in (3) is exactly the least attainable pole sum.

## Comparison and verification status

The topological degree-doubling construction is from the work on Möbius-band telescopes cited above. The new use here is to make valuation cocycles mandatory for arbitrary independent tensor mode transformations, via the constant-rank radical filtration and the two identities (5). The earlier quadratic degeneration-chain result counts strict orbit steps, while the present result bounds the minimum order of a single degeneration. The separate Kempf construction gives exponential lower bounds on weight spread for homogeneous forms, including for Laurent changes of coordinates. Here the three mode maps are independent, the forward entry poles alone suffice, and the output tensor follows a linear arc. [Kempf degeneration degree](https://github.com/Dugongue/MathProofs/blob/main/KempfDegenerationDegree/PROOF.md)

Ganesh, Koiran and Oliveira study error degree and degeneration order with a diagonal rank source. Here the source is the specified multiplication tensor $T_m^+$, so the relative-order result makes no claim about the smallest order using arbitrary border rank decompositions of $T_m^-$. [Ganesh–Koiran–Oliveira, definitions and bounds](https://arxiv.org/html/2608.10179v1)

These results are written proofs. An exact check of the integer simplicial boundary sums on seven successive blocks verified the doubling identities, the punctured cap relation, the subdivision counts, and retention of the degree-two corner at the deleted face. The lower bound concerns integer valuations of formal Laurent series with the displayed uniformizer. It applies over any coefficient field and continues to apply after extending that coefficient field.

## Determinant-one variant

Adjoin a new last vertex to the ordered graph and adjoin just one arrow from the former last vertex to it. Give this arrow zero products with all edges. The two algebras gain two basis vectors and still have the same intrinsic graded supports. Reachability is still a total order, and the doubling cycles and their corners are unchanged, so the lower bound for arbitrary three-mode Laurent witnesses applies verbatim. Extend \(D(t)\) by the identity on the new vertex and by \(\det(D(t))^{-1}\) on the new arrow. No nonzero edge product involves the new arrow, and its unit actions are unchanged by diagonal scaling. The extended map therefore realizes precisely the same linear orbit arc on the enlarged tensors. Its determinant is one, so both inverse-transpose input maps and the output map have determinant one. The added Laurent entry has absolute exponent at most \(N_m\) times the previous maximum. Thus the relative exponential separation also holds for determinant-one degenerations.
