# Arbitrarily many real-cospectral matching minimizers distinguished in characteristic two

For every integer \(q\ge1\), there are \(q+1\) connected bipartite graphs of order \(282q+3\), matching number \(12q\) and cycle rank \(10q\), each minimizing adjacency spectral radius in that prescribed bipartite class. Their common spectral radius is \(\sqrt{28}\) for all \(q\). The graphs have identical full adjacency characteristic polynomials over \(\mathbb Z\), while the ranks of the cubes of their adjacency matrices over \(\mathbb F_2\) are pairwise distinct. In particular the adjacency matrices are pairwise nonsimilar over \(\mathbb F_2\).

The adjacency matrices are all similar over \(\mathbb Q\), since they are rational matrices diagonalizable over \(\mathbb R\) and share a characteristic polynomial. For such a semisimple rational operator that polynomial determines its elementary divisors. Yet their integral similarity classes and their similarity classes over \(\mathbb Z/2^a\mathbb Z\) for every \(a\ge1\) are pairwise distinct, since similarity would pass to \(\mathbb F_2\). The construction combines the matching-minimal subdivision method with the exact modular similarity transfer in [the transporter theorem](SpectralTransporterSchemes.md).

## The finite witness

Let \(A,B\) be trees on \(1,\ldots,11\), with respective edge lists

\[
\begin{aligned}
A:&\ 12,23,34,45,56,67,78,69,9\mathord{-}10,9\mathord{-}11,\\
B:&\ 12,23,34,45,56,57,78,79,9\mathord{-}10,10\mathord{-}11.
\end{aligned}
\]

An adjacent pair of one-digit labels stands for the corresponding edge. Their shared monic Laplacian characteristic polynomial has the following coefficients in decreasing powers:

\[
(1,-20,169,-788,2222,-3908,4271,-2804,1028,-182,11,0).
\]

Here is a direct recurrence verifying the integer calculation. Root each tree at vertex one. For a vertex \(v\) let \(D_v(t)\) be the determinant of the principal subtree block of \(tI-L\), with its original full-tree diagonal entries, and let \(E_v(t)\) be that block determinant with \(v\) removed. At a leaf \(E_v=1\), \(D_v=t-d(v)\). With child set \(C_v\) the complete computation is

\[
E_v=\prod_{u\in C_v}D_u,\qquad
D_v=(t-d(v))E_v-\sum_{u\in C_v}E_u\prod_{w\in C_v\setminus\{u\}}D_w.
\]

In the determinant expansion, a permutation involving a nontrivial cycle must use a transposition along one tree edge. For the root, either it is fixed and gives the first term, or it transposes with one child and gives the corresponding negative term. This proves the recurrence, whose value at the root is the polynomial displayed above.

The ranks of \(L_A-I\) and \(L_B-I\) over \(\mathbb F_2\) are respectively nine and ten. For a reproducible certificate, list each nonzero row of reduced row-echelon form by its set of occupied columns:

\[
\begin{aligned}
A:&\ (1,10,11),(2),(3,10,11),(4,10,11),(5),(6,10,11),(7),(8,10,11),(9),\\
B:&\ (1,6),(2),(3,6),(4,6),(5),(7),(8),(9),(10),(11).
\end{aligned}
\]

These lists result from the two stated graphs by making each row the neighbor incidence row, toggling its diagonal when the degree is even, and clearing columns from left to right using the first available pivot row. The number of nonzero rows certifies each rank.

## Repeating the witness along a path

For \(0\le r\le q\), take \(q-r\) disjoint copies of \(A\) and \(r\) copies of \(B\). Add one vertex to each copy and join it to every vertex of that copy. Join these new vertices along a path, and call the resulting core \(H_r\). Every core has \(k=12q\) vertices, \(m=22q-1\) edges and maximum degree at most thirteen. Work first over \(\mathbb R\) and then over \(\mathbb F_2\). In either field 11 is invertible. The coordinate space of each copy is the direct sum of its constant line and its ten-dimensional sum-zero subspace. Taking all copies and the new path vertices yields a direct-sum decomposition for the Laplacian of \(H_r\). On the sum-zero subspace for one copy the Laplacian is \(L_A+I\) or \(L_B+I\). The complement of copy constants and path coordinates is invariant, and its matrix depends only on \(q\). On the \(i\)-th copy a constant \(a_i\) maps to \(a_i-b_i\), while on the path the vectors \(a,b\) give \(L(P_q)b+11(b-a)\).

The real characteristic polynomials of all \(H_r\) Laplacians are therefore equal, by the identical polynomials of \(L_A,L_B\) and the same shifts and complements. Over \(\mathbb F_2\) the added identity is also the subtracted identity. The ranks on a sum-zero copy are eight and nine respectively, since the full-copy ranks are nine and ten and each constant line contributes one. The rank of the whole Laplacian is thus \(8q+r\) plus the same complementary rank for every \(r\). These ranks are distinct.

## Turning the cores into extremizers

Choose \(c=28\). Subdivide each edge of \(H_r\) and attach \(c-2d_{H_r}(v)\) leaves at each original vertex. All leaf counts are at least two, so the exact similarity transfer applies. All resulting graphs have the same order \(n=(c+1)k-3m=282q+3\), matching number \(k\), and adjacency spectral radius \(\sqrt{28}\). They attain the minimum among connected graphs of matching number \(k\), order \(n\), prescribed cycle rank \(m-k+1=10q\), and minimum vertex cover size \(k\), by the sharp [cycle-rank theorem](MatchingCycleRankExtrema.md). They therefore attain the same minimum in the subclass of connected bipartite graphs. The characteristic polynomial of the adjacency matrix is

\[
t^{n-2k}\det\bigl(t^2I_k-(cI_k-L(H_r))\bigr),
\]

by the bipartite block multiplication or the Schur determinant identity. It is independent of \(r\). The simultaneous normal form in the exact transporter theorem writes the adjacency action as \(T_K(x,y,z,w)=(y,Kx,x,0)\) with \(K=cI-L(H_r)\). Then \(T_K^3(x,y,z,w)=(Ky,K^2x,Kx,0)\), an image of dimension \(2\operatorname{rank}(K)\). Since \(c\) is even, \(K=L(H_r)\) over \(\mathbb F_2\), so these cube ranks differ in steps of two. This also proves pairwise nonsimilarity directly.

The extremality statement uses the displayed cycle rank and cover hypotheses. [Hou and Tan's matching-minimal construction](https://arxiv.org/html/2607.11061v2) · [MathProofs arithmetic tensor comparison](https://github.com/Dugongue/MathProofs/blob/main/OrdinaryTensorTransferFallout/Arithmetic.md)
