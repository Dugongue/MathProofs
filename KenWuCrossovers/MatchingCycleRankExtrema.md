# Sharp cyclomatic spectral bounds with a prescribed matching and minimum cover

Let \(G\) be a connected simple graph on \(n\) vertices with matching number \(k\ge2\), minimum vertex cover size \(k\), and cycle rank \(g=|E(G)|-n+1\). In particular the hypotheses apply to every connected bipartite graph with matching number \(k\). Set \(m=k-1+g\). Then

\[
\rho(G)^2\ge c:=\frac{n+2k-3+3g}{k}.
\tag{1}
\]

There is equality exactly for the following graphs. The number \(c\) must be an integer. Take a connected loopless multigraph \(H\) of order \(k\) with exactly \(m\) edges and maximum degree at most \(D=\lfloor c/2\rfloor\). Subdivide each of its edges once and attach \(c-2d_H(v)\) leaves at each original vertex \(v\). Parallel edges in \(H\) have distinct subdividers, so the resulting graph is simple.

The equality families are nonempty precisely when \(c\) is integral and the following conditions hold. For \(k=2\), the condition is \(m\le D\). For \(k\ge3\), the conditions are \(D\ge2\) and \(2m\le kD\). Thus these conditions give the exact spectral minimum and all minimizers in every stated attainable cycle-rank slice. When they fail, the lower bound is strict in that slice.

For an equality graph built from \(H\), its entire nonzero adjacency spectrum is the pair of signs of the square roots of the positive eigenvalues of \(cI-L(H)\), including multiplicity. The zero multiplicity is the graph order minus twice the number of these positive eigenvalues. This identifies spectral ties in all the attained slices with Laplacian cospectrality of their multigraph cores. Here and below the parameters \(n,k,g\) are fixed when comparing equality graphs.

## Bound and equality

Choose a minimum vertex cover \(X\) of size \(k\). The adjacency matrix relative to \(X\) and its independent complement \(Y\) is \(\begin{pmatrix}A&B\\B^T&0\end{pmatrix}\). At \(\rho=\rho(G)\), the Schur complement of \(\rho I-A(G)\) is positive semidefinite. As in [the matching-residue theorem](MatchingResidueTwo.md), evaluating it at the all-ones vector gives the explicit refinement

\[
k\rho^2\ge n+2k-3+3g+(2\rho-3)e(G[X])
 +\sum_{y\in Y}(d_G(y)-1)(d_G(y)-2).
\tag{2}
\]

Connectivity and \(k\ge2\) imply \(\rho\ge\rho(P_4)>3/2\). Thus (2) proves (1). Equality in (1) forces \(e(G[X])=0\) and \(d_G(y)\in\{1,2\}\) for all \(y\in Y\). Suppressing the vertices of degree two in \(Y\) and removing its vertices of degree one gives a connected loopless multigraph on \(X\). The original graph is simple, so the two neighbors of each suppressed vertex are distinct. By connectivity of \(G\), this multigraph is connected. Each subdivider contributes two edges and one vertex, and each leaf contributes one edge and one vertex. Therefore the multigraph has \(k-1+g=m\) edges. Write \(f_v\) for the number of leaves at \(v\). In those coordinates,

\[
BB^T=\operatorname{diag}(2d_H+f)-L(H).
\tag{3}
\]

Equality also forces the all-ones vector into the kernel of the positive semidefinite matrix \(\rho^2I-BB^T\): a zero Rayleigh value for a positive semidefinite form makes the vector a null vector. Thus (3) gives the constant row sum \(2d_H(v)+f_v=\rho^2=c\) for every \(v\). This proves the required integrality and the form and degree bound of the multigraph.

In the other direction, every indicated multigraph yields exactly \(k+m+ck-4m=n\) vertices and cycle rank \(g\). It has a matching of size \(k\). If \(g>0\), choose a spanning unicyclic subgraph of \(H\) and orient the cycle consistently and its branches outwards. This also works for a two-edge parallel cycle. Each core vertex is then assigned its unique incoming edge, and it is matched to that edge's subdivider. If \(g=0\), the number of leaves is \(n-2k+1\ge1\), since the hypotheses include \(n\ge2k\). Root the underlying tree at a vertex with a leaf and match it to that leaf. Match every other vertex to the subdivider on its parent edge. In either case the cover \(X\) certifies maximum matching number \(k\) and minimum cover size \(k\). Finally (3) has row sum \(c\) and is entrywise nonnegative, so its largest eigenvalue is \(c\). This proves equality. The spectral assertion follows from the singular-value decomposition of the rectangular matrix \(B\), since its squared singular values, including zeros on the smaller side, are the eigenvalues of \(BB^T=cI-L(H)\).

## When the multigraph exists

For \(k=2\), take \(m\) parallel edges. The degree bound is exactly \(m\le D\). For \(k\ge3\), a connected graph on \(k\) vertices needs maximum degree at least two, and summing the degrees gives \(2m\le kD\). These conditions suffice. If \(m=k-1\), take the path. If \(m\ge k\), start with the simple cycle through all \(k\) vertices. Each vertex then has residual capacity \(D-2\). Drop one unit of capacity at one vertex if the total is odd. The residual degree sequence with even sum is realized by a loopless multigraph. Indeed, any nonnegative integer sequence of total \(2s\) and largest entry at most \(s\) is realized as follows. Repeatedly join two distinct entries of greatest positive size, decrementing both. The largest new entry is at most \(s-1\) because any entry previously equal to \(s\) is among the two chosen. This gives the construction by induction on \(s\). The residual sequence satisfies its bound since the capacities are equal before the possible drop of one unit and \(k\ge3\). Add any \(m-k\) of these extra edges to the starting cycle. The cycle remains spanning and the maximum degree is at most \(D\).

## Scope and sources

The tree case \(g=0\) at equality is Hou and Tan's sharp result, which was the setting of Wu's boundary observation. Das and Mondal characterize minimizers for several prescribed matching numbers at cycle rank one. Formula (2) keeps the cycle-rank and degree-defect terms for arbitrary rank and gives a sharp classification in the cover-equals-matching class on the stated parameter slices. The cover hypothesis is explicit throughout. [Hou and Tan](https://arxiv.org/html/2607.11061v2) · [Wu's matching-spectral note](https://kenwu-lab.wooqianghao.workers.dev/papers/matching-number-minimal-spectral/) · [Das and Mondal](https://arxiv.org/abs/2606.16369)
