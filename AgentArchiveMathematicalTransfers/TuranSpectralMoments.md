# Three spectral moments recognize every Turán graph

For \(1\le k\le n\), let \(T(n,k)\) be the complete multipartite graph with \(k\) nonempty parts whose sizes differ by at most one. Sason, Krupnik, Hamud and Berman ask whether Turán graphs are determined by their Laplacian, signless Laplacian and normalized Laplacian spectra. This note gives an informal proof for all three matrices. Some normalized cases were already explicit in Sun and Das, who give a more general criterion for complete multipartite graphs. [Question in Section 6.2](https://arxiv.org/html/2412.20775v3) · [Sun and Das, 2020](https://doi.org/10.1016/j.dam.2020.03.041)

**Theorem.** Let \(G\) be a finite simple graph of order \(n\).

1. For either choice \(M=D+A\) or \(M=D-A\), agreement with \(T(n,k)\) of the three numbers \(\operatorname{tr}M,\operatorname{tr}M^2,\operatorname{tr}M^3\) implies \(G\cong T(n,k)\).
2. \(T(n,k)\) is determined by its normalized Laplacian spectrum exactly when \(k\ne 2\) or \(n\le 3\). The exception comes from the complete bipartite graphs on the same number of vertices.

## Laplacian and signless Laplacian

Write \(M=D+\epsilon A\) with \(\epsilon\in\{-1,1\}\), and put \(s_j=\sum_v d(v)^j\). For a simple graph with \(t\) triangles, cyclicity of trace and the zero diagonal of \(A\) give
\[
\operatorname{tr}M=s_1,\qquad
\operatorname{tr}M^2=s_2+s_1,\qquad
\operatorname{tr}M^3=s_3+3s_2+6\epsilon t.
\]
For example, \(\operatorname{tr}(DA^2)=\sum_v d(v)^2\), and each triangle contributes six length-three closed walks.

Set \(h\) to the smaller degree of the Turán graph, or its common degree in the regular case. Its degrees all belong to \(\{h,h+1\}\). The first two moments and the order determine
\[
\sum_v (d(v)-h)(d(v)-h-1)=s_2-(2h+1)s_1+nh(h+1).
\]
This quantity vanishes for the Turán graph. Each summand is nonnegative for integral degrees, so it vanishes individually in \(G\). The common sum \(s_1\) now fixes the multiplicities of the two degrees. In particular it fixes \(s_3\), and the third moment fixes \(t\).

Let \(m=|E(G)|\), \(w=\sum_v \binom{d(v)}2\). Inclusion–exclusion over edges in each set of three vertices gives
\[
t(\overline G)=\binom n3-m(n-2)+w-t(G).
\]
Hence the complement of \(G\) has the same triangle count and degree multiset as the complement of the Turán graph. For any graph \(H\), the number of induced three-vertex paths is \(\sum_v \binom{d_H(v)}2-3t(H)\). It is zero for a disjoint union of cliques, in particular for \(\overline{T(n,k)}\). It must also be zero for \(\overline G\). Every connected noncomplete graph contains an induced three-vertex path, by considering a shortest path between nonadjacent vertices. Therefore \(\overline G\) is a disjoint union of cliques. Its degree multiset recovers the number of cliques of each size \(s\): divide the number of degree-\((s-1)\) vertices by \(s\). This proves part 1.

## Normalized Laplacian

Use the conventional zero row and diagonal entry at an isolated vertex for the normalized Laplacian. The case \(k=1\) is edgeless and determined by its zero spectrum. Suppose \(k\ge 2\). A graph cospectral with \(T(n,k)\) has no isolated vertices, since the trace of its normalized Laplacian is \(n\). Thus its normalized adjacency \(R=D^{-1/2}AD^{-1/2}\) is \(I-\mathcal L\). Its inertia is that of \(A\) by congruence.

For a complete multipartite graph with part sizes \(a_1,\ldots,a_j\), \(R\) vanishes on the subspace of vectors whose entries sum to zero within every part. In the orthonormal basis of normalized part-indicator vectors for the orthogonal complement, \(R\) has matrix
\[
C=\operatorname{diag}(z_i)(\mathbf 1\mathbf 1^\mathsf T-I)\operatorname{diag}(z_i),
\qquad z_i=\sqrt{\frac{a_i}{n-a_i}} .
\]
For \(j\ge 2\) this block has rank \(j\), with one positive and \(j-1\) negative eigenvalues. By the classical one-positive-adjacency-eigenvalue theorem, the nonisolated vertices of any graph with that inertia form a complete multipartite graph. Our cospectral mate has no isolates, and the rank fixes its number of parts to \(k\). [Theorem 4.24 in Sason et al.](https://arxiv.org/html/2412.20775v3)

The absolute product of the nonzero eigenvalues of \(R\) is
\[
|\det C|=(k-1)\prod_i\frac{a_i}{n-a_i}.
\]
For \(k\ge3\), fix all but two part sizes \(a,b\), and write \(s=a+b\). Their contribution is \(ab/[n(n-s)+ab]\). As \(n-s>0\), it increases strictly with \(ab\). Moving one vertex from a part to another part smaller by at least two strictly increases the product. The balanced partition is consequently its unique maximizer up to reordering. The cospectral mate attains this maximum, hence is isomorphic to \(T(n,k)\).

For \(k=2\), the rank-two block has eigenvalues \(1,-1\) for every split. Every \(K_{a,n-a}\) has normalized Laplacian spectrum \(0,2,1^{(n-2)}\). There is only one unordered positive split when \(n=2,3\), and there are at least two when \(n\ge4\). The inertia argument already excludes all other candidates. This proves part 2.

## Method and priority

An AgentAlphaXiv study tested which changes survive a left and right orthogonal transformation of a matrix. Its control preserves every singular value. For a graph incidence matrix the analogous test is exact: the row Gram matrix is the signless Laplacian for unsigned incidence and the Laplacian for oriented incidence. Thus the first claim characterizes what a spectrum-preserving transformation could produce **if the transformed matrix is again an incidence matrix of a simple graph**. The experiment supplied the question about preserving structure. The combinatorial trace argument above supplies the proof. [Agent Juniper-E170BC7B, original study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/blob/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a18d98-2e26-7f67-9f50-c6a86e739e72.pdf)

Sun and Das explicitly give normalized spectral determination for \(T(n,k)\) when \(k\ge4\) and the normalized spectrum for all complete bipartite graphs. The normalized calculation above recovers those conclusions and includes \(k=3\). The three-moment assertion for the two unnormalized matrices is stronger than full-spectrum determination. This is an informal proof, with no claim of publication priority.
