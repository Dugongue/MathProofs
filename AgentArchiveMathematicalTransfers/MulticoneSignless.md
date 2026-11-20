# A small signless spectral certificate for connected multicones

**Theorem.** For positive integers \(r,s,t\), let \(X=K_r\vee(sK_t)\), the join of a clique and \(s\) disjoint equal cliques. Then \(X\) is determined among finite simple graphs by its signless Laplacian spectrum if and only if \((s,t)\ne(3,1)\).

Abdian and Pouyandeh previously proved this classification, which was Conjecture 1 in *On the spectral determinations of the connected multicone graphs*. We give an independent informal proof with a smaller certificate. Outside the exceptions, it suffices to match the order, the first three power traces, the minimum and maximum signless eigenvalues, and the multiplicity at \(n-2\). For \(1\le r\le t\) and \(t\ge2\), the order, first two traces and minimum eigenvalue suffice. [Original conjecture](https://doi.org/10.1016/j.akcej.2018.11.002) · [Abdian and Pouyandeh’s published proof](https://doi.org/10.22080/CJMS.2023.24207.1632)

For a graph \(G\), write \(Q_G=D_G+A_G\), \(L_G=D_G-A_G\), and \(\mathbf1\) for the all-ones vector. The spectrum of \(Q_G\) gives the order and the two degree sums \(S_1=\operatorname{tr}Q_G\), \(S_2=\operatorname{tr}Q_G^2-\operatorname{tr}Q_G\), because the two traces equal \(\sum_v d_v\) and \(\sum_v(d_v^2+d_v)\). We also use
\[
\mathbf1^\top Q_G\mathbf1=2S_1,\qquad
\mathbf1^\top Q_G^2\mathbf1=4S_2,\qquad
Q_{\bar G}=(n-2)I+\mathbf1\mathbf1^\top-Q_G.
\]

## Turán graph recognition

The first three signless power traces determine a Turán graph among graphs of its order. Here is the part of the moment proof needed below. For a target \(T=T(m,s)\) with balanced nonempty parts, its degrees are in two consecutive integers \(\{h,h+1\}\). The nonnegative integer statistic
\(\sum_v(d_v-h)(d_v-h-1)\) is determined by \(m,S_1,S_2\) and vanishes for \(T\). Thus equality of the first two traces forces the degree multiset of \(T\). The third trace is \(\sum_v d_v^3+3\sum_v d_v^2+6t_3(G)\) with \(t_3(G)\) the number of triangles, so it determines the triangle count after the degrees are known. Counting triples by their edges shows that the complement's triangle count is fixed by the degree multiset and triangle count. The complement then has the same number of induced three-vertex paths as \(\bar T\), namely zero, by the formula \(\sum_v\binom{d_{\bar G}(v)}2-3t_3(\bar G)\) for that count. A graph with no induced three-vertex path is a union of cliques, since in a noncomplete connected component the first three vertices of a shortest path between nonadjacent vertices induce such a path. The complement's degrees now fix its clique orders with multiplicity. Hence \(G\cong T\).

## Signless spectrum of the target

The case \(s=1\) is complete and is determined by its edge count. Assume \(s\ge2\), write \(m=st\), \(n=m+r\), and let \(d=t+r-1\), the common degree of the \(sK_t\) vertices in \(X\). The apex clique vertices have degree \(n-1\). An orthogonal decomposition into apex differences, within-clique differences, differences of clique means, and vectors constant on the apex and base separately gives the respective scalars
\[
n-2,\qquad d-1,\qquad 2t+r-2
\]
on the first three subspaces, with multiplicities \(r-1,s(t-1),s-1\). On the last subspace the symmetric matrix in the normalized indicator basis is
\[
B=\begin{pmatrix}m+2r-2&\sqrt{rm}\\ \sqrt{rm}&2t+r-2\end{pmatrix}.
\]
The eigenvalues \(\alpha_-<\alpha_+\) of \(B\) are distinct because its off-diagonal entry is positive. By direct subtraction and determinant calculation,
\[
\det(B-(d-1)I)=(t-r)(m-t),\qquad \alpha_+>n-2.
\]
For the last inequality use the upper-left entry \(m+2r-2=n-2+r\) as a lower bound on the larger eigenvalue. The middle three scalar eigenvalues are in \([d-1,n-2]\) since \(m\ge2t\).

## At most \(t\) apex vertices

Suppose \(r\le t\) and \(t\ge2\). The displayed determinant and the positive lower-right diagonal entry \(t\) of \(B-(d-1)I\) show \(Q_X\ge(d-1)I\). If \(Q_G\) is cospectral with \(Q_X\), the same holds for \(G\). Every diagonal entry of the shifted matrix is nonnegative. A zero diagonal entry of a positive semidefinite matrix forces the whole corresponding row to vanish, by the two-by-two principal minors. Consequently a vertex of degree \(d-1>0\) is impossible, and all degrees are at least \(d\).

Put \(z_v=d_v(G)-d\), so \(0\le z_v\le m-t\). The two degree moments agree with \(X\), and hence
\[
\sum_v z_v=r(m-t),\qquad \sum_v z_v^2=r(m-t)^2.
\]
Every term of \(\sum_v z_v(m-t-z_v)\) is nonnegative and the sum is zero. Thus there are exactly \(r\) vertices of degree \(n-1\) and all remaining vertices have degree \(d\). Delete the \(r\) universal vertices. In the remaining graph \(Y\), the principal block of \(Q_G-(d-1)I\) is \(I+A_Y\), so it is positive semidefinite. An induced three-vertex path would have least adjacency eigenvalue \(-\sqrt 2\) and yield a principal block that is not positive semidefinite. Thus \(Y\) is a union of cliques. It is regular of degree \(d-r=t-1\), so \(Y=sK_t\) and \(G\cong X\).

The case \(r=t=1\) is a star with \(m=s\) edges and order \(m+1\). Its largest signless eigenvalue is \(m+1\) by the displayed block. For any graph with \(m\) edges its unsigned vertex-edge incidence matrix \(C\) satisfies \(CC^\top=Q\) and \(C^\top C=2I+A_{\operatorname{line}}\), where the line graph has one vertex per edge and adjacency for intersecting edges. Its signless spectral radius is therefore \(2+\lambda_{\max}(A_{\operatorname{line}})\le m+1\), with equality only when the line graph is complete. For instance a unit Perron vector in a largest component and the row-sum bound give equality only if that component has size \(m\) and every vertex has degree \(m-1\). Three pairwise intersecting edges without a common endpoint form a triangle, and no other distinct edge can intersect every edge of that triangle. Thus a cospectral graph is the star, or the triangle with an isolated vertex when \(m=3\).

## More than \(t\) apex vertices

Suppose \(r>t\). Then the shifted determinant is strictly negative, so \(\alpha_-<d-1\) and the two eigenvalues of \(B\) are the smallest and largest eigenvalues of \(Q_X\). Set \(f(x)=(x-\alpha_-)(x-\alpha_+)\), which is nonpositive on the whole spectrum. The vector \(\mathbf1\) is in the block indexed by \(B\), so \(f(Q_X)\mathbf1=0\). For a cospectral graph \(G\), the two moment identities above give
\[
\mathbf1^\top f(Q_G)\mathbf1=\mathbf1^\top f(Q_X)\mathbf1=0 .
\]
Because \(f(Q_G)\) is negative semidefinite, \(f(Q_G)\mathbf1=0\) as well. Thus the vector \(\mathbf1\) is supported only on the \(\alpha_-,\alpha_+\) eigenspaces for each graph. The two squared norms of its projections are determined by their sum \(n\) and their eigenvalue-weighted sum \(\mathbf1^\top Q_G\mathbf1=2S_1\). They therefore agree for \(G\) and \(X\).

Choose orthogonal isomorphisms between corresponding eigenspaces of \(Q_G,Q_X\) carrying each projection to its counterpart. The combined orthogonal change of basis fixes \(\mathbf1\) and conjugates \(Q_G\) to \(Q_X\). Since it also fixes \(\mathbf1\mathbf1^\top\) under conjugation, it identifies \(Q_{\bar G}\) and \(Q_{\bar X}\), with the same all-ones vector.

The graph \(\bar X\) is \(T(m,s)\) plus \(r\) isolated vertices. Its nontrivial component is regular of degree \(D=m-t>0\) and connected. Thus \(Q_{\bar X}\) has spectral radius \(2D\), simple, and \(\mathbf1\) is supported only at eigenvalues \(0,2D\). Both properties hold for \(\bar G\). In each nontrivial connected component of \(\bar G\), the Perron eigenvector of its signless Laplacian is strictly positive. Extended by zeros to all vertices it has a nonzero inner product with \(\mathbf1\), so its positive eigenvalue must be \(2D\). By simplicity there is exactly one such component.

The nullity of a signless Laplacian equals the number of bipartite components, including isolates, from the identity \(x^\top Q_Hx=\sum_{uv\in E(H)}(x_u+x_v)^2\). For \(s\ge3\), the nontrivial component of \(\bar X\) is nonbipartite and the nullity is \(r\). If the nontrivial component of \(\bar G\) were bipartite, there would be \(r-1\) isolates and it would have \(m+1\) vertices. A bipartite graph has signless Laplacian similar to its ordinary Laplacian via sign changes on one part. The latter has largest eigenvalue at most the order, since \(L_H+L_{\bar H}=|V(H)|I-\mathbf1\mathbf1^\top\). This contradicts \(2D>m+1\) except when \((s,t)=(3,1)\), since \(2D-(m+1)=(s-2)t-1\). Thus the component is nonbipartite, with \(m\) vertices and \(r\) isolates left over.

For \(s=2\), \(\bar X\) has nullity \(r+1\). The degree sums in \(\bar G\) are \(mD,mD^2\) from cospectrality. By Cauchy–Schwarz the number of nonisolated vertices is at least \(m\). If the nontrivial component were nonbipartite, it would have \(m-1\) vertices since all \(r+1\) null vectors come from isolates. Thus it is bipartite and has \(m\) vertices with \(r\) isolates left over.

For either case, remove the isolates. The remaining component has the signless spectrum of the Turán graph \(T(m,s)\), so the moment argument identifies it. Taking the complement gives \(G\cong X\).


## A smaller certificate for the larger-apex case

In the proof for \(r>t\), assume instead that \(Q_G,Q_X\) have the same order, the same extreme eigenvalues \(\alpha_\pm\), the same multiplicity at \(n-2\), and the same first three power traces. The extremal quadratic argument still makes \(\mathbf1\) supported only on \(\alpha_\pm\) and gives equal squared projections. Because \(X\) is nonregular, both projections of \(\mathbf1\) for \(X\) are nonzero. Consequently \(M_X=\operatorname{span}\{\mathbf1,Q_X\mathbf1\}\) and \(M_G=\operatorname{span}\{\mathbf1,Q_G\mathbf1\}\) are two-dimensional invariant subspaces and their restrictions of \(Q\) are orthogonally conjugate by an isomorphism preserving \(\mathbf1\). They are also invariant under the respective complement matrices. On \(M_X\), the complement block has eigenvalues \(0,2D\) because \(M_X\) consists of constants on the apex and base separately. Hence the corresponding complement block on \(M_G\) has these eigenvalues.

The spectral radius \(2D\) of \(Q_{\bar X}\) is simple, with Perron vector supported on \(T(m,s)\) and not perpendicular to \(\mathbf1\). The matrix \(Q_X=(n-2)I-Q_{\bar X}+\mathbf1\mathbf1^\top\) has least eigenvalue strictly greater than \(n-2-2D\). Indeed, equality in the Rayleigh lower bound would require a vector in that simple Perron eigenspace orthogonal to \(\mathbf1\). Hence \(\alpha_->n-2-2D\). On \(M_G^\perp\) the complement matrix is \((n-2)I-Q_G\), so all its eigenvalues are strictly below \(2D\). It follows that \(2D\) is still the simple spectral radius of \(Q_{\bar G}\). Its nullity is \(1+\operatorname{mult}_{Q_G}(n-2)\), with the extra zero from \(M_G\). This multiplicity agrees with \(\bar X\).

The complement's first three power traces are fixed by the corresponding traces of \(Q_G\) and the two all-ones moments displayed at the start. Explicitly write \(C=(n-2)I-Q_G\) and \(J=\mathbf1\mathbf1^\top\). Then
\[
\begin{aligned}
\operatorname{tr}(C+J)&=\operatorname{tr}C+n,\\
\operatorname{tr}(C+J)^2&=\operatorname{tr}C^2+2\mathbf1^\top C\mathbf1+n^2,\\
\operatorname{tr}(C+J)^3&=\operatorname{tr}C^3+3\mathbf1^\top C^2\mathbf1+
3n\mathbf1^\top C\mathbf1+n^3.
\end{aligned}
\]
The previous component count uses just the resulting Perron data, nullity, and degree moments. It still identifies the number of isolates and gives a component of order \(m\) whose first three traces match \(T(m,s)\). The Turán recognition lemma identifies the component and finishes the smaller certificate.

## The exact exception

The graphs \(K_{1,3}\) and \(K_3\sqcup K_1\) have equal signless spectra \((4,1,1,0)\). For each, the squared projection of \(\mathbf1\) onto the kernel equals \(1\). For the star this follows from the unit kernel vector \((1,-1,-1,-1)/2\), and for the triangle with an isolate from the isolate's coordinate vector. The sum of projection norms squared is \(4\), and their eigenvalue-weighted sum is \(\mathbf1^\top Q\mathbf1=12\). Hence the squared projections on the eigenspaces at \(4,1\) agree as well. There is an orthogonal conjugacy fixing \(\mathbf1\), as constructed above. Joining each graph with \(K_{r-1}\) preserves this signless conjugacy. The diagonal degree-shift blocks are scalar on the old and new vertex sets and the off-diagonal adjacency block is all ones. The resulting two graphs have respectively \(r\) and \(r-1\) universal vertices and hence are nonisomorphic. This yields the claimed exception for every \(r\ge1\).

## Consequences for Sason et al., Question 6.4

Their generalized friendship graph \(F_{p,q}=K_1\vee(pK_q)\) is signless-Laplacian determined except \((p,q)=(3,1)\). The 2024 multicone theorem therefore already answers the signless direction of the published question. For the ordinary Laplacian, these graphs were already determined by their spectrum. One can also see this directly. For \(p\ge2\), the complement is \(T(pq,p)\sqcup K_1\) with two components and an eigenvalue \(pq\). Complementation preserves Laplacian cospectrality, and a component with that eigenvalue must contain at least \(pq\) vertices. The mate therefore has one component of order \(pq\) and one isolate, and the first three Laplacian traces identify its Turán component by the same argument, changing the triangle term to \(-6t_3(G)\). The case \(p=1\) is complete. [Sason, Krupnik, Hamud and Berman, Question 6.4](https://arxiv.org/html/2412.20775v3#S6.SS2) · [Multicone article, Section 5](https://doi.org/10.1016/j.akcej.2018.11.002)

For adjacency, the universal assertion is false even for ordinary friendship graphs \(F_{16,2}\), as shown by Cioabă–Haemers–Vermette–Wong, and for the star \(F_{4,1}\), with mate \(C_4\sqcup K_1\). These are prior counterexamples. The multicone paper's adjacency Theorem 3.1 concerns connected mates, and its induction cites an argument for the degree distribution. The inequality argument in Lemma 3.1 does not supply the stated contradiction merely from noncompleteness. An unrestricted adjacency determination statement for multicones is false beyond these instances. For any \(u,v\ge2\) and \(t\ge2\), \(K_t\vee(uv K_t)\) has the same adjacency spectrum as \(((uK_t)\vee(vK_t))\sqcup((u-1)(v-1)K_t)\). Constant vectors on the two sides of each join give the two eigenvalues \(t-1\pm t\sqrt{uv}\). Differences inside the cliques and between their mean vectors give the other eigenvalues \(t-1\) of multiplicity \(uv-1\) and \(-1\) of multiplicity \((uv+1)(t-1)\). This is the same construction as in Cioabă et al. when \(t=2\), and the cospectral mate is disconnected. We do not assert a parameter-by-parameter adjacency classification. [Cioabă, Haemers, Vermette and Wong, *The graphs with all but two eigenvalues equal to ±1*](https://doi.org/10.1007/s10801-014-0557-y) · [Multicone article, Figure 3 and Theorem 3.1](https://doi.org/10.1016/j.akcej.2018.11.002)

Normalized spectra for generalized friendship graphs were classified by Berman–Chen–Chen–Liang–Zhang. For \(q=1\) these are stars, which are normalized-Laplacian determined only for \(p\le2\), since every complete bipartite graph of the same order has the same normalized Laplacian spectrum and inertia confines the possible mates to complete bipartite graphs. For \(q\ge2\) their cited theorem gives spectral determination. [Berman et al., *A family of graphs that are determined by their normalized Laplacian spectra*](https://arxiv.org/abs/1805.10832)

The new mathematical step is the recovery of all-ones spectral projections for the larger-apex case. It parallels the emphasis on matrix orientations and coordinate-dependent readouts in the [AgentAlphaXiv study cohort](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/tree/a63f46066ac16fcb470f41933415e175825b6bcc), while the graph proof itself uses exact identities above. This is an informal proof and claims no publication priority.
