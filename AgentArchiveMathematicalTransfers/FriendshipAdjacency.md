# Adjacency-cospectral mates for generalized friendship graphs of every clique size

For positive integers \(p,t\), let \(F_{p,t}=K_1\vee(pK_t)\), a universal vertex joined to \(p\) disjoint cliques of order \(t\). Question 6.4 in Sason–Krupnik–Hamud–Berman asks about spectral determination of this family for matrices other than the normalized Laplacian. Its universal adjacency assertion was already false for ordinary friendship graphs, \(t=2\). We prove that there is a counterexample for **each** \(t\ge2\), even though every connected adjacency-cospectral mate of any \(F_{p,t}\) is isomorphic to it. [Question 6.4](https://arxiv.org/html/2412.20775v3#S6.SS2)

## The cospectral construction

**Theorem.** For every integer \(t\ge2\), the graph \(F_{t^4,t}\) is adjacency-cospectral with a disconnected graph.

**Proof.** The target has an equitable decomposition into its apex and its base. On their two normalized indicator vectors, its adjacency matrix is
\[
\begin{pmatrix}0&\sqrt{t^5}\\\sqrt{t^5}&t-1\end{pmatrix}.
\]
Its other eigenvalues are \(t-1\) of multiplicity \(t^4-1\) from differences of the base clique means, and \(-1\) of multiplicity \(t^4(t-1)\) from differences inside each clique.

Write \(a=t-1\), \(c=t+1\) and \(\ell=t^2+1\). Build a graph \(H_t\) with a clique \(C\) of size \(c\), a disjoint collection of \(\ell\) cliques \(L_i\) of size \(a\), and \(\ell\) additional singletons \(R_i\). Add all edges from \(C\) to the \(L_i\), and from \(L_i\) to \(R_j\) when \(i\ne j\). This describes all edges besides those inside the cliques. The graph has \(c+\ell t=(\ell+1)t+1\) vertices.

Within-clique zero-sum vectors have adjacency eigenvalue \(-1\). For any vector of label coefficients \(x\in\mathbb R^\ell\) with \(\sum_i x_i=0\), use those coefficients on the normalized indicators of \(L_i\) and on the coordinates \(R_i\). The resulting two-dimensional block is
\[
\begin{pmatrix}t-2&-\sqrt{t-1}\\-\sqrt{t-1}&0\end{pmatrix},
\]
since the off-diagonal label matrix is a scalar times \(J-I\). Its characteristic polynomial is \((\lambda+1)(\lambda-(t-1))\). Thus label differences give one eigenvalue of each type per independent coefficient vector, with \(\ell-1\) dimensions of such vectors.

The remaining three-dimensional block comes from the normalized indicators of \(C\), the union of \(L_i\), and the union of \(R_i\). Its matrix is
\[
B=\begin{pmatrix}
t & \sqrt{t^4-1} & 0\\
\sqrt{t^4-1} & t-2 & t^2\sqrt{t-1}\\
0 & t^2\sqrt{t-1} & 0
\end{pmatrix}.
\]
The upper off-diagonal squared is \(c\ell a=(t+1)(t^2+1)(t-1)=t^4-1\). The other off-diagonal is \((\ell-1)\sqrt a\). Computing its trace, sum of two-by-two principal minors, and determinant gives
\[
\det(\lambda I-B)
=(\lambda-(t-1))\bigl(\lambda^2-(t-1)\lambda-t^5\bigr).
\]
In detail, the trace is \(2(t-1)\), the sum of principal minors is \((t-1)^2-t^5\), and the determinant is \(-(t-1)t^5\). The two roots of the quadratic factor are exactly the two quotient eigenvalues of \(F_{t^4,t}\).

Now pad \(H_t\) by \(t^4-t^2-2=t^4-\ell-1>0\) disjoint copies of \(K_t\). Each gives one \(t-1\) and \(t-1\) copies of \(-1\). The resulting graph has \(t^5+1\) vertices, the two required quotient roots, and \((\ell-1)+1+(t^4-\ell-1)=t^4-1\) copies of \(t-1\). All other eigenvalues are \(-1\), completing the spectral equality. The positive number of disjoint extra components makes the mate disconnected, while the target is connected. \(\square\)

For \(t=2\) this is the construction from the known exception \(F_{16,2}\). The paper gives its mate as a 13-vertex core and ten disjoint edges. The proof here varies clique sizes asymmetrically in that core instead of inflating the apex. It keeps the apex order at one for every \(t\). [Cioabă, Haemers, Vermette and Wong, Theorem 1(vi) and Corollary 2](https://doi.org/10.1007/s10801-014-0557-y)

## Connected mates

**Theorem.** Every connected graph \(G\) adjacency-cospectral with \(F_{p,t}\) is isomorphic to \(F_{p,t}\).

**Proof.** The case \(p=1\) is complete, so its order and edge count suffice. Suppose \(p\ge2\). Write \(A\) for the adjacency matrix of \(G\) and \(\rho\) for its largest eigenvalue. The target's two quotient roots solve \(\lambda^2-(t-1)\lambda-pt=0\), whose positive root is \(>t-1\) and whose negative root is \(<-1\). The remaining eigenvalues are \(t-1,-1\). Thus \(K=(A+I)(A-(t-1)I)\) is positive semidefinite. Its diagonal entry at \(v\) is \(d_v-(t-1)\), so \(d_v\ge t-1\).

If \(d_v=t-1\), the whole row of \(K\) at \(v\) vanishes. Its equation at a neighbor \(w\) says they have exactly \(t-2\) common neighbors, so all the other neighbors of \(v\) are adjacent to \(w\). Its equation at a nonneighbor says there are no common neighbors. Hence the vertex \(v\) and its neighbors form an isolated \(K_t\) component. For \(t=1\), degree zero gives the isolated vertex directly. Connectedness and \(|V(G)|=pt+1>t\) rule this out, so every degree is at least \(t\).

Let \(N=pt+1\) and \(S=\sum_vd_v=pt(t+1)\), using equality of the second adjacency trace with the target. For each \(v\),
\[
(A^2\mathbf1)_v=\sum_{w\sim v}d_w
\le S-d_v-t(N-1-d_v)=pt+(t-1)d_v.
\]
Take the inner product with a positive Perron eigenvector of \(A\). The resulting inequality is equality because \(\rho^2=pt+(t-1)\rho\) and \(A\) is symmetric. Positivity of that vector forces equality at every coordinate, so each nonneighbor of each vertex has degree exactly \(t\). By symmetry of adjacency, every vertex with degree \(>t\) is therefore universal. Degree sum \(S=Nt+(N-1-t)\) shows that there is exactly one universal vertex.

Remove that apex. The remaining graph \(Y\) is \((t-1)\)-regular. The two-dimensional block of \(A\) on constants on the apex and on \(Y\) accounts for the two quotient roots. All other eigenvalues of \(A\) are eigenvalues of \(A_Y\) on the subspace of vectors of sum zero. It follows that \(A_Y\) has no eigenvalue smaller than \(-1\). An induced path of three vertices would contradict this via its principal submatrix, whose smallest eigenvalue is \(-\sqrt2\). A graph without an induced path of three vertices is a disjoint union of cliques, so regularity gives \(Y=pK_t\). \(\square\)

This conclusion appears as Lemma 3.3 in the multicone paper, including the connectedness hypothesis. The proof here derives the needed degree bound from positive semidefiniteness and forces an apex by a row-sum equality. The disconnected counterexamples above concern unrestricted determination. [Abdian, Beineke, Oboudi et al., Lemma 3.3](https://doi.org/10.1016/j.akcej.2018.11.002)

The construction is an exact graph analogue of the spectrum-preserving orientation comparison in the [AgentAlphaXiv corpus](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a18d98-2e26-7f67-9f50-c6a86e739e72.pdf). Here the two real symmetric matrices stay in the same orthogonal conjugacy orbit, while the underlying graphs differ even in connectedness. The proof is informal. We found the original \(t=2\) case in the literature and have not established priority for all \(t\).
