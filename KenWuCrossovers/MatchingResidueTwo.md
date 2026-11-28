# Spectrally minimal graphs when the order is two modulo the matching number

Let \(k\ge 2\) and \(c\ge 3\) be integers, and set \(n=(c-1)k+2\). Among connected simple graphs of order \(n\) and matching number \(k\), there is a unique adjacency-spectral-radius minimizer up to isomorphism. Here is its construction.

1. Build a rooted tree \(H\) on \(k\) vertices. At its root, split the other \(k-1\) vertices as equally as possible into \(\lfloor c/2\rfloor\) slots, ignoring empty slots. In every slot do the same recursively, with \(\lfloor(c+1)/2\rfloor-1\) slots for each nonroot vertex's children.
2. Subdivide every edge of \(H\) once. At each original vertex \(v\), attach \(w_v-2d_H(v)\) leaves, where the root has \(w_v=c\) and every other vertex has \(w_v=c+1\).

In particular this proves the Hou–Tan structural claim for all \(n>2k\) with \(n\equiv 2\pmod k\). For \(c\ge 2k-2\) the core is the star rooted at its center, and the minimum spectral radius has square

\[
c+1-\frac{k+1-\sqrt{(k+1)^2-4}}2.
\]

The proof also gives a rooted-tree extremum independent of matching theory. With an upper bound \(D\) on the number of children of the root and \(B\) on that of every other vertex, where \(D,B\ge1\), this recursive equal splitting is the unique order-\(k\) rooted tree maximizing \(\lambda_{\min}(L(H)+E_v)\). Here \(L\) is the tree Laplacian and \(E_v\) has a single one at the root's diagonal entry. The positive definite matrix \(L+E_v\) describes a unit grounding at that vertex.

The minimizing graph also has a uniform logspace constructor. Given \(n,k\) in binary under the congruence promise, it outputs a labeled adjacency list with \(O(\log n)\) working bits.

## A strengthened Schur bound

A connected graph contains a spanning tree through any prescribed matching, by extending that acyclic edge set. For a connected graph with cycles this spanning tree has strictly smaller adjacency spectral radius, by the positive Perron eigenvector of the tree and the Rayleigh quotient. Thus all minimizers are trees. By König's theorem, a tree with matching number \(k\) has a vertex cover \(X\) of size \(k\).

Here is a bound valid for any connected graph \(G\) with such a cover and matching number \(k\). Write \(Y=V(G)\setminus X\), \(u=e(G[X])\), \(g=|E(G)|-|V(G)|+1\), and \(\rho=\rho(G)\). The adjacency matrix is \(\begin{pmatrix}A&B\\B^T&0\end{pmatrix}\), since \(Y\) is independent. The matrix \(\rho I-A(G)\) is positive semidefinite. Its lower diagonal block \(\rho I_Y\) is positive definite, so its Schur complement yields \(\rho^2 I_X-\rho A-BB^T\succeq0\). Testing on the vector of all ones yields

\[
 k\rho^2\ge 2\rho u+\sum_{y\in Y}d_G(y)^2
 =n+2k-3+3g+(2\rho-3)u+\sum_{y\in Y}(d_G(y)-1)(d_G(y)-2).
\tag{1}
\]

The identity follows by summing \(d^2=1+3(d-1)+(d-1)(d-2)\) on \(Y\) and using \(\sum_{y\in Y}(d_G(y)-1)=k-1+g-u\). The last two terms are nonnegative. Connectivity gives \(d_G(y)\ge1\). The graph contains a four-vertex path, because the two edges of any size-two matching can be joined by a path of minimum length between their endpoint sets. The resulting simple path has at least three edges. So \(\rho\ge\rho(P_4)=(1+\sqrt5)/2>3/2\).

## Forcing the structure and the two weights

Given a tree \(H\) on \(k\) vertices and integers \(w_v\ge2d_H(v)\), perform the subdivision and leaf construction above. Its bipartite block at the original vertices satisfies

\[
BB^T=\operatorname{diag}(w)-L(H).
\tag{2}
\]

Indeed, the diagonal is \(d_H(v)+w_v-2d_H(v)\), and each core edge produces one common neighbor between its endpoints. The squared adjacency spectral radius of the constructed tree is the largest eigenvalue of (2). If there is at least one added leaf, match its original vertex to it, root \(H\) there, and match every other original vertex to the subdivider on its parent edge. This proves matching number \(k\), since the original vertices also form a cover.

Use a path core, take weight \(c\) at an endpoint and weight \(c+1\) everywhere else. The leaf counts are nonnegative since \(c\ge3\), and their sum is positive since the endpoints have degree one. The total order is \(k+(k-1)+\sum_v(w_v-2d_H(v))=(c-1)k+2\). By (2) its squared spectral radius is strictly less than \(c+1\), since \(L(H)+E_v\) is positive definite. A minimizer therefore satisfies \(k\rho^2<(c+1)k\). The base term of (1) for a tree is \(n+2k-3=(c+1)k-1\). When \(c\ge4\), this implies \(\rho\ge2\), so \(u\ge1\) would add at least one to (1). For \(c=3\), we know \(\rho<2\). If \(u\ge1\), then (1) gives \(k\rho^2\ge4k-4+2\rho\), since \(2\rho-3>0\). Rearranging gives \(k(2-\rho)(2+\rho)\le 2(2-\rho)\). This forces \(k(2+\rho)\le2\), which is impossible. Thus \(u=0\) for every \(c\ge3\). Every \(y\in Y\) has degree one or two, since any degree at least three would contribute at least two to (1). Suppress the degree-two vertices of \(Y\) and delete its leaves. This produces a tree \(H\) on \(X\) with the original graph precisely its subdivision and leaf construction. In particular (2) applies.

Set \(a_v=c+1-w_v\). Equation (2) gives \(L(H)+\operatorname{diag}(a)\succ0\), and the order identity gives \(\sum_v a_v=1\). We show that any integral tuple with these properties has one entry one and the rest zero. For a rooted branch \(S\) across a cut edge, write \(A_S=\sum_{v\in S}a_v\). Eliminate the descendants of the branch root by Schur complement. The resulting pivot at this root equals \(1+h_S\), where the one comes from the cut edge and

\[
h_S=a_v+\sum_{T\text{ child branch}}\frac{h_T}{1+h_T}.
\]

This follows by subtracting \(1/(1+h_T)\) from the parent pivot for the edge to each child. Positive definiteness makes every \(1+h_T\) and \(1+h_S\) positive. The inequality \(x/(1+x)\le x\) for \(x>-1\) now gives \(h_S\le A_S\) by induction. In particular the integer \(A_S\) is greater than \(-1\), so it is nonnegative. This applies to either orientation of every edge. Since the total is one, each such branch sum is zero or one.

If a vertex \(v\) had \(a_v<0\), root the whole tree there. The root pivot is \(a_v+\sum_T h_T/(1+h_T)\) over its branches. The map \(x/(1+x)\) increases on \((-1,\infty)\), so the pivot is at most

\[
a_v+\sum_T \frac{A_T}{1+A_T}=a_v+\frac{1-a_v}{2}\le0.
\]

This contradicts positive definiteness. The integrality and total sum prove the claim. Thus exactly one \(w_v\) equals \(c\), and each other weight equals \(c+1\). The inequality \(w_v\ge2d_H(v)\) gives exactly the root and nonroot bounds in the theorem.

## Optimal grounded tree

For a rooted tree \(H\), put \(C_H=(L(H)+E_v)^{-1}\). Its \((i,j)\)-entry is one plus the number of common edges in the paths from the root to vertices \(i,j\). To see this, pass from vertex values to their consecutive differences along edges, with the root value regarded as its difference from an adjoined vertex held at zero. The quadratic form of \(L+E_v\) is the sum of the squares of the differences. The inverse matrix for this change of coordinates records path membership, giving the formula. In particular, with child subtrees \(H_1,\ldots,H_d\) we have

\[
C_H=\mathbf1\mathbf1^T+\operatorname{diag}(0,C_{H_1},\ldots,C_{H_d}).
\tag{3}
\]

Fix \(\lambda>0\). Define the response of a nonempty tree to be \(R_H=\mathbf1^T(\lambda I-C_H)^{-1}\mathbf1\) when \(\lambda>\rho(C_H)\), and \(+\infty\) otherwise. Empty slots have response zero. From (3), putting \(g=1/\lambda+\sum_i R_{H_i}\), one has

\[
R_H=q(g),\qquad q(g)=\frac{g}{1-g}\text{ for }0\le g<1,\quad q(g)=+\infty\text{ for }g\ge1.
\tag{4}
\]

Indeed, when the child blocks are positive definite, the rank-one update is positive definite exactly when \(g<1\). Direct inversion in the all-ones direction gives (4). If any child response is infinite then the corresponding child block already prevents the full matrix from being positive definite.

For trees with at most \(B\) children per vertex, define the candidates \(f_m\) as the responses of the recursively evenly split trees of size \(m\), including \(f_0=0\). For \(m\ge1\), let \(m-1=Bq_m+r_m\) with \(0\le r_m<B\). The input of the function in (4) is

\[
g_m=\lambda^{-1}+(B-r_m)f_{q_m}+r_m f_{q_m+1}.
\]

Terms with zero coefficient are omitted. The finite entries of \(f_m\) form an initial segment, and their consecutive differences are positive and strictly increasing. For details set \(g_0=0\). When \(f_1\) is finite, \(g_1-g_0=\lambda^{-1}\) and \(g_2-g_1=f_1>\lambda^{-1}\). Each later difference \(g_{m+1}-g_m\) between finite inputs is \(f_{q_m+1}-f_{q_m}\): in the balanced list of \(B\) slot sizes just one entry increases by one. Those indices are at most \(m\), so the increasing-differences assertion follows inductively from the strict increase and strict convexity of \(q(g)=g/(1-g)\) on \([0,1)\). Once an input reaches one or becomes infinite, subsequent inputs do too. The sorted slot sizes increase coordinatewise and inherited finite responses increase. These arguments apply also for \(B=1\) and for \(\lambda\le1\), in which latter case only \(f_0\) is finite.

If a size partition of \(m-1\) yields finite child responses, then replacing unequal slot sizes \(a>b+1\) by \(a-1,b+1\) strictly decreases the sum of their \(f\)-values. The initial-segment property keeps both new values finite. The difference comparison is \(f_a-f_{a-1}>f_{b+1}-f_b\). Thus the balanced list is the unique best multiset of sizes whenever the sum can be finite. By induction on \(m\), using (4), \(f_m\) is the minimum response at size \(m\); whenever finite it is attained by exactly the recursively evenly split tree, up to rooted isomorphism.

Now take \(\lambda=\rho(C_{H_*})\) for the proposed optimum \(H_*\), with root cap \(D\) and cap \(B\) below it. Every nonempty child of \(H_*\) has matrix spectral radius strictly less than \(\lambda\), by (3) and positivity. The finite scalar \(g\) at the root is exactly one. Any competing tree with spectral radius at most \(\lambda\) has finite child responses for the same reason, and its scalar \(g\) is at most one, by the positive-semidefinite rank-one criterion. The lowest possible sum with \(D\) child slots is attained uniquely by evenly splitting the sizes and using their individually optimal shapes. This follows from the same strict difference argument on the already proved \(f_m\). Thus the competing tree must be \(H_*\). Minimizing \(\rho(C_H)\) is equivalent to maximizing \(\lambda_{\min}(L+E_v)\). Equation (2) completes the proof. For the rooted star, restricting \(L+E_v\) to vectors constant on the leaves gives eigenvalues solving \(x^2-(k+1)x+1=0\). Its other eigenvalues are one, so the lower root gives the displayed formula.

## Logspace construction

Number core vertices in preorder, placing larger child slots first. A subtree occupies a contiguous interval of known size, and its root is its interval's first vertex. To recover the parent and degree of a core index, start with the full interval and repeatedly compute the sizes of the equal child intervals by division with remainder. Descend into the unique interval containing the index, retaining only its first index, size and the previous interval's root. At the desired root the child count is the smaller of its slot cap and its interval size minus one. Each retained value fits in \(O(\log n)\) bits, and the descent strictly decreases the interval size. Assign one subdivider in a fixed consecutive range to each nonroot core index. Assign the leaves a further consecutive range, in batches ordered by core index. The offset of one batch can be recomputed by summing the leaf counts on the earlier core indices. The graph is generated by emitting the two parent-edge incidences of every subdivider and the one core edge of each leaf. All counters and recompute operations use \(O(\log n)\) working bits. This is the same recomputation approach that gives witness generation without storing all intermediate choices in the portfolio's logspace results. [MathProofs logspace minimum generation](https://github.com/Dugongue/MathProofs/blob/main/LogspaceMinimumGeneration/Proof.md)

## Scope and sources

Ken Wu's boundary observation addresses order \(2k\). Hou and Tan determine the sharp equality case on order \(3\) modulo \(k\) and pose the general structural question about the two consecutive weights. Liu, Lou and Trevisan classify the small matching numbers two through four. The \(c=3\) case here belongs to Pirzada and Bhat's range \(k=\lfloor n/2\rfloor-1\). The general result treats an unbounded matching number throughout the stated residue class and determines the unique rooted core. The grounded inverse formula is classical, also called the bottleneck matrix. The comparison argument uses its complete resolvent response with a strict discrete-convexity calculation. The argument is an informal proof and external priority remains provisional. [Ken Wu's note](https://kenwu-lab.wooqianghao.workers.dev/papers/matching-number-minimal-spectral/) · [Hou and Tan](https://arxiv.org/html/2607.11061v2) · [Liu, Lou and Trevisan](https://arxiv.org/abs/2601.18223) · [Pirzada and Bhat](https://doi.org/10.1016/j.disc.2026.115031) · [Andrade and Dahl on rooted-tree Perron values](https://doi.org/10.1016/j.laa.2022.01.005)
