# Integral transporter schemes and proof degree inside matching spectral minimizers

Let \(H,H'\) be connected loopless multigraphs, each with \(k\ge2\) vertices and \(m\) edges. Fix an integer \(c\) such that \(c\ge2\max\{\Delta(H),\Delta(H')\}+2\). Replace each edge of each core by a two-edge path and add \(c-2d(v)\) leaves at each core vertex \(v\). Denote the resulting bipartite graphs by \(G,G'\). They are extremal graphs in the sharp [prescribed-cycle-rank bound](MatchingCycleRankExtrema.md). They have the same order and the same spectral radius \(\sqrt c\), and each original vertex has at least two added leaves.

Write the adjacency matrices as \(A_G=\begin{pmatrix}0&B\\B^{\mathsf T}&0\end{pmatrix}\) and analogously for \(G'\), ordering the core vertices first. Let \(L,L'\) be the integral Laplacians of \(H,H'\). The following equivalences and transfers hold.

1. Over every commutative ring \(R\), there is a block-diagonal conjugator \(\operatorname{diag}(P,Q)\) from \(A_G\) to \(A_{G'}\) if and only if \(L,L'\) are similar over \(R\). The map of conjugator schemes \((P,Q)\mapsto P\) is a smooth surjection with a section over \(\mathbb Z\).
2. Over every field, the same similarity equivalence holds even when the conjugator between \(A_G,A_{G'}\) is unrestricted. It covers characteristic two and all primes at which the Laplacian has nontrivial Jordan blocks.
3. Over every field, minimum Polynomial Calculus refutation degree for the colored adjacency conjugacy equations with explicit inverse variables equals the minimum for the literal Laplacian conjugacy equations with an explicit inverse. Use degree \(+\infty\) for a system with no refutation.

Thus a connected family with one fixed optimum spectral radius retains the full modular Laplacian similarity classes of its cores, and retains the exact colored conjugacy proof degrees.

## An integral simultaneous normal form

Put \(K=cI-L\), \(K'=cI-L'\). We have \(BB^{\mathsf T}=K\) and \(B'B'^{\mathsf T}=K'\) by direct counting. Let \(\ell\) be the number of vertices in the second color. Choose one of the two available leaves at each core vertex and order these \(k\) leaf columns first. Then \(B=[I\ C]\) and \(B^{\mathsf T}=(I,C^{\mathsf T})^{\mathsf T}\). Change basis on the second color, keeping the first color fixed, by the integral unimodular matrix

\[
W=\begin{pmatrix}I&-C\\0&I\end{pmatrix}.
\]

It gives \(BW=[I\ 0]\) and \(W^{-1}B^{\mathsf T}=(K,C^{\mathsf T})^{\mathsf T}\). Among the kernel coordinates of \([I\ 0]\), the chosen second leaf at each vertex supplies one row of an identity submatrix of \(C^{\mathsf T}\). Reorder these rows first in the kernel and write that column block as \(\begin{pmatrix}I\\D\end{pmatrix}\). Subtract \(D\) times the first kernel block from the remaining one. These changes give the simultaneous normal form

\[
B_0=[I\ 0\ 0],\qquad B_1=\begin{pmatrix}K\\I\\0\end{pmatrix},
\tag{1}
\]

now written as a pair of maps in opposite directions. They need not remain transposes after a general basis change. The three blocks of the second color have sizes \(k,k,\ell-2k\). The same construction applies to \(G'\), giving \(K'\) in the top row of its opposite map. Integral changes ensure that the normal form works functorially after every base change.

## Colored conjugacy and its full scheme

The normalized block equations are \(PB_0=B_0Q\) and \(QB_1=B'_1P\). The first forces the first row of blocks in \(Q\) to equal \([P\ 0\ 0]\). Writing the second equation by rows gives \(PK=K'P\) and the further constraints \(Q_{21}K+Q_{22}=P\), \(Q_{31}K+Q_{32}=0\). Thus exactly the conjugators are

\[
PK=K'P,\qquad P\in\mathrm{GL}_k,\qquad
Q=\begin{pmatrix}
P&0&0\\
U&P-UK&V\\
W_0&-W_0K&Z
\end{pmatrix},\qquad Q\text{ invertible}.
\tag{2}
\]

Here \(U,V,W_0,Z\) are arbitrary matching-sized matrices subject only to the open determinant condition shown. Also \(PK=K'P\) is precisely \(PL=L'P\). Projection in (2) is an open subspace of an affine space over the Laplacian transporter followed by affine-space projection, so it is smooth. Setting \(U,V,W_0=0\) and \(Z=I\) defines a section, and proves surjectivity on all ring-valued points. If the final block is empty, interpret that identity and its determinant in size zero. Undoing the integral changes gives the stated scheme over \(\mathbb Z\).

## Uncolored conjugacy over fields

In the normalized model, with coordinates \((x,y,z,w)\) on the total space, the adjacency operator is

\[
T_K(x,y,z,w)=(y,Kx,x,0).
\]

Its image is the free space of vectors \((a,Kb,b,0)\). In those image coordinates \((a,b)\), the restriction of \(T_K\) is \((a,b)\mapsto(Kb,a)\). Its square restricts to \(\operatorname{diag}(K,K)\). If \(A_G,A_{G'}\) are similar, the similarity maps image to image and intertwines the restricted squares. Hence \(K\oplus K\) is similar to \(K'\oplus K'\). Over a field, the elementary-divisor multiset of the direct sum is obtained by doubling that of the original operator, so \(K\) and \(K'\) are similar. The converse follows from the section in (2). This proof does not need to cancel doubled integral conjugacy classes over arbitrary rings.

## Exact Polynomial Calculus degree

For the Laplacian system take variables \(P,S\) and impose the matrix-entry equations of \(PK-K'P=0\) and \(PS=SP=I\). For the colored adjacency system take \(P,S,Q,T\) and impose the two intertwiner equations and \(PS=SP=I\), \(QT=TQ=I\). Minimum refutation degree here uses the ordinary rules of linear combination and multiplication by a variable, measuring total degree of proof lines.

Integral basis changes in the second color act by invertible linear substitutions in \(Q,T\), leaving \(P,S\) fixed. Each old axiom is a constant linear combination of the transformed entries, and conversely. Multiplication by a linear form can be implemented by separate multiplications by variables and a linear combination, retaining the degree of the original multiplication step. Therefore the minimum degree is the same in the original and normalized presentations. The same reasoning allows substitution even with constants. In a refutation of degree \(d\), a multiplication step with nonzero predecessor has predecessor degree at most \(d-1\); zero predecessors need no multiplication step.

The linear Laplacian intertwiner equations follow from linear combinations of the normalized colored graph axioms. Specifically, substitute \(Q_{11}=P, Q_{12}=0\) in the first row of \(QB_1-B'_1P\), using constant matrix coefficients. The inverse equations for \(P,S\) already occur. This transfers a Laplacian refutation to the colored graph system with the same degree. In the other direction substitute \(Q=\operatorname{diag}(P,P,I)\) and \(T=\operatorname{diag}(S,S,I)\) in a refutation of the normalized graph system. Every axiom becomes zero or an axiom of the Laplacian system up to sign. The substitutions are affine linear and preserve the refutation degree bound. This proves equality, including the case of infinite degree.

## Scope and sources

The subdivision construction and Laplacian square spectrum build on the matching-radius equality cases of Hou and Tan and the Wu matching note. The integral simultaneous form, the scheme-level section and the exact-degree translations apply to the colored transporter, with the additional uncolored field result supplied by elementary divisors. The proof-complexity comparison uses the literal inverse-variable convention of the portfolio's matrix-conjugacy work. [Hou and Tan](https://arxiv.org/html/2607.11061v2) · [Wu](https://kenwu-lab.wooqianghao.workers.dev/papers/matching-number-minimal-spectral/) · [Exact matrix conjugacy and congruence proof degrees](https://github.com/Dugongue/MathProofs/blob/main/GeneralCongruenceSparseConjugacy/RESULTS.md) · [Transporter-scheme constructions](https://github.com/Dugongue/MathProofs/blob/main/UniversalityConsequences/ExactTransporterSchemes.md)
