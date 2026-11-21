# A single mixed quartic is TOCI-complete

## GP-0262, GP-0254, and GP-0255

Orbit-closure intersection for the diagonal action of $\mathrm{GL}(W)$ on $W^{\otimes 2}\otimes(W^*)^{\otimes 2}$ is TOCI-complete under efficient algebraic reductions. The encoding triples the space dimension and is affine linear in the input pair of quartics. It also gives completeness of the exact quartic-plus-matrix and pure balanced sextic signatures.

Lysikov and Walter prove that the problem for a pair of mixed quartics under a common $\mathrm{GL}(X)$ action is TOCI-complete. Their single-tensor completeness theorem uses balanced order eight. The reduction below uses order four and resolves all three signatures in the first part of their Question I.12. [Lysikov–Walter, Question I.12](https://arxiv.org/html/2411.04639v2#S1.SS4) · [Theorems V.12 and V.14](https://arxiv.org/html/2411.04639v2#S5.SS1)

### Restricting an orbit-closure problem to a marked fiber

Use the following fact twice in these reductions. Let a complex algebraic group $G$ act on varieties $M$ and $A$, and let $\pi:M\to A$ be an equivariant regular map. Fix $a\in A$ with closed orbit and let $H=G_a$. For any $x,y\in\pi^{-1}(a)$, their $G$-orbit closures intersect exactly when their $H$-orbit closures intersect.

For the reverse implication of interest, take a common point $z$ of the $G$-orbit closures. Equivariance and closedness give $\pi(z)\in Ga$, so translate $z$ to the fiber over $a$. A complex algebraic orbit is constructible, so its Euclidean and Zariski closures agree. From a sequence $g_jx\to z$, obtain $g_ja\to a$. The orbit map $G\to Ga$ is a smooth complex submersion and has a local analytic section $s$ near $a$ with $s(a)=1$. Thus $s(g_ja)^{-1}g_j\in H$ and its action on $x$ still tends to $z$. The same argument applies to $y$. The other implication follows from $H\subseteq G$. The section establishes reflection and is unnecessary to compute the reduction.

### Three copies and one partial trace

Identify mixed quartics with $\operatorname{End}(X\otimes X)$, with $\mathrm{GL}(X)$ acting by conjugation with $g\otimes g$. Let $W=X_1\oplus X_2\oplus X_3$ be three coordinate copies of $X$. Assume $X\ne0$, since dimension zero is immediate. Write $D=\operatorname{diag}(I,2I,3I)$ on this sum. For $i=2,3$, form a bridge $B_{1i}$ on $W\otimes W$ with two nonzero blocks. One block goes from $X_1\otimes X_i$ to $X_i\otimes X_1$ using the product of the two coordinate identifications. The other block is its inverse between these two spaces. All its other blocks are zero.

For input $(Q,R)\in\operatorname{End}(X\otimes X)^{\oplus2}$, embed $Q$ as the block $X_2\otimes X_3\to X_3\otimes X_2$ and $R$ as the reverse block, using the displayed order of factors. Let their embeddings be $\widehat Q,\widehat R$. The output is the single quartic
$$
T(Q,R)=A+\widehat Q+\widehat R,\qquad
A=D\otimes I_W+B_{12}+B_{13}.
$$
Both bridges and both data blocks have an off-diagonal map in each of the two ordered matched legs. Thus the partial trace on the second leg returns $(\dim W)D$ for every encoded point, including $A$. For arbitrary quartic $T$, put $D(T)=(\dim W)^{-1}\operatorname{Tr}_2(T)$. Evaluate the three degree-two Lagrange interpolation polynomials for eigenvalues $1,2,3$ at $D(T)$ to obtain equivariant polynomial operators $P_i(T)$. At encoded points they are the displayed color projectors. Define $\pi(T)$ by subtracting the two data blocks, computed by pre- and post-composing $T$ with the corresponding tensor products of $P_i(T)$. This is a globally regular equivariant map, with $\pi(T(Q,R))=A$.

The orbit of $A$ is closed. Regard it as an endomorphism on the standard Hermitian space $W\otimes W$. It is self-adjoint since both bridges include their adjoints. For the $\mathrm{GL}(W)$ action by tensor-square conjugation, the moment functional on a Hermitian matrix $K$ is
$$
\left\langle[K\otimes I+I\otimes K,A],A\right\rangle_{\rm HS}
=\operatorname{Tr}((K\otimes I+I\otimes K)[A,A^*])=0.
$$
Kempf–Ness now gives closedness. The Hermitian structure serves the proof while the output tensor uses only rational entries and the given input coefficients.

The stabilizer of $A$ preserves $D$, so it has blocks $g_1,g_2,g_3$. In the bridge block $X_1\otimes X_i\to X_i\otimes X_1$, preservation is the equality
$$
(g_i g_1^{-1})\otimes(g_1g_i^{-1})=I\otimes I
$$
after identifying copies. Equality of nonzero pure tensors implies $g_i$ is a scalar multiple of $g_1$. Conversely these constraints stabilize both bridges and $D\otimes I$. On each data block the two central scalars cancel, so the action is exactly conjugation by $g_1\otimes g_1$ on each of $Q,R$. The affine subspace of encoded points is closed and stable under that stabilizer, and is equivariantly isomorphic to the input module for this action. The marked-fiber fact now proves both preservation and reflection. All arrays have polynomial size, and the target signature itself belongs to TOCI.

### Two exact target signatures

For a mixed quartic plus a matrix, send $T$ to $(T,0)$. The inclusion into that exact module is equivariant and has the first-coordinate projection as a retraction. This gives both preservation and reflection and answers GP-0254.

For one balanced sextic, send $T$ to $T\otimes I_W$, regarding the identity as a $(1,1)$ tensor. Contraction of the added dual pair gives $(\dim W)T$, so normalized contraction is an equivariant retraction. The map is polynomial-size and gives both directions for the sextic signature in GP-0255. Both targets are fixed tensor signatures of TOCI.
