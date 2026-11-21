# Determinant images and special-linear transport by oriented castling

## GP-0280

Over every explicitly represented finite field, there is a deterministic polynomial-bit-time algorithm computing the exact three-determinant image of the stabilizer of any tensor accepted by the rank test below. With an accepted source it also decides and constructs all-target special-linear transport, including over $\mathbb F_3$. The test uses iterated dimension-decreasing castling and may accept long sequences of format changes. Neither ordinary tensor-isomorphism oracles nor discrete logarithms are used. This is a sufficient class for the determinant-image question. [Original castling transform, Sato–Kimura §2](https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/classification-of-irreducible-prehomogeneous-vector-spaces-and-their-relative-invariants/89C47A4810A6F02971D393FD1FE44653) · [Special-linear tensor-isomorphism question](https://arxiv.org/html/2306.03135v2)

### Oriented transport through annihilators

Use positive dimensions and fixed ordered bases. Write a tensor as $F:Z^*\to V\otimes W$, in format $a\times b\times c$, with $c<ab$ and $F$ injective. Put $U=\operatorname{im} F$, and extend the ordered list of columns of $F$ to a basis of $V\otimes W$. Scale its final vector so the determinant of the concatenated basis is one. Choose the annihilator $U^\perp\subset V^*\otimes W^*$ with basis dual to the appended columns, and declare those ordered columns to be the new tensor, of format $a\times b\times(ab-c)$. All of this is ordinary finite-field linear algebra.

Suppose $F_x,F_y$ are two injective flattenings being compared. A transporter with local maps $A,B,C$ satisfies
$$
F_y C^{-\mathsf T}=(A\otimes B)F_x .
$$
For given $A,B$, this is possible exactly when $A\otimes B$ takes $U_x$ onto $U_y$, in which case $C$ is uniquely determined. The same condition says that $A^{-\mathsf T}\otimes B^{-\mathsf T}$ carries $U_x^\perp$ to $U_y^\perp$, and the third map of the transformed comparison is again unique. This gives inverse constructive correspondences of transporters. In a stabilizer comparison it also gives a group isomorphism.

Write $(\alpha,\beta,\gamma)=(\det A,\det B,\det C)$. In the two chosen concatenated bases, the determinant of the induced map on the quotient $(V\otimes W)/U$ is
$$
\frac{\det(A\otimes B)}{\det(C^{-\mathsf T})}
=\alpha^b\beta^a\gamma .
$$
The ambient determinant uses the original fixed coordinates because both concatenated bases have determinant one. The induced contragredient map on the annihilators has reciprocal determinant. Its inverse transpose is the third map of the transformed transporter. Thus the determinant transformation is exactly
$$
(\alpha,\beta,\gamma)\longmapsto
(\alpha^{-1},\beta^{-1},\alpha^b\beta^a\gamma).
$$
It is an invertible monomial map with unimodular exponent matrix, so it preserves simultaneous determinant one in both directions. These identities compare two specific tensors and do not appeal to geometric or generic orbit equivalence.

### Acceptance and terminal calculation

At every step sort the dimensions $a\le b\le c$, recording the corresponding permutation of determinant coordinates. If $c\ge ab$, check that the largest flattening is surjective, and accept if it is. For $ab/2<c<ab$, test injectivity of that flattening, apply the oriented transformation if it is injective, and continue. The remaining cases fall outside the acceptance test. The sum of the three dimensions strictly decreases whenever the transform is applied. Ranks and the ability to continue are invariant under ordinary transport by the correspondence just proved. Thus a source passing this test cannot be equivalent to a target that fails it. For an accepted pair the format sequence is the same.

At a surjective terminal pair, arbitrary first and second local maps lift to the third leg by choosing splittings of the two flattenings and an isomorphism of their kernels. If $c>ab$, the kernel has positive dimension, so its isomorphism can be given any nonzero determinant. Hence any prescribed triple is possible. If $c=ab$, the unique third map has determinant $\det(F_y)/(\det(F_x)\alpha^b\beta^a)$. Thus a prescribed triple is possible exactly when
$$
\alpha^b\beta^a\gamma=\det(F_y)/\det(F_x).
$$
Choose the first and second maps diagonal with given determinants and construct the third by the same basis calculation. These tests therefore produce witnesses, and the inverse transformations recover witnesses at all prior steps.

For the stabilizer set $F_y=F_x$. The terminal image is the entire torus in the first case and the kernel of the primitive character with exponent row $(b,a,1)$ in the second. Pull it back through the unimodular transformations and permutations. The outcome is the entire torus or the kernel of one explicitly computed primitive character. In the latter case its order over $\mathbb F_q$ is $(q-1)^2$, since the primitive row is onto on the finite torus. Querying membership and constructing a witness use only field operations. The dimensions of all arrays are bounded polynomially by the initial dimensions, and the exponent row has polynomial bit length by repeated multiplication of bounded-size integer matrices with bounded entries. This proves the claimed bit complexity.

The accepted class includes, for example, every injective format with $c=ab-1>ab/2$ for which the one-dimensional annihilator is represented by a full-rank $a\times b$ matrix. The next sorted format is $1\times a\times b$, whose largest flattening is then surjective. More generally the defining rank checks are explicit at every step. No conclusion on unaccepted formats is needed.
