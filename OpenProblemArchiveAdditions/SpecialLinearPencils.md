# Special-linear isomorphism of matrix pencils over fixed finite fields

**Theorem.** Fix a finite field $F=\mathbb F_q$ and a positive integer $k$. Given arbitrary tensors in $F^k\otimes F^a\otimes F^b$, special-linear isomorphism on all three modes can be decided deterministically in polynomial bit time. This includes all two-slice matrix pencils, with no regularity, squareness, or separability hypothesis. This informal proof gives a fixed-mode-dimension case of Open Question 1.9. The argument enumerates the first-mode action, so its polynomial bound is for fixed $k$ and $F$. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

The archive treats two slices by Kronecker normal form. MathProofs already gives an ordered-slice determinant computation over $\mathbb F_3$ using radical layers. Here the image is computed from indecomposable multiplicities, yielding a direct formula over each fixed finite field for any fixed slice count. [Determinant Cosets from Castling and Normalized Matrix Pencils](../DeterminantCosetsByCastling/PROOF.md)

## The joint determinant image

Write an ordered tuple as a representation $M$ on two vertices, with arrow maps $A_i\colon U\to V$ for $1\le i\le k$. A transporter to $M'$ is a pair $(P,Q)$ satisfying $A'_iP=QA_i$ for all $i$. On the tensor modes the maps are $P^{-T}$ and $Q$, so requiring both determinants to be $1$ is equivalent to requiring $\det P=\det Q=1$. Suppose the underlying ordinary module isomorphism problem supplies one transporter $(P_0,Q_0)$. Every transporter is then $(P_0,Q_0)$ composed with an automorphism of $M$. Thus a determinant-one transporter exists exactly when $(\det P_0^{-1},\det Q_0^{-1})$ belongs to the joint determinant image $K_M\subseteq(F^\times)^2$ of $\operatorname{Aut}(M)$.

Decompose $M=\bigoplus_i M_i^{m_i}$ with pairwise nonisomorphic indecomposables. Let $E_i=\operatorname{End}(M_i)$, which is local by the Fitting lemma. The division quotient $D_i=E_i/\operatorname{rad}E_i$ is a finite field. Write $d_i=[D_i:F]$ and let $a_i,b_i$ denote the $F$-dimensions at the two vertices of $M_i$. Then
$$
K_M=\left\langle
(t^{a_i/d_i},t^{b_i/d_i})
\ \middle|\ i,\ t\in F^\times
\right\rangle .
$$

Indeed, for $E=\operatorname{End}(M)$ the semisimple quotient is $\prod_i M_{m_i}(D_i)$ by the endomorphism-ring form of Krull–Schmidt. The induced map on units has kernel $1+\operatorname{rad}E$. Every element of the kernel is unipotent on each vertex, since the radical is nilpotent and the vertex spaces are preserved. Its determinant pair is therefore $(1,1)$.

By Wedderburn–Malcev, the quotient map $E_i\to D_i$ has an $F$-algebra section, since $D_i/F$ is separable. The section acts on each vertex, making the two vertex spaces of $M_i$ into $D_i$-vector spaces of dimensions $a_i/d_i$ and $b_i/d_i$. Using the same section on every copy realizes $\mathrm{GL}_{m_i}(D_i)$ inside $\operatorname{Aut}(M_i^{m_i})$ as matrices of those endomorphisms. A matrix with determinant $\delta$ over $D_i$ has determinant pair over $F$ equal to
$$
\left(
\operatorname{Norm}_{D_i/F}(\delta)^{a_i/d_i},
\operatorname{Norm}_{D_i/F}(\delta)^{b_i/d_i}
\right).
$$
This follows by writing its action as a direct sum of copies of the natural $D_i$-linear action, then restricting scalars. The determinant on each factor takes all values in $D_i^\times$, and the finite-field norm is onto $F^\times$. The lifted factors span the unit group of the semisimple quotient, and the radical kernel contributes the trivial determinant. This proves the formula. Repeated indecomposables are handled by the full matrix factor, so the exponents come from one indecomposable copy.

For a two-arrow pencil the formula recovers the familiar contributions from the Kronecker blocks. The two rectangular types of dimensions $(r,r+1)$ and $(r+1,r)$ have residue field $F$. A regular primary block for a projective factor of degree $d$ and exponent $e$ has dimensions $(de,de)$ and residue field of degree $d$, hence contributes $(t^e,t^e)$. The algorithm below uses the general formula directly.

## Algorithm and bit bound

Represent the arrow maps by block matrices on $U\oplus V$, together with the projections onto $U$ and $V$. These specify a module over the path algebra of two vertices and $k$ parallel arrows. Its dimension is $k+2$, since no two arrows compose. A module isomorphism fixes the vertex decomposition and is precisely a strict transporter. Use the module algorithms of Chistov, Ivanyos and Karpinski for constructing one transporter and finding an indecomposable decomposition. Their finite-field algorithms, including the radical and idempotent steps, have deterministic polynomial bounds for fixed field. In particular their Section 4 discusses deterministic semisimple decomposition with polynomial dependence on the field characteristic. [Polynomial time algorithms for modules over finite dimensional algebras](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf)

For every indecomposable summand compute its endomorphism algebra by linear equations, its dimension of radical by the finite-field radical algorithm, and hence $d_i=\dim_F E_i-\dim_F\operatorname{rad} E_i$. Read vertex dimensions from the projections. One may use every copy in the decomposition, since repeating a generator family does not change the subgroup. Enumerate the subgroup generated by the displayed pairs in an ambient group of size $(q-1)^2$. No explicit Wedderburn–Malcev section or norm preimage is needed for the decision. [Rónyai, Computing the structure of finite algebras](https://www.sciencedirect.com/science/article/pii/S074771710880017X)

Enumerate the elements of $\mathrm{SL}_k(F)$, apply each to the slice mode of the first tensor, and run the strict transporter test on the resulting tuple and the second tensor. For every successful ordinary transporter, check membership of its inverse determinant pair in the computed subgroup. Accept exactly when one check succeeds. Both the slice-mode enumeration and the subgroup search have size bounded by constants depending only on $k,q$. The other computations use module dimensions and matrix sizes polynomial in the dense input size. Field operations over fixed $F$ have constant bit cost. The same test computes the full joint determinant-pair coset for any prescribed slice-mode map, with a polynomial cost per map.
