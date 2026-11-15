# Exact rank fingerprints for matrix-code equivalence

This implementation compares full-rank bases of equal-dimensional subspaces of $m\times n$ matrices over a prime field. Its equivalence relation is $D=L C R^{-1}$ with invertible left and right maps. Transposition enters an internal computation to optimize the order of elimination. It is not allowed as an additional isometry. The binary companion uses packed elimination and two-dimensional coefficient-plane invariants.

## Rank and incidence reduce the search

For a basis $(A_i)_{i=1}^k$, let $A(x)=\sum_i x_iA_i$. An equivalence induces $S\in\operatorname{GL}_k$ with $L A(x)=B(Sx)R$. Therefore $\mathrm{rank}(A(x))=\mathrm{rank}(B(Sx))$, and rank is constant on each projective line of coefficient vectors. Jointly color the two projective spaces by these ranks. A rank-histogram mismatch certifies non-equivalence. Select whole rare rank classes from the two spaces as candidate anchors. If hyperplanes are represented by their normal vectors, the map $S$ transports these normals by $S^{-\mathsf T}$. The counts of colors among incident anchors therefore give legitimate hyperplane colors. Counts of hyperplane colors at individual anchors refine their colors in turn. All these signatures are compared exactly without hashing collisions.

In the selected anchor set, greedily choose a basis $u_1,\ldots,u_k$ if it spans. An equivalence must send each $u_i$ to a scalar multiple $\lambda_i v_i$ of a matching target anchor. For any additional singleton-color anchor $u=\sum_i a_i u_i$ with unique matching point represented by $v=\sum_i b_i v_i$, its support has to agree in these coordinates and the ratios $\lambda_i/(b_i/a_i)$ are constant on the common support. Propagating these ratios leaves one free scale per connected component of the support constraints. One global scale does not affect equivalence because it can be absorbed in $L$. Enumerating the remaining scales and checking the full selected color support therefore covers every coefficient map up to scalar, when the search finishes. The implementation can explicitly report that the search cap prevented coverage.

In the binary companion, another invariant attaches a rank to each two-dimensional coefficient subspace. Vertically stack $A(x),A(y)$ for any basis of that subspace, and take the matrix rank. Changing the basis of the plane applies an invertible block row operation, and an equivalence acts by block-diagonal left changes and a common right change. Thus this rank is well defined on planes and preserved under $S$. It can separate points even when all single-slice ranks are equal.

These are variants of the earlier tensor solver's contraction-rank and checked-witness approach. The rank-geometry step is compatible with full general-linear equivalence. A fixed orthogonal Gram on the coefficients need not be preserved.

## Lift a coefficient match in the original matrix representation

After fixing $S$, write $B'_i=B(Se_i)$. The remaining equations $L A_i=B'_i R$ are homogeneous linear equations in the entries of the two matrices. If the vertical stack of the $B'_i$ has full column rank, let $H$ be a matrix with rows spanning its left nullspace. Write $A_\mathrm{st}$ for the vertical stack of the $A_i$. One can eliminate $R$ exactly by imposing
$$
H(I_k\otimes L) A_\mathrm{st}=0.
$$
The right factor is recovered uniquely by evaluating the stacked equation on independent rows of $B'_\mathrm{st}$. This leaves $m^2$ scalar unknowns instead of $m^2+n^2$. A transpose on both sides gives the analogous $n^2$-variable method and is undone when reporting the witnesses. A full square invertible slice sometimes allows cyclic-vector compression with only $n$ unknowns. The unrestricted linear system handles the remaining modest-size cases.

The solver tests the nullspace for jointly invertible matrices. It checks candidate basis elements, exhausts small spaces, and otherwise tries a bounded sequence of seeded combinations. A returned positive is verified by checking invertibility of all three maps and every original slice equation. Exhausting all candidates permits an exact negative. An exhausted budget or unsuccessful bounded unit search returns unknown. A small-side fallback enumerates projective left maps and solves the corresponding right-factor linear equations, giving another exact route where the smaller side is short.

The implementation also uses the Frobenius inner product to pass to a lower-dimensional trace dual where appropriate. The identity
$$
( L C R^{-1} )^\perp=L^{-\mathsf T} C^\perp R^{\mathsf T}
$$
shows that solving the dual pair and inverting and transposing its factors preserves the original equivalence relation. The implementation then recovers the original basis map and verifies the original slice equations.

## Scope

These algorithms retain a field-size or coefficient-dimension dependence because the rank table explicitly enumerates projective directions. The binary backend has a separate coefficient-space cap and handles larger row and column dimensions using packed linear algebra. The official MEDS test vectors test import and explicit refusal at the projective cap. The smaller Oxford teaching example provides a published instance on which coefficient recovery finishes. The proof and software were reviewed informally, and the checks are reproducible.
