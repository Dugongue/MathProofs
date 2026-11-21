# Mixed Hamming and matrix-rank equivalence

## GP-0332

Over any explicitly represented finite field $F$, consider linear codes inside a marked direct sum $F^h\oplus\operatorname{Mat}_{a,b}(F)$. The allowed equivalences are independent linear ambient isometries for Hamming weight and matrix rank on the respective blocks, acting on one common domain of code generators. Decision is polynomial-time equivalent to ordinary three-tensor isomorphism over $F$. In the orientation-preserving matrix-rank model there are many-one reductions in both directions. Allowing matrix transpose on square rank blocks takes at most two nonadaptive tensor-isomorphism queries for the upper reduction. The hardness holds with one genuine Hamming coordinate, a rectangular rank block, and raw generator matrices. This result concerns the base-field matrix-rank model.

### The allowed linear actions

A linear Hamming isometry of $F^h$ is monomial, since it permutes the weight-one lines. A linear matrix-rank isometry is left-right equivalence, with possible composition by transpose when the format is square. For the latter assertion identify the rank-one matrices with decomposable tensors in $A\otimes B$. If both dimensions are at least two, the maximal subspaces consisting of tensors of rank at most one are $u\otimes B$ and $A\otimes v$. Two rank-one tensors with independent first factors and independent second factors have sum of rank two. This observation proves the stated maximal-subspace description. Subspaces in different rulings meet in a line, whereas distinct subspaces in the same ruling meet trivially. An isometry therefore preserves both rulings or exchanges both, the latter possible only when the dimensions agree. After a transpose if needed, choose bases $e_i,f_j$, and write their image lines as $F u_i,F v_j$. The vectors $u_i,v_j$ form bases by invertibility of the full map. The image of $e_i\otimes f_j$ is $c_{ij}u_i\otimes v_j$ with $c_{ij}\ne0$. Rank preservation at $(e_i+e_k)\otimes(f_j+f_l)$ implies that every $2$-by-$2$ minor of $(c_{ij})$ vanishes, so its coefficients factor into a row and a column scaling. When one side has dimension one the classification is immediate.

### A simultaneous tensor reduction

Replace each raw generator list by a basis of its span. If code dimensions differ, reject. In the common generator coordinate space $V=F^k$, let $c_i$ be the column for Hamming coordinate $i$, and let $T_R\in V\otimes A\otimes B$ be the tensor of the rank block, with $A=F^a$, $B=F^b$. Let $U,C,D$ be three further $h$-dimensional spaces with corresponding bases $u_i,e_i,f_i$. Use the following three tensors:
$$
T_R,\qquad T_H=\sum_i c_i\otimes e_i\otimes f_i,\qquad
\Delta=\sum_i u_i\otimes e_i\otimes f_i.
$$
Place them at their indicated block positions in $(V\oplus U)\otimes(A\oplus C)\otimes(B\oplus D)$, and require all six axis blocks to be preserved individually. The two data tensors then use exactly the same basis change on $V$.

The anchor $\Delta$ forces the two changes on $C,D$ to be monomial with the same permutation. To see this, contraction in $U$ gives the subspace of diagonal matrices on $C,D$. Its rank-one projective lines are precisely the coordinate matrices $e_i\otimes f_i$. Preservation of that subspace sends each coordinate line to a coordinate line, proving the asserted form of the changes on $C,D$. Conversely two such monomial maps with a common permutation extend to an automorphism of $\Delta$ by the reciprocal products of their scalings on $U$. On $T_H$ the induced action is therefore exactly an arbitrary Hamming monomial action, alongside the arbitrary basis change on $V$. The $A,B$ changes act on $T_R$ as exactly the other desired isometry. This proves equivalence in both directions to the partitioned tensor problem. Its number of parts per axis is two, so it reduces to ordinary TI by the constant-part case of Grochow–Qiao IV, Theorem 5.1. [Partitioned tensor isomorphism](https://arxiv.org/html/2306.16317#S5)

When transpose is allowed, apply the same comparison to both the original rank tensor and the tensor with its matrix legs exchanged. The raw code is still taken with the same relation between its two blocks. Removing an empty block causes no difficulty because it has no active constraint.

For the reverse reduction take a TI instance as two matrix spaces with slice bases, after deleting dependent slices and rejecting unequal slice ranks. Pad one matrix axis by zero rows, if needed, to make the format rectangular of unequal dimensions. This preserves and reflects TI: the common span of the columns is intrinsic and a transporter restricts to that span and extends over any added complement. Encode each matrix space $S$ by the mixed code
$$
\{(t,M):t\in F,\ M\in S\}.
$$
Its first coordinate is a genuine Hamming block. Equivalence of these mixed codes is exactly left-right equivalence of the matrix spaces. This closes the base-field block model without synchronizing independent decision oracles.

The construction reuses constant-part tensor individualization. The new point is the single diagonal anchor that makes the Hamming scales and permutation compatible with the same row action used by the matrix block. [Earlier matrix-space embedding reductions](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/GrochowCatalogueProofsIII/MatrixSpaceClassifications.md)
