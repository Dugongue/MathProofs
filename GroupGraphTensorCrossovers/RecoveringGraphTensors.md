# Recovering a graph from a tensor in arbitrary coordinates

**Theorem.** Let $X$ be a simple graph on $m$ vertices containing a triangle and having an invertible adjacency submatrix on two row vertices and two column vertices disjoint from the rows. Form the $m\times m\times(m+1)$ tensor of the matrix space
$$
S_X=\{\operatorname{diag}(x_1,\ldots,x_m)+t A_X:x_i,t\in F\}.
$$
Given a raw tensor, one can recognize whether it is isomorphic to such an encoding with $X$ connected and nonbipartite, recover $X$ up to vertex relabeling, and exhibit the tensor isomorphism to the decoded encoding. The algorithm is deterministic polynomial bit time over every fixed finite field and over $\mathbb Q$. Over arbitrary explicitly represented finite fields its deterministic work is polynomial apart from split univariate factorization, giving a Las Vegas polynomial-bit-time version. It applies to the encodings of arbitrary graphs in the companion proof, with the graph recovered by removing the recognized tags.

Here the input consists of the entries of the tensor in arbitrary bases. Graph Isomorphism to Tensor Isomorphism through code equivalence was established by Grochow and Qiao. The result below gives recognition of the image up to tensor isomorphism for this particular matrix-space construction. [Grochow–Qiao, Part I, Appendix B](https://arxiv.org/abs/1907.00309)

## Recover the diagonal space by linear equations on minors

Regard the $m+1$ raw tensor slices as a matrix space $S$, rejecting if they are linearly dependent. For a formal combination of these slices, collect the $2\times 2$ minors as homogeneous quadratics on $S$ and form their linear span $I_2\subseteq\operatorname{Sym}^2 S^*$. Left and right multiplication by invertible matrices changes the list of minors by invertible exterior-square changes. A basis change in $S$ just changes its coordinates. Thus $I_2$ is intrinsic.

Work first in the displayed coordinates of $S_X$. The minor on the disjoint row and column sets from the theorem is a nonzero multiple of $t^2$. For each vertex $i$, choose an edge $jk$ with $i,j,k$ distinct, which exists by the triangle. The minor on rows $i,j$ and columns $i,k$ is $t x_i$ plus a multiple of $t^2$. Hence $t x_i\in I_2$. Principal minors at distinct vertices $i,j$ give $x_i x_j$ after adding a multiple of $t^2$. Conversely no minor contains $x_i^2$ because it uses distinct rows and columns. Therefore
$$
 I_2=\langle t^2,\ t x_i,\ x_i x_j\ (i\ne j)\rangle.
$$
This calculation uses formal monomials, so it also holds in characteristic two. The subspace
$$
 L=\{\ell\in S^*: \ell S^*\subseteq I_2\}
$$
is exactly the line $F t$. It contains $t$, and if $\ell$ has a nonzero $x_i$ coefficient then $\ell x_i$ has a nonzero $x_i^2$ coefficient. The space $L$ is computed by solving linear equations on multiplication by each member of a basis of $S^*$. Reject if it has dimension different from one. Its common zero space $D\subset S$ is the hidden diagonal matrix space on every valid input.

## Extract both rank-one coordinate frames

If $D=P\operatorname{Diag}_m(F)Q$ for invertible $P,Q$, its algebra of left multipliers is
$$
 \mathcal A=\{B\in M_m(F):BD\subseteq D\}
             =P\operatorname{Diag}_m(F)P^{-1}.
$$
To prove this, conjugate and cancel $P,Q$. Multiplying the diagonal identity shows that a left multiplier of all diagonal matrices must itself be diagonal. The converse is immediate. The condition defining $\mathcal A$ is a homogeneous linear system in the entries of $B$.

Compute the simultaneous eigenspaces of a basis of $\mathcal A$ by factoring their characteristic polynomials and refining intersections of eigenspaces. Reject unless the matrices are simultaneously diagonalizable over $F$ with $m$ one-dimensional common eigenspaces. This succeeds for the full split diagonal algebra, whose joint characters are all different. Pick one vector $p_i$ on each eigenline. The projection $E_i$ onto this line along all the others is explicit in the resulting basis. Compute $E_iD$ by projecting a basis of $D$. Reject unless it has dimension one for each $i$; in the valid case it consists of multiples of $p_i q_i$ for a nonzero row covector $q_i$. Verify that the $q_i$ are independent. Then $P=(p_1,\ldots,p_m)$ and the matrix $Q$ of rows $q_i$ give $D=P\operatorname{Diag}_m(F)Q$, since $\dim D=m$. These computations produce the two coordinate frames in matching order.

The required factorizations are deterministic polynomial time over $\mathbb Q$ by LLL polynomial factorization. Over a fixed finite field enumerate field elements for each eigenvalue calculation and solve the eigenspace equations. Over general finite fields use randomized exact factoring with verification of the split factors and their multiplicities. One may compute each common eigenspace as the solution of stacked equations in the original basis matrices, so that in the rational case only polynomial-bit linear systems and factorizations occur. [Lenstra–Lenstra–Lovász, *Factoring polynomials with rational coefficients*](https://doi.org/10.1007/BF01457454) · [Cantor–Zassenhaus, *A new algorithm for factoring polynomials over finite fields*](https://doi.org/10.1090/S0025-5718-1981-0606517-5)

## Recover edges and certify the coefficients

Take any $B\in S\setminus D$, normalize it to $P^{-1}BQ^{-1}$, and subtract its diagonal. Let $C$ be the resulting off-diagonal matrix. The support of $C$ on valid inputs is exactly the adjacency pattern of $X$, up to one common permutation of its rows and columns. The eigenspace computation has only chosen the coordinate ordering and independent row and column scales, so this support is independent of those choices up to graph isomorphism.

To recognize inputs outside the promise as well, require symmetric support, build its simple graph $X$, and check the triangle, disjoint minor, connectivity, and nonbipartiteness conditions. Certify that all edge coefficients can be made equal to $1$ by row and column scalings. On the bipartite support graph with one copy of each row and column vertex, solve $r_i s_j=C_{ij}$ for a nonzero scale at every incident vertex. Choose a root scale $1$ in each component. Propagate the equations along a spanning tree and verify all the remaining edges. Every solution can be normalized to the chosen root scale by multiplying all row scales in that component by a scalar and dividing all column scales by it, so this procedure is complete. On a true encoded tensor, the graph adjacency coefficient, basis scales and the choice of $B$ give one such solution. Conversely a successful certificate shows that the recovered $S$ is carried to $S_X$ by explicit changes of row and column bases.

The original $m+1$ slices and the canonical diagonal-plus-adjacency basis now span the same matrix space. Solve the basis-change equations to obtain the third-mode map. For the padded family from the companion proof, the uniquely largest-degree vertex and its two paths distinguish the added vertices. Checking this pattern and deleting those vertices gives the original graph up to relabeling. This gives a polynomial many-one reduction from Tensor Isomorphism on the recognized image to Graph Isomorphism, with witnesses recovered in both directions. Graph canonization on that image also gives tensor canonization there by re-encoding the canonical graph.

## The square encoding and its determinant constraint

The trace-zero square encoding of the companion proof also admits raw recognition and decoding. In that case use $S_X^0=D_0+F A_X$ with $D_0=\{ \operatorname{diag}(x):\sum_i x_i=0\}$. The padded graph has an induced matching of size three. Work in the formal coordinates $t,x_i$ with the one relation $\sum_i x_i=0$.

Let $I_3$ be the span of the $3\times 3$ minors of a formal slice. The matching gives $t^3$ from its disjoint three rows and columns. For any $i$, at least two matching edges avoid $i$. Use their endpoints as disjoint rows and columns and add $i$ to both. Expansion gives $t^2x_i$ plus a multiple of $t^3$. For $i\ne j$, at least one matching edge avoids both. Add its row and column to the two rows and columns $i,j$. The resulting minor gives $t x_i x_j$ after subtracting the already obtained terms. The trace relation gives $t x_i^2=-\sum_{j\ne i}t x_i x_j$. Thus $t\operatorname{Sym}^2 S^*\subseteq I_3$. Conversely, any $\ell$ with $\ell\operatorname{Sym}^2 S^*\subseteq I_3$ vanishes at each rank-two point $E_{ii}-E_{jj}$, since every minor is zero there and some linear form has nonzero value there. These points span $D_0$. Therefore the space of such $\ell$ is precisely $Ft$. In raw coordinates this again finds $D_0$ by linear equations.

For the square case recover the diagonal algebra from
$$
 \{(B,C)\in M_m(F)^2: B D=D C\text{ for every }D\in D_0\},
$$
In the hidden diagonal frames, the off-diagonal equations are $B_{ij}x_j=C_{ij}x_i$. The coordinates $x_i,x_j$ are independent on $\sum x_i=0$ because $m\ge3$. Thus both matrices are diagonal, with the same diagonal entries. The left projection is the full split diagonal algebra in its hidden basis, so recover eigenlines and $E_iD_0$ as before. Verify that the resulting diagonal hyperplane has a defining linear form with all coefficients nonzero. Row scaling then makes its defining equation the coordinate sum.

For any residual slice require that its diagonal have trace zero, then subtract that diagonal. Require symmetric support and the tagged graph pattern. For the remaining off-diagonal matrix $C'$, the admissible changes from one trace-zero diagonal space to itself have row and column scalings whose coordinatewise products are constant. Consequently the remaining coefficients are valid exactly when
$$
 C'_{ij}=\kappa r_i/r_j
$$
on every ordered edge, for some nonzero $r_i,\kappa$. Necessity follows because diagonal gauge products must all be equal and the adjacency slice has only one overall scale. Sufficiency follows by applying the corresponding row and inverse column scales, which preserve the trace-zero space. To test it take one edge $ij$ and find the field roots of $\kappa^2=C'_{ij}C'_{ji}$. Try the at most two nonzero roots, solve the equations along a spanning tree, and verify all directed edges. The quadratic root step fits the same factoring model as diagonal splitting. Thus both square and rectangular encodings are recognizable from raw tensors.

For the square special-linear comparison, let $g_T,g_U$ be the explicit changes from the two raw tensors $T,U$ to decoded square graph tensors $S_X^0,S_Y^0$, and write $\rho_i=\det(g_{U,i})/\det(g_{T,i})$ for the three factors. A tensor isomorphism in the decoded gauges must have those determinants to correspond to a special-linear isomorphism of the raw inputs. The companion proof shows that these determinants are $s^m\epsilon,t^m\epsilon,(st)^{-m}\epsilon$ for a graph isomorphism of sign $\epsilon$. Thus $\epsilon=\rho_1\rho_2\rho_3$ in the field, and the remaining numerical tests are the two $m$-th root tests $s^m=\rho_1/\epsilon,\ t^m=\rho_2/\epsilon$. The third determinant equation is then automatic. In characteristic two the sign in the field is $1$. With the numerical tests satisfied, an ordinary graph isomorphism oracle decides the required sign in polynomially many queries. First find one graph isomorphism by progressive vertex marking. If its sign differs, test whether the graph automorphism group has an odd element, by computing generators through the same successive marking and orbit representatives. These tests and the verified gauge changes also construct the required special-linear maps. Over the fields with the deterministic decoding above, this gives a deterministic polynomial-time Turing reduction of special-linear isomorphism on the recognized square family to ordinary Graph Isomorphism.

Conversely ordinary Graph Isomorphism reduces to special-linear square tensor isomorphism in the recognized family. Adjoin two isolated vertices to each original graph before applying the tags. This preserves the isomorphism answer and supplies a transposition of isolated vertices, so any isomorphic pair has an even isomorphism. The square encoding then gives a single special-linear tensor instance.

All spaces and polynomial expressions used before the eigenspace calculation have dimensions polynomial in $m$. This is an informal proof.
