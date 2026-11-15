# Sparse graph tensors with exact transporters and determinant sign

Let $F$ be any field. There are explicit reductions from isomorphism of simple graphs on $n\geq 2$ vertices to ordinary tensor isomorphism in formats $(n+15,n+15,n+16)$ and $(n+15,n+15,n+15)$. Every tensor isomorphism in either construction determines a graph isomorphism, with precisely two independent scalar parameters above each graph isomorphism. For the square construction, the product of the three determinants is the sign of the graph isomorphism in $F^\times$. In odd characteristic the same pair of tensors is special-linearly isomorphic exactly when the graphs have an even isomorphism.

There is also a symmetric trilinear construction in dimension $2n+31$ for which the same permutation acts on all tensor modes. Its full stabilizer is $\operatorname{Aut}(G)\times F^\times$ in characteristic different from $3$. In characteristic $3$ there is an additional explicitly described additive subgroup.

Graph isomorphism already reduces to several variants of tensor isomorphism. The claims here concern the small formats, the exact transporter fibers, and the determinant and symmetric stabilizer formulas. [Grochow and Qiao, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I*](https://arxiv.org/abs/1907.00309) · [Chen et al., *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials III*](https://arxiv.org/abs/2306.03135) · [Li et al., *Connections Between Graphs and Matrix Spaces*](https://www.ias.edu/sites/default/files/LiQiWiWiZh22.pdf).

## A fixed graph augmentation

From $G$ construct $\Gamma(G)$ by adding vertices $r,a,b$ and two tails of lengths four and eight. Connect $r$ to all old vertices and to $a,b$, and join $a$ to $b$. The tails are the paths $a-a_1-\cdots-a_4$ and $b-b_1-\cdots-b_8$. They are disjoint from each other and from the old graph except at their indicated attachment vertices. Denote $N=n+15$ and write $A$ for the $0,1$ adjacency matrix of $\Gamma(G)$.

Vertex $r$ is the unique vertex of degree $n+2$ or more. Old vertices have degree at most $n$, while the other new vertices have degree at most three. Among its neighbors, $a,b$ are precisely the ones adjacent to a nonneighbor of $r$. The endpoints $a,b$ are distinguished by the sizes four and eight of the two corresponding components on nonneighbors of $r$. Once these endpoints are known, every tail vertex is fixed by its distance to the attachment vertex. Thus every isomorphism of augmented graphs restricts to an isomorphism of the old graphs and fixes the corresponding added labels. Conversely every old graph isomorphism has exactly one extension. Label added vertices in the same fixed order after the old vertices in both graphs. The extension preserves the sign of the underlying permutation.

The augmentation is connected, contains the triangle $r,a,b$, and is not complete. The submatrix of $A$ on rows $a_2,b_2,b_6$ and columns $a_3,b_3,b_7$ is $I_3$, with disjoint row and column index sets. Also, for each vertex $v$ there is an edge whose endpoints are both distinct from and nonadjacent to $v$. For a vertex on either tail one may use an interior edge of the other tail, and for any other vertex one may use $a_2a_3$. Graphs of order at most one have only one labeled graph for each order and may be handled separately.

## Rectangular tensor and full transporter

Let $\mathcal D\subseteq M_N(F)$ be the space of diagonal matrices in the given vertex basis. The rectangular tensor has independent slices forming the space
$$
\mathcal S_G=\mathcal D+F A.
$$
Use the $N$ diagonal basis matrices and $A$ as its ordered slices. Equivalence of tensors whose slices are independent is equivalent to left-right equivalence of slice spaces. More precisely, the first two mode matrices $P,Q$ must satisfy $P\mathcal S_G Q^{\mathsf T}=\mathcal S_H$, and such $P,Q$ determine a unique third mode matrix. That third matrix is the inverse transpose of the induced map on the ordered slice coordinates. This follows by evaluating each tensor against an arbitrary covector in the third mode.

The only projective rank-one points of $\mathcal S_G$ are the lines $F E_{ii}$. If the coefficient of $A$ is nonzero, the displayed disjoint $3\times 3$ submatrix produces rank at least three because a diagonal summand vanishes on those positions. If the coefficient of $A$ is zero, a diagonal matrix has rank one precisely when it has one nonzero diagonal entry. A left-right equivalence preserves these lines and both their column and row lines. Therefore there is one permutation $\pi$ with $P e_i=s_i e_{\pi(i)}$ and $Qe_i=t_i e_{\pi(i)}$, for $s_i,t_i\in F^\times$.

The off-diagonal entries of $PA_GQ^{\mathsf T}$ are a fixed nonzero scalar $\lambda$ times those of $A_H$. In particular, $\pi$ is a graph isomorphism, and for every undirected edge $ij$ we obtain
$$
s_i t_j=s_j t_i=\lambda.
$$
Two vertices at the ends of a walk of length two have equal $s$-values and equal $t$-values by these equations. In a connected graph with an odd cycle, every pair of vertices has an even walk between them. If a path has odd length, detouring to an odd cycle and back and going once around the cycle reverses its parity. Thus $s_i=s$ and $t_i=t$ are constant across all vertices.

Conversely, for each graph isomorphism $\pi$ and pair $s,t\in F^\times$, the first two modes $sP_\pi,tP_\pi$ induce the slice-space equivalence. The induced slice map is $st$ times the direct sum of the permutation on diagonal coordinates and the identity on the adjacency coordinate. Its inverse transpose gives the third mode. For each $G$, the permutations so lifted form a copy of $\operatorname{Aut}(G)$ and commute with both scalar actions. The full stabilizer is consequently $\operatorname{Aut}(G)\times(F^\times)^2$. The same formulas provide the claimed transporter parametrization between different graphs.

## Square tensor and determinant sign

Replace $\mathcal D$ by its trace-zero subspace $\mathcal D_0$, of dimension $N-1$, and use the $N$ independent slices
$$
E_{ii}-E_{NN}\quad(1\leq i<N),\qquad A.
$$
The off-diagonal $3\times 3$ minor still excludes every slice with nonzero adjacency coefficient from rank at most two. There is no nonzero rank-one diagonal matrix of trace zero. The projective points of rank two are exactly $F(E_{ii}-E_{jj})$ for unordered pairs $\{i,j\}$.

For these points the column spaces on the left and the row spaces on the right form exactly the collections of coordinate two-planes. The nonzero intersections of distinct planes in either collection recover the coordinate lines. Consequently any left-right equivalence is monomial on both sides. Moreover, for each rank-two slice the two support pairs of its image must be the same pair, so the two permutations of the coordinate lines agree on every unordered pair. Since $N\geq 3$, they are the same permutation on vertices. The off-diagonal argument from the rectangular case gives the same graph isomorphism and two global scalars. Conversely a common permutation preserves trace zero, hence all the previously described pairs lift uniquely to a square tensor isomorphism. The full stabilizer is again $\operatorname{Aut}(G)\times(F^\times)^2$.

Write $\epsilon=\operatorname{sgn}(\pi)$ as an element of $F^\times$. The determinant of the permutation on $\mathcal D_0$ is $\epsilon$, including when the characteristic divides $N$. Indeed it acts with determinant $\epsilon$ on $\mathcal D$, and the quotient $\mathcal D/\mathcal D_0$ has the trivial action because it is given by the coordinate sum. The adjacency coordinate is fixed by the unscaled slice map. Thus the determinants in the three modes are
$$
s^N\epsilon,\qquad t^N\epsilon,\qquad(st)^{-N}\epsilon.
$$
Their product is $\epsilon$. In odd characteristic a triple of determinant-one matrices therefore requires an even graph isomorphism, and any even graph isomorphism yields such a triple by setting $s=t=1$. In characteristic two the sign in the field is always $1$, and the same choice permits every graph isomorphism.

Over $\mathbb F_q$ the ordinary transporter has cardinality $(q-1)^2$ times the graph transporter cardinality. In odd characteristic the special-linear transporter has cardinality $\gcd(N,q-1)^2$ times the number of even graph isomorphisms, because for an even permutation the remaining conditions are $s^N=t^N=1$. In characteristic two replace the even graph isomorphisms by all graph isomorphisms. In particular ordinary tensor automorphism and graph automorphism are identified exactly over $\mathbb F_2$. The two tensor encodings have respectively $N+2|E(\Gamma(G))|$ and $2N-2+2|E(\Gamma(G))|$ nonzero entries in the displayed bases.

## Symmetric trilinear tensor with controlled shears

Work on $X\oplus Z$ where $X=F^N$ has the vertex basis and $Z=F^{N+1}$ has basis $d_1,\ldots,d_N,h$. Write $M_G:Z\to \mathcal S_G$ for the rectangular slice identification with $M_G(d_i)=E_{ii}$ and $M_G(h)=A_G$. Define a symmetric trilinear form $B_G$ by
$$
B_G(z,x,y)=x^{\mathsf T} M_G(z)y
$$
for $x,y\in X,z\in Z$, extend by symmetry, and set it to zero on triples with zero or at least two entries from $Z$. The matrix $A_G$ is symmetric, so this gives a well-defined trilinear form in every characteristic.

For any vector $x+z$ with $x\ne 0$, the contraction with that vector has matrix
$$
\begin{pmatrix}M_G(z)&C(x)\\ C(x)^{\mathsf T}&0\end{pmatrix}
$$
relative to $X\oplus Z$, where the off-diagonal block $C(x)$ is nonzero. For some $i$, its entry at $e_i,d_i$ is $x_i\ne0$. The corresponding two-by-two principal submatrix has nonzero determinant, giving rank at least two. For a vector in $Z$, contraction rank one occurs exactly on the lines $Fd_i$ by the rectangular argument. Their span $D_Z$ is therefore intrinsic, as is $Z$ itself, since
$$
Z=\{v:B_G(d,v,w)=0\text{ for every }d\in D_Z,\ w\in X\oplus Z\}.
$$
The equality follows from the independent coordinate diagonal forms.

An isomorphism of these trilinear forms therefore preserves the distinguished $Z$ spaces. Its induced map on the $X$ quotients and its restriction to $Z$ induce a congruence of the rectangular slice spaces. Applying the rectangular result with the first two maps equal, we obtain a graph isomorphism $\pi$, a scalar $s$ on the $X$ map $sP_\pi$, and the $Z$ map $s^{-2}(P_\pi\oplus1)$. This block-diagonal map is itself a trilinear isomorphism. Composing with its inverse reduces the remaining freedom to a shear $x+z\mapsto x+z+f(x)$ for a linear map $f:X\to Z$.

Write $f(e_j)=\sum_i t_{ij}d_i+c_j h$. The shear preserves the trilinear form exactly when its contribution on any three $X$ basis elements sums to zero. Terms of order two and three in $f$ vanish because their arguments contain at least two $Z$ entries. On triples of distinct indices the conditions are
$$
c_i A_{jk}+c_j A_{ik}+c_k A_{ij}=0.
$$
At the triple $i,i,j$, with $i\ne j$, the condition is $t_{ij}+2c_i A_{ij}=0$, and at $i,i,i$ it is $3t_{ii}=0$. For each $i$ use an edge $jk$ whose endpoints are both distinct from and nonadjacent to $i$. The first condition gives $c_i=0$. The second then gives $t_{ij}=0$ for all $i\ne j$.

It follows that in characteristic different from $3$ all shears vanish. The stabilizer is then exactly $\operatorname{Aut}(G)\times F^\times$. In characteristic $3$ the shears form a copy of the additive group $F^N$, with $f(e_i)=t_{ii}d_i$ arbitrary. The stabilizer is the semidirect product by the same graded group, which acts on the shear coefficients by permutation and the factor $s^{-3}$. Over characteristic different from $2,3$, ordinary polarization identifies this result with the corresponding statement about cubic forms $v\mapsto B_G(v,v,v)/3$.

These are informal proofs. Targeted source searches found the established graph-to-tensor decision reductions and graph matrix-space constructions cited above. The extra conclusions here are the exact scalar fibers, square determinant sign, and intrinsic symmetric shear computation.
