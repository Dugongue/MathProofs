# Linear refutation degree for equivalence of sparse cubic forms

**Theorem.** Fix a field of characteristic different from $2$ and $3$. There are pairs of non-equivalent homogeneous cubic forms in $N$ variables, each with $O(N)$ monomials, whose equivalence equations with a variable matrix and its inverse require polynomial calculus degree $\Omega(N)$. The matrices in the equations act through a single change of variables. Over $\mathbb R$ the same construction gives a sum-of-squares degree lower bound $\Omega(N)$. Over a fixed finite field the polynomial calculus bound also holds when the field equations are included.

The construction uses the companion graph encoding by symmetric trilinear forms. For each instance the group of linear symmetries is an explicit graph automorphism group times the same scalar group $F^\times$. Earlier work proved the linear lower bound for ordinary tensor isomorphism and used three independent changes of basis there. [Galesi–Grochow–Pitassi–She, Theorem 5.2 and the graph equations in §5](https://arxiv.org/html/2305.19320#S5)

## The sparse form and its witnesses

Take bounded-degree graphs $G,H$ on the same $n$ vertices with the linear degree lower bound of Berkholz and Grohe for their graph isomorphism equations. These are the source instances used in Theorem 5.2 just cited. The available lower bounds cover each field, and over the reals also sum of squares. [Berkholz–Grohe, *Limitations of Algebraic Approaches to Graph Isomorphism Testing*](https://arxiv.org/abs/1502.05912) · [Berkholz–Grohe, *Linear Diophantine Equations, Group CSPs, and Graph Isomorphism*](https://arxiv.org/abs/1607.04287)

For each graph add a root, its two tagged neighbors, and the two fixed paths of the companion proof. Call the resulting graph $X$ on $m=n+O(1)$ vertices. The extension has $O(n)$ edges since the only growing list of added edges is from the root to the old vertices. Attach to $X$ the cubic on $2m+1$ variables
$$
 f_X(x,z,h)=\sum_{i=1}^m z_i x_i^2
       +h\sum_{i,j=1}^m (A_X)_{ij}x_i x_j.
$$
Over the stated characteristic this is the diagonal evaluation divided by $3$ of the symmetric trilinear form proved in the companion construction. Polarization recovers that form from the cubic. Thus the cubic transporter projects onto the graph transporter, with exactly one free nonzero scalar. Nonisomorphic source graphs give non-equivalent forms. The number of monomials is $m+|E(X)|$. [Sparse graph tensor transporters](SparseGraphTensorTransporters.md)

## A constant-degree substitution

For two extended graphs $X,Y$, write the polynomial system in matrices $U,V$ imposing $UV=VU=I$ and the vanishing of every coefficient of $f_Y(Uw)-f_X(w)$. Here $w$ is a formal vector of ordinary cubic-form variables, whereas the proof variables are the entries of $U,V$.

Let $P$ denote the matrix of graph isomorphism variables from the original vertices of $G$ to those of $H$. Extend it by the identity on the added vertices to obtain $P_*=P\oplus I$. Put $B=P_*\oplus P_*\oplus 1$ on the three groups of variables $x,z,h$. Substitute $U=B$ and $V=B^{\mathsf T}$. Every entry is a graph variable or a constant.

All substituted equations have derivations of degree at most three from the graph isomorphism equations. For orthogonality $P^{\mathsf T}P=PP^{\mathsf T}=I$, an off-diagonal entry vanishes by the row and column incompatibility equations. A diagonal entry is $1$ by the Boolean and sum equations. The analogue for $B$ follows blockwise.

For the $h$-dependent term, the substituted coefficient equations follow from $P_*^{\mathsf T}A_Y P_*=A_X$. For original vertices $i,j$, the difference of the two entries can be written
$$
\sum_{u,v}\big((A_H)_{uv}-(A_G)_{ij}\big)P_{ui}P_{vj}
+(A_G)_{ij}\left(\Big(\sum_u P_{ui}\Big)\Big(\sum_v P_{vj}\Big)-1\right).
$$
The first sum uses only incompatible edge or nonedge pairs. The last term follows from column sums in degree two. For a cross term between an original vertex and an added vertex, adjacency to any one added vertex is constant across original vertices, so column sums again suffice. The added-to-added terms are fixed constants.

For the remaining term the substitution yields coefficients of the form $\sum_u(P_*)_{ui}(P_*)_{uj}(P_*)_{uk}$. If the three indices are different or only two match, each product contains two variables in the same row at different columns, or is a zero constant in an added block. If all indices match, apply $z^3-z=(z+1)(z^2-z)$ to each entry and use the column sum. This proves that the coefficient of $z_i x_j x_k$ is exactly the required one, with the usual factor for permuted $j,k$, using degree at most three.

Composition with a degree-$d$ polynomial calculus refutation of the cubic equations gives a graph refutation of degree at most $\max(d,3)$. Every input equation after substitution has the bounded-degree derivation just given, and multiplication by a variable in the target proof becomes multiplication by one variable or a constant. Over a fixed finite field the extra equations substitute to $z^q-z$ for a Boolean $z$, which is a multiple of $z^2-z$ with bounded degree depending only on the field. Over the reals the displayed derivations are identities writing each target equation as a bounded-degree combination of input equations. Substitution in a sum-of-squares certificate preserves squares, and replacing those entries by the graph identities raises the degree by at most a constant. The source lower bounds now give the claimed linear lower bounds in $N=2m+1$.

This is an informal proof. It uses graph instances with a fixed tag extension and sparse cubic forms with a single linear action.
