# Algorithms for equations and exact degrees of Segre secants

Let $V_i=\mathbb C^{n_i}$ for $1\le i\le d$ and $N=\prod_i n_i$ be the number of tensor entries. Use the convention that $X_r$ is the projective variety of border rank at most $r$, and write its affine cone as $\widehat X_r$. Assume $r\ge1$ and $n_i\ge1$.

## GP-0221 — Deterministic equation generation at fixed rank

For each fixed $r$, the number of arithmetic operations and the rational bit complexity of producing a set of equations for $\widehat X_r$ are polynomial in $N+d$, including when $d$ grows. For fixed $r,d$ one can effectively precompute the bound and produce generators of the prime ideal over $\mathbb C$. For varying $d$ at fixed $r$ the statement is set-theoretic and the algorithm uses a single rank-dependent degree bound.

For every $j\le D$, construct the coefficient matrix of the homogeneous degree-$j$ pullback whose coordinate substitutions are
$$
 T_{u_1,\dots,u_d}\longmapsto \sum_{\ell=1}^r\prod_{i=1}^d a_{i,\ell,u_i}.
$$
The substitution parametrizes the rank-at-most-$r$ locus, which is dense in $\widehat X_r$. Thus its homogeneous kernel is exactly the relevant homogeneous piece of the vanishing ideal. There are $N^{O(D)}$ degree-$\le D$ source monomials and each expands into at most $r^D$ parameter monomials. Keep only the parameter monomials actually generated, each encoded by its list of at most $dD$ factor labels with multiplicities. This gives a coefficient matrix of polynomial size in the dense format plus the length of the dimension list for fixed $r,D$, using integers of height at most $r^D$. Factors of dimension one may be omitted after reading the dimension list, so the number of necessary factors is at most $1+\log_2 N$. Fraction-free elimination computes a basis of every kernel and gives polynomial output coefficient bit length by the minor bound. Return the corresponding polynomials, each as its explicit monomial expansion.

Draisma and Kuttler's Main Theorem I supplies a uniform set-theoretic degree bound $D(r)$ independent of format and number of tensor factors. Use that integer fixed once for the given $r$. The resulting algorithm works uniformly in all formats at that rank. This use of a fixed constant places no effectiveness bound on the dependence $r\mapsto D(r)$. [Draisma–Kuttler, Main Theorem I](https://arxiv.org/abs/1103.5336)

When $d$ too is fixed, compute a degree bound by elimination in dimension $r$ in every factor. The ideal of that capped-format secant is the elimination ideal of the equations identifying the tensor entries with the rank-$r$ parametrization above, so a Gröbner basis computes a finite generating set from $d,r$ alone. Landsberg and Weyman's Proposition 5.1 gives generators in all larger formats by inheritance of the capped generators and the $(r+1)$-minors defining the multilinear rank subspace variety. Thus the greater of $r+1$ and the maximum computed degree bounds ideal-generator degrees in every larger format. Smaller axes can be embedded in axes of dimension $r$. Restriction of the larger-format ideal along the embedding equals the smaller-format ideal, since any smaller-format equation lifts via the coordinate projection preserving border rank. The computed basis of all pieces up to the bound therefore generates the ideal. [Landsberg–Weyman, Proposition 5.1](https://arxiv.org/abs/math/0601452)

## GP-0223 — Deterministic exact degree at fixed rank and fixed order

For every fixed $r,d$, there is an algorithm to compute the projective degree of $X_r$ in time polynomial in $N$, using rational bit operations. This works for arbitrary unequal factor dimensions. The constants may depend on $r,d$, including when the small-format secant is defective.

### A proper birational parameter space

Write $s_i=\min(r,n_i,\prod_{j\ne i}n_j)$. This is the generic $i$-flattening rank on $\widehat X_r$. To attain the bound for one fixed mode $i$, choose $s_i$ terms of the rank parametrization with distinct basis vectors in mode $i$ and with distinct tensor products of basis vectors in the other modes. This gives a matrix of rank $s_i$. The locus attaining this rank is open nonempty, and the parameter space is irreducible, so the open loci meet for all modes. Every point of the secant has flattening ranks at most $s_i$ by the corresponding minor equations.

On $B=\prod_i\operatorname{Gr}(s_i,n_i)$, let $S_i$ be the tautological subbundles and $E=\bigotimes_i S_i$. In each fiber of $\mathbb P(E)$ impose the rank-$r$ secant variety for the fixed smaller format $(s_1,\dots,s_d)$. These fiber conditions glue to a closed subvariety $Y$, because the ideal is preserved by all changes of frame. The projection $Y\to X_r$ is proper and onto: extend each contraction support to dimension $s_i$ and project the big factors back to these extended subspaces. Projection preserves border rank, so the original tensor regarded in this smaller tensor product is a point of its secant. The inverse on the generic locus assigns the unique tuple of contraction support subspaces, and it is rational by the minor coordinates. Hence the projection is birational.

Let $h=c_1(\mathcal O_{\mathbb P(E)}(1))$ for lines in $E$, and let $t$ be the projective dimension of the capped secant and $m=\dim B+t=\dim Y$. The pullback of the original projective hyperplane is $h$. Consequently $\deg X_r=\int_{\mathbb P(E)}h^m[Y]$.

### Computing the cycle class once in each capped format

Let $x_{i,j}$ be formal Chern roots of $S_i^\vee$, and put $w_{\alpha}=\sum_i x_{i,\alpha_i}$ for a tensor coordinate $\alpha$ of the capped format. A polynomial $Q(h,x)$ representing $[Y]$ can be computed in fixed size from the capped format as follows. Eliminate the secant parametrization to get its homogeneous ideal $I$, and take a coordinate Gröbner degeneration to its monomial initial ideal. The ideal $I$ is multigraded by the diagonal tori of all factors and by common degree. An initial-ideal degeneration can therefore be taken equivariant for this multigrading, so it preserves the torus-equivariant cycle class. Decompose the top-dimensional components of the monomial initial ideal as coordinate subspaces $T_\alpha=0$ for sets $J$ of coordinates, with their cycle multiplicities $m_J$. Their equivariant classes in the projective tensor space give the polynomial
$$
 Q(h,x)=\sum_J m_J\prod_{\alpha\in J}(h-w_\alpha).
$$
Each linear factor is the divisor class of one projected tautological line section, a section of $\mathcal O(1)\otimes\bigotimes_i L_{i,\alpha_i}$ when the tautological bundles split into lines $L_{i,j}$. This calculation applies over the base $B$ by the splitting principle: pull back to the complete flag bundles and then to the affine bundles of splittings, where the line weights and torus-equivariant family are realized. Pullback on Chow rings in this process is injective. For integration one may symmetrize the resulting root polynomial within each factor over the rationals, since permutations of the line summands preserve the same equivariant class. All these Gröbner, multiplicity and dimension calculations take only constant work once $d,r$ are fixed. [Equivariant multidegrees from Gröbner degeneration](https://arxiv.org/abs/math/0110058)

### Computing the remaining intersection number in polynomial time

Set $e=\operatorname{rank}(E)=\prod_i s_i$. The projective bundle pushforward of $h^j$ is zero for $j<e-1$ and for $j=e-1+\ell$ it is
$$
 [z^\ell]\prod_\alpha(1-w_\alpha z)^{-1}.
$$
This is the Segre class formula, using Chern roots $-w_\alpha$ of $E$. Apply it term by term to $h^m Q(h,x)$. For each Grassmannian $\operatorname{Gr}(s,n)$ with dual tautological roots $x_1,\dots,x_s$, integration of a symmetric top-degree class $f$ is given by
$$
 [x_1^{n-1}x_2^{n-2}\cdots x_s^{n-s}]\ f(x)\prod_{u<v}(x_u-x_v).
$$
It is the usual coefficient formula for Grassmannian integration, obtained by evaluation in the Schur basis and identifying the top Schur rectangle. Use a separate Vandermonde and coefficient extraction for each factor. [Grassmannian integration via Chern roots](https://arxiv.org/abs/1607.04850)

There are at most $dr$ root variables and $r^d$ linear forms in the Segre product. The largest truncation degree is $O_{r,d}(\sum_i n_i)$. Expanding these bounded-variable polynomial products to the required degree takes polynomially many rational operations. Coefficient lengths are polynomial in the same parameters, for example by bounding the sum of absolute coefficients of each power of each fixed linear form and counting the resulting compositions. This gives the deterministic bit bound. The argument does not give a polynomial algorithm uniform in growing tensor order, since the capped Gröbner calculations then grow.

The fixed-format proof also extends the use of contraction supports in the prior concise-secant notes from membership comparisons to degree computation. [Catalogue context](https://arxiv.org/html/2604.24879) · [Prior concise degeneration notes](https://github.com/Dugongue/MathProofs/tree/d7366c4348bc03f0e93cb8674db191de32ba58bf/ConciseTensorDegenerationDepth)
