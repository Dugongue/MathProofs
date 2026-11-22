# Degree-constrained sum-of-squares tensor ranks

Let $x=(x_1,\ldots,x_n)$ be real variables. The separation rank of a polynomial is the least number of products of univariate polynomials whose sum is the polynomial. For integers $r,d\ge1$, let $C_{r,d}$ consist of the real polynomials of total degree at most $2d$ that are sums of squares of polynomials of separation rank at most $r$. Write $\overline C_{r,d}$ for its closure in this fixed coefficient space. Positivity of squares ensures that every square root in such a representation has total degree at most $d$. The degree constraint is thus on the ambient approximations, independently of the rank constraint on the square roots.

For a real positive semidefinite matrix $A$, its factor width is the least $k$ for which $A=\sum_j a_j a_j^{\mathsf T}$ with each $a_j$ supported on at most $k$ coordinates. Denote the corresponding cone by $\mathrm{FW}_k$, using $\mathrm{FW}_k=\mathrm{FW}_n$ for $k\ge n$. This is the established matrix invariant of Boman, Chen, Parekh and Toledo. [Factor width](https://doi.org/10.1016/j.laa.2005.03.029)

**Theorem.** For every $d\ge1$ and every real symmetric $A$,
$$
 x^{\mathsf T} A x\in C_{r,d}\quad\Longleftrightarrow\quad A\in\mathrm{FW}_r .
$$
For border membership the first three ranks are exact:
$$
 \{A:x^{\mathsf T}Ax\in\overline C_{1,d}\}=\mathrm{FW}_1,
 \qquad
 \boxed{\{A:x^{\mathsf T}Ax\in\overline C_{r,d}\}=\mathrm{FW}_{rd}\quad(r=2,3)} .
$$
More generally, for every $r\ge2$,
$$
 \mathrm{FW}_{rd}
 \;\subseteq\;\{A:x^{\mathsf T}Ax\in\overline C_{r,d}\}
 \;\subseteq\;\mathrm{FW}_{r(d+1)-1}.
$$
In particular, on the target $L^2$ for a linear form $L$ with $k$ nonzero coefficients, the exact sum-of-squares rank is $k$. The least permitted total approximation degree for border rank at most two is exactly $2\lceil k/2\rceil$ when $k\ge1$. At ranks two and three the theorem decides membership on the entire positive semidefinite quadratic slice by a finite semidefinite feasibility system on supports of size at most $\min(rd,n)$.

## Low total degree forces bounded variable support

A polynomial is multiaffine if each variable has individual degree at most one. Projecting in every variable onto its constant and linear coefficients is a tensor product of linear maps. This preserves the upper bound on separation rank, cannot increase total degree, and fixes a linear target.

Suppose a nonzero multiaffine polynomial $q$ of total degree at most $d$ is a sum of at most two products of affine one-variable factors. In a nonzero product, its active support consists of coordinates with a nonzero slope. Call the two supports $S,T$. If each has size at most $d$, the union has size at most $2d$. If $|S|>d$, the top squarefree monomial on $S$ must cancel, so $S\subseteq T$. The same argument for $T$ gives $S=T$. Absorb all slopes and inactive constants into scalars to write the expression as
$$
 c\prod_{i\in S}(x_i+b_i)+c'\prod_{i\in S}(x_i+b'_i).
$$
The top coefficient gives $c'=-c$. If $|S|\ge d+2$, the coefficients of the distinct degree-$(|S|-1)$ monomials each give $c(b_i-b'_i)=0$. Then the expression is zero. Thus $|S|\le d+1\le2d$. Every nonzero $q$ in question depends on at most $2d$ variables.

For three product terms, every inclusion-maximal support of size greater than $d$ must occur at least twice, since only a term with a containing support can cancel its top monomial. If every support has size at most $d$, their union has size at most $3d$. Otherwise choose a maximal repeated support $S$ of size greater than $d$. If exactly two terms have this support and the third support $T$ has size at most $d$, the pair has degree at most $d$ separately. It is either zero or uses at most $d+1$ variables by the two-term proof. The whole expression then uses at most $2d+1\le3d$ variables. If $T$ has size greater than $d$, it is a proper subset of $S$, since otherwise it would be another maximal large support occurring once. If $|S|\le d+1$, the support bound is immediate. For $|S|\ge d+2$, compare the top monomial and the monomials omitting a single variable. If $T$ misses at least two variables, none of these monomials occurs in the third term, so the two terms with support $S$ cancel. If $T$ misses just one variable $j$, the shifts in all positions except $j$ agree. Subtracting the two products with opposite leading coefficients leaves one product on $T$. In both cases the two-term result applies to what remains.

Finally, if all three terms have support $S$, it suffices to consider $|S|\ge d+3$. Write them as $\sum_{a=1}^3 c_a\prod_{i\in S}(x_i+b_{a,i})$. Put $v_i=(b_{a,i})_{a=1}^3$ and let $\lambda$ be the linear functional with coefficients $c_a$. Vanishing in the top three degrees gives $\lambda(\mathbf 1)=\lambda(v_i)=\lambda(v_i v_j)=0$ for all distinct $i,j$, with coordinatewise multiplication. Since $\lambda$ is nonzero, its kernel is spanned by $\mathbf 1$ and some $v$ independent of $\mathbf 1$. If $\lambda(v^2)=0$, this span is a subalgebra and contains all the squarefree products of the $v_i$. If $\lambda(v^2)\ne0$, writing $v_i=a_i\mathbf 1+b_i v$ gives $b_i b_j=0$ for $i\ne j$. At most one input vector has a nonzero $v$-coefficient, so again every squarefree product lies in the kernel. Either way the original polynomial is zero. Thus in the remaining case $|S|\le d+2\le3d$. In all cases a nonzero degree-$d$ multiaffine polynomial of separation rank three or less uses at most $3d$ variables.

A general support estimate uses the same polynomial space. Suppose $q\ne0$ has separation rank at most $r$, and let $s\le r$ be the number of its nonzero product terms in a chosen decomposition. Translate the variables by one real point where all nonzero affine factors have nonzero values and all nonzero first partial derivatives of $q$ have nonzero values. Such a point exists because a finite product of nonzero real polynomials is nonzero. Translation preserves total degree, separation rank and the set of active variables. Rename and order the $N$ active variables. Then
$$
 q=\sum_{a=1}^s\lambda_a\prod_{i=1}^N(1+z_{a,i}x_i),\qquad
 z_i=(z_{a,i})_{a=1}^s\in\mathbb R^s,\qquad \lambda(z_i)\ne0,
$$
where $\lambda$ is the functional with coefficients $\lambda_a$ and we multiply vectors coordinatewise. If inactive variables appear in any individual terms, first specialize them at the translation point and retain the same polynomial. For $0\le i\le N$ and $k\ge1$, let $W_{i,k}$ be the span of squarefree products of at least $k$ distinct $z_j$ with $j\le i$. The total degree bound gives $\lambda(W_{i,d+1})=0$.

For any $i$, some $W_{i,k}$ with $1\le k\le d+1$ grows strictly relative to $W_{i-1,k}$. Otherwise $z_i\in W_{i-1,1}$, and the inclusions $z_i W_{i-1,k}\subseteq W_{i-1,k+1}$ for $k\le d$ show $z_i^{d+1}\in W_{i-1,d+1}$. Also $z_i W_{i-1,d+1}\subseteq W_{i,d+1}=W_{i-1,d+1}$, so every higher power belongs to the same space. There is a real polynomial $P$ with $t^{d+1}P(t)=t$ on the finite set of coordinate values of $z_i$. Interpolate $P(t)=t^{-d}$ at the distinct nonzero values, and the equality at zero is automatic. Hence $z_i$ itself belongs to $W_{i-1,d+1}$, contradicting $\lambda(z_i)\ne0$. Starting with zero spaces, counting dimension increases gives
$$
 N\le \sum_{k=1}^{d+1}\dim W_{N,k}\le s(d+1)-1.
$$
A rank-one multiaffine polynomial of degree at most $d$ uses at most $d$ variables. For rank one converging to a homogeneous linear polynomial, the special rank-one closure argument below improves this to one variable.

## Passing from square roots to the quadratic slice

Write $V_d=\mathbb R[x]_{\le d}$, of dimension $M$. For a sequence of approximants $p_\nu\to x^{\mathsf T}Ax$ in $C_{r,d}$, normalize each nonzero square root in the norm $\|q\|^2=\int_{[-1,1]^n}q^2$, pulling its squared norm out as a nonnegative coefficient. The total coefficient weight is $\int p_\nu$ and stays bounded by coefficient convergence. Each representation uses a conic combination of at most $\dim V_{2d}$ normalized squares. To reduce to this length, whenever more squares are present, take a linear relation among them, orient it to have a positive coefficient, and subtract a maximal multiple of the relation while preserving nonnegative weights. At least one weight is removed. Reabsorb the bounded weights into the normalized roots, then pad to fixed length by zeros. By finite-dimensional compactness a subsequence converges simultaneously in $V_d$ to polynomials $q_j$ with $\sum_j q_j^2=x^{\mathsf T}Ax$.

Every $q_j$ is homogeneous linear or zero. Indeed a maximal root degree greater than one would produce a nonzero sum of squares in the top homogeneous degree, and evaluation at zero eliminates all constant terms. Project each sequence of roots onto multiaffine polynomials. This fixes the limit and preserves rank and total degree. For $r=2,3$, each projected root is supported on at most $rd$ variables by the preceding arguments. For general $r$ the bound is $r(d+1)-1$. The polynomials supported on at most any fixed number of variables form a finite union of closed linear spaces, so these same support bounds hold for the limiting homogeneous linear forms. Reading their coefficient vectors gives the desired factor-width upper bounds.

When $r=1$, the rank-one cone in the multiaffine coefficient space is closed, including zero. For example, write a nonzero decomposable tensor as a product of unit vectors times a coefficient, and use compactness of the product of unit spheres and the equality of that coefficient's absolute value with the tensor's Euclidean norm. A homogeneous linear polynomial that is a single product has at most one active factor, by additivity of total degree for nonzero products. Hence each limiting root at rank one is supported on at most one variable.

For exact membership, every root of the quadratic form is already homogeneous linear, by the same leading-degree and constant-term arguments. A homogeneous linear form supported on $k$ variables has separation rank $k$. To check the lower bound, apply the multiaffine projection and scale the active variables to reduce to $L=x_1+\cdots+x_k$. Its two slices in the first variable are $L'=x_2+\cdots+x_k$ and $1$. In an $s$-term product decomposition, some term has a nonzero slope in that first factor. Eliminate it by subtracting from $L'$ the corresponding scalar multiple of the slope slice. The resulting polynomial $L'-c$ has separation rank at most $s-1$ and the same rank as $L'$ by translation in one of its remaining active variables. Induction, starting with $k=1$, gives $s\ge k$. The converse follows by writing $L$ as the sum of its $k$ monomials. This proves the exact membership criterion.

## Constructing all approximations in the inner cone

Suppose $r\ge2$ and $L=\sum_i a_i x_i$ has at most $rd$ nonzero coefficients. Partition its support into $r$ sets $S_1,\dots,S_r$ of size at most $d$, allowing empty sets. Pick nonzero real $c_1,\dots,c_r$ with $\sum_j c_j=0$. For $t\ne0$, put
$$
 q_t=\frac1t\sum_{j=1}^r c_j\prod_{i\in S_j}(1+t a_i x_i/c_j).
$$
It has separation rank at most $r$, total degree at most $d$, and tends coefficientwise to $L$, by cancellation of the constant numerator and the explicit linear coefficient. For $A=\sum_j a_j a_j^{\mathsf T}$ in $\mathrm{FW}_{rd}$, approximate each linear form $a_j^{\mathsf T}x$ in this way and sum the squares. This proves the inner inclusion and equality at $r=2,3$. The case $r=1$ follows using exact diagonal squares.

As a rank-one positive semidefinite matrix, $aa^{\mathsf T}$ has factor width exactly the support size of $a$. For every rank-one positive summand in any decomposition its vector is proportional to $a$, as follows by testing any vector orthogonal to $a$. This proves the sharp total-degree threshold. As another example, for $n=9$ the form $(x_1+\cdots+x_9)^2$ requires degree 10 approximations at border rank two, while its exact rank remains 9.

## Research program

The object is the degree-indexed family $\overline C_{r,d}$, in which the number of product terms in a square root and the permitted degree of the approximation are measured separately. Prior work supplies the factor-width cone and the positive polynomial rank framework. The portfolio's earlier squared-linear-form example shows an unbounded gap under fixed individual degree. The theorem above finds the sharp total-degree threshold and identifies the entire quadratic slice at ranks two and three. [Positive polynomial ranks](https://arxiv.org/abs/2109.06680) · [Positive and invariant border ranks](https://arxiv.org/abs/2304.13478) · [Earlier squared-linear-form gap](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/PositivePolynomialBorderRank/Proof.md)

A concrete next problem asks whether $\mathrm{FW}_{rd}$ is the whole quadratic slice for every $r\ge4$. The proof above leaves at most $r-1$ coordinates between the two width bounds at every fixed $r,d$. A second question asks how coefficient accuracy constrains the sizes of the product coefficients in the construction. This is a written proof and makes no claim of established priority.
