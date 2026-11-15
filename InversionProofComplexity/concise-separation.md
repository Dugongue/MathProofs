# An exponential proof-size separation on concise multiplication tensors

**Theorem.** Fix a prime $p$. Over every field of characteristic $p$, for every sufficiently large $n$ there are explicit $0$–$1$ tensors $T,T'$ in $F^{n\times n\times n}$, each the multiplication tensor of a split semisimple unital associative algebra, with the following properties.

- Every mode flattening of each tensor has rank $n$.
- The standard ordinary Polynomial Calculus (PC) equations for their isomorphism require degree $\Omega_p(n)$ and sparse size $2^{\Omega_p(n)}$. Sparse size counts monomial occurrences in the proof.
- The same equations have polynomial-size PC+INV refutations of degree at most five. There is exactly one inversion inference and all its matrix entries belong to $\{0\}$ or are original variables. This size bound includes all annotation entries and premise references.

The upper bound and nonisomorphism hold over every field. The lower bound includes the variant with field equations over each fixed finite field. The proof combines the rectangular bijection reduction with an obstruction intrinsic to the algebras, and uses the inversion rule from [Galesi–Grochow–Pitassi–She, §2.3](https://arxiv.org/html/2305.19320#S2.SS3).

## The tensor family

Choose a power $q=p^a\ge3$ and put $r=4q$, $s=3q$. The two algebras are
$$
 A=M_2(F)^r\times F^{4s}\times F^h,\qquad
 B=M_2(F)^s\times F^{4r}\times F^h,
 \qquad n=4(r+s)+h.
$$
Organize the $F^{4s}$ and $F^{4r}$ parts into groups of four scalar factors for the basis. Use the four matrix units on each matrix factor and the coordinate idempotents on the scalar factors. Let $T,T'$ encode multiplication in these bases, in the input-dual, input-dual, output convention. The coefficients are all $0$ or $1$.

Surjectivity of multiplication, from $a=a1$, proves full output support. In either input mode, a vector whose partial multiplication is identically zero must vanish by evaluating at the unit on the other side. Thus both input flattenings are full as well.

The standard equations use three invertible matrices $G_i$ with inverse variables and the usual cubic tensor action. Write $X=G_1^{-\mathsf T}$, $Y=G_2^{-\mathsf T}$ and $Z=G_3$, with inverse notation denoting original inverse variables. In these coordinates, the action equations imply
$$
 Z(ab)=X(a)Y(b)
$$
for source basis elements $a,b$. Indeed the original equations read $Z(X^{-1}(c)Y^{-1}(d))=cd$ on target vectors. Multiply coefficientwise by the entries of $X$ and $Y$ and sum, then apply the two inverse identities. This is an ordinary-PC derivation of degree at most five. The identity extends linearly to all fixed source vectors $a,b$ without changing that bound. Here and below a product by a polynomial of bounded degree means repeated PC variable multiplication for its monomials, followed by linear combinations. Each indexed sum and each such bounded-degree polynomial has only polynomially many terms in $n$. All derivations expand into polynomial sparse size.

## An explicitly annotated single inversion

Take a scalar-factor projection $\lambda\colon B\to F$. Put $x_a=\lambda X(a)$, $y_a=\lambda Y(a)$, $z_a=\lambda Z(a)$, $\alpha=x_{1_A}$ and $\beta=y_{1_A}$. The isotopy equations give
$$
 z_{ab}=x_a y_b,\qquad z_a=\alpha y_a=x_a\beta
$$
for all fixed $a,b$. Both $\alpha$ and $\beta$ have polynomial inverse witnesses of degree two. With $L_u$ and $R_v$ denoting multiplication by $u=X(1_A)$ and $v=Y(1_A)$ on the indicated side, the unit substitutions give $Z=L_uY=R_vX$. Right multiplication by $Z^{-1}$ and evaluation at $1_B$ give
$$
 u\,Y Z^{-1}(1_B)=1_B,\qquad X Z^{-1}(1_B)\,v=1_B.
$$
These lines are derived in degree at most three. Applying $\lambda$ gives $\alpha\alpha'=1$, $\beta\beta'=1$, with $\deg \alpha',\deg \beta'\le2$.

In ordinary PC of degree at most four, multiply $z_{ab}-x_ay_b$ by $\alpha\beta$, and replace $x_a\beta$ and $\alpha y_b$ by $z_a,z_b$. Subtracting the result for $(b,a)$ yields
$$
 \alpha\beta(z_{ab}-z_{ba})=0.
$$
Multiply the degree-three line by $\alpha'$ and use $\alpha\alpha'=1$ to derive the simplified degree-two line $\beta(z_{ab}-z_{ba})=0$, with intermediate degree at most five. Multiply that line by $\beta'$ and use $\beta\beta'=1$ to derive $z_{ab}-z_{ba}=0$ in degree at most four. In particular, $z_{E_{12}}=z_{E_{21}}=0$ on every source matrix factor, by the commutators $[E_{11},E_{12}]$ and $[E_{22},E_{21}]$. Use $z_{E_{ij}}=x_{E_{ij}}\beta$ and the inverse of $\beta$ to obtain $x_{E_{12}}=x_{E_{21}}=0$. Finally $E_{11}=E_{12}E_{21}$ and $E_{22}=E_{21}E_{12}$ give $z_{E_{11}}=z_{E_{22}}=0$. These operations have degree at most four once the off-diagonal vanishing is available.

Thus $Z$ sends the full $4r$-dimensional matrix-factor coordinate subspace of $A$ into the $4s$-dimensional matrix-factor coordinate subspace of $B$. This holds simultaneously for all scalar target coordinates, including the $h$ common ones. Put $P$ equal to the $4s\times4r$ submatrix of $Z$ between those subspaces and $Q$ equal to the reverse $4r\times4s$ submatrix of $Z^{-1}$. Deleting the terms containing the proved zero entries in $Z^{-1}Z=I_n$ yields $QP=I_{4r}$ in degree two. This also proves nonisomorphism over every extension by the ordinary rank inequality.

Use the single inversion inference with side $4r$ and matrices
$$
 A_0=[\,Q\mid 0\,],\qquad
 B_0=\begin{bmatrix}P\\0\end{bmatrix}.
$$
All premise entries of $A_0B_0-I_{4r}$ are the derived $QP-I_{4r}$ entries. On any diagonal position beyond $4s$, the selected entry of $B_0A_0-I_{4r}$ is $-1$. Rescale to $1$. Each matrix is explicitly written with $O(n^2)$ entries and the rule references $O(n^2)$ premises. All entries are zero or original variables, including those of $Z^{-1}$.

## The sparse lower bound for the same inputs

Let $B_{r,s}$ be the rectangular bijection equations with variables $u_{ij}$, row and column sums $1$, Boolean equations, and row and column collision equations. Use $U=(u_{ij})$ of size $r\times s$. Substitute into each of the three action matrices the same block diagonal matrix
$$
 W=\operatorname{diag}(U^{\mathsf T}\otimes I_4, U\otimes I_4, I_h),
$$
where the rectangular block rows and columns follow the respective target and source order. Substitute $W^{\mathsf T}$ into each inverse matrix. Every substituted variable becomes $0$, $1$, or one $u_{ij}$.

The projected two-sided inverse equations are the equations for $U^{\mathsf T}U=I_s$ or $UU^{\mathsf T}=I_r$, duplicated in same-coordinate entries. Their off-diagonal equations are sums of collisions, and their diagonal equations follow from Boolean and sum axioms in degree two. For an action coefficient, all three input indices in a nonzero source tensor entry refer to the same algebra copy, so the output coefficient is zero unless all three target indices match that source block type. For a fixed type and fixed inner coordinates, the coefficient is the common multiplication coefficient, multiplied by a sum of products of three $u$ entries. If target copy indices differ, each term has a collision. If all three copies agree, the cubes sum to one by a row or column sum and $u^3-u=(u+1)(u^2-u)$. Common scalar copies have identity substitution and their equations vanish. This gives every projected tensor action axiom in degree three and total polynomial size. A field equation $z^{|F|}-z=0$ substitutes to zero or a polynomial multiple of $u^2-u$ in degree $|F|$.

This projection never increases the number of monomial occurrences on a proof line. Simulate the projected axioms once and replay the proof. A sparse proof of size $S$ would therefore give a sparse refutation of $B_{r,s}$ of size $S+\operatorname{poly}(n)$, with at most a fixed additive degree bound from the projected axioms.

Here is the rectangle lower bound used in this argument. By [Riis, Lemma 14.1](https://arxiv.org/html/2611.07280v1), the transpose of $B_{3q,2q}$ has no PC refutation of degree at most $q-1$. Randomly choose $q$ distinct rows of the $4q\times3q$ rectangle and match them uniformly injectively into the columns. Set the matched entries to one and the other entries touching matched rows or columns to zero. The unrestricted rows and columns give the $3q\times2q$ rectangle. Quotient by the Boolean and collision axioms on the remaining variables. Its monomial normal forms are squarefree partial matchings and zero.

A partial matching monomial of support size $k$ can survive only if its $K$ chosen rows are all assigned the prescribed partners. Conditional on the selected rows, this has probability at most $b^K$ with $b=1/(2q+1)$. If $I_i$ denotes nonselection of the $i$-th row in the support, the probability that a fixed set of $j$ support rows is unselected is at most $(3/4)^j$. Expanding the nonnegative product gives
$$
 \mathbb E b^K=\mathbb E\prod_{i=1}^k(b+(1-b)I_i)
 \le (b+(1-b)3/4)^k\le(5/6)^k.
$$
A monomial containing a collision always vanishes after restriction and normalization. With fewer than $(6/5)^{q-1}$ monomial occurrences, some outcome kills every nonzero normal-form monomial originally of support at least $q-1$. Powers reduce to their support. The normalized proof has degree at most $q-2$. It simulates in ordinary PC with degree at most $q-1$: after each variable multiplication expand the product, reduce collisions by subtracting monomial multiples of collision axioms and squares by multiples of Boolean axioms. All terms before reduction have degree at most $q-1$. This contradicts the cited rectangle obstruction. The degree lower bound on the starting rectangle follows directly from the same lemma, with dimensions $3q,4q$.

For arbitrary sufficiently large $n$, choose the largest power $q$ of $p$ with $28q\le n$ and set $h=n-28q$. Then $q>n/(28p)$ and the stated bounds follow.

## Scope and attribution

The single inversion has a synthetic rank-deficient right factor, following the principle behind [Galesi–Grochow–Pitassi–She, §3.2](https://arxiv.org/html/2305.19320#S3.SS2). The earlier [MathProofs sparse-size argument](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/Proof.md) supplies the rectangle restriction and diagonal-instance projection. The construction here uses full-support multiplication tensors and the polynomial derivation of the matrix-factor support obstruction from the bare tensor equations. Compare the separate diagonal CP-rank lower bounds in [Meta-Mathematics of Algebraic Complexity](https://arxiv.org/abs/2610.33938). The lower bound here is for ordinary PC and counts sparse monomials, while the PC+INV upper bound charges its matrix entries.

This is an informal proof. Publication priority for the concise separation remains unestablished.
