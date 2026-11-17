# Determinant constraints from Frobenius forms on singular pencils

Fix an odd finite field $F=\mathbb F_q$, with $M=q-1$. Use the usual covariant action of three general linear groups on a tensor of format $(r+1,N,N)$. Assume $r$ is positive and divisible by $2M$ and $\gcd(N,M)=1$. Let $Q=q^j$ for an integer $j\ge1$, $d=Q+1$, and $K=N-d>d$. Contract in the first mode and write the determinant polynomial of the resulting square matrix pencil as $f(x)$, with $x$ in the dual of the first mode. Consider the following promise on the raw source tensor:
$$
 f(x)=z(x)^K P(x),\qquad P(x)=(x^{[Q]})^{\mathsf T}B x,\qquad z\ne0 .
$$
Here $z$ is an $F$-linear form and $x^{[Q]}$ denotes coordinatewise $Q$-th powers. The alternating part $B-B^{\mathsf T}$ restricts to a nonsingular form on $H=\ker z$. The exponent $j$, the matrix $B$, the factor $z$ and any reference frames are recovered from the raw input.

**Theorem.** Under the stated promise, testing for any prescribed determinant triple is deterministically polynomial-time many-one reducible to ordinary TI over $F$. There is no bound on the degree of $P$, and no hypothesis that a contraction at an $F$-point is invertible. The target tensor may be arbitrary if the source satisfies the promise.

## 1. Recover the factor and form without general multivariate factoring

Work temporarily in an explicit extension $E/F$ with $N+2<|E|\le q(N+3)$. For fixed $F$ this is constructible in polynomial time by enumerating polynomials of the required degree and using irreducibility tests. It is used for arithmetic only. All final markers are over $F$.

At least one restriction of $P$ to a coordinate plane of dimension at most two is a nonzero polynomial because every monomial uses at most two variables. Adjoin one coordinate on which $z$ is nonzero. Consequently $f=z^KP$ restricts nontrivially on some coordinate subspace of dimension at most three. Try all such subspaces and all points of $E$ in their at most three coordinates, evaluating the original determinant. Since the per-variable degree is at most $N<|E|$, a nonzero restriction has a nonzero evaluation. Obtain a point $v$ with $f(v)\ne0$, so $z(v)\ne0$.

For every coordinate $i$, interpolate the univariate polynomial $f(v+t e_i)$ of degree at most $N$ by determinant evaluations. A root of multiplicity greater than $N/2$ exists precisely when $z(e_i)\ne0$, and in that case it is the unique root $-z(v)/z(e_i)$ of the linear factor restricted to the line. The remaining polynomial has degree at most $d$. Find the root by checking the field elements and computing exact univariate divisibility. Thus recover every ratio $z(e_i)/z(v)$, taking zero if no such root appears. Normalize with respect to a nonzero coefficient and absorb the resulting nonzero constant into $P$. The recovered $z$ is over $F$. This also proves that its line is intrinsic: it is the unique irreducible factor of multiplicity greater than $N/2$ in $f$.

To recover $K$ itself, use an $F$-basis of $H=\ker z$ and test all points $u$ of $E$ supported on at most two of those basis vectors. The restriction of $P$ to $H$ is a formal Frobenius form whose matrix has nonzero alternating part. Thus it is a nonzero polynomial, with a nonzero evaluation among these points by the same interpolation argument. Interpolate $f(u+t v)$ for every tested $u$ and take the least order at $t=0$ among the nonzero restrictions. Every restriction is divisible by $t^K$, while for a point with $P(u)\ne0$ the order is exactly $K$. This recovers $K$, then $d=N-K$ and $Q=d-1$. Reject on the target if the exponents differ from the source or are incompatible with the promise.
For each desired $w$, evaluate $P(w)$ as $f(w)/z(w)^K$ when $z(w)\ne0$. Otherwise evaluate this quotient at sufficiently many points on $w+t v$ and interpolate the degree-at-most-$d$ polynomial whose value at $t=0$ is desired. There is at most one unusable parameter. Recover $B_{ii}$ from $P(e_i)$ and the two ordered off-diagonal entries from the coefficients of $t^Q$ and $t$ in $P(t e_i+e_k)$ for $i\ne k$. These two coefficients are distinct because $Q>1$. Every indicated evaluation and interpolation uses polynomial time. On the source promise these computations recover the exact raw form. The target side rejects a failed operation, a result outside $F$, or a degenerate restriction of the alternating part. An ordinarily equivalent target satisfies the same promise and so passes all these checks. In the converse direction every output isomorphism still satisfies the original tensor equations.

## 2. Convert one factor scale to the full determinant triple

For a genuine ordinary transporter $(g_1,g_2,g_3)$ let $s=g_1^{-\mathsf T}$ be the map on first-mode contraction data, and let $c=\det g_2\det g_3$. The contraction identity gives
$$
 f_S(sx)=c f_T(x).
$$
Uniqueness of the high-multiplicity factor gives $z_Ss=a z_T$ for a scalar $a\in F^\times$. Dividing the polynomial identity by $z_T^K$ gives $P_S(sx)=bP_T(x)$ for $b=c/a^K$. Since $Q$ is a power of $q$, $s^{[Q]}=s$ for every matrix over $F$. Coefficient comparison therefore gives
$$
 s^{\mathsf T}B_Ss=b B_T.
$$
This is an exact relation for a bilinear form encoded by a high-degree polynomial, even if that polynomial vanishes at every base-field point.

Choose ordered bases of $H_T,H_S$, followed by a vector on which the respective $z$ equals one, and let $C_T,C_S$ be the associated frame matrices. Write $A_T,A_S$ for the restrictions of the alternating parts to these bases of the hyperplanes. The Pfaffian identity gives
$$
 \det(s|_{H_T})=b^{r/2}\,\frac{\operatorname{Pf}(A_T)}{\operatorname{Pf}(A_S)}.
$$
Here $s|_{H_T}$ uses the two chosen hyperplane bases. The factor $b^{r/2}$ is one because $M\mid r/2$. Put
$$
 \eta=\frac{\det C_S}{\det C_T}\frac{\operatorname{Pf}(A_T)}{\operatorname{Pf}(A_S)}.
$$
In the original bases, $\det s=\eta a$. Thus a prescribed determinant triple $(\delta_1,\delta_2,\delta_3)$ gives the two fixed target scales
$$
       a=\delta_1^{-1}/\eta,\qquad b=\delta_2\delta_3/a^K.
$$

Attach to the original tensors the labeled linear-form relation $z_S s=a z_T$ and the labeled bilinear relation $B_S(sx,sy)=bB_T(x,y)$, using the same first-mode dual map in both. A determinant-constrained transporter extends. Conversely an isomorphism of this system is an original transporter with $\det g_1=\delta_1$ and $\det g_2\det g_3=\delta_2\delta_3$. Indeed the relations give $a,b$ on the actual map and the nonzero polynomial $P$ determines its scale. Multiplying the second and third mode maps by $\lambda$ and $\lambda^{-1}$ preserves the source tensor and its first-mode marks. Since $\gcd(N,M)=1$, some $\lambda$ corrects the second determinant, after which the third is correct as well. This proves equivalence. The typed tensor-system compiler takes the constant number of original, dual, linear and bilinear sorts to one ordinary 3-TI instance over $F$. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

## 3. Explicit growing family with every rational slice singular

Choose any $r$ divisible by $2M$ and any $j\ge1$, and use $r$ variables $x_i$ and one more variable $z$. Put
$$
 P(x)=\sum_{i=1}^{r/2}(x_{2i-1}^Q x_{2i}-x_{2i}^Q x_{2i-1}).
$$
The matrix of this Frobenius form on the first $r$ coordinates is the standard alternating matrix, so its alternating part is twice that matrix and nonsingular. The polynomial is nonzero formally and vanishes at all $F$-points.

Here is an explicit pencil. Use a directed acyclic graph with a source $s_0$, a sink $t_0$, and one internally disjoint path of length $d$ for each of the $r$ signed monomials. Assign variables, with the sign on one edge, so the product on a path is its monomial. Let $D$ be the vertex count and $A(x)$ the adjacency matrix in topological order, with rows indexed by tails. The matrix
$$
 \begin{pmatrix} zI_D-A(x)&z e_{t_0}\\ z e_{s_0}^{\mathsf T}&0\end{pmatrix}
$$
has determinant $-z^{D+1-d}P(x)$. Indeed $A(x)$ is strictly triangular and its powers count paths. Over the fraction field use the inverse of $zI_D-A(x)$ as a finite nilpotent geometric series and take the Schur complement. Polynomial equality then holds. Add a diagonal block of copies of $z$ so that the final side $N$ satisfies $N>2d$ and $N\equiv1\bmod M$. The additional length is polynomial in $r,d$. A sign in front of $P$ is immaterial and is included in the recovered $B$.

This pencil is concise: the label slices are independent because $z$ has diagonal entries and every $x_i$ occurs at private path edges, while a generically invertible evaluated slice implies full support in the two matrix modes. On any base-field label vector its determinant is zero. The argument above applies to arbitrary raw rebasings. Taking both $r$ and $j$ to infinity gives a family with all mode dimensions and the degree of the non-linear factor unbounded. These formats can be far from balanced.

Frobenius forms and the algebraic Pfaffian identity are classical. The construction uses a high-multiplicity hyperplane to isolate the form by bounded-support determinant evaluations, then retains the alternating form on the hyperplane to read the sign or base-field determinant. This differs from the bounded-degree quadratic polar form route: there is no bound on the factor degree and every base-field contraction may be singular. This is a sufficient raw-pencil theorem and leaves general balanced tensors open. [Frobenius forms](https://arxiv.org/abs/2009.13679) · [Grochow–Qiao, partitioned TI](https://arxiv.org/html/2306.16317)
