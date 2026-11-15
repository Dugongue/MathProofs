# Exact degree amplification and the sharp rank bound for inversion

Informal proof. Nonlinear polynomial substitutions whose leading forms are a regular sequence exactly preserve weighted Polynomial Calculus and Nullstellensatz degree. Pure-power substitutions also preserve sparse lower bounds. This gives an all-field sharpness family for the companion rank-sensitive inversion simulation.

## 1. Exact degree under nonlinear polynomial substitutions

Let $F$ be a field, let $x=(x_1,\ldots,x_N)$ and $y=(y_1,\ldots,y_m)$, and let $\phi_i(x)$ have positive total degree $w_i$ for $1\le i\le m$. Suppose their highest-degree homogeneous parts $g_1,\ldots,g_m$ form a regular sequence in $F[x]$. Thus multiplication by $g_i$ is injective modulo the preceding $g_j$. Write $\Phi$ for substitution $y_i\mapsto\phi_i(x)$, and give $y_i$ weight $w_i$.

**Theorem.** For any finite set of axioms $f_i(y)=0$ and any target $h(y)=0$, the least ordinary Polynomial Calculus degree for deriving $\Phi(h)=0$ from the $\Phi(f_i)=0$ equals the least weighted Polynomial Calculus degree for deriving $h=0$ from the $f_i=0$. The same equality holds for Nullstellensatz, with certificate degree of $\sum_i a_i f_i=h$ defined as the greatest degree among its nonzero products $a_i f_i$. An impossible derivation has degree $+\infty$. If $m=N$, the substitution defines a finite free map of rank $\prod_i w_i$. Every point over the algebraic closure has a preimage, so the new equations have the same geometric satisfiability as the original equations. The theorem applies over every field. It includes field or Boolean equations when those are among the named axioms and undergo the same substitution.

### A filtered free basis

Choose homogeneous representatives $b_\lambda(x)$ of a homogeneous vector-space basis of $F[x]/(g_1,\ldots,g_m)$, including $b_0=1$. Write $e_\lambda=\deg b_\lambda$. Degree induction shows that the products $b_\lambda g_1^{a_1}\cdots g_m^{a_m}$ span $F[x]$. A homogeneous polynomial is a linear combination of representatives plus $\sum_i g_i p_i$, with each homogeneous $p_i$ of strictly smaller degree. The graded vector space with formal basis symbols $b_\lambda y^a$ has the same Hilbert series as $F[x]$. The regular-sequence exact sequences give
$$
H_{F[x]/(g_1,\ldots,g_m)}(z)
=\frac{\prod_i(1-z^{w_i})}{(1-z)^N},
$$
and adjoining the formal $y$ variables divides that series by $\prod_i(1-z^{w_i})$. The spanning map $b_\lambda y^a\mapsto b_\lambda g^a$ is therefore an isomorphism in each degree.

Substitute $\phi_i$ for $g_i$ in these products. The top homogeneous part of $b_\lambda\phi^a$ is $b_\lambda g^a$. These top parts form a homogeneous basis. Successively subtracting top-degree terms therefore gives a unique expansion
$$
P(x)=\sum_\lambda b_\lambda(x)\,\Phi(P_\lambda(y)),
\qquad
\deg P=\max_{\lambda:P_\lambda\ne0}\bigl(e_\lambda+\deg_w P_\lambda\bigr).
$$
All sums for individual polynomials are finite, even if the quotient basis is infinite. In particular $\Phi$ is injective and $\deg\Phi(f)=\deg_w f$ for nonzero $f$. For $m=N$, the quotient basis has cardinality $\prod_i w_i$ by the Hilbert series. The display gives a free basis over $F[y]$. After extending scalars to an algebraic closure and setting $y$ equal to a point, the resulting nonzero algebra is the fiber algebra. The weak Nullstellensatz gives a point in each fiber.

### Transport of derivations

Forward transport substitutes $\phi_i$ into every line of a weighted proof. A multiplication by $y_i$ becomes multiplication by $\phi_i$. Expand $\phi_i$ into monomials and use variable multiplications and linear combinations. Every intermediate line has degree at most the weight of the original multiplied line because all terms of $\phi_i$ have degree at most $w_i$.

For reverse transport, expand each proof line into the basis above and derive its coefficient polynomials. A pulled-back axiom has only the $b_0$ coefficient. For a linear combination, coefficient extraction commutes with the combination. Let the next line be $x_jP$. Define $c_{\mu\lambda}(y)$ by
$$
x_j b_\lambda(x)=\sum_\mu b_\mu(x)\,\Phi(c_{\mu\lambda}(y)).
$$
The normal form gives $\deg_w c_{\mu\lambda}\le 1+e_\lambda-e_\mu$ for nonzero coefficients. Thus every product $c_{\mu\lambda}P_\lambda$ in the new $b_\mu$ coefficient has weighted degree at most $1+\deg P-e_\mu$. Derive the products by variable multiplication and linear combination. Since a nonzero $P$ satisfies $\deg(x_j P)=1+\deg P$, the original line's degree bounds every intermediate weighted line. Zero coefficients may be omitted, with a reusable zero line available by a zero linear combination if needed. The last $b_0$ coefficient of $\Phi(h)$ is $h$. This proves equality of minimum PC degrees.

For Nullstellensatz, forward transport substitutes. For reverse transport take the coefficient of $b_0$ in $\sum_i A_i(x)\Phi(f_i)=\Phi(h)$. This gives $\sum_i (A_i)_0(y)f_i=h$. Every weighted product has degree at most its original total degree since $\deg_w (A_i)_0\le\deg A_i$ and $\deg\Phi(f_i)=\deg_w f_i$. This proves equality of minimum Nullstellensatz degrees.

## 2. Sparse size under pure powers

For $\phi_i=x_i^{w_i}$ and $m=N$, the basis consists of $b_\rho=x^\rho$ with $0\le\rho_i<w_i$. The coefficient supports come from partitioning the monomials of $P$ by their exponent residues and stripping the residues. The sum of their cardinalities is exactly the number of nonzero monomials of $P$. Multiplication by $x_j$ takes each coefficient to a unique new residue, multiplying it by $y_j$ precisely on a carry. Each nonzero new coefficient needs at most one PC line. Linear combinations also use at most one line per nonzero new coefficient. Reverse transport has sparse size at most that of the given pulled-back proof. Forward transport chains $w_i$ multiplications by $x_i$ for a multiplication by $y_i$, so sparse size grows by at most $\max_i w_i$. These counts measure nonzero monomials summed over proof lines and exclude the bits used to write exponents. The degree result for general substitutions is independent of sparse size.

## 3. Both parameters in the inversion simulation are necessary

The companion simulation of the Inversion Rule bounds the ordinary PC degree of an inversion by $(t+1)(a+b)$, with $t=\operatorname{rank}_{F(x)}(AB-I)$, $a=\max_{ij}\deg A_{ij}$ and $b=\max_{ij}\deg B_{ij}$. The following family attains the order of growth jointly in rank and degree.

Fix integers $t\ge2$ and $D\ge1$. Start from the rank principle $XY=I_t$ with $X$ of size $t\times(t-1)$, $Y$ of size $(t-1)\times t$, and distinct variables in every entry. Theorem 3.5 of Galesi, Grochow, Pitassi and She gives ordinary PC refutation degree at least $(t-1)/2+1$ over every field, including the version without Boolean axioms. Raise each variable to the $D$th power and call the resulting matrices $X_D,Y_D$. The exact degree transfer gives a lower bound of $D((t-1)/2+1)$ for $X_DY_D=I_t$. [Rank principle and its PC lower bound](https://arxiv.org/html/2305.19320#S3.SS3)

Extend to square matrices $A=[X_D\ 0]$ and $B=[Y_D;0]$ of side $t$. Their premise matrix is $X_DY_D-I_t$. Its determinant at the all-zero assignment is $(-1)^t$, so its rank over the rational function field is $t$. Both annotation entry degrees are $D$. A single inversion gives the $(t,t)$ entry of $BA-I_t$, the constant $-1$, and rescaling concludes the degree-$2D$ refutation. The entries in the annotations are individual monomials or zero. Padding both matrices by identity blocks gives any ambient side at least $t$ with the same nonzero premises, rank and degrees.

This proves that the ordinary PC degree can grow as $\Omega(tD)$ for a single inversion with annotation degrees $D$, premise rank $t$, and proof-line degree $2D$. The underlying rank principle and its PC lower bound are prior. The transfer proves the joint sharpness of the two parameters and works even when $D$ is divisible by the characteristic. Publication priority for the extensions here is unestablished. [Published Inversion Rule](https://arxiv.org/html/2305.19320#S2.SS3)

## 4. Exact finite controls

Take the axioms $y_1y_2-1$, $y_1^2$, $y_2^2$ with weights $(2,3)$. Degree-bounded span saturation by Gaussian elimination gave minimum degree $7$ over each of $\mathbb F_2,\mathbb F_3,\mathbb F_5$. The pulled-back ordinary minimum was $7$ in all nine combinations of these fields and the maps $(x_1^2,x_2^3)$, $(x_1^2+x_2,x_2^3+x_1x_2+1)$ and $(x_1^2+x_1x_2+1,x_2^3+x_1)$. In the last map the leading forms are a coupled regular sequence since their only common affine zero over the algebraic closure is the origin. These controls used formal polynomials and the named axioms.
