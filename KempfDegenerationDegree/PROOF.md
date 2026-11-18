# Exponential Laurent degree for stable degenerations of sparse forms

Grochow, Mulmuley, and Qiao's Question 4.5 has an affirmative answer over the complex numbers. An explicit family in VP on $m+1$ variables has a stable degeneration for which every one-parameter subgroup reaching the closed orbit has eigenweight diameter at least $2^m-1$. In particular, this applies to the canonical Kempf subgroup. The lower bound also applies to arbitrary Laurent-series changes of coordinates, where it bounds the spread of the smallest exponents in the rows. [Grochow–Mulmuley–Qiao, *Boundaries of VP and VNP*, §§3.1 and 4.1](https://arxiv.org/html/1605.02815#S4.SS1)

## 1. The forms and a degeneration

For $m\ge 1$ set
$$
F_m=(x_0x_1\cdots x_m)^5,\qquad
G_m=F_m+F_m\frac{x_1}{x_0}
     +\sum_{i=1}^{m-1}F_m\frac{x_0x_{i+1}}{x_i^2}.
$$
These expressions denote polynomials. Each displayed summand is a monomial of degree $5(m+1)$, and every monomial is divisible by $\prod_{i=0}^m x_i^3$. In particular $G_m$ has $m+1$ monomials and arithmetic formulas of size $O(m^2)$. The family $F_m$ also has polynomial-size formulas.

Take integers $b_i=2^i-1$ for $0\le i<m$, and set $b_m=2^m-1+\delta$, where $\delta\in\{0,\ldots,m\}$ is chosen so that $\sum_i b_i$ is divisible by $m+1$. Define $u_i=b_i-\sum_j b_j/(m+1)$. The diagonal matrix $D(t)=\operatorname{diag}(t^{u_0},\ldots,t^{u_m})$ has determinant one. Substituting $D(t)x$ keeps $F_m$ unchanged and multiplies the other monomials by positive powers of $t$. The extra exponent for the second term is $b_1-b_0>0$. The extra exponent for the summand indexed by $i$ is $b_{i+1}-2b_i+b_0>0$, since it equals $1$ before the last index and $1+\delta$ there. With the inverse convention for the action, the subgroup giving the degeneration is $D(t)^{-1}$. Thus the limit is $F_m$, with eigenweight diameter at most $2^m-1+m$.

## 2. The orbit of the limit is closed

Write $N=m+1$. Let $A_j\in\mathrm{SL}_N(\mathbb C)$ be a sequence for which $F_m(A_jx)$ converges in the coefficient space. Divide each linear row form of $A_jx$ by its Euclidean coefficient norm to obtain unit linear forms $\ell_{j,0},\ldots,\ell_{j,m}$, and let $s_j$ be the product of those norms. By passing to a subsequence, each $\ell_{j,i}$ converges to a unit form $\ell_i$. Their product to the fifth power converges to a nonzero polynomial, since the polynomial ring is an integral domain. The identity
$$
F_m(A_jx)=s_j^5\prod_i \ell_{j,i}^5
$$
and convergence of its left side imply that the positive numbers $s_j$ are bounded. Hadamard's inequality gives $s_j\ge |\det A_j|=1$. Pass to a further subsequence with $s_j\to s\ge1$. The matrix of the normalized row forms has determinant $1/s_j$, so the limiting row forms have determinant $1/s$. Multiplying the first limiting row by $s$ gives a matrix of determinant one whose substitution into $F_m$ yields the limit of $F_m(A_jx)$.

This proves Euclidean closedness of the orbit, equivalent to Zariski closedness for this complex algebraic group orbit, as used in §1 of the source paper. The Zariski closure of any orbit for this action on the fixed homogeneous piece contains a unique closed orbit. Since the degeneration in §1 reaches $F_m$, its orbit is that unique closed orbit. The degeneration is stable in the sense of the question. [Source definition and closed-orbit facts](https://arxiv.org/html/1605.02815#S3.SS1)

## 3. All changes of coordinates reaching the closed orbit have large degree

Let $A(t)$ be any invertible matrix over $\mathbb C((t))$ for which $G_m(A(t)x)$ has coefficients in $\mathbb C[[t]]$, and suppose its constant coefficient in $t$ is $H\in\mathrm{SL}_N(\mathbb C)\cdot F_m$. Write the row forms as
$$
(A(t)x)_i=t^{w_i}(\alpha_i(x)+tR_i(t,x)),
$$
where $w_i\in\mathbb Z$, $\alpha_i$ is a nonzero complex linear form, and $R_i$ is linear in $x$ with power-series coefficients.

For nonzero polynomials in $x$ with Laurent-series coefficients, the least exponent of $t$ with a nonzero polynomial coefficient is additive under multiplication. The coefficient at that least exponent is multiplicative. This follows by multiplying the lowest terms in the domain $\mathbb C[x]$. Because $\prod_i x_i^3$ divides $G_m$, it follows that $\prod_i\alpha_i^3$ divides $H$.

Every member of the closed orbit of $F_m$ has exactly $N$ distinct linear factors up to proportionality, each with multiplicity five, and their coefficient vectors are a basis. If two $\alpha_i$ were proportional, their product to the third powers would give a linear factor of $H$ of multiplicity at least six. Thus the $\alpha_i$ represent all the distinct factors of $H$ and form a basis. In particular $H=c\prod_i\alpha_i^5$ for a nonzero complex $c$.

Under $A(t)$, each monomial $x^\beta$ of $G_m$ has least $t$-exponent $\sum_i\beta_i w_i$ and corresponding coefficient $\prod_i\alpha_i^{\beta_i}$. The monomials in the $\alpha_i$ arising this way are distinct, so they are linearly independent. Hence the smallest of these $t$-exponents is the least $t$-exponent of $G_m(A(t)x)$, and the coefficient there is the sum of the leading monomials of precisely the summands attaining that smallest exponent. Since the coefficient limit is the nonzero polynomial $c\prod_i\alpha_i^5$, the smallest exponent is zero and it is attained by the summand $F_m$ alone.

Subtracting the exponent of $F_m$ from the other exponents gives the inequalities
$$
w_1-w_0\ge1,\qquad w_{i+1}-2w_i+w_0\ge1 \quad (1\le i<m).
$$
The gaps $d_i=w_i-w_0$ satisfy $d_0=0$, $d_1\ge1$ and $d_{i+1}\ge 2d_i+1$. Induction gives $d_i\ge2^i-1$. In particular $\max_i w_i-\min_i w_i\ge 2^m-1$. Each $w_i$ is the least exponent occurring in its matrix row. Thus some matrix entry has a nonzero coefficient at an exponent of absolute value at least $(2^m-1)/2$. This applies in particular when every entry is a Laurent polynomial.

## 4. The canonical subgroup

Any algebraic one-parameter subgroup supplying a change of coordinates is a constant conjugate of $\operatorname{diag}(t^{v_0},\ldots,t^{v_m})$ for integers $v_i$. Every exponent occurring in any matrix entry is one of the $v_i$, so its eigenweight diameter is at least the diameter of the row valuations above. The inverse subgroup has weights $-v_i$, of the same diameter. For comparison with the total-size convention of §4.1, in the standard Cartan basis $h_i=E_{ii}-E_{i+1,i+1}$ the vector of diagonal eigenweights of $\sum_i c_i h_i$ has all entries of absolute value at most $\sum_i |c_i|$. The total size is therefore at least half the diameter. Both conventions give $\Omega(2^m)$.

The argument applies to every subgroup whose coefficient limit belongs to the unique closed orbit, including any optimal Kempf subgroup for that orbit. It gives the requested exponential lower bound with $a=1$ when the family index is $m$. The source and the limit themselves both have polynomial-size formulas. The result rules out an upper bound polynomial in $m$ on the degree of these coordinate paths and leaves the class comparison $\mathsf{Stable\text{-}VP}=\mathsf{VP}$ open.

## 5. Dependence on the degree of the source forms

For any integer $r\ge 2$, the same construction works with
$$
F_{m,r}=(x_0\cdots x_m)^{2r+1},\qquad
G_{m,r}=F_{m,r}+F_{m,r}\frac{x_1}{x_0}
  +\sum_{i=1}^{m-1}F_{m,r}\frac{x_0^{r-1}x_{i+1}}{x_i^r}.
$$
The common coordinate factors have multiplicity at least $r+1$. Since $2(r+1)>2r+1$, the leading linear forms in the path argument still cannot coincide. Closedness follows from the same row-normalization proof with $2r+1$ in place of five. The resulting inequalities are $d_1\ge1$ and $d_{i+1}\ge r d_i+1$, giving diameter at least $\sum_{j=0}^{m-1}r^j$. The explicit diagonal construction sets $b_i=\sum_{j=0}^{i-1}r^j$, adjusts the last $b_m$ by at most $m$ for divisibility, and subtracts the integral mean. For $r=m\ge2$, both form families have degree $O(m^2)$ and polynomial-size formulas, and the lower bound rises to $m^{m-1}=2^{\Omega(m\log m)}$.
