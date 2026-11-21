# Hasse derivative hitting sets in fixed positive characteristic

## GP-0691

For each fixed finite field $F$ there is a deterministic polynomial-time construction of a hitting set of size $\operatorname{poly}(n,d,r)$ for all $n$-variate polynomials of total degree at most $d$ over $F$ whose full Hasse derivative space has dimension at most $r$. The points lie in an explicitly constructed extension of degree $O(\log(n+d+r+2))$. The construction uses a multiplicative difference operator in place of characteristic-zero formal integration.

### A difference system with no polynomial invariants

Choose a finite extension $k$ of $F$ containing $n$ distinct nonzero elements $a_1,\ldots,a_n$. Put $K=k(u)$ for a transcendental $u$. The operator $\sigma$ sends $t$ to $ut$, fixing $K$, on the fields $K(t)$ and $K((t))$. Their fixed fields are both $K$. For the Laurent series field this follows coefficientwise from $u^j\ne1$ for every nonzero integer $j$. Put
$$
b_i(t)=\frac{t}{t-a_i},\qquad
P_i(t)=-\sum_{j\ge1}\frac{a_i^{-j}t^j}{u^j-1}.
$$
Thus $\sigma P_i-P_i=b_i$. Extend $\sigma$ to an automorphism $\tau$ of $K(t)[x_1,\ldots,x_n]$ by sending $x_i$ to $x_i+b_i(t)$.

The only $\tau$-invariant polynomials are the elements of $K$. To prove this, let $h(t,x)=h(u^m t,x+B^{(m)}(t))$ for every positive integer $m$, where $B_i^{(m)}=\sum_{j=0}^{m-1}b_i(u^j t)$. Suppose $h$ has positive $x_i$-degree $e$. The points $a_i u^j$ form an infinite orbit disjoint from those for the other $a_j$. Choose $m$ large enough to find $j$ with $0\le j<m$ such that:
- all coefficients of $h$ are regular at both $t_0=a_i u^{-j}$ and $u^m t_0=a_i u^{m-j}$,
- at least one fixed nonzero coefficient in the leading $x_i$ coefficient of $h$ is nonzero at $u^m t_0$.

Only a fixed finite number of indices are forbidden, since each rational coefficient has finitely many zeros and poles. At $t_0$, the function $B_i^{(m)}$ has a simple pole, and every other $B_\ell^{(m)}$ is regular. Specialize the invariance equation at $x_i=0$, keeping the other $x$ variables formal. On the right the leading $x_i$ coefficient remains nonzero modulo $t-t_0$, because translation of the remaining variables by the regular values is an invertible substitution. It contributes a pole of order $e$. All lower powers contribute poles of smaller order. The left side is regular, a contradiction. Thus $h$ is independent of all $x_i$ and lies in $K$.

Evaluation $x_i\mapsto P_i(t)$ is injective on $K(t)[x]$. It commutes with the two automorphisms above. If its kernel were nonzero, choose a nonzero element of least $x$-degree and then fewest terms of that top degree. Scale it so one top coefficient is $1$. Subtracting it from its $\tau$-image cancels that top term and introduces no new top monomials. By minimality the difference is zero. Invariance then puts the element in $K$, where evaluation is injective, a contradiction.

### Rank controls the truncation order

Take nonzero $f$ and let $f_1,\ldots,f_s$ be a basis of its full Hasse derivative space, with $f_s=f$, ordered by increasing degree and adapted to the degree filtration. This space is closed under Hasse derivatives, by their composition formula. Translation on it has matrix $U(x)$, upper triangular with diagonal entries $1$, in the sense that the row vector $\mathbf f(y+x)$ equals $\mathbf f(y)U(x)$. The Hasse Taylor identity gives this because positive-order derivatives lower degree. Extension of scalars from $F$ to $K(t)$ preserves independence of the basis. The injectivity just proved implies $f_j(P(t))$ are linearly independent over $K$.

For clarity, in any difference field with automorphism $\sigma$ and fixed field $K$, the matrix with entries $\sigma^a(g_j)$, $0\le a<s$, has nonzero determinant when the $g_j$ are $K$-linearly independent. Induct on $s$. If the determinant vanishes, solve for the last column as a combination of the first $s-1$ on the first $s-1$ rows by the induction hypothesis. It holds on the last row as well by the zero determinant. Applying $\sigma$ on the first $s-1$ rows and comparing with the last $s-1$ rows forces the combination coefficients to be fixed by $\sigma$. This contradicts the independence.

Apply this criterion to $g_j=f_j(P(t))$. Since $\sigma^aP=P+B^{(a)}$, the matrix with rows $\mathbf f(x+B^{(a)}(t))$ factors as the matrix with rows $\mathbf f(B^{(a)}(t))$ times $U(x)$. Its determinant is independent of $x$, so the determinant for the $g_j$ is the determinant of the rational matrix obtained at $x=0$. A common denominator for every coordinate of every $B^{(a)}$ is the product of at most $L=n(s-1)$ linear factors $u^j t-a_i$. Its value at zero is nonzero. Each coordinate numerator has degree at most $L$ in $t$. Clear the $d$th power of this product from each matrix row. The determinant numerator has degree at most $sdL$ in $t$. Its order at zero is thus at most $sdL$.

Every entry in the column for $f_s$ in the original difference matrix has order $\operatorname{ord}_t f(P(t))$, since $\sigma$ preserves order. All other entries have nonnegative order. It follows that $\operatorname{ord}_t f(P(t))\le sdL\le ndr(r-1)$. Setting $N=ndr(r-1)$, replacing each $P_i$ by its truncation through degree $N$ therefore preserves nonzeroness of $f(P(t))$. The case $N=0$ is covered by the same argument, or simply by evaluating nonzero constant polynomials.

### Finite sets of evaluations

Let $D(u)=\prod_{j=1}^N(u^j-1)$ and $W=N(N+1)/2$. If $P_i^{[N]}$ denotes the truncation, then
$$
D(u)^d f(P_1^{[N]}(t),\ldots,P_n^{[N]}(t))
$$
is a nonzero polynomial, of separate degrees at most $dW$ in $u$ and $dN$ in $t$. Take any set of $(d+1)W+1$ distinct possible $u$ values, ignoring zeros of $D$, and $dN+1$ distinct $t$ values. At least one $u$ leaves a nonzero univariate polynomial in $t$ and has $D(u)\ne0$, by applying the root bound to one nonzero coefficient times $D$. Then some $t$ from the second grid yields a nonzero evaluation. Output the points $(P_i^{[N]}(t))_{i=1}^n$ for the surviving grid pairs.

A single extension of the fixed input field of polynomial cardinality supplies the $a_i$ and both grids. Try all monic polynomials of the required logarithmic degree until an irreducible one is found, using standard finite-field irreducibility tests or trial division in polynomial time since the field size is fixed. The number of grid pairs and the work to evaluate them are polynomial in $n,d,r$. No characteristic restriction on $d$ or $r$ is needed.

This uses the same translation-matrix identity as the characteristic-zero derivative-space argument. The difference equation, the pole-orbit independence proof, and the finite two-coordinate evaluation supply the positive-characteristic step. [Characteristic-zero source, Section 3](https://eccc.weizmann.ac.il/report/2026/217/revision/1/download/)
