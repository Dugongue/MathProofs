# GP-0669 · Succinct stabilizer dimension strata

For a rational circuit family of homogeneous forms $f_T(X)$ of size $s$ in $n$ variables, one can construct in polynomial time succinct equations for every dimension-jump locus for the $\operatorname{GL}_n$ stabilizer over characteristic zero. The encoding uses one circuit polynomial per rank threshold, whose coefficients in auxiliary variables are the equations in $T$. Point membership in this encoding is a polynomial identity test, and membership for one rank threshold is PIT-hard. If one requires explicit enumeration over a univariate parameter, the output can have exponentially many points.

For fixed parameter $\tau$ the Lie-algebra stabilizer is the kernel of
$$
\Phi_\tau\colon \mathfrak{gl}_n\longrightarrow\mathbb C[X],\qquad
A\longmapsto \sum_{i,j} A_{ij}X_j\partial_i f_\tau .
$$
This is the differential of the change-of-variables action, up to sign. Characteristic zero makes the stabilizer smooth, so its dimension is $n^2-\operatorname{rank}\Phi_\tau$. Build the $r=n^2$ column polynomials by differentiating the given circuit gate by gate with the Leibniz rule.

Use $r$ independent $n$-tuples $Y^{(1)},\ldots,Y^{(r)}$ and let $B(T,Y)$ be the $r\times r$ evaluation matrix, with row $i$ evaluating the column polynomials at $Y^{(i)}$. For every complex $\tau$, the rank of $B(\tau,Y)$ over $\mathbb C(Y)$ equals $\operatorname{rank}\Phi_\tau$. Evaluation cannot enlarge rank. Conversely, for any linearly independent $k$ of the column polynomials, evaluation vectors span $\mathbb C^k$: a functional vanishing on all of them would give a polynomial identity among the columns. Thus $k$ evaluation points give a nonzero $k$-minor, proving the other inequality. The same argument works over any algebraically closed characteristic-zero field.

Let $A$ and $D$ be diagonal matrices on independent scalar variables $a_i,d_i$. Compute the coefficients
$$
P_k=[z^k]\det(I+z A B D B^{\mathsf T}),\qquad 1\le k\le r .
$$
The coefficient of $\prod_{i\in I}a_i\prod_{j\in J}d_j$ in $P_k$ is precisely $\det B_{I,J}^2$ for $|I|=|J|=k$. Expand in principal minors and apply Cauchy–Binet. Distinct $(I,J)$ give distinct monomials, so cancellations between minors cannot mask a nonzero minor. Therefore $\dim\operatorname{Stab}(f_\tau)\ge r-k+1$ exactly when $P_k(\tau,Y,a,d)$ is the zero polynomial. This is an exact Zariski-closed condition on $\tau$ expressed by explicitly constructed coefficient circuits. Compute the characteristic polynomial by a division-free polynomial-size circuit, or interpolate in $z$ at $r+1$ rational points. There are only polynomially many formal variables, gates, and threshold circuits. No degree bound on the $T$ or $Y$ circuit outputs is needed for the representation.

For the output obstruction use one variable $X$ and $f_t=(t^{2^s}-1)X$. Away from the roots the form lies in the single orbit of $X$ and has zero-dimensional stabilizer. At the $2^s$ roots it is zero and has one-dimensional stabilizer. The path has size $O(s)$ by repeated squaring and lies in that orbit closure. For PIT-hard membership take an arbitrary polynomial circuit $g(X)$ and adjoin an extra variable $U$ to form $U g(X)$. The stabilizer has full dimension iff this form is zero: a full-dimensional closed subgroup of connected $\operatorname{GL}_{n+1}$ is the whole group, and a nonzero polynomial divisible by $U$ cannot be fixed by all scalar dilations. If homogeneity is required, homogenize by a new variable $V$ gate by gate. A gate with syntactic degree bound $e$ becomes homogeneous degree $e$ by replacing each addition by a sum whose lower-degree input is multiplied by the needed power of $V$. Powers use repeated squaring, with binary exponents of polynomial bit length. This preserves the PIT reduction and yields positive-degree homogeneous forms. In the polynomial-size circuit representation the test is PIT-complete. [Stabilizers and orbit closures](https://arxiv.org/abs/1911.03990)
