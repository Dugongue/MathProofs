# Quantitative border top-fan-in with growing bottom degree

## GP-0563

Let $P_{k+1,n}$ be the sum of $k+1$ disjoint squarefree monomials of degree $n$. Over an algebraically closed characteristic-zero field and for $k\ge2$, it has border top fan-in two and bottom degree at most $\delta$ with size
$$
(k+1)\operatorname{poly}(n)\,2^{\lceil n/\delta\rceil}
$$
for $1\le\delta\le n$. The construction works for every $\delta$, including growing bottom degree. Combined with Dey–Dutta–Guo's quantitative Theorem 6.1, it places the general size at fixed $k$ between $2^{\Omega_k(n/\delta^k)}$ and $2^{O(n/\delta)}\operatorname{poly}(n)$ when $n\ge C_k(2\delta)^{C'_k}$ for suitable constants. In the submodel where bottom factors are affine-linear in designated chunk monomials, the exponent $n/\delta$ is optimal up to constants at fixed $k$.

Split each target monomial into $m=\lceil n/\delta\rceil$ consecutive chunks, with each chunk monomial $y_{ij}$ of degree at most $\delta$. Regard the $y_{ij}$ first as independent variables. Polarization gives
$$
\prod_{j=1}^m y_{ij}
 =\frac1{m!}\sum_{A\subseteq[m]}(-1)^{m-|A|}
       \left(\sum_{j\in A}y_{ij}\right)^m.
$$
Indeed a term missing a variable cancels by summing over subsets containing its support; the only remaining degree-$m$ monomial using every variable is the displayed product and its multinomial coefficient is $m!$. This is a sum of at most $(k+1)2^m$ powers $c_\nu L_\nu(y)^m$ for the complete target.

Put $Q_\varepsilon=\prod_\nu(1+\varepsilon^m c_\nu L_\nu(y)^m)$. Each factor splits over the coefficient field as a product of $m$ factors affine-linear in $\varepsilon L_\nu(y)$, simply by factoring $1+c_\nu z^m$. Therefore
$$
\varepsilon^{-m}\bigl(Q_\varepsilon-1\bigr)
\longrightarrow P_{k+1,n}(y)
$$
as $\varepsilon\to0$, and this expression has two top summands. After substituting the designated chunks, every bottom factor has degree at most $\delta$ and at most $m+1$ monomials. Writing each monomial as a product of the original variables gives the stated size bound, for example $O((k+1)2^m m^2(n+1))$. For $\delta\ge n$ the target itself is one permitted bottom polynomial.

For the advertised lower bound in the general commutative model, Theorem 6.1 bounds
$$
n\le O\bigl(k(4\delta)^k\log s\bigr)+(2\delta)^{O(k^2)}.
$$
At fixed $k$, choose constants large enough that the second term is at most $n/2$ on the stated regime, then rearrange. For example this retains a superpolynomial lower bound when $\delta$ grows polylogarithmically in $n$. It does not yield matching exponents for general growing $\delta$.

For the matching restricted-model lower bound, assume all bottom polynomials are affine-linear combinations of the specified chunks. The substitution from the independent $y$ variables into the original variables is injective on monomials, since the nonempty chunks have disjoint supports. It also reflects coefficientwise Laurent-series convergence, because each original monomial receives at most one $y$ monomial. Thus a border circuit in this submodel would give a genuine border depth-three circuit of top fan-in $k$ for $P_{k+1,m}$ in the independent variables. The same published theorem, now with bottom degree one, gives size $2^{\Omega_k(m)}$. This establishes the exact exponential regime for chunk-aligned factors, while the polarized upper bound is available without that restriction.

[Quantitative lower bound, Theorem 6.1](https://eccc.weizmann.ac.il/report/2026/297/download/)
