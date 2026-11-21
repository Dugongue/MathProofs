# Black-box recovery of one product of affine forms

## GP-0559

If an oracle can be queried only at points of its ground field, black-box reconstruction of formal depth-three circuits over arbitrary finite fields is impossible even at top fan-in one. If queries over finite extensions are permitted, top fan-in one instead admits randomized proper reconstruction in polynomial bit time. In that extension model its deterministic version is polynomial-time oracle reducible to deterministic factoring of split univariate polynomials over explicitly represented finite fields. Conversely deterministic ground-field recovery in this extended model would factor every promised split univariate input over the ground field. This does not provide reconstruction at arbitrary constant top fan-in.

The impossibility follows from the two distinct products $x(x^q-x)$ and $(x-1)(x^q-x)$ over $\mathbb F_q$. They both have degree $q+1$, both split into affine forms, and both give the zero function on every available point, even with adaptive queries. A polynomial-size algorithm would have to produce identical output on the two identical oracles.

### Finding a line with distinct intersections

Suppose the nonzero unknown polynomial is a scalar times a product of affine forms, of degree at most $D$ in $n$ variables. Group proportional factors into distinct hyperplanes, with multiplicities $m_i$. Work over an extension $E$ containing more than a fixed polynomial in $n,D$ elements. If the ground field is too small, an extension of logarithmic degree over it has polynomial cardinality in $n,D$ and can be constructed by enumerating monic polynomials of that degree and testing irreducibility. If it already has enough elements use it directly. The number of field operations and bit costs are polynomial in $n,D,\log q$.

Take a candidate line $a+tb$ where $a=(v,v^2,\ldots,v^n)$ and $b=(1,u,\ldots,u^{n-1})$. For a distinct factor $L_i$, write $L_i^{\rm lin}$ for its linear part. The polynomial $L_i^{\rm lin}(b)$ is nonzero as a polynomial in $u$. For nonproportional affine forms $L_i,L_j$, the collision numerator
$$
L_i(a)L_j^{\rm lin}(b)-L_j(a)L_i^{\rm lin}(b)
$$
is also nonzero as a polynomial in $u,v$. Otherwise comparison of coefficients in $v$ shows the entire affine coefficient vectors proportional over $E(u)$ and hence over the ground field. The product of all these avoidance polynomials has each coordinate degree $O(nD^2)$. The ordinary grid bound yields a polynomial-size search for a line where all are nonzero. Use univariate interpolation of the restrictions and factor them, choosing maximum degree first and maximum distinct-root count second. The maximum degree is the actual degree. Among those restrictions every factor has a nonzero slope, and the greatest distinct-root count marks precisely the collision-free case. A constant or the zero polynomial is handled by the same interpolation.

### Matching roots without differentiating

Fix the resulting $a,b$. The $i$th line intersection is a distinct root $r_i$ with multiplicity $m_i$, and
$$
L_i(a+tb+\eta e_j)/L_i^{\rm lin}(b)
     = t-r_i+\eta\beta_{ij}
$$
for an unknown scalar $\beta_{ij}$. For every coordinate $j$, restrict to these displaced lines at $D+1$ distinct values of $\eta$, including $0,1$, and find their root sets by split univariate factoring. For each baseline root $r_i$ enumerate candidate affine root trajectories through $r_i$ and one of the roots at $\eta=1$. Retain a candidate when it yields a root at every sampled $\eta$. A false candidate agrees with each true trajectory at at most one value, so it can pass at most $D$ samples. The correct trajectory always passes, even at a collision. Its slope recovers $\beta_{ij}$. This avoids any characteristic assumption on the multiplicities.

The normalized affine factor in the original coordinates is then $\sum_j\beta_{ij}(x_j-a_j)-r_i$. Its coefficients lie in $E$. Divide by a nonzero linear coefficient, for example the first in index order. The result descends to the ground field, because it is a scalar multiple of a factor originally defined there and now has its pivot equal to one. Recover the residual scalar by evaluation on the baseline line away from its roots. This outputs a proper factorization, including all multiplicities. All query coordinates and field values have polynomial encoding size. Split univariate factoring is randomized polynomial time, so randomized reconstruction with extension queries follows. A given split univariate polynomial can itself supply the oracle over extensions by evaluation, proving the stated reverse comparison.

[Constant-top-fan-in reconstruction context](https://doi.org/10.1145/3798129.3800878)
