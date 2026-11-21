# Exact depth-three limits with compressed Laurent weights

**GP-0697, a compressed-pole class.** Fix $r$. Consider a one-parameter depth-three expression over $\mathbb Q$ presented as
$$
\mathcal F(t,x)=
\frac{\displaystyle\sum_a t^{b_a}\prod_j
        \left(\sum_u \ell_{a,j,u}(x)t^{w\cdot u}\right)}
     {D(t)}.
$$
Here $w\in\mathbb Z^r$ and all $b_a\in\mathbb Z$ are written in binary, the $\ell_{a,j,u}$ are explicitly given rational affine linear forms, and the $u\in\mathbb N^r$ are listed with polynomially bounded coordinates, for example in unary. The nonzero scalar denominator is given as a product of explicitly listed sparse rational Laurent polynomials in $t$, with binary exponents. If the limit at $t=0$ exists as a polynomial in $x$, it has an exact rational depth-three circuit computable in deterministic polynomial bit time. In particular, the bit bound has no polynomial dependence on the pole order itself. Negative generator weights and equal-weight cancellations are allowed.

The theorem also covers separately factored scalar denominators per summand when their factors have the same signed generator representation up to monomial shifts. Multiplying each numerator by complementary denominator factors gives the displayed input in polynomial size. The extra scalar factors are particular affine forms with constant value.

## Leading denominator

Combine equal exponents in each scalar denominator factor, using exact rational sums. The smallest surviving exponent of a product is the sum $v$ of these smallest exponents, and its coefficient is the product $c\ne0$ of the corresponding coefficients. Both are computable in polynomial bit time. If $N(t,x)$ denotes the numerator, convergence implies that its exponents below $v$ have zero coefficients, and the answer is $[t^v]N(t,x)/c$. This follows by writing $D=t^v(c+tR)$ and comparing the lowest Laurent powers. In particular the promised convergence lets the extraction use just one coefficient even if exponentially large negative terms cancel.

## Interpolate before substituting large weights

Introduce $r$ formal variables $z$. For summand $a$ put
$$
P_a(x,z)=\prod_j\left(\sum_u\ell_{a,j,u}(x)z^u\right).
$$
Choose $B$ at least the maximum individual degree in $z$ of all these products, using the sum of the displayed maxima per factor. It is polynomial in the input for the stated encoding. On the grid $\{0,1,\ldots,B\}^r$ write $P_a=\sum_{\gamma}P_a(x,\gamma)L_{\gamma}(z)$ by tensor-product Lagrange interpolation. This identity holds with coefficients in $\mathbb Q[x]$. Define the scalar $\lambda_{a,\gamma}$ to be the sum of the coefficients $[z^u]L_\gamma$ over $u\in\{0,\ldots,B\}^r$ with $w\cdot u=v-b_a$. Then
$$
\lim_{t\to0}\mathcal F(t,x)=
c^{-1}\sum_{a,\gamma}\lambda_{a,\gamma}P_a(x,\gamma).
$$
The formula includes all collisions of the large signed weights, because it sums all preimages of the target exponent. Computation of each scalar uses exact binary integer weights and at most $(B+1)^r$ univariate-product coefficients, of polynomial bit length. In detail, the univariate Lagrange numerator is a product of $B$ linear factors with integer coefficients bounded by $B$, and the denominator is a product of $B$ nonzero integer differences bounded by $B$. Also each evaluated affine coefficient is a sum of displayed rational coefficients multiplied by grid integers raised to exponents at most $B$, giving polynomial bit lengths. Each $P_a(x,\gamma)$ is one product of affine forms. This proves the claimed output format and bit time.

The scope is a fixed number of shared signed weight generators with small coefficient-coordinate bounds after lifting, which can still encode poles of exponential order. It neither tests convergence for arbitrary representations nor resolves conversion with unrestricted generators. [Border depth-three context, Bhat, Dutta and Shringi](https://eccc.weizmann.ac.il/report/2026/245/).
