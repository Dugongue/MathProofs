# Exact tensor transport in a marked congruence class

Let $p$ be a prime, $a\ge1$, and $R=\mathbb Z/p^a\mathbb Z$. The input is a pair of explicit dense three-tensors of the same format, and a specified residue class of invertible mode maps modulo $p^k$, for $1\le k\le a$. Decide whether this class contains a transporter, optionally with three prescribed determinants. In a positive case, construct one and count all of them.

The connection is to Alpöge's formal theta-lattice calculation. The released theorem **PositivityTheory.Sph.below_iff_rows** turns integral matrix motion with bounded additive errors into a row-lattice test. The later **PositivityTheory.Sph.latSt** proof separates its strata by triangular subtraction. For tensors, the action is nonlinear. A change of $p$-adic coordinates makes its selected projection an actual row-lattice image and makes the remaining rows exact functions of those coordinates at the requested precision. The transfer uses the algebraic lattice calculation. It is independent of the analytic RH and GRH conclusions. [Released lattice source](https://raw.githubusercontent.com/CocoSgt/riemann-hypothesis-lean/main/src/Development/WeilBound/ThetaLifts/SphericalLattices/BelowIffRows.lean) · [Grochow–Qiao–Stange–Sun on TI over commutative rings](https://arxiv.org/abs/2611.00735)

## The depth test

Choose any lift $g_0$ of the specified residue class to a triple over $R$. Invertibility follows from invertibility modulo $p$. Normalize the target by $g_0^{-1}$ and replace each requested determinant $\delta_i$ by $\delta_i/\det(g_{0,i})$. This reduces to the principal congruence subgroup $K_k=\prod_i(1+p^kM_{n_i}(R))$. For $k=a$, only the identity in this subgroup needs testing.

Let $d=\sum_i n_i^2$. In the ordinary case the source point is $s=A$. To prescribe determinants use the action on the direct sum of tensor space and three lines, with the $i$-th scalar line acted on by the determinant of the $i$-th mode map. The source is then $s=(A,1,1,1)$, and the target $u$ is the normalized target tensor with the normalized determinants appended. Write $D_s$ for the resulting infinitesimal action on $s$ from the $d$ matrix entries. Its tensor block is $\sum_i X_i\cdot_i A$, with $X_i$ acting in mode $i$ alone. The optional line block is $(\operatorname{tr}X_1,\operatorname{tr}X_2,\operatorname{tr}X_3)$.

Compute the Smith valuations over $R$, assigning valuation $a$ to zero pivots, and let $\sigma_1,\ldots,\sigma_r$ be exactly those strictly below $a-k$. The theorem applies under either of these checks.

- $2k\ge a$.
- $k\ge2$ and every $\sigma_i\le k-2$.

The latter check only concerns the valuations visible after multiplying by $p^k$ at precision $a$. Invariant factors at or above $a-k$ may be arbitrarily deep. No smoothness condition on the stabilizer is imposed. Under either check, the decision, construction and exact count take deterministic time polynomial in the dense input length, $a$, and $\log p$. Every nonempty witness set in the specified class has cardinality
$$
p^{(a-k)d-\sum_{i=1}^{r}(a-k-\sigma_i)}.
$$
The corresponding orbit of $s$, with determinant coordinates included when requested, has size $p^{\sum_i(a-k-\sigma_i)}$. The theorem includes $p=2$.

## Square-zero precision

When $2k\ge a$, multiplying out the tensor action of the three matrices $1+p^kX_i$ leaves just its linear correction. The same expansion in the determinant gives $\det(1+p^kX_i)=1+p^k\operatorname{tr}X_i$. Hence the orbit is exactly $s+\operatorname{im}(p^kD_s)$, and a Smith solve provides a witness and the fiber count. Each surviving Smith coordinate contributes $p^{a-k-\sigma_i}$ image elements.

## Congruence coordinates below the square-zero range

Lift all input entries to integers and work temporarily over $\mathbb Z_p$. The principal congruence groups there surject onto the corresponding groups over $R$. Let $U,V$ be invertible row and column Smith matrices over $R$, with the visible valuations first, and lift $U,V$ to invertible matrices over $\mathbb Z_p$. Write $C(x)=V(x,0)$ and $K(y)=V(0,y)$ in the module of matrix triples, for $x\in\mathbb Z_p^r$ and $y\in\mathbb Z_p^{d-r}$. Thus $C(x)+K(y)$ gives unimodular coordinates on the full module, and
$$
D_sK(y)\in p^{a-k}\mathbb Z_p^{\dim s}.
$$

In the maximum entrywise $p$-adic norm we have the estimates
$$
\exp(p^kX)=1+p^kX+p^{2k-1}E(X),\qquad
\log(1+p^kX)=p^kX+p^{2k-1}L(X)
$$
for $k\ge2$, with integral $1$-Lipschitz remainders $E,L$. Indeed $v_p(j!)\le j-1$ and $v_p(j)\le j-1$, so for $j\ge2$ the coefficients after division by $p^{2k-1}$ are integral, with valuations tending to infinity. The telescoping formula for a difference of matrix powers makes each normalized summand $1$-Lipschitz. The convergent one-variable series are inverse on these neighborhoods by their formal identities. Multiplying the two first-order expansions and then applying the logarithm gives
$$
p^{-k}\log\bigl(\exp(p^k C(x))\exp(p^k K(y))\bigr)
  = C(x)+K(y)+p^{k-1}H(x,y)
$$
with another integral $1$-Lipschitz remainder. In $V$-coordinates this is the identity plus a strict contraction. Such a map is an isometry and a bijection. For each target $w$, solve $z=w-h(z)$ by fixed-point iteration, where $h$ is the contracting error. The same argument gives bijections at each finite precision. Every group element therefore has these product coordinates.

The factor $\exp(p^kK(y))$ fixes $s$ modulo $p^a$. Write $d\rho$ for the differentiated action. The identity $\rho(\exp Z)=\exp(d\rho(Z))$ follows on the tensors by multiplying exponentials of the commuting one-mode operators. On the scalar lines it is $\det(\exp Z)=\exp(\operatorname{tr}Z)$, obtained by differentiating the determinant series with its initial value at zero. For $Z=K(y)$ the $j$-th nonconstant term acting on $s$ is
$$
\frac{p^{k(j-1)}}{j!}(d\rho(Z))^{j-1}\bigl(p^kD_sZ\bigr).
$$
Its scalar coefficient is integral and the last vector is divisible by $p^a$. Hence all terms vanish at the needed precision. This conclusion uses an approximate kernel at the specified precision. It requires no exact equality between the kernel columns and an integral stabilizer.

## The row lattice and reconstruction

Define $F(x)=U\bigl(\rho(\exp(p^k C(x)))s-s\bigr)$. The expansion and the lifted Smith relation give
$$
F(x)=
  (p^{k+\sigma_1}x_1,\ldots,p^{k+\sigma_r}x_r,0,\ldots,0)
  +p^{2k-1}E_1(x), \tag{1}
$$
with $E_1$ integral and $1$-Lipschitz. Any error in the lifted Smith relation starts at $p^{a+k}$ and is included in this remainder. Dividing each selected row by $p^{k+\sigma_i}$ gives a map $G$ satisfying
$$
G_i(x)=x_i+p^{k-1-\sigma_i}(E_1)_i(x).
$$
Since $k-1-\sigma_i\ge1$, this map too is an isometric bijection by contraction.

Consider the transposed tangent map on the selected Smith rows with the factor $p^k$ included. In the released row-lattice theorem use that matrix as $Y_0$, take $t=p^a$, and set one row of $Y$ to the projected target difference with the other rows zero. Its row lattice is
$$
\bigoplus_{i=1}^r p^{k+\sigma_i}\mathbb Z_p+p^a\mathbb Z_p^r.
$$
Equation (1) and the bijection $G$ identify this same lattice with the allowable projected differences of the **nonlinear** tensor orbit at precision $a$. In particular, test the selected rows of $U(u-s)$ in this lattice. If they pass, divide to obtain residues $z_i$ modulo $p^{b_i}$, where $b_i=a-k-\sigma_i$. Pick any integral lifts of them and solve $G(x)=z$.

All values in unselected rows modulo $p^a$ are independent of those choices. Two allowed lifts agree modulo $p^{b_{\min}}$, where $b_{\min}=\min_i b_i$. Their preimages under $G$ also agree at this precision. In an unselected row the linear term in (1) is zero, so the difference of output values is divisible by
$$
p^{2k-1+b_{\min}},\qquad 2k-1+b_{\min}=a+k-1-\max_i\sigma_i\ge a.
$$
When $r=0$, the earlier approximate-kernel argument shows directly that the orbit is a singleton. Otherwise evaluate the tuple $\exp(p^k C(x))$ once and check the full equality to the normalized target. A successful comparison gives a genuine transporter after reinserting $g_0$. On failure, the product coordinates of any hypothetical transporter would have the same selected residues and therefore the same unselected rows, which is impossible. This proves the decision and construction assertions. In particular the selected projection gives a necessary row test and all remaining equations are explicitly verified.

## Counting, depth strata, and bit complexity

Every choice of the $p^{b_i}$ allowed residues in each selected coordinate is attained. Their unselected rows are then forced, so the augmented orbit has $p^{\sum_i b_i}$ points. The number of elements of $K_k$ over $R$ is $p^{(a-k)d}$. Fibers of its orbit map are stabilizer cosets of equal size, giving the formula. This argument counts witnesses to the specified determinants because the determinant lines are part of the orbit point.

One also gets exact counts by congruence depth around the same reference $g_0$. For each $\ell=k,\ldots,a$ count solutions in $g_0K_\ell$. The visible valuations at a deeper level are a subset of those at the initial level, and the depth criterion persists or enters the square-zero regime. Subtract adjacent counts to recover the number in $g_0K_\ell$ outside $g_0K_{\ell+1}$, with $g_0K_a$ the final singleton. This is triangular subtraction over a finite chain of congruence strata.

Smith operations over $R$ use valuation-minimal pivots, removal of their unit factors, and elementary row and column operations. For an entry divisible by a pivot $p^\sigma$ one divides modulo $p^{a-\sigma}$, which suffices to clear its row or column. These operations have polynomial bit cost. For the fixed-point iteration used to recover $x$, preserve $p$-adic precision $\max_i b_i\le a-k$. Dividing the selected rows only requires evaluating $F$ to at most $a+\max_i\sigma_i\le2a$ digits. For $k\ge2$ the term of order $j$ in the exponential has valuation at least $j(k-1)+1$, so $O(a)$ terms suffice. Remove $p$-powers from the denominators before modular division and invert only the unit parts, using $O(a)$ extra digits as needed. The contraction gains at least one digit per iteration. Limits are not computed. The finite-precision representative obtained after at most $a$ iterations suffices by the reconstruction argument. The counts have $O(ad\log p)$ bits. This proves the claimed bit bound.

For a concrete family with visible torsion, take $p=2$, all mode dimensions $2$, and $A=2^e e_1\otimes e_1\otimes e_1$. The determinant-augmented derivative has three unit pivots from the traces and four pivots of valuation $e$. Traceless diagonal and single off-diagonal moves give independent coordinates at $111,211,121,112$ multiplied by $2^e$, and all other tensor entries have zero differential. The chart applies from depth $e+2$ for arbitrarily large precision. Two nonzero off-diagonal corrections produce a coefficient at valuation $e+2k$ in one of the entries with zero differential, so the reconstruction can be genuinely nonlinear.

The result is an exact algorithm in a supplied congruence class. Finding a suitable class without such an input remains a separate TI problem. The proof treats arbitrary normalized target tensors and finds an actual transporter above the marked precision; previous determinant correction of a known transporter addresses a different input. This transfer is a proof in prose. Its Lean statements have not been checked.
