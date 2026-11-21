# Sparse Newton iteration for product Hamiltonians

The bounded-treewidth, nondegenerate-minimum case of Problem 6.2 admits a quadratically convergent iteration. An additional gap-dominance condition gives a unique global product minimizer and a globally convergent initializer. The bounds below count arithmetic operations. [Simons Workshop Problem 6.2](https://arxiv.org/html/2602.05394v3#S6.SS2)

## Theorem

Write the Hermitian product-state energy as

$$
f(P)=\sum_i \operatorname{tr}(F_iP_i)
+\sum_{e=\{i,j\}}\sum_{a=1}^{k_e}
\operatorname{tr}(G_{ea}P_i)\operatorname{tr}(K_{ea}P_j).
$$

The variables are rank-one orthogonal projectors in complex dimension $n\ge2$, and $i,j$ have a fixed ordering at each edge. Each interaction edge has at most $k$ terms. Supply an elimination order of width $w$ for the interaction graph on $d$ sites.

At every local minimum with positive definite Hessian in projective coordinates, there is a quadratically convergent Newton iteration with arithmetic cost $O(d((w+1)^2n^3+wkn^2))$ and additional memory $O(d(w+1)n^2)$ per step, given the filled graph and its order. The same result holds for real rank-one projectors.

Suppose in addition that every $F_i$ has a simple bottom eigenvalue with gap at least $\gamma>0$, and define

$$
s_e=\sum_a\Vert G_{ea}\Vert\Vert K_{ea}\Vert,\qquad
\rho=\max_i\sum_{e\ni i}s_e .
$$

If $\rho<\gamma/8$, then there is a unique global product minimizer, it is nondegenerate, and simultaneous exact site ground-state updates converge to it from any initial product state with contraction factor at most $2\rho/(\gamma-4\rho)$ in maximum site projector operator norm. Newton can then be applied in a fixed chart given by the uncoupled ground states.

## Sparse Newton step

At site $i$, choose a unit reference vector $u_i$ with nonzero inner product with the solution ray, and an orthonormal frame $Z_i$ of its orthogonal complement. The projective chart uses the unit representative

$$
x_i(y_i)=(u_i+Z_iy_i)/\sqrt{1+\Vert y_i\Vert^2}.
$$

Use real coordinates on complex $y_i$. In the local algorithm the reference can be the initial iterate, sufficiently close to the minimum. For any Hermitian $M$, the value $x_i^*Mx_i$ is a real quadratic polynomial divided by $1+\Vert y_i\Vert^2$. Its value, gradient, and Hessian use $O(n^2)$ operations after the one-time change of matrix coordinates. If the workshop Hamiltonian has terms with both factors on a single site, absorb their Hermitian parts into the corresponding $F_i$. This preserves the expectation of the Hermitian Hamiltonian.

Each edge contributes diagonal blocks and one pair of transposed mixed blocks. The mixed block is a sum of outer products of endpoint gradients. Off-diagonal blocks away from interaction edges vanish. At most $dw$ input edges occur, so assembling the gradient and Hessian takes $O(d(1+wk)n^2)$ operations. Near the minimum the Hessian is positive definite. Use block Cholesky in the supplied order. Each real block has dimension at most $2(n-1)$, couples to at most $w$ future blocks at elimination, and changes at most $w^2$ blocks by its Schur complement. Factorization and solution cost $O(d(w+1)^2n^3)$ and use storage for $O(d(w+1))$ blocks. The filled pattern can be constructed once by the width-order clique updates.

The chart energy is real analytic. The Hessian stays positive definite with bounded inverse near the minimizer $y_*$ and obeys a local Lipschitz bound. Integrating the Hessian on the segment from $y_*$ to $y$ expresses the gradient difference. Subtracting the Newton step bounds the new error by a constant times $\Vert y-y_*\Vert^2$. A sufficiently small ball is therefore invariant and has quadratic convergence. The chart and inverse have bounded derivatives locally, giving the same rate for projectors.

## Gap dominance and a global initializer

The conditional energy at site $i$ is $\operatorname{tr}(H_i(P)P_i)$, where $H_i(P)$ is $F_i$ plus the incident terms on site $i$, each scaled by the expectation at the other site. The perturbation from $F_i$ has norm at most $\rho$. The min-max principle gives a bottom eigengap at least $g=\gamma-2\rho$. Let $T_i(P)$ denote its bottom rank-one eigenspace projector.

For two such conditional matrices $A,B$ at the same site, their distance is at most $2\rho<g$. Let $u,v$ be bottom unit eigenvectors of $A,B$, respectively. Project $(A-\lambda_{\min}(B)I)v=(A-B)v$ onto $u^\perp$. The inverse on that space has norm at most $1/(g-\Vert A-B\Vert)$, since the bottom eigenvalues differ by at most $\Vert A-B\Vert$. The norm of the projected vector is exactly $\Vert uu^*-vv^*\Vert$, by restricting the projector difference to their span. Consequently,

$$
\Vert T_i(P)-T_i(Q)\Vert
\le \Vert H_i(P)-H_i(Q)\Vert/(\gamma-4\rho).
$$

The difference of two rank-one projectors has rank at most two, so $|\operatorname{tr}(K(P_j-Q_j))|\le2\Vert K\Vert\Vert P_j-Q_j\Vert$. Summing over incident edges gives the asserted contraction factor, which is strictly less than one. The product projector space is compact and complete. A global minimizer exists and must be a fixed point because each conditional bottom ray is unique. Contraction gives exactly one fixed point, with convergence from every starting point.

At the fixed point use charts centered at its rays. Along tangent coordinates $\eta_i$, each diagonal Hessian block contributes at least $2g\Vert\eta_i\Vert^2$ by differentiating the conditional Rayleigh quotient at its ground vector. Each edge contributes at most $8s_e\Vert\eta_i\Vert\Vert\eta_j\Vert$ in absolute mixed quadratic form. Indeed each first derivative of a site factor is at most twice its operator norm times the site tangent norm, and both mixed blocks contribute. Thus $2ab\le a^2+b^2$ yields

$$
D^2f(P_*)[\eta,\eta]\ge (2\gamma-8\rho)\sum_i\Vert\eta_i\Vert^2 .
$$

For the fixed uncoupled chart, apply the earlier eigenspace estimate to $A=F_i$ and $B=H_i(P_*)$. The angle sine is at most $\rho/(\gamma-\rho)<1$, so that chart contains the minimizer. Its Hessian is positive definite there by the invertible chart change at a stationary point. Ground-state iteration eventually enters any prescribed local Newton neighborhood.

## Verification

Paper proof. The stated complexity bounds are arithmetic costs for Newton steps.
