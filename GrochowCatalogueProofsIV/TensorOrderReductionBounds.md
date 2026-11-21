# Representation and orbit-count bounds on dimensional compression

## GP-0276 — Sharp dimension bound for equivariant polynomial order maps

Let $K$ be algebraically closed of arbitrary characteristic, $n\ge2$, $d\ge4$ and $G=\mathrm{SL}_n(K)^d$. Let $W_1,W_2,W_3$ be finite-dimensional rational $G$-representations, so the actions on them come from algebraic homomorphisms into their general linear groups. Suppose
$$
\Phi:(K^n)^{\otimes d}\longrightarrow W_1\otimes W_2\otimes W_3
$$
is a polynomial equivariant map that distinguishes zero from a nonzero pure tensor. Then $\max_i\dim W_i\ge n^{\lceil d/3\rceil}$. The assertion even permits arbitrary target orbit actions beyond the image of $G$, since distinguishing the source orbits forces the two output values to differ. For $3\nmid d$ the lower bound exceeds $O(n^{d/3})$.

Use the standard diagonal torus in each source group factor. For $v=e_1^{\otimes d}$, those tori act by a character $\chi$ whose component on every factor is the first-coordinate character. Every homogeneous part $\Phi_\ell$ is equivariant, because the two group actions are linear and a polynomial separates into degrees. By transitivity of $G$ on nonzero pure tensors, $\Phi(v)\ne\Phi(0)$. Thus $\Phi_\ell(v)\ne0$ for some $\ell>0$. For diagonal $t$ we have
$$
 t\Phi_\ell(v)=\Phi_\ell(tv)=\chi(t)^\ell\Phi_\ell(v).
$$
The weight $\chi^\ell$ is nontrivial on every factor, including when the characteristic divides $\ell$, because this is an algebraic torus character.

Decompose each $W_i$ into torus weight spaces. Some triple of occurring weights $\lambda_1,\lambda_2,\lambda_3$ has sum $\ell\chi$, writing torus characters additively. Their sets of factors on which they are nontrivial cover all $d$, so one weight $\lambda_i$ has at least $\lceil d/3\rceil$ such factors. The normalizer of the torus preserves the weight set and acts by permutations of the $n$ diagonal coordinates independently in each factor. A nonzero character of one $\mathrm{SL}_n$ torus is represented by an integer vector modulo the all-ones vector, with at least two distinct entries. Two permutations of that vector are equivalent in the quotient only if equal, since their coordinate sums agree. Thus it has at least $n$ distinct Weyl translates, by the multinomial count for arrangements of a nonconstant multiset of $n$ entries. Independent translates across the active factors give at least $n^{\lceil d/3\rceil}$ distinct occurring weights in $W_i$, proving the bound.

The bound applies to the equivariant polynomial model even with nonlinear auxiliary slots. It leaves arbitrary non-equivariant encodings as a separate question. Balanced grouping of factor representations already attains this exponent for the equivariant map condition, without making any assertion of orbit reflection for the bare grouping. [Catalogue context](https://arxiv.org/abs/1907.00309) · [Prior functorial reductions](https://github.com/Dugongue/MathProofs/tree/d7366c4348bc03f0e93cb8674db191de32ba58bf/FunctorialTensorReductions)

## GP-0278 — Exponential density loss for exact deterministic fixed-format reductions

Fix $d>3$. Let a deterministic map from all order-$d$, side-$n$ tensors over $\mathbb F_q$ into one fixed rectangular three-tensor format over $\mathbb F_q$ preserve and reflect product-GL orbit equivalence. If the domain is uniform, the support of the output distribution has density at most
$$
q^{-\Omega_d(n^{2d/3})}
$$
relative to uniform output tensors. The estimate does not require equivariance, a complexity bound, or an injective object map. It rules out inverse-polynomial support density for such a reduction.

The number of source orbits is at least $q^{n^d-dn^2}$, since $|\mathrm{GL}_n(q)|\le q^{n^2}$. Let $a$ be the largest output axis dimension and $b$ the product of the other two, so the target volume is $M=ab$ and $a\ge M^{1/3}$. Acting only on the largest output axis turns each flattened $a$-by-$b$ matrix into any other matrix with the same row space. Thus the number of target orbits under the full action is at most
$$
 \sum_{j=0}^{\min(a,b)} {b\brack j}_q
 \le4(b+1)q^{\max_{0\le j\le\min(a,b)}j(b-j)}.
$$
The factor 4 bounds the product of $(1-q^{-t})^{-1}$ in the Gaussian binomial formula, since $q\ge2$. If $a\le b/2$ the exponent is $M-a^2$. If $a>b/2$ the exponent is at most $b^2/4<M/2$. This yields
$$
 \log_q(\#\text{ target orbits})
 \le M-\min(a^2,M/2)+O(\log(M+1)).
$$

The map injects source orbit classes into target classes. If $M\ge2n^d$ the claimed lower bound on volume surplus follows. Otherwise the displayed bounds first imply $M\ge n^d/2$ for sufficiently large $n$. Then the loss term $\min(a^2,M/2)$ is $\Omega_d(n^{2d/3})$, which dominates $dn^2+O(\log(M+1))$. Hence $M\ge n^d+\Omega_d(n^{2d/3})$. The deterministic output support has at most $q^{n^d}$ tensors out of $q^M$. This also bounds the total variation distance from uniform below by one minus the stated support-density bound.

The estimate is uniform in $q$ and does not invoke the equivariant argument for GP-0276. Independent randomization within the output orbits can change the support count and is outside this statement. [Catalogue context](https://arxiv.org/abs/1907.00309) · [Previous tensor order and packing notes](https://github.com/Dugongue/MathProofs/tree/d7366c4348bc03f0e93cb8674db191de32ba58bf/TensorSignPacking)
