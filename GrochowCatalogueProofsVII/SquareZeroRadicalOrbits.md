# Polynomial radical-orbit testing for square-zero classical commutants

## GP-0285

Let $K$ have characteristic zero or be finite with efficient field arithmetic. In each of three classical tensor modes let an adjoint-stable finite-dimensional algebra $B_i\subseteq\operatorname{End}(V_i)$ have square-zero radical $J_i$. Suppose that the $J_i$ are displayed by bases. Given two tensors, one can decide whether they are related by the kernel of the map from the product of isometry groups in $B_i^\times$ to their semisimple tops, and return a transporter. The algorithm uses polynomially many field operations in the matrix and coefficient dimensions. As a consequence a supplied classical transporter on the top can be tested for compatibility with the full tensors in polynomial time, with no assumptions on the sizes, commutativity, or number of its simple factors. This addresses the radical lifting subproblem. Finding the top transporter is a separate part of the general catalogue question. [Classical tensor covariance context](https://arxiv.org/html/2604.00591v2)

Work over the adjoint fixed field when the adjoint is semilinear, using restriction of scalars. Let $J_i^-$ be the subspace of $x\in J_i$ with $x^*=-x$. The isometries lifting identity in the top are exactly $1+J_i^-$ because
$$
 (1+x)^*(1+x)=1+x^*+x
$$
when $x\in J_i$. In the full tensor module let $E$ be the vector space of sums of the three local operators from $J_i^-$. All elements of $E$ commute: products of two operators acting in the same mode vanish, and operators on different modes commute. Let $\mathcal A$ be the unital commutative algebra they generate and $J$ its ideal spanned by positive-degree products. Then $J^4=0$. In characteristic zero, for $X=\sum_i x_i\in E$, the product action equals
$$
 \prod_{i=1}^3(1+x_i)=\exp(X)=1+X+X^2/2+X^3/6 .
$$
Conversely every element $\exp(X)$ with $X\in E$ is such a product. This is a direct expansion, with at most one participating operator per mode.

Given the source tensor $T=0$, accept exactly when the target is zero. Otherwise enumerate the words of length at most three in displayed bases for $E$. Evaluate them on $T$ and take a basis of their span $M=\mathcal A T$. This computation is polynomial. The space $M$ identifies with the cyclic quotient algebra $\overline{\mathcal A}=\mathcal A/\operatorname{Ann}_{\mathcal A}(T)$ by $f\mapsto fT$. Its multiplication table is computed by applying operator representatives for the retained basis and expressing the outputs in that basis. First test that the target lies in $M$. Let $\overline f$ be its unique quotient coordinate. Test $\overline f-1\in\overline J$ and compute
$$
 \log(\overline f)=(\overline f-1)-(\overline f-1)^2/2+(\overline f-1)^3/3 .
$$
The truncated exponential and logarithm are inverse polynomials on this nilpotent ideal, as verified by substitution modulo degree four. Therefore the lifting condition is precisely that $\log(\overline f)$ lie in the image of $E$ in the cyclic quotient. Solve this last linear membership problem with coefficients. Any recovered $X=\sum_i x_i$ yields the required transporter $\prod_i(1+x_i)$. This also gives exact stabilizer parameters for the kernel, since its stabilizer is the exponential of the nullspace of $E\to M$.


### Positive characteristic

Use the same cyclic quotient, and let $P=J_1^-\oplus J_2^-\oplus J_3^-$ as a vector space over the prime field $\mathbb F_p$. The map $\phi:P\to 1+\overline J$ given by the product action is a group homomorphism from the additive group. Let $P_k$ be the preimage of $1+\overline J^k$. The map
$$
 P_k\longrightarrow \overline J^k/\overline J^{k+1},
 \qquad x\longmapsto \phi(x)-1
$$
is additive and hence $\mathbb F_p$-linear, since the product of two terms in $\overline J^k$ lies in $\overline J^{k+1}$. Evaluate this map on a basis over the prime field. Given a current product matching the required quotient element modulo $\overline J^k$, multiply it out of the target and solve the linear system for the residual image in the displayed quotient. Its kernel is the next space $P_{k+1}$. Starting with $P_1=P$ and requiring $\overline f\in1+\overline J$, three such steps decide and construct the exact orbit transport. The final kernel is the stabilizer in $P$. This works in characteristics two and three as well as in larger positive characteristics, with a number of arithmetic operations polynomial in the field encoding length and matrix sizes.
The same procedure applies to a supplied top transporter. Given an invertible arbitrary lift $g$ in one mode whose top is unitary, put $D=g^*g-1\in J_i$. To correct $g$ on the right by $1+x$ is precisely to solve $x+x^*=-D$ in $J_i$, since
$$
 (1+x)^*(1+D)(1+x)=1+D+x+x^*.
$$
If the linear system is inconsistent no lift of that top exists. Otherwise $g(1+x)$ is an isometric lift with the same top; in odd characteristic $x=-D/2$ always works. An arbitrary lift of a unit in the top is invertible because the radical is nilpotent. Lift each supplied mode, apply the resulting product action to the source, and run the kernel test just proved. All operations use linear algebra, degree-three products, and explicit matrices. Over rational arithmetic or a fixed explicitly represented finite field this gives polynomial bit complexity as well.
