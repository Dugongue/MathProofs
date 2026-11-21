# Linear-size uniform row sketches for a kernel column-selection class

[Simons Workshop Problem 4.4](https://arxiv.org/html/2602.05394v3#S4.SS1.SSS3) asks for conditions on the kernel giving reliable column selection from O(k) uniformly sampled rows. The following conditions apply directly to a kernel feature representation, and yield a constant-factor transfer with an explicit efficient selector for orthogonal feature clusters.

Let f(x,ω)=z(x)ᵀa(ω), where z takes values in R^D and a may be complex. The uniform law on the row nodes satisfies E[z zᵀ]=I and, for every real unit u, E exp((uᵀz)^2/L²)≤2. Suppose D≤C₀ k. For 0<η<1 and failure tolerance δ, a sample of
$$
r\ge C L^4\eta^{-2}(D+\log(2/\delta))
$$
rows preserves every squared norm in the entire column space within factors 1±η, after scaling by n/r. This holds for independent sampling or uniform sampling without replacement. If the displayed requirement exceeds n, take all n rows. The condition is independent of the frequency grid or coefficient geometry. For example, a kernel which is affine-linear in D independent signs on the full Boolean cube, including a constant as an extra feature when desired, has L bounded by an absolute constant by the elementary Rademacher moment generating function bound.

For proof, center the fixed-direction squares (uᵀz)^2 at their mean one. The exponential moment assumption gives moments of order j bounded by 2 j! L^(2j) before centering. The scalar Bernstein bound gives two-sided deviation at most η/2 with failure probability at most 2 exp(−c r η²/L⁴). For sampling without replacement, Hoeffding's comparison of moment generating functions gives the same bound. Take a 1/4-net of the unit sphere of size at most 9^D. A symmetric matrix whose quadratic form is bounded by η/2 on the net has operator norm at most η, by writing each unit vector as a net vector plus an error of norm at most 1/4. Apply this to the empirical feature Gram matrix minus I and take a union bound. The resulting real quadratic-form bound also holds for complex coefficients by applying it to real and imaginary parts.

For any column index set J and coefficient matrix T, apply the embedding to each column of A−A[:,J]T. This gives both inequalities for its squared Frobenius norm. If J̃ has residual on the sketch at most α times that of a comparator J, then
$$
\|\Pi_{\tilde J} A-A\|_F
\le \alpha\sqrt{\frac{1+\eta}{1-\eta}}\ \|\Pi_J A-A\|_F .
$$
Indeed each residual minimized over T is distorted by at most the same factors. In particular the exact sketch optimizer obeys the estimate with α=1. This is uniform over selected indices and loses neither a union bound over subsets nor an extra log k in the number of rows.

## An explicit selector

Assume additionally that the coefficient vectors are nonzero multiples of a specified collection of mutually orthogonal feature directions, with zero columns ignored. This is a further direct property of the kernel expansion. One column from any group spans the entire group. On the full grid, the groups have orthogonal column spans by isotropy, so the squared residual of selecting one column from each of k groups is exactly the sum of the omitted groups' squared column energies. Select the k groups of highest empirical total energy, taking one column per group. Every group total is preserved within 1±η. Since the omitted group sum was minimized on the sample, its true value is at most (1+η)/(1−η) times the true minimum. This gives the same constant-factor guarantee and uses O(rm) entries and arithmetic plus sorting the group totals, with the group assignments read from the kernel. For fixed η,L, even inverse-polynomial failure probabilities in k require only O(k) rows in both the transfer theorem and this efficient case.

[Hoeffding, Probability Inequalities for Sums of Bounded Random Variables, Theorem 4](https://doi.org/10.1080/01621459.1963.10500830).
