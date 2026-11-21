# Exact Rényi divergence for alternating and Hermitian tensor Gram matrices

## GP-0281

The formulas below give the full density relative to the uniform matrix model, and therefore the optimal Rényi divergence at every order and all rectangular dimensions. They apply to a Gram matrix from any one flattening of an independent uniform tensor, with the other two mode dimensions combined into the width. The alternating model uses a fixed nondegenerate alternating form on that width. They do not assume that the three different tensor marginals are independent. [Finite-field Gram transfer context](https://arxiv.org/html/2604.00591v2)

### The two models and their uniform rank counts

Use the following parameters in the two cases.

| Model | Coordinate field size $Q$ | Ambient width $d$ | Isometry group $G_j$ | Matrix-space dimension $D$ over $\mathbb F_q$ |
| --- | --- | --- | --- | --- |
| Alternating | $q$ | even | $\mathrm{Sp}_j(q)$, with $j$ even | $n(n-1)/2$ |
| Hermitian | $q^2$ | arbitrary | $\mathrm U_j(q)$ | $n^2$ |

Let $X$ be a uniform $n$ by $d$ coordinate matrix. The random matrix is $XJX^{\mathsf T}$ in the alternating case, with a fixed symplectic matrix $J$, and $XX^*$ in the Hermitian case. Set all empty products to one and $|G_0|=1$. Allowed ranks $r$ satisfy $0\le r\le n$ and are even in the alternating case. The number of rank-$r$ matrices in the uniform comparison space is
$$
 C_r={n\brack r}_{Q}\,\frac{|\mathrm{GL}_r(Q)|}{|G_r|}.
$$
Here the Gaussian binomial chooses the radical, and the quotient factor counts the nondegenerate forms on the quotient. Over the finite fields in question, nondegenerate alternating or Hermitian forms of a fixed dimension are each a single congruence class. The standard group orders used here are
$$
 |\mathrm{Sp}_{2h}(q)|=q^{h^2}\prod_{i=1}^{h}(q^{2i}-1),\qquad
 |\mathrm U_h(q)|=q^{h(h-1)/2}\prod_{i=1}^{h}(q^i-(-1)^i).
$$
One can obtain the first by counting symplectic frames successively, and the second by choosing orthonormal vectors successively; the number of norm-one vectors in dimension $j$ is $q^{j-1}(q^j-(-1)^j)$.

### Exact density by ranks

Let $L_t$ count isotropic lines in a nondegenerate space of dimension $t$ of the selected type. In the alternating case $L_t=(q^t-1)/(q-1)$. In the Hermitian case set $L_0=0$ and, for $t\ge1$, use
$$
 L_t=\frac{q^{2t-1}+(q-1)(-1)^t q^{t-1}-1}{q^2-1}.
$$
Indeed the norm homomorphism on $\mathbb F_{q^2}^\times$ is onto $\mathbb F_q^\times$, with $q+1$ preimages of each nonzero element. Consequently a nontrivial additive character of the norm of a uniform coordinate has mean $-1/q$. Character orthogonality gives the number of norm-zero vectors in the numerator before subtracting one. The same argument at norm one gives the frame count above. Write
$$
 I(t,s)=\frac{\prod_{j=0}^{s-1}L_{t-2j}}
                {\prod_{j=1}^{s}(Q^j-1)/(Q-1)}
 \quad (0\le s\le \lfloor t/2\rfloor)
$$
for the number of totally isotropic $s$-spaces, and take zero for larger $s$. This counts flags by successive lines in the nondegenerate quotient by the previously chosen isotropic flag, and divides by the number of complete flags of an $s$-space.

For a fixed rank-$r$ matrix in the comparison space, the density of its Gram law $\mu$ relative to uniform $\nu$ is zero if $r>d$, and otherwise is
$$
 \ell_r=\frac{q^D}{Q^{nd}}\frac{|G_d|}{|G_{d-r}|}
       \sum_{s=0}^{\min(n-r,\lfloor(d-r)/2\rfloor)}
       I(d-r,s)\prod_{j=0}^{s-1}(Q^{n-r}-Q^j).
$$
To prove the formula, view a matrix yielding the prescribed Gram as a linear map from its $n$-dimensional form space to the nondegenerate $d$-dimensional space. In the Hermitian convention one may take $X^*$ as that map, which is still uniform. Choose a nondegenerate complement of dimension $r$ to the prescribed radical. Its isometric embedding has $|G_d|/|G_{d-r}|$ choices by extension of a nondegenerate frame and transitivity. The radical must map into the perpendicular complement, with totally isotropic image. Fixing an image of dimension $s$ leaves exactly the displayed number of surjections from the $(n-r)$-space to it. Multiplying these counts and dividing by the total $Q^{nd}$ gives the point probability. Multiplication by $q^D$ converts it to the density.

In particular the exact divergence for $0<\alpha<\infty$, $\alpha\ne1$, is
$$
 D_\alpha(\mu\Vert\nu)=\frac{1}{\alpha-1}
 \log\!\left(q^{-D}\sum_r C_r\,\ell_r^\alpha\right).
$$
At order one the expression is $q^{-D}\sum_r C_r\ell_r\log\ell_r$, with zero terms omitted. At infinity it is $\log\max_r\ell_r$. These dimension-uniform identities include every width, whether or not the law has full support.

### Simpler exact Fourier formulas for order two

In the alternating case use the additive dual pairing on upper-triangle entries. One symplectic pair of columns $u,v$ contributes $uv^{\mathsf T}-vu^{\mathsf T}$, and an additive character indexed by an alternating matrix of rank $r$ evaluates this summand as $\psi(u^{\mathsf T}Hv)$ for its corresponding alternating index $H$. This assertion is still valid in characteristic two, since the pairing uses one representative entry per off-diagonal pair. Averaging first over $u$ and then $v$ gives $q^{-r}$. Thus with $d/2$ independent pairs the Fourier coefficient is $q^{-dr/2}$. In the Hermitian case use the nondegenerate trace pairing on Hermitian matrices. A rank-$r$ index can be diagonalized by congruence, its one-column Fourier coefficient is $(-1/q)^r$ by the norm calculation, and $d$ columns give $(-1/q)^{dr}$. Plancherel gives
$$
 \exp(D_2(\mu\Vert\nu))=
 \begin{cases}
 \displaystyle\sum_r C_r q^{-dr}, &\text{alternating},\\[2pt]
 \displaystyle\sum_r C_r q^{-2dr}, &\text{Hermitian}.
 \end{cases}
$$
The alternating Fourier coefficients are all nonnegative, so Fourier inversion gives $\ell_0=\max_r\ell_r=\sum_r C_rq^{-dr/2}$. Likewise in the Hermitian case the maximum occurs at zero when $d$ is even and equals $\sum_r C_rq^{-dr}$. The rank-density formula covers odd Hermitian widths without a sign restriction.
