# Reduced conormal bound for determinant pencils

## GP-0587

Let a nonzero homogeneous determinant $F_0=\det A(x)$ on $\mathbb P^n_{\mathbb C}$ come from an $m$ by $m$ matrix of linear forms, with $n\ge 2$. Write $F_0=\text{constant}\cdot\prod_i f_i^{a_i}$ into pairwise distinct irreducible factors. The following weighted cycle bound holds:
$$
\sum_i a_i\,\delta_{n-2}\big(\operatorname{Con}(V(f_i))\big)
\ \le\
\sum_{j=1}^{n-1}\binom{m}{j}\binom{m-1}{n-1-j}\binom{n-2}{j-1}.
$$
For symmetric $A$ the right side can be replaced by $2^{n-2}\binom{m}{n-1}$. Taking weight one for every factor gives the full reduced conormal bound asked in Remark 4.4. In fact the argument below shows survival with factor multiplicity in every conormal multidegree under an arbitrary squarefree smoothing of fixed total degree. [Determinant conormal estimate, Theorem 1.4](https://arxiv.org/html/2606.13628#S1) · [Reduced conormal question, Remark 4.4](https://arxiv.org/html/2606.13628#S4)

### A squarefree pencil deformation

Choose projective coordinates $(x_0,v_1,\ldots,v_{n-1},z)$ such that the projective point of the $z$ axis has $F_0\ne 0$. After dehomogenizing $x_0=1$, the polynomial $F_0(v,z)$ then has degree $m$ in $z$ with a nonzero constant leading coefficient. Each factor has the same property with its own degree and no component lies at infinity. Let $B$ be diagonal with entries $z-\lambda_j x_0$ for distinct complex scalars $\lambda_j$ and put $F_t=\det(A+tB)$. The leading $z$ coefficient of $F_t$ is a unit near $t=0$. Its univariate discriminant in $z$ is nonzero over $\mathbb C(v,t)$, since at $u=0$ the rescaled determinant $u^m F_{1/u}=\det(uA+B)$ has the distinct roots $\lambda_j$. The dehomogenized polynomial has no factor independent of $z$ over $\overline{\mathbb C(t)}$ because its leading coefficient is constant in $v$. Its degree in $z$ also rules out an $x_0$ factor on homogenizing. Thus the generic projective determinant is geometrically squarefree. The construction keeps symmetry whenever the original pencil is symmetric.

### An effective specialized cycle

Over the discrete valuation ring $R=\mathbb C[t]_{(t)}$, take the scheme-theoretic closure $Z$ of the reduced generic conormal in the product of projective point and dual spaces. This closure is flat: its affine coordinate rings have no $t$-torsion because they inject into their generic-fibre localizations. Each irreducible component of the closure dominates the base and has relative dimension $n-1$ generically. The special fibre is a Cartier divisor on the closure and its support has pure dimension $n-1$, as can be checked by viewing the closure around zero as a finite-type family over the affine parameter line and using the dimension theorem on each dominating component. The fundamental cycle $[Z_0]$ is effective. Its multidegrees equal the generic ones by flat projectivity. For example, use constancy of the Hilbert polynomials under each ample polarization $\mathcal O(b,c)$ with positive integers $b,c$. Their leading coefficients form a homogeneous polynomial in $b,c$ whose coefficients are the indicated mixed hyperplane intersection degrees.

### A transverse generic projection and its roots

Put $k=\mathbb C(v_1,\ldots,v_{n-1})$. On the generic $v$-fibre the points of the hypersurface are exactly the $m$ distinct roots of $F_t(v,z)$ over an algebraic closure. Along every such root, $F_{t,z}$ is nonzero, so its conormal is in the dual affine chart with $z$-coordinate normalized to one. Its normalized $v_j$-coordinate is the ratio $F_{t,v_j}/F_{t,z}$. Its $x_0$-coordinate is determined by the incidence condition that the hyperplane contain the point.

Divide $F_t(v,z)$ by its leading coefficient to get a monic polynomial over $k[t]_{(t)}$. Over $\bar{k}$, Newton–Puiseux gives a common positive integer $N$ such that all its roots $z_\ell(u)$ lie in $\bar{k}[[u]]$ with $t=u^N$. The monic condition implies their valuations are nonnegative. Reduction gives each root $\alpha$ of a reduced factor $f_i(v,z)$ exactly $a_i$ times, since the factor is separable over $k$ in characteristic zero. Extend the derivations $\partial/\partial v_j$ uniquely from $k$ to $\bar{k}$ and then coefficientwise to the Laurent series field, with $u$ fixed. Differentiating $F_t(v,z_\ell(u))=0$ gives
$$
\frac{F_{t,v_j}}{F_{t,z}}\big(v,z_\ell(u)\big)
=-\frac{\partial z_\ell(u)}{\partial v_j}.
$$
The right side has no negative powers and reduces to $-\partial\alpha/\partial v_j$. Differentiating $f_i(v,\alpha)=0$ identifies this value with $(f_i)_{v_j}/(f_i)_z$. Incidence then gives the same limiting $x_0$-coordinate as the normalized conormal to $V(f_i)$. Thus every branch above $\alpha$ specializes to the corresponding conormal point of the reduced factor, including when every ambient derivative of $F_0$ vanishes along that factor.

### Multiplicity at a reduced conormal

In the two affine charts just used, pass to the generic $v$-fibre and then to $\bar{k}[[u]]$. These operations are flat and commute with taking the closure of the generic fibre: on an affine coordinate ring this closure is obtained by quotienting by the parameter-torsion ideal, and flat base change preserves the injection of the resulting ring into its parameter localization. The generic points are now the $m$ distinct series sections just constructed. Their closure is the scheme-theoretic union of these sections. Its coordinate algebra is a subalgebra of $\bar{k}[[u]]^m$ by simultaneous evaluation, so it is finite and torsion-free over the series ring and therefore free of rank $m$. The characteristic polynomial of multiplication by $z$ is $\prod_\ell(T-z_\ell(u))$, as is seen on the generic fibre. On the special fibre, the summand at $z=\alpha$ has length $a_i$, given by the multiplicity of $\alpha$ in the specialized characteristic polynomial. Every section over $\alpha$ has the same special dual coordinates, so this summand is supported at one point.

The conormal to $V(f_i)$ projects dominantly to the $v$-space. Restricting to its generic fibre and extending the ground field to $\bar{k}$ splits its residue field into separable points without changing the local length at each. Hence $\operatorname{Con}(V(f_i))$ occurs in $[Z_0]$ with coefficient $a_i$. Components of $[Z_0]$ supported outside the chosen charts or above proper subvarieties of the $v$-space can only add effective terms. Mixed hyperplane degrees are nonnegative on effective cycles, so the weighted sum is bounded by the generic conormal multidegree.

To apply the complex determinant estimate to the generic fibre, take the subfield generated over $\mathbb Q$ by all finitely many pencil coefficients. It is countable. Sending the indeterminate $t$ to any complex number transcendental over it gives a complex pencil with the same generic fibre after ground-field extension, hence the same conormal multidegrees. Its determinant is squarefree by the discriminant test, so Theorem 1.4 bounds its full conormal. This supplies both displayed bounds. The repeated-factor specialization here is a written proof. The formula of Sabbah is the broader context for conormal multiplicities. Borovik and Briand state the multiplicity-one conclusion for a reduced special fibre, while the generic transverse projection above calculates the top-dimensional terms when the special equation has repeated factors. [Lagrangian specialization, Theorem 3.16 and Corollary 3.17](https://arxiv.org/html/2607.17966v1#S3)
