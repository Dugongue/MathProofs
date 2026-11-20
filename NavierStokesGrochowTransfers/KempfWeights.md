# Exponential Kempf weights for sparse forms of degree eight

For every integer $m\ge1$ there are explicit homogeneous forms $F_m,G_m$ of degree eight on $2(m+1)$ complex variables. The form $F_m$ is in the unique closed $\mathrm{SL}_{2(m+1)}(\mathbb C)$-orbit in the orbit closure of $G_m$. Every primitive optimal Kempf subgroup driving $G_m$ into this closed orbit has eigenweight diameter at least $2^{m-1}$. In fact its primitive weight multiset is given explicitly below. The forms have at most $3m$ monomials and formulas of size $O(m)$ over $\mathbb C$.

This strengthens the variable-degree example for Grochow–Mulmuley–Qiao Question 4.5 by keeping the form degree fixed. The result concerns optimal cocharacters for this family. [Question 4.5](https://arxiv.org/html/1605.02815#S4.SS1) · [Earlier MathProofs construction](https://github.com/Dugongue/MathProofs/tree/84b007e/KempfDegenerationDegree)

## 1. Forms and finite characters

Use variables $x_0,\ldots,x_m,y_0,\ldots,y_m$. Write $[X^\alpha]$ for the monomial $X^\alpha$ scaled to unit length in the standard unitary-invariant Hermitian form on $\operatorname{Sym}^8(\mathbb C^{2m+2})$. Explicitly the scale is $\sqrt{8!/\prod_j\alpha_j!}$. These vectors are orthonormal. Let
$$
 P_j=x_j^4y_j^4,\qquad
 E_i=x_{i+1}^2y_i^4x_0^2,\qquad
 E_i'=y_{i+1}^2x_i^4y_0^2,\qquad
 M=x_1^2y_0^2(x_m y_m)^2
$$
where $0\le j\le m$ and $1\le i<m$. All these monomials are distinct, including when $m=1$ and the list of $E_i$ is empty. For a given $j$, the sum of exponents of $x_j$ across the $E_i,E_i'$ equals that of $y_j$ by interchange of $x$ and $y$. Call this integer $c_j$. Set $C=2m+6$ and define
$$
 F_m=\sum_{j=0}^m\sqrt{(C-c_j)/4}\,[P_j] + \sum_{i=1}^{m-1}([E_i]+[E_i']),\qquad
 G_m=F_m+[M].
$$
For $j=0$ one has $c_0=2(m-1)$. For other $j$, the only possible contributions are $2$ and $4$. Thus every coefficient of a $[P_j]$ is strictly positive. The exponents are bounded by eight, and the constants are explicit square roots of rationals.

Let $H$ be the finite group of diagonal changes of variables
$$
 x_j\longmapsto \epsilon_j\zeta x_j,\qquad
 y_j\longmapsto \epsilon_j\zeta^{-1}y_j,\qquad
 \epsilon_j\in\{1,-1\},\quad\zeta^4=1.
$$
Each pair has determinant one. Every displayed monomial is fixed by $H$, since its exponents are even and the difference between the total $x$ and total $y$ exponents is divisible by four. The coordinate characters are pairwise distinct. The independent signs distinguish different indices, and $\zeta=i$ distinguishes $x_j$ and $y_j$ at the same index.

The exact transfer from the Navier–Stokes proof is its normalized character projection in the harmonic split. Replace the torus integral against a character by the finite average $|H|^{-1}\sum_{h\in H}\overline{\chi(h)}\,h$. As in the harmonic split, this operator preserves the prescribed character sector and kills the others. Here the zero-character projector for conjugation on matrices is $A\mapsto |H|^{-1}\sum_h hAh^{-1}$, which keeps exactly the diagonal. The projectors on the underlying vector space have one-dimensional images. These identities give both the moment calculation and the optimal flag reduction. [Alpöge–Buckmaster, harmonic split at the pinned revision](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L148)

## 2. Closed orbit and transverse direction

Let $S$ denote the diagonal maximal torus of $\mathrm{SL}_{2m+2}(\mathbb C)$. Write the action as $g\cdot f(X)=f(g^{\mathsf T}X)$ so the weights of diagonal changes agree with the displayed substitutions. For an infinitesimal traceless change of variables $A$, let $A\cdot F_m$ denote the derivative of the action. By $H$-invariance of $F_m$ and unitarity of $H$,
$$
 \langle A\cdot F_m,F_m\rangle
 =\langle \operatorname{avg}_{h\in H}(hAh^{-1})\cdot F_m,F_m\rangle.
$$
For diagonal $A$ with entries $a_j$, this is $\sum_j a_j\sum_\alpha \alpha_j |(F_m)_\alpha|^2$. The inner sum is $C$ for every coordinate by construction. The result vanishes because $A$ has trace zero. The Kempf–Ness criterion therefore gives a closed orbit $O=\mathrm{SL}_{2m+2}(\mathbb C)\cdot F_m$. [Kempf–Ness, moment-map formulation](https://seigal.github.io/amendola2024bridge.pdf)

The monomial $[M]$ is transverse to $O$ at $F_m$. If it belonged to $T_{F_m}O$, the orbit differential would give $A\cdot F_m=[M]$ for some traceless $A$. Averaging $A$ under $H$ would keep the right side because $[M]$ is fixed, and would replace $A$ by a diagonal matrix. A diagonal infinitesimal action stays in the span of the support of $F_m$, which does not contain $[M]$. This proves transversality.

Take the diagonal subgroup with weights $u_0=0$, $u_j=2^{j-1}$ for $1\le j\le m$ on $x_j$ and weights $-u_j$ on $y_j$. The trace of the weights is zero. The $P_j,E_i,E_i'$ have weight zero and $M$ has weight two. This subgroup sends $G_m$ along $F_m+t^2[M]$ and gives $F_m$ at $t=0$. If $G_m$ were in $O$, the whole line $F_m+s[M]$ would be in $O$ since every nonzero complex number is a square. Its tangent would contradict transversality. The closed orbit $O$ is the unique closed orbit in the closure of the orbit of $G_m$, by affine geometric invariant theory. [Orbit-closure conventions](https://arxiv.org/html/1605.02815#S3.SS1)

## 3. Every optimum can be computed in the diagonal torus

Apply Kempf's optimality theorem to $G_m$ with closed invariant target $O$. The theorem gives a common parabolic $P$ for the primitive optimal cocharacters. It contains the stabilizer of $G_m$. Indeed the stabilizer normalizes the optimal class by equivariance, hence normalizes $P$, and parabolics are self-normalizing. In particular $H\subseteq P$. Any parabolic in the special linear group stabilizes a partial flag of the defining space. Each space of the flag is $H$-invariant. Applying the one-dimensional character projectors to a vector in a flag space shows that the space is a sum of coordinate lines. Thus $S\subseteq P$. Kempf's theorem gives a primitive optimum in $S$, and all primitive optima are conjugate to it. Conjugation preserves eigenweights. [Kempf, Theorem 3.4](https://annals.math.princeton.edu/1978/108-2/p04) · [Bate–Martin–Röhrle–Tange, relative Theorem 4.5](https://rtange.github.io/research/git.pdf#page=15)

For any diagonal cocharacter with limit in $O$, all supported monomial weights of $G_m$ are nonnegative because its limit exists. Write $u_j,v_j$ for the weights on $x_j,y_j$. The identity
$$
 \sum_\alpha |(F_m)_\alpha|^2\,\langle\alpha,(u,v)\rangle
 =C\sum_j(u_j+v_j)=0
$$
forces every supported monomial weight of $F_m$ to vanish. The weight of $M$ must be positive, since a zero weight would give $G_m$ itself as the limit. The $P_j$ give $v_j=-u_j$ and the $E_i$ give $u_{i+1}-u_0=2(u_i-u_0)$. The weight of $M$ is $2(u_1-u_0)$, so $d=u_1-u_0$ is a positive integer. Consequently
$$
 u_j=u_0+2^{j-1}d \quad (1\le j\le m),\qquad u_m-u_0\ge 2^{m-1}.
$$
This bound applies to the eigenweight diameter of each optimum. The largest absolute eigenweight is at least half the diameter, which also lower-bounds the maximum Laurent degree of a matrix entry for any constant conjugate. The sum of absolute eigenweights, the total degree in Grochow–Mulmuley–Qiao Theorem 7, is at least the diameter. The simple-coroot coordinate sum in Theorem 8 is at least the largest absolute eigenweight.

## 4. Exact primitive optimum

The order of contact of the line $F_m+s[M]$ with $O$ is one. The orbit is closed, and transversality means that some polynomial in its vanishing ideal has nonzero derivative in direction $[M]$ at $F_m$. Every polynomial in that ideal vanishes at $s=0$. Substituting $s=t^{2d}$ gives precisely order $2d$ for the pulled-back ideal along each admissible diagonal cocharacter. This is Kempf's numerator for the relative closed target.

Write $b_0=0$, $b_j=2^{j-1}$ for $j\ge1$, and $a=u_0$. The square of the Weyl-invariant Euclidean length is $2\sum_j(a+db_j)^2$. For fixed ratio $a/d$, the numerator and denominator are homogeneous of degree one in $d>0$. Completing the square shows that their ratio is uniquely maximized at
$$
 a/d=-\frac{2^m-1}{m+1}.
$$
The optimal ratio is rational and is achieved by integral weights. Put $g=\gcd(2^m-1,m+1)$. The primitive pair is
$$
 a=-(2^m-1)/g,\qquad d=(m+1)/g.
$$
These are coprime, and the greatest common divisor of all the weights is $\gcd(a,d)$ because $u_0=a$ and $u_1=a+d$. This gives a primitive subgroup with weights $\{a+db_j,-a-db_j:0\le j\le m\}$, the multiset for every primitive optimum. Its diameter is
$$
 \frac{2((m-1)2^{m-1}+1)}{g},
$$
since $u_0$ and $u_m$ are the extreme $x$-weights and $|u_m|\ge |u_0|$ for $m\ge1$. The fixed degree keeps the input form and its closed-orbit limit in VP.

## Verification

The geometric theorem is a written proof. The companion Lean theorem covers the integer weight inequalities in Section 3. The geometric invariant theory arguments are in the written proof.
