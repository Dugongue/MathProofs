# Condensing the embedded first rank-drop scheme over finite fields

Let $k=\mathbb F_q$ be fixed and let $T\subseteq\mathbb P^{b-1}_k$, $b\ge2$, be a nonempty finite closed subscheme of length $\delta=\dim_k\Gamma(T,\mathcal O_T)$. Write $e$ for its maximum geometric tangent dimension and set $s=\max(2,e+1)$. Use the symmetric matrix presentation of the preceding first rank-drop construction, with $m=h+1$, $h\ge2$. Its full first rank-drop scheme is $T\times\operatorname{OGr}(m,2m)$. Its embedding in the direction Grassmannian is built from the repeated support $\ell\otimes k^{2m}$, for the line $\ell$ of a point of $T$. [First rank-drop geometry and repeated supports](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md)

**Theorem.** There is a deterministic scheme-preserving compression of this embedded rank-drop scheme with the following bounds.

1. An input-independent family of $(b-1)\delta^2+1$ linear projections over a common finite extension contains one whose restriction to $T$ is a closed immersion into $\mathbb P^{s-1}$. The family is explicit and can be listed in time polynomial in $b,\delta$ for fixed $q$. A slightly larger family of $(b-1)(\delta^2+\delta)+1$ projections can be certified by a single affine chart using the finite coordinate algebra of $T$. When $T$ has at least two geometric points, the target projective dimension $s-1$ is optimal for any closed immersion, even after field extension.
2. Given the finite algebra $A=\Gamma(T,\mathcal O_T)$ by a multiplication table and its $b$ projective coordinate functions in a trivialization of $\mathcal O_T(1)$, a deterministic polynomial-time algorithm over $k$ finds a linear projection to $\mathbb P^{w-1}_k$ with
   $$
   w\ \le\ \min\{\,b,\ s+\lceil\log_q(\delta^2)\rceil\,\}
   $$
   whose restriction to $T$ is a closed immersion. The algorithm works across conjugate support points and preserves arbitrary nilpotents.

A successful projection with $k$-linear output dimension $w$, or extension-linear dimension $s$ in the first variant, induces a closed immersion of the full rank-drop scheme into the Grassmannian of $m$-planes in $2mw$ or $2ms$ dimensions, respectively. The same map preserves the marked pure section. The ground-field bound uses the supplied finite coordinate algebra. Existence and certification are separate from finding that algebra from a general quadratic presentation.

## 1. Which subspaces must retain rank

Work first over an algebraic closure $\bar k$. For every geometric point $p$ of $T$, let $J_p\subset\bar k^b$ be the ambient vector space of its embedded projective tangent space. This contains the support line $\ell_p$ and has dimension $1+\dim T_pT$. For every unordered pair of distinct points $p,p'$, also take the secant span $J_{pp'}=\ell_p+\ell_{p'}$ of dimension two. A linear map injective on all these listed spaces defines a projective map on $T$, separates its geometric points, and has injective tangent maps there.

These conditions imply a closed immersion with the original scheme structure. Over $\bar k$, take an affine chart containing all projected points. The map from its coordinate ring to the local Artin ring at each point surjects. Indeed the induced map generates the maximal ideal modulo its square by tangent injectivity. These elements generate the local algebra by successively generating the powers of its maximal ideal, which terminates by nilpotence. The kernels of the maps to the local rings are comaximal for distinct images, since the distinct supporting maximal ideals have powers in the kernels. The Chinese remainder theorem gives surjectivity onto the product of the local rings. Thus the map is a closed immersion in that chart. Its image is also closed in projective space, for instance by properness of the finite scheme. Closed immersion descends along the extension of fields. This is the finite-scheme instance of separation of points and tangent vectors. [Stacks Project, separating points and tangent vectors](https://stacks.math.columbia.edu/tag/0E8R)

If $T$ has $N_0$ geometric points, then $N_0\le\delta$ and
$$
   \sum_p \dim J_p\le\delta,\qquad
   \sum_p\dim J_p+\sum_{\{p,p'\}}\dim J_{pp'}\le\delta^2.
   \tag{1}
$$
The first inequality is the bound $1+\dim(\mathfrak m_p/\mathfrak m_p^2)\le\operatorname{length}(\mathcal O_{T_{\bar k},p})$ at each local Artin ring. The second uses $2\binom{N_0}{2}\le\delta(\delta-1)$. Any closed immersion separates at least two geometric points if there are two and injects the largest tangent space. Thus its target projective dimension is at least $\max(1,e)=s-1$ when there are two or more points.

## 2. A uniform seed family at the optimal extension width

Identify vectors in $k^b$ with polynomials in $x$ of degree below $b$. Choose a finite extension $E/k$ of size greater than both $b$ and $(b-1)\delta^2$. Choose $\omega\in E^\times$ of order at least $b$. For a seed $t\in E$, use
$$
              L_t(f)=(f(t),f(\omega t),\ldots,f(\omega^{s-1}t)).
   \tag{2}
$$
For a fixed $r$-dimensional geometric test space $J$ in Section 1, choose a basis $f_1,\ldots,f_r$ of strictly increasing degrees $d_j$, by polynomial coefficient elimination. The determinant of the first $r$ coordinates of (2) on this basis is a nonzero polynomial in the seed. Its leading coefficient is the product of leading coefficients of the $f_j$ times the Vandermonde determinant in $\omega^{d_1},\ldots,\omega^{d_r}$. These are distinct, and the degree of the seed determinant is at most $r(b-1)$. This argument holds for $J$ over $\bar k$, whether or not $J$ is defined over the chosen finite extension. Each bad seed is a root of this determinant. By (1) the total number of bad seeds is at most $(b-1)\delta^2$. Any list of one more distinct seeds contains a successful projection.

If a single declared chart is wanted for validation, for each support line additionally demand that the first output coordinate $f_p(t)$ be nonzero. This is a nonzero polynomial of degree below $b$. There are at most $\delta$ supports, so $(b-1)(\delta^2+\delta)+1$ seeds suffice. For fixed $q$, choose the smallest extension degree with $q^a$ above the stated bounds. Construct the extension deterministically by enumerating monic degree-$a$ polynomials until an irreducible one is found, using Frobenius gcd tests. The search space is polynomial in $b,\delta$, since $q$ is fixed. Enumerate elements and test that the first $b-1$ powers of $\omega$ are different from $1$. Cyclicity of $E^\times$ ensures success. The seed family and its construction cost are thus polynomial under the stated model.

To validate a seed with a finite algebra presentation, evaluate its $s$ output forms $a_0,\ldots,a_{s-1}$ in $A_E=A\otimes_k E$. Invertibility of $a_0$ is invertibility of its multiplication matrix. When invertible, compute the subalgebra generated by $a_i/a_0$ by repeatedly expanding a basis under multiplication by the generators. This reaches a fixed point in at most $\delta$ rank increases. The induced affine map is a closed immersion precisely when the generated subalgebra is $A_E$, because its coordinate map has image that subalgebra. Hence validation uses only linear algebra in the given finite algebra. An extension-only family can also be expanded over $k$ by stacking each coefficient coordinate of $E$ in a $k$-basis. A successful extension matrix is an $E$-linear combination of the resulting rows, so injectivity on each test space is inherited by this same-field map. This gives $as$ output coordinates without explicit support extraction. The next construction gives an additive width with that extraction. [Guruswami and Kopparty, Explicit subspace designs](https://www.math.utoronto.ca/swastik/subspace-designs.pdf) · [Forbes and Guruswami, Dimension expanders via rank condensers](https://arxiv.org/abs/1411.7455)

## 3. Selecting a narrow same-field projection

We use a simultaneous condenser for an explicitly supplied finite list of spaces $W_\nu\subset E_\nu^b$, where each $E_\nu/k$ is a finite extension with a supplied basis. Different spaces can live over different extensions. Let $N$ be the number of spaces, and assume each has dimension at most $s$ over its extension. There is a deterministic algorithm producing one ground-field map injective on every $W_\nu$, with at most $s+\lceil\log_q N\rceil$ rows when $N\ge1$. Existing rows cut out residual subspaces $W_\nu^0$, with dimensions $d_\nu$. Maintain the integer potential
$$
                    \Phi=\sum_\nu(q^{d_\nu}-1).
$$

For $d=d_\nu>0$, a uniform random row in $k^b$ vanishes on $W_\nu^0$ with probability at most $q^{-d}$, even when the space is defined over an extension. Indeed the $d$ annihilation equations have $d$ pivot columns over that extension. Fixing the remaining ground-field coefficients determines at most one choice of the $d$ pivot coefficients. Unless the row vanishes on this space it decreases the dimension by one. Its expected contribution to the new potential is consequently at most
$$
        q^{-d}(q^d-1)+(1-q^{-d})(q^{d-1}-1)
              =q^{-1}(q^d-1).
$$
Zero-dimensional residual spaces contribute zero. Thus the expected new potential is at most $\Phi/q$.

Choose the row deterministically, one coefficient at a time. For every tried prefix and every residual subspace, the event of annihilation on a random completion is an affine linear system in the remaining coefficients over $k$. Expand its extension-field coefficients in a ground-field basis. Gaussian elimination gives probability zero for an inconsistent system, or $q^{-c}$ for a consistent system of rank $c$. The conditional expectation is therefore the sum of exactly computable rational weights. Pick one of the $q$ next coefficients attaining at most the current average. After the row has been fixed, update the residual spaces by linear algebra. With $s+\lceil\log_q N\rceil$ choices of rows the initial bound $\Phi\le N(q^s-1)$ drops below one, so every residual space is zero. This proves the bound and the algorithm. It uses polynomially many operations in the explicit field-and-space descriptions for fixed $q$. Rational weights have polynomial bit length because their denominators are powers of $q$ with exponents at most $b$.

### Obtaining the list from the finite scheme

The coordinate functions used as input are elements $a_1,\ldots,a_b$ of $A$ in a chosen trivialization of $\mathcal O_T(1)$, so they generate the unit ideal and give the original projective embedding. Such a trivialization exists on a finite scheme, since each local rank-one module is free. The list needed for the condenser can be calculated polynomially from this data.

First, for $q^\ell\ge\delta$, the $q^\ell$-power Frobenius on $A$ kills its nilradical. Its image is a copy of the finite reduced algebra $A_{\mathrm{red}}$ inside $A$: the induced Frobenius on the product of its residue fields is an automorphism. Split this reduced algebra into its field factors over $k$ as follows. Its $q$-Frobenius fixed subalgebra is a product of copies of $k$, one for each field factor. Compute it as a kernel of a linear map. Unless it has dimension one, choose a nonscalar element $c$ in it. The kernels of multiplication by $c-\lambda$, for $\lambda\in k$, split the algebra as ideals, and at least two are nonzero. Iterate. This is deterministic linear algebra for fixed $q$, and each factor is a field with an explicit multiplication table. Its identity idempotent in $A$ singles out the corresponding local Artin factor.

For a local factor with residue field $E_i$ and maximal ideal $\mathfrak m_i$, choose a projective coordinate $a_j$ that is a unit there. Form the affine coordinates $x_k=a_k/a_j$. The geometric point is represented over $E_i$ by the vector of residues of the $x_k$. The embedded tangent directions are obtained by evaluating an $E_i$-dual basis of $\mathfrak m_i/\mathfrak m_i^2$ on $x_k-\overline{x_k}$, using the embedded residue field to regard each $\overline{x_k}$ as an element of $A$. Adjoin the point vector itself to the tangent direction vectors. This computes a representative of each geometric tangent span up to its field conjugates. A ground-field map preserving a representative preserves every conjugate.

To obtain secants, for each ordered pair of residue fields $E_i,E_j$, split the finite reduced algebra $E_i\otimes_k E_j$ by the same algorithm. In each field factor the two point lines are available through the two inclusions. Keep their span when distinct. This covers all geometric pairs, including pairs of conjugates of the same closed point. One need not construct a single field containing all support points. The sum of the dimensions of the tensor products is $(\sum_i [E_i:k])^2=N_0^2$. Over an algebraic closure these tensor products have $N_0^2$ factors counted with multiplicity as an ordered list of pairs. At least $N_0$ of those represent equal point pairs and are discarded. The remaining field factors number at most $N_0^2-N_0$. Adding at most $N_0$ tangent representatives gives $N\le N_0^2\le\delta^2$. All involved field representations and linear systems have size polynomial in $b,\delta$.

Apply the condenser to these spaces. Its output is injective on all test spaces of Section 1. This proves the second theorem, using the original identity map if the stated row budget reaches $b$. The closed immersion preserves the full finite algebra, including its nonreduced structure.

## 4. The compressed rank-drop embedding

For the symmetric matrix realization, the support of the rank-one line $\ell$ in the first detector is $\ell\otimes C$, where $C$ is a fixed $2m$-dimensional vector space carrying the split quadratic form. The common line twist on the two repeated halves gives this expression on test rings. In particular the embedded detector is
$$
       (\ell,U)\longmapsto\ell\otimes U,\qquad
       (\ell,U)\in T\times\operatorname{OGr}(m,C).
$$
Apply a successful projection $L$ to the first factor in the ambient support. It takes the displayed $m$-plane to $L(\ell)\otimes U$, still an $m$-plane. All these maps are functorial on the test schemes of the incidence because $L$ is nonvanishing on the tautological line over $T$.

For any vector space $K$, the map
$\mathbb P(K)\times\operatorname{Gr}(m,C)\to\operatorname{Gr}(m,K\otimes C)$
given by $(\ell,U)\mapsto\ell\otimes U$ is a closed immersion. To see it in charts, pick an index $i$ where the line coordinate is a unit and a set of $m$ coordinate rows $J$ giving a unit minor for $U$. The target chart uses the $m$ pivot coordinates $(i,J)$. Its inverse image is exactly the product of the corresponding charts because the chosen minor is the minor of $U$ times the $m$-th power of the line coordinate. Normalize the line coordinate $i$ to one and the pivot minor of $U$ to the identity. All coordinates of $U$ can then be read from the block indexed by $i$. The other line coordinates can be read from the corresponding pivot positions in the other blocks. These chart coordinates generate both source coordinate rings, proving closed immersion on charts covering the image. The source is projective, so the image is closed globally. This proof works scheme-theoretically in every characteristic.

Apply this to $K=k^w$ or $E^s$ and restrict to the closed orthogonal Grassmannian factor. The projected $T$ is a closed immersion by Sections 1–3, so the whole first rank-drop scheme embeds with precisely its original scheme structure in the smaller Grassmannian. Fixing the standard pure isotropic subspace of $C$ identifies its pure section with the projected copy of $T$.

An exact finite control used $A=\mathbb F_2[\epsilon]/(\epsilon^3)\times\mathbb F_4$ in seven homogeneous coordinates. Over $\mathbb F_{256}$, let $\alpha,\alpha^2$ be the two nontrivial cube roots of unity, so the two last entries below describe the geometric splitting of the $\mathbb F_4$-factor. Write five coordinates of $A_{\mathbb F_{256}}$ as the constant, $\epsilon$, $\epsilon^2$, and two field coordinates. The seven chosen elements are
$$
 (1,0,0,1,1),\ (0,1,0,\alpha,\alpha^2),\ (0,0,0,1,1),
 \ (0,0,1,0,0),\ (0,0,0,\alpha,\alpha^2),\ 0,\
 (0,1,1,\alpha+1,\alpha^2+1).
$$
The six tangent and secant spaces had dimensions $2,1,1,2,2,2$. Exact averaging over ground-field row completions selected three rows, with potentials $14,4,1,0$. Among 181 tested extension seeds, 179 passed both rank and affine-chart tests. Each of those generated the whole length-five algebra after dividing by the first coordinate, which checks that the triple point was retained.

## Scope and sources

The construction compresses the *embedded detector*. Its input for explicit same-field selection is the finite coordinate algebra and the projective coordinates. Whole-pencil substitution profiles require a separate compression construction. The preceding rational-point counting result demonstrates a separate hardness issue for implicit quadratic presentations. [Counting at the first rank drop](https://github.com/Dugongue/MathProofs/blob/main/FirstRankDropFour/Counting.md)

Folded Wronskians and seeded rank condensers are established constructions. Classical projective projection separates points and tangent vectors, and the Grassmannian charts express how to preserve them here. The contribution is the simultaneous tangent–secant rank budget, the additive same-field width with deterministic selection from an explicit finite algebra, and their application to the nonreduced detector geometry. The proof is in prose. Lean verification and publication priority are unestablished. [Guruswami and Kopparty](https://www.math.utoronto.ca/swastik/subspace-designs.pdf) · [Forbes and Guruswami](https://arxiv.org/abs/1411.7455) · [Grochow and Qiao, tensor-isomorphism reductions](https://arxiv.org/abs/2306.16317)
