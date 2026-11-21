# Pure-cube directions and cubic orbit closures in characteristic three

Let $K$ be algebraically closed of characteristic three, $V$ an $n$-dimensional vector space, and $\mathcal F=\operatorname{Sym}^3 V^*$. For a formal cubic $f$, let $T_f$ be the symmetric trilinear form obtained as the coefficient of $stu$ in $f(sx+ty+uz)$. Write $R_f=\ker(v\mapsto T_f(v,-,-))$ and $\pi:f\mapsto T_f$. Orbit closures below are reduced and affine. The notation $\operatorname{GL}(V) f$ denotes the orbit under substitutions. A linear substitution from the source to the target is a transporter if $g(A v)=f(v)$.

**Theorem.** The reduced $\operatorname{GL}(V)$-orbit closure of every $f\in\mathcal F$ admits the following descriptions.

- If $f|_{R_f}\neq0$, then
  $$
  \overline{\operatorname{GL}(V)f}
      =\pi^{-1}\!\left(\overline{\operatorname{GL}(V)T_f}\right).
  $$
  In particular, a linear section of $\pi$ gives a global product of the polarization orbit closure and $\mathbb A^n$. The equality includes degenerations with arbitrary drops of polarization rank.
- If $f|_{R_f}=0$, let $r=\dim R_f$, $c=n-r$, and let $C_0$ be the orbit closure of the induced cubic $f_0$ on $V/R_f$, with that quotient identified with $K^c$. A cubic $g$ belongs to $\overline{\operatorname{GL}(V)f}$ exactly when there is an $r$-plane $S\subseteq R_g$ with $g|_S=0$ such that the induced cubic $g_{V/S}$ lies in $C_0$ after a quotient frame is chosen. The incidence space of all such pairs $(S,g)$ maps projectively and birationally onto the closure. Its nonempty reduced fiber at $g$ is $\operatorname{Gr}(r,\ker\ell_g)$, where $g|_{R_g}=\ell_g^3$.

The product theorem involves a smooth projection between reduced closures. The orbit map that realizes its affine directions through radical substitutions factors through a finite radicial map of degree $3^n$. The transporter calculation below makes this distinction scheme-theoretic.

## Radical decomposition and the nonzero branch

In monomial coordinates the polarization reads a mixed coefficient with multiplicity $1$ or $2$ and a pure-cube coefficient with multiplicity $6=0$. Thus the kernel $D$ of $\pi$ is the $n$-dimensional linear space of pure-cube sums. This calculation is valid over every commutative algebra of characteristic three. Also, if $V=C\oplus R_f$, every non-pure monomial involving a radical variable has zero coefficient. Consequently
$$
 f(x+y)=f_C(x)+q_f(y),\qquad x\in C,\ y\in R_f .
$$
The quotient polar tensor on $C$ has zero contraction kernel. The pure-cube sum $q_f$ is $\ell_f^3$ for a unique linear form on $R_f$, since cubing is bijective in $K$.

Suppose $q_f\neq0$, and take $g$ with $T_g\in \operatorname{GL}(V)T_f$ and $q_g\neq0$. A quotient polarization transporter $A_0:C_f\to C_g$ exists. Choose $U:R_f\to R_g$ invertible with $\ell_g U=\ell_f$. The quotient discrepancy $f_{C_f}-g_{C_g}\circ A_0$ has zero polarization. It is $b^3$ for a linear form $b$ on $C_f$. A shear $W:C_f\to R_g$ with $\ell_g W=b$ then satisfies
$$
 g(A_0 x+Wx+Uy)=f(x+y).
$$
Conversely, any cubic transporter preserves the polarization and the zero or nonzero type of the restriction. Thus over the polarization orbit $\mathcal O=\operatorname{GL}(V)T_f$, the cubic orbit is exactly the nonzero-restriction part of $\pi^{-1}(\mathcal O)$.

The radical is a vector bundle over the polarization orbit, since the contraction matrix has constant rank and its kernel has local bases given by minors. Restriction of a cubic to this bundle is regular. Its nonvanishing therefore defines an open set, which is dense in every affine fiber of $\pi$ over $\mathcal O$. Indeed in an adapted basis one can vary the pure coefficient of any radical variable independently. The orbit is dense in $\pi^{-1}(\mathcal O)$. Take closure after splitting the linear map $\pi$ onto its image. The closure of $\pi^{-1}(\mathcal O)$ is now $\overline{\mathcal O}\times D$, proving the first branch. As both sides are reduced, equality of their closed points gives equality as varieties. In particular local singularities of the polarization orbit closure are preserved up to $n$ smooth variables throughout the cubic closure.

## The zero branch and its fibers

For any $r$-plane $S\subseteq R_g$, the same mixed monomial calculation shows that $g$ descends to $V/S$ exactly when $g|_S=0$. Over $\operatorname{Gr}(r,V)$, the space of cubics pulled back from $V/S$ is a vector subbundle of the trivial cubic bundle. Locally choose frames for the universal quotient $V/S$. The condition $g_{V/S}\in C_0$ defines the product with $C_0$ in each such chart. These local products agree on overlaps because $C_0$ is invariant under quotient change of basis. This defines a reduced closed incidence variety $Z\subseteq \operatorname{Gr}(r,V)\times\mathcal F$.

Projection to $\mathcal F$ is projective. The part of $Z$ in which the quotient cubic is actually in the orbit of $f_0$ is dense and projects exactly onto the orbit of $f$. Density follows from the local product and density of the quotient orbit. For the image assertion, any quotient isomorphism can be extended to an isomorphism of the full spaces by choosing a radical isomorphism and a splitting, and the cubics are independent of the radical coordinates. It follows that the whole projected image is the closure of the orbit of $f$.

Every polarization on the image has contraction rank at most $c$. On the open rank-$c$ part the plane $S$ is forced to be $R_g$, and is recovered regularly by forming the kernel of a constant-rank matrix. The projection is an isomorphism over this nonempty open subset, proving birationality.

For a fixed $g$, all candidate planes are in $\ker\ell_g\subseteq R_g$. If one gives the required quotient degeneration, so do all the others. Indeed the subgroup of $\operatorname{GL}(R_g)$ preserving $\ell_g$, extended by the identity on a chosen complement, preserves $g$ and acts transitively on $r$-planes in $\ker\ell_g$. Every invertible linear map on $\ker\ell_g$ extends to such a map on $R_g$. Thus the reduced fiber is the indicated Grassmannian whenever nonempty. Equivalently, after checking $\dim\ker\ell_g\geq r$, it suffices to test the quotient cubic for any one choice of $S$. The fiber statement concerns the reduction of the scheme fiber.

## Relative orbit closures for determinant-one substitutions

Fix polarization contraction rank $c$, and consider the pair space
$$
 \mathcal B_c=\{(T,q):T\in\operatorname{im}\pi,\ \operatorname{rank}_{\rm contr}T=c,\
               q\text{ a pure-cube sum on }\ker T\}.
$$
Here $\ker T$ is the kernel of the contraction matrix. The map $\beta:f\mapsto(T_f,f|_{R_f})$ from the rank-$c$ cubic stratum to $\mathcal B_c$ is a locally trivial affine bundle of fiber dimension $c$. In a neighborhood with frames for the radical and a complementary subspace, choose a linear section of $\pi$ and use pure coefficients to set the radical restriction. Restriction on the pure-cube kernel is surjective onto the $n-c$ radical coordinates, leaving exactly the $c$ complementary coordinates free. This also shows that $\mathcal B_c$ is a vector bundle over the polarization stratum.

If $q_f\neq0$, determinant-one shears change the $c$ complementary pure coefficients arbitrarily within the fiber of $\beta$, since they add $(\ell_f W)^3$. Therefore for $G=\operatorname{SL}(V)$ or $G=\operatorname{GL}(V)$, the $G$-orbit of $f$ is precisely $\beta^{-1}(G\beta(f))$. Its closure relative to the fixed-rank cubic stratum is the inverse image of the closure of $G\beta(f)$ in $\mathcal B_c$, by local triviality. This includes zero restrictions in that relative closure if the pair limits to them. When $r=n-c\geq2$ and $q_f\neq0$, an arbitrary determinant can already be realized by a stabilizer element acting on $\ker\ell_f$ and fixing its chosen complement. Thus the ordinary affine $\operatorname{SL}$ and $\operatorname{GL}$ orbits of $f$, and their closures, coincide for $r\geq2$. The pair-space description also applies when $r=1$.

## The transporter scheme

Let both $q_f$ and $q_g$ be nonzero and suppose the radical dimensions agree. The following calculation works over a perfect field of characteristic three as well. Choose bases for the radical so that $\ell_f,\ell_g$ are first coordinate functionals. Let $\mathcal I$ be the polarization transporter scheme on the $c$-dimensional quotients. It may have nilpotents. Let $\gamma_i(A_0)$ be the pure-cube coefficients of $f_{C_f}-g_{C_g}\circ A_0$ on $\mathcal I$. The full cubic transporter scheme is a product over $\mathcal I$ of
$$
 \left\{ (A_0,s,\eta) :
 s_i^3=\gamma_i(A_0)\ (1\leq i\leq c),\
 \eta_j^3=0\ (1\leq j\leq r)\right\}
$$
and a freely chosen factor $\operatorname{GL}_{r-1}\times\mathbb A^{(r-1)(c+1)}$.

To prove this on schemes, evaluate on an arbitrary commutative base algebra. The contraction kernel commutes with base change from the field, so a polarization transporter has block form $\left(\begin{smallmatrix}A_0&0\\W&U\end{smallmatrix}\right)$. Its first row on $W$ consists of the $s_i$. The first row of $U$ is $(1+\eta_1,\eta_2,\ldots,\eta_r)$, by the equations $U_{1j}^3=\delta_{1j}$. These and the displayed equations for $s_i$ are exactly the cubic constraints, by the formal coefficient identity in characteristic three. The lower rows of $W$ are free. In $U=\left(\begin{smallmatrix}1+\eta_1&\eta'\\u&B\end{smallmatrix}\right)$, the lower first column $u$ is free and invertibility is equivalent to the invertibility of $B-u(1+\eta_1)^{-1}\eta'$. The inverse of $1+\eta_1$ is a polynomial since $\eta_1^3=0$. These formulas give inverse natural transformations and prove the scheme description. The convention at $r=1$ is that the free factor is a point.

The root-equation factor is finite flat and radicial of rank $3^{c+r}$ over $\mathcal I$. The monic equations give the monomial basis with exponents $0,1,2$. Over a geometric point each equation has a unique root, and the corresponding factor is a point of length three. In particular over a fixed quotient polarization transporter the reduced full fiber is smooth of dimension $(r-1)n$, and its nonreduced part is given by $n$ length-three factors. The relative radical-block orbit map is the row-selection map $(W,U)\mapsto(W_{1*},U_{1*})$, followed by coordinate cubing, with the translation by the original complementary coefficients understood. Row selection is smooth and surjective onto $\mathbb A^c\times(\mathbb A^r\setminus0)$, as Gaussian pivot charts show. Coordinate cubing is finite radicial of degree $3^n$.

For the full stabilizer, take $g=f$ and let $d\gamma$ denote the differential of the discrepancy at the identity of the quotient polarization stabilizer $\mathcal I$. The Lie dimension of the cubic stabilizer is
$$
 \dim \operatorname{Lie}(\mathcal I)-\operatorname{rank}d\gamma+rn ,
$$
because the $n$ cubic-power equations constrain no first-order variable of $W,U$. Its Krull dimension is $\dim\mathcal I+(r-1)n$. Their difference is at least $n-c=r>0$, since $d\gamma$ has rank at most $c$ and the tangent dimension of $\mathcal I$ is at least its dimension at the identity. Thus the full stabilizer is non-smooth, even though the reduced closure in the nonzero branch is a product with an affine space.

When both restrictions vanish, the same block calculation leaves $W,U$ free and the base becomes the exact quotient cubic transporter scheme. Differing zero and nonzero types give an empty transporter scheme, since an invertible radical map cannot carry a nonzero pure-cube restriction to zero, even after base change.

## Controls and prior work

For $x,y,z$ independent in characteristic three, the substitution $z\mapsto tz+y$ takes $x^2y+z^3$ to $x^2y+y^3+t^3z^3$. The special fiber has the same rank-two polarization and now zero radical restriction. It cannot degenerate back to $x^2y+z^3$ by the zero branch, since the rank-two endpoints force the plane $S$ to be the radical line in the $z$-direction. In contrast, $x^2y$ degenerates by $y\mapsto x+ty$ to $x^3$, which has zero polarization and nonzero radical restriction. At this last target the reduced incidence fiber is $\operatorname{Gr}(1,\ker x)\cong\mathbb P^1$.

Geometry.py checks all 11,232 invertible ternary substitutions over the field of three elements. The fixed-polarization fibers in the two example orbits have sizes 3 and 18. It also checks the 81 first-order cubic stabilizer lifts, the 243 polarization stabilizer lifts, and the 27 cubic stabilizer lifts with quotient block fixed, as well as the four rational lines in the reduced incidence fiber.

Perfectness matters for rational orbit transitivity. For example, $x^2y+z^3$ and $x^2y+u z^3$ over $\mathbb F_3(u)$ have the same polarization but no rational transporter. On the one-dimensional radical a transporter would require a cube root of $u^{-1}$. The algebraically closed orbit-closure theorem and the scheme equations retain the distinction between geometric and rational data.

Garibaldi and Nakano describe the Frobenius-twist kernel of degree-$p$ polarization. The calculation above uses that kernel to determine complete reduced closures and the transporter scheme in the nonzero radical case. The zero-restriction incidence uses the classical homogeneous-bundle collapsing construction, here with the quotient cubic orbit closure as fiber and with explicit reduced fibers. [Garibaldi and Nakano, Bilinear and Quadratic Forms on Rational Modules of Split Reductive Groups, Proposition 3.5.1](https://arxiv.org/abs/1501.07515) · [Lőrincz, On the collapsing of homogeneous bundles in arbitrary characteristic](https://arxiv.org/abs/2008.08270)

Grochow, Mulmuley and Qiao study orbit-closure degeneration and border complexity. Grochow and Qiao connect cubic-form equivalence to tensor and algebra isomorphism and analyze faster algorithms in good characteristic. The geometric result here identifies when a characteristic-three cubic degeneration problem is exactly a polarization degeneration problem, and when quotient cubic data still enter. These statements concern reduced geometric orbit closures and the explicit transporter schemes above. The proof is mathematical prose, with no Lean verification or claim of literature priority. [Grochow, Mulmuley and Qiao, Boundaries of VP and VNP](https://doi.org/10.4230/LIPIcs.ICALP.2016.34) · [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110) · [Grochow and Qiao, Linear-Length Reductions](https://arxiv.org/abs/2306.16317)
