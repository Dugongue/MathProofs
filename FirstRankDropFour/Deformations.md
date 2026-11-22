# Recovering polarized deformations from unmarked tensor pencils

**Theorem.** Fix a field $k$, a nonempty projective $k$-scheme $X_0$, and an ample polarization $L_0$. For every prescribed first-detection size $m\ge3$ there is a base-change-compatible construction on flat polarized deformations over local Artinian $k$-algebras. It produces a three-tensor and an unmarked square-zero slice pencil. The rank-one incidence of the raw tensor recovers the whole deformation scheme. Over any test base satisfying the stated cohomology hypotheses, its entire ordinary three-mode transporter functor is the functor of scheme isomorphisms equipped with two line-bundle isomorphisms for consecutive powers of an auxiliary polarization.

An arbitrary ordinary transporter of the unmarked pencils over an Artinian base induces an isomorphism of the schemes preserving the auxiliary polarization. Every such polarized isomorphism lifts to a pencil transporter. When $L_0$ is sufficiently positive, the auxiliary polarization can be the original $L$. For arbitrary $L_0$, choose one prime-to-characteristic high power at the special fiber. Mark-compatible pencil transporters then reflect isomorphism of the **original** marked polarized deformations, including their infinitesimal line-bundle data. The unmarked statement in this general case recovers the chosen high power. All statements include nonreduced fibers and bases.

## 1. Mixed rank-one sections over a base

Let $X\subset\mathbb P_Z(B^*)$ be a flat closed family over a base $Z$, with $A=\mathcal O_X(1)$. Here $B$ is the module of ambient linear forms. Work locally on $Z$ with bases of the vector bundles. Choose $e\ge1$ so that for $d=e,e+1,2e+1$ the restriction
$$
\operatorname{Sym}^d B\ \longrightarrow\ C_d=\pi_* A^d
$$
is a surjection onto a vector bundle and commutes with base change. Assume the degree-$(2e+1)$ ideal sections generate the sheaf $\mathcal I_X(2e+1)$, compatibly with pullback. Assume the complete systems $C_e,C_{e+1}$ embed $X$. These hypotheses are verified for the Artinian deformation setting in Section 4. Multiplication $C_e\otimes C_{e+1}\to C_{2e+1}$ is surjective because multiplication is surjective in the ambient polynomial ring. Form its dual inclusion
$$
M_X=C_{2e+1}^*\ \hookrightarrow\ E\otimes F,\qquad E=C_e^*,\quad F=C_{e+1}^*.
\tag{1}
$$
The inclusion is locally split. It is the three-tensor, with the domain $M_X$ serving as the slice leg.

The rank-one section of $\mathbb P(M_X)$ in the Segre scheme of $\mathbb P(E)\times\mathbb P(F)$ is exactly $X$ embedded by the pair of complete systems. Here and below projective spaces of dual section modules parameterize lines. We prove the scheme assertion on arbitrary test bases.

First take the ambient polynomial ring, with monomials of degrees $e,e+1$ indexed by $\alpha,\beta$. On the Segre the condition that the product has entries indexed only by $\alpha+\beta$ is
$$
a_\alpha b_\beta=a_{\alpha'}b_{\beta'}
\quad\text{if }\alpha+\beta=\alpha'+\beta'.
\tag{2}
$$
At any geometric point, choose a coordinate variable $i$ occurring in some monomial with a nonzero coordinate on either side. Let $s,t$ be the largest exponents of $i$ in nonzero coordinates on the two sides. A pair attaining these maxima has nonzero product. Every splitting of its exponent sum gives the same nonzero product by (2). Maximizing the $i$-exponent on either side gives $s=\min(e,s+t)$ and $t=\min(e+1,s+t)$. Since $s+t>0$, these identities force $s=e,t=e+1$. Thus the opens where $a_{i^e}$ and $b_{i^{e+1}}$ are units cover the intersection scheme.

On such an open normalize both distinguished coordinates to one. Set $z_i=1$ and $z_j=a_{i^{e-1}j}=b_{i^e j}$. For every $\alpha$ with $\alpha_j>0$, $j\ne i$, equation (2) gives
$$
a_\alpha=a_{\alpha-j+i} b_{i^e j}=a_{\alpha-j+i}z_j .
$$
The analogous swap on the other factor gives $b_\beta=z_j b_{\beta-j+i}$. Induction on the exponent outside $i$ shows $a_\alpha=z^\alpha$, $b_\beta=z^\beta$ over the test ring itself. The inverse is monomial evaluation. These pivot charts prove that the ambient mixed rank-one section is the paired Veronese graph, in every characteristic and over an arbitrary base.

For (1), the additional linear equations in the ambient degree-$(2e+1)$ dual space are annihilation of the degree-$(2e+1)$ ideal sections of $X$. On the paired graph they cut out $X$ scheme-theoretically by the generation hypothesis. A point of $X$ already annihilates the lower degree ideal sections in each factor, so restriction to the smaller projective factors creates exactly the same scheme. This proves the rank-one recovery on all test schemes.

## 2. Exact transporter functor of the raw tensor

For two such families $X,X'$, an ordinary transporter for (1) is a pair of invertible maps $P:E\to E'$, $Q:F\to F'$ carrying $M_X$ onto $M_{X'}$ under $P\otimes Q$. The slice-leg map is then uniquely determined. This description works for vector bundles and therefore for arrays after local trivialization.

A transporter induces the same scheme map $f:X\to X'$ on both projections of the paired graph. The actual linear maps induce isomorphisms $f^* (A')^e\simeq A^e$ and $f^*(A')^{e+1}\simeq A^{e+1}$ on the restricted $\mathcal O(1)$ bundles. Conversely, a scheme isomorphism furnished with these two line-bundle maps induces the indicated linear maps on the dual complete sections. Their tensor product carries the rank-one incidence to its counterpart. It therefore preserves its linear span as a subbundle. Indeed the scheme in $\mathbb P(M_X)$ has $\mathcal O(1)=A^{2e+1}$, and every section of this line is an ambient linear form, with restriction $M_X^*\to H^0(A^{2e+1})$ the identity under (1). The same holds after base change. Thus in the larger matrix space the annihilator of the scheme's degree-one vanishing forms is exactly $M_X$. This proves the inverse map on transporters. Completeness of the two degree systems makes recovery of $P,Q$ from the indicated line maps unique. The result is natural on test bases, including those with nilpotents.

Taking the ratio of the two line maps recovers $f^*A'\simeq A$. Conversely a choice of this isomorphism supplies the two choices by taking powers. The full tensor transporter retains both choices, so its kernel over the group of polarized maps has the corresponding independent line-linearization gauges. This identifies the transporter functor without assuming that global units on $X$ are scalars.

## 3. Reflection by the unmarked square-zero pencil

We give the argument over an Artinian local base $R$. Use the oriented rectangular rows of the preceding construction, with a spare rank-one summand in $Z_1=F^*\oplus E\oplus R$. For $A_1\in M_X$ let $\widetilde A_1$ send $F^*$ to $E$ by contraction and kill the other summands. Form
$$
B(x,y,A_1)=[\,xI+\widetilde A_1,\ yI\,].
$$
The spare coordinate is unused by the data. Repeat $m$ copies in a bipartite quadratic $q_B$, use disjoint variable halves, and denote the resulting quadratic subbundle by $H_X\subset\operatorname{Sym}^2 V$. A retraction onto one copy, together with extraction of $x,y$ and the data block, shows it is a subbundle. Over the residue field every nonzero element has polarization rank at least $2m$. Hence its residue has no nonzero sum of two products of linear forms, including in characteristic two. Let
$$
W_0=\operatorname{Sym}^2 V/H_X,\qquad
W=W_0\oplus H_X\oplus R^\delta,\qquad
J=V\oplus W ,
$$
where $\delta\in\{0,1\}$ is chosen so $n=\operatorname{rank}J$ is a unit. The added summands of $W$ are inert. The pencil is $L_X(r,u)=rI+N_u$, where $N_u$ takes $v\in V$ to $[uv]\in W_0$ and kills $W$. These are products over $R$ itself. Arbitrary base change preserves the construction and the pointed Artinian dimensions. [Previous square-zero pencil](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md).

Suppose an arbitrary independent-mode transporter relates two such pencils. The image of the unit slice has scalar part $r_0$ a unit, since every slice has determinant $r^n$. Right-dividing by the image of the unit normalizes the transporter to similarity. Products of centered slices vanish, so the normalized target scalar part at $(r,u)$ is $r'(r,u)/r_0$. Trace, divided by $n$, forces $r'=r_0r$, and the comparison restricts to an equivalence on the centered modes. Their common kernel is $W$: any lift of a nonzero residue direction has multiplication $V\to W_0$ with a full-column unit minor, hence injective. Their total image is $W_0$, since products generate the symmetric square quotient. Consequently the transporter induces an ordinary independent-mode equivalence of the bipartite product $\beta(u,v)=[uv]$.

Write $P,Q$ for the maps of the two $V$-spaces in this product. Its symmetry gives, on the target and with $S=QP^{-1}$,
$$
u(Sv)-v(Su)\in H_{X'} .
\tag{3}
$$
Over the residue field this polynomial is zero by the two-product exclusion. In a basis the equations $e_i S e_j=e_j S e_i$ force $S$ scalar by divisibility and comparison of coefficients. To lift this conclusion, scale $S$ to be identity modulo the maximal ideal $\mathfrak m$. If $S=I\bmod\mathfrak m^j$, expand $S-I$ in a $k$-basis of $\mathfrak m^j/\mathfrak m^{j+1}$. The subbundle $H_{X'}$ is split, so (3) puts each coefficient in the residue $H_{X'}$. Each coefficient is again a difference of two products and hence zero. The same coefficient argument makes each component of $S-I$ scalar. One scalar unit corrects that layer, and nilpotence then makes $S$ scalar over $R$. Thus $\operatorname{Sym}^2(P)$ carries the actual quadratic subbundle $H_X$ to $H_{X'}$.

Inside $\mathbb P(H_X)$, take the scheme defined by $(2m+1)$-minors of the polarization. This scheme is $\Sigma_{M_X}$, the rank-one scheme of the raw matrix space, intrinsically under any quadratic change. On geometric points the polar rank is $2m\operatorname{rank}B$, so a point on the minor locus has rank one and has a pivot in the data block. On a pivot chart, eliminate the unit data entry of $B$ and its copies. The $2m$ pivot rows and columns of the polarization give an invertible block. Minors extending that block force every entry of each copy of the remaining Schur complement to vanish. The spare coordinate in the second block gives $y=0$, and its first-block diagonal gives $x=0$, since both corrections at the unused coordinate are zero. The remaining equations are exactly the rank-one minors of $A_1$. This proves the identification over arbitrary test rings. In the first-row substitution family, a relation on a $j$-plane lies in $UV$ and has polar rank at most $2j$. The geometric fibers therefore have no such relations for $j<m$, and their maximal minors generate the unit ideal locally. At $j=m$ any geometric rank-one point gives a relation by choosing the repeated pure column half of its support. Thus the marked first-row rank drop occurs first at $m$. The reflector itself uses the intrinsic rank-one scheme in the quadratic subbundle. [First rank-drop geometry](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md).

An unmarked pencil transporter therefore gives an isomorphism $f:X\to X'$, with an isomorphism between its universal polar-image subbundles. The latter subbundle is the image of the polarization evaluated on the universal quadratic line. A rank-one $A_1$ factors locally into a column and row with unit coordinates, making this image the sum of $m$ copies of each of their two lines. By the paired graph these restricted tautological lines are $A^{-e}$ and $A^{-(e+1)}$. Thus the transporter recovers an isomorphism between
$$
(A^{-e})^{\oplus m}\oplus(A^{-(e+1)})^{\oplus m}
\quad\text{and}\quad
(f^*(A')^{-e})^{\oplus m}\oplus(f^*(A')^{-(e+1)})^{\oplus m}.
\tag{4}
$$
This identification uses the image subbundle itself and no choice of its two halves.

Over the Artinian base, $H^0(X,\mathcal O_X)$ is a finite Artinian algebra by properness. Its connected factors split $X$ by idempotents. On each connected factor a line bundle has local endomorphism ring $H^0(\mathcal O)$. The standard uniqueness argument for finite sums with local endomorphism rings applies to (4): projecting a summand across an isomorphism and its inverse expresses its identity as a sum, so one term is a unit and the matching summand cancels. Repetition gives the same multiset of line-bundle classes. On a positive-dimensional connected factor the two displayed powers are distinct, and matching them in reverse order would imply $f^*A'\simeq A^{-1}$ by taking a ratio. An ample line bundle has nonample inverse on a positive-dimensional proper scheme, as can be checked on an integral projective curve after extending the residue field. On zero-dimensional factors every line bundle is trivial because the scheme is affine Artinian. Thus the matching always gives $f^*A'\simeq A$. Conversely an $A$-polarized isomorphism extends via (1) to the rectangular rows, the repeated quadratic subbundle, its symmetric-square quotient and the pencil. This proves reflection and preservation for the unmarked pencil, without asserting that it has the same full transporter functor as (1).

## 4. Uniform Artinian deformation and recovery of the original polarization

Choose $c$ large with $A_0=L_0^c$ very ample and higher cohomology zero. If $L_0$ already has these properties set $c=1$. Otherwise take $c$ prime to the positive characteristic, or any sufficiently large $c$ in characteristic zero. For a deformation $(X,L)$, set $A=L^c$. Proper flat cohomology and base change gives a free complete section module for $A$ and identifies its special fiber with the complete system of $A_0$. Evaluation is surjective by Nakayama. The resulting morphism to projective space is a closed immersion: it is proper and quasi-finite since the special morphism is a closed immersion and the base is a nilpotent thickening, hence finite. The map of structure sheaves is surjective by reduction and Nakayama. Now choose $e$ once from the special embedded ideal so that $\mathcal I_{X_0}(d)$ and $A_0^d$ have vanishing higher cohomology for $d=e,e+1,2e+1$ and these twists of the ideal are globally generated. The ideal is flat over the Artinian base because the ambient and quotient structure sheaves are flat. Cohomology and base change gives the free modules, surjections and compatibility required in Section 1. Global generation lifts by Nakayama. All choices of exponents can therefore be made at the special fiber, before the Artinian deformation is supplied. [Stacks Project, cohomology and base change](https://stacks.math.columbia.edu/tag/0A1G).

For marked deformations, a pencil transporter compatible with the special markings induces the identity map on the marked special scheme by its intrinsic rank-one recovery. If $f^*(L')^c\simeq L^c$, the ratio $T=f^*L'\otimes L^{-1}$ is trivial on the special fiber and $T^c\simeq\mathcal O_X$. The following argument removes the power without any restriction on global functions.

Put $D_0=H^0(X_0,\mathcal O_{X_0})$. This finite Artinian $k$-algebra contains a finite étale subalgebra consisting of lifts of the maximal separable subfields of its residue factors. Existence follows by formally étale lifting through the nilpotent radicals of the factors. Modulo $c$th powers every unit of $D_0$ comes from this étale subalgebra. Principal units have unique $c$th roots by nilpotent lifting, and for each residue field in positive characteristic a sufficiently large $p$-power maps into its separable subfield. Bézout for $c,p^j$ proves the assertion there. Characteristic zero has no inseparable factors. The map from $X_0$ to the spectrum of this étale subalgebra lifts to $X$ after base extension to $R$, by formal étaleness. Its units therefore lift to global units on $X$.

Choose a trivialization of $T^c$. Relative to a trivialization of $T$ on $X_0$, its restriction gives a unit in $D_0$. Using the preceding unit description, change the global trivialization by a lifted unit and the special trivialization by a $c$th root so that they agree. The finite étale scheme of $c$th roots of the resulting trivialization has a section on $X_0$. Formal étaleness uniquely lifts that section to $X$. It trivializes $T$, proving reflection for the original marked polarization. [Stacks Project, invariance of étale morphisms under thickenings](https://stacks.math.columbia.edu/tag/04DY).

For a concrete infinitesimal check, over $k[\epsilon]/(\epsilon^2)$ in characteristic two compare the trivial double point $t^2=0$ and the flat double point $t^2=\epsilon$. The two families have the same special fiber and are intrinsically inequivalent: in the former algebra every square is in $k$, while the latter contains $t$ with square $\epsilon$. Both can be placed in projective space with their very ample restricted line. The rank-one scheme in the mixed tensor and the intrinsic polar-rank scheme in the unmarked pencil distinguish them. Exact controls verified the mixed degree-two/degree-three pivot equations against monomial parametrization for all 1,024 coordinate tuples over the dual numbers of $\mathbb F_2$ and all 59,049 over the dual numbers of $\mathbb F_3$. Upon extension to $\mathbb F_2[z]/(z^4)$ with $\epsilon=z^2$, the mixed degree-five relations of the nontrivial family were exactly the equation $t^2=z^2$ in the affine pivot coordinate.

Sidman and Smith prove determinantal descriptions of sufficiently ample projective embeddings and discuss the classical linear Veronese-section construction. Grochow and Qiao supply the tensor-isomorphism setting and linear-length reduction techniques. The distinction here is the exact raw transporter functor from two consecutive polarizations, and the recovery of those powers from an unmarked pencil over Artinian bases. The latter uses the intrinsic polar-image bundle and the two-product filtration argument. The proof is informal. Publication priority for this package remains unverified. [Sidman–Smith, *Linear determinantal equations for all projective schemes*](https://arxiv.org/abs/0910.2424) · [Grochow–Qiao IV](https://arxiv.org/html/2306.16317).
