# The moduli groupoid of cubic-anchor algebras

Fix $n\geq2$. All constructions in the groupoid calculation work over arbitrary base schemes and in every characteristic. Put $V=\mathbb Z^n$, $Q=\operatorname{Sym}^2V$, $P=\operatorname{Sym}^3V$, and $\Phi=\operatorname{Hom}(V,P)$ for the framed coordinate spaces. Use the same letters for the vector bundles obtained by base extension. In formulas over a ring, a form $f\in P$ and a defect $\phi\in\Phi$ define an augmented commutative algebra with filtered basis
$$
 1,\quad V\oplus Rz,\quad Q\oplus Rz^2,\quad P .
$$
The ordinary $V$-monomial products through degree three are retained. The additional rules are $z^3=f$ and $zv=\phi(v)$, and products of filtration degree at least four vanish. Every mixed product of total filtration degree three is zero. Denote the result by $A(f,\phi)$. The case $\phi=0$ is the graded cubic-anchor construction.

**Theorem.** The groupoid of augmented anchored algebras, defined below by intrinsic graded conditions, has an explicit global presentation over $\mathbb Z$ with framed objects $(f,\phi)\in P\times\Phi$. Its graded stack is canonically
$$
 [\,P/\operatorname{GL}(V)\,]\times B\mathbb G_m .
$$
The filtered stack admits a smooth gerbe onto the quotient that retains only the graded changes of basis and the translations
$$
 \phi\longmapsto\phi-B_f(q,\lambda),
 \qquad B_f(q,\lambda)(v)=qv+\lambda(v)f,\qquad
 (q,\lambda)\in Q\oplus V^* .
$$
The kernel of this gerbe is given below by a two-step unipotent group with a polynomial multiplication law. Off the zero cubic the quotient is the vector-bundle stack of the cokernel of $B_f$, with rank $n\binom{n+2}{3}-\binom{n+1}{2}-n$. Over $f=0$ it has extra additive inertia $V^*$.

For the universal family over a field, the group of automorphisms inducing the identity on the associated graded is not flat at $f=0$. Before blowing up, nonzero nilpotent structure is supported at the intersection of its two reduced components. On the blow-up of the cubic space at zero, in a chart $f=t u$ with $u$ primitive, this automorphism group scheme is the direct product of the smooth kernel group and the additive group scheme cut out by $t\lambda=0$. In particular that pullback is reduced over a field, and the closure of the group over nonzero cubics is the smooth kernel factor. The blow-up is also the graph closure of the rank-$n$ translation-image planes, and their map from projective cubics is a closed immersion.

## Intrinsic conditions and descent of the frames

An augmented anchored algebra on a scheme has an augmentation to the structure sheaf. Its augmentation ideal $M$ satisfies $M^4=0$ and has locally free quotients $M/M^2,M^2/M^3,M^3$. The degree-one piece of $\operatorname{gr}_M A$ locally admits a decomposition $V\oplus L$, where $V$ has rank $n$, $L$ is a line, and $LV=0$ in degree two. The induced multiplication maps
$$
 \operatorname{Sym}^2 V\oplus L^{\otimes2}\longrightarrow M^2/M^3,
 \qquad
 \operatorname{Sym}^3 V\longrightarrow M^3
$$
are isomorphisms. These conditions specify the class of algebras. Neither a basis nor a splitting of the filtration is part of an object. Morphisms preserve the augmentation. The locally free ideal-power filtrations are locally split, so formation of these powers and their quotients commutes with arbitrary base change.

The line $L$ is intrinsic as a projective scheme, even on a nonreduced base. To see it, take coordinates for a degree-one element $v=\sum a_i x_i+bz$. The $2\times2$ minors of the multiplication map by $v$ from degree one to degree two generate
$$
 (a_i a_j,\ a_i b:1\leq i,j\leq n).
$$
For $a_i^2$, use columns $x_i,x_j$ for $j\neq i$ and rows $x_i^2,x_ix_j$. Using the same columns and rows $x_i^2,x_j^2$ gives $a_i a_j$ when $i\neq j$. Columns $x_i,z$ and rows $x_i^2,z^2$ give $a_i b$. Every minor vanishes at $a=0$, so no other generators are needed. On the projective rank-at-most-one locus, all charts where some $a_i$ is invertible are empty since $a_i^2=0$. The chart $b\neq0$ has all $a_i=0$, giving exactly the line $L$. The kernel of multiplication by its local generator is $V$, since the square of the generator spans the complementary summand. Hence $V$ is intrinsic too, and the local descriptions glue.

The graded objects are equivalently $(V,L,f:L^{\otimes3}\to\operatorname{Sym}^3 V)$. Putting $U=V\otimes L^{-1}$ identifies $f$ with a section of $\operatorname{Sym}^3 U$, leaving $L$ independent. Conversely $V=U\otimes L$ recovers the data. These equivalences are functorial on morphisms and on base change, proving the graded stack formula.

Choose local lifts of bases of $V,L$ to $M$. Their quadratic products give a basis modulo $M^3$, and the cubic products in the $V$-lifts give a basis of $M^3$. Together they give the displayed filtered basis, by the successive locally free quotients. The products $zv$ lie in $M^3$ and record $\phi$. Associativity and $M^4=0$ force $zvv'=0$ and $z^2v=0$. This gives the stated normal form. Conversely every $(f,\phi)$ defines an associative algebra by those rules. A triple of positive filtration degree with total degree at least four has zero product in either parenthesization. The remaining triples give the usual cubic products, $z^3$, or zero for mixed terms. The unit extends associativity to all triples. These arguments use identities in the base ring.

## Exact changes of lifts and groupoid multiplication

Write $E_1=V\oplus Rz$ and $E_2=Q\oplus Rz^2$. A map inducing the identity on the associated graded necessarily has the form
$$
 a\longmapsto a+u(a)+w(a)\qquad(a\in E_1)
$$
with $u:E_1\to E_2$, $w:E_1\to P$. Decompose
$$
 u(v)=\alpha(v)+\lambda(v)z^2,\qquad u(z)=q+\rho z^2 .
$$
The induced map on $E_2$ is $b\mapsto b+\delta_f(u)b$, where $\delta_f(u):E_2\to P$ is
$$
 \delta_f(u)(vv')=\alpha(v)v'+\alpha(v')v,\qquad
 \delta_f(u)(z^2)=2\rho f .
$$
The map on $P$ is the identity. These formulas come from multiplying the changed lifts. In particular they hold in characteristic two and do not depend on $\phi$. Computing the mixed products of the changed lifts in the target gives the additional term $qv+\lambda(v)f$. The cubic relation $z^3=f$ is unaffected by terms of filtration degree two and higher. It follows that these data give an isomorphism $A(f,\phi)\to A(f,\phi')$ exactly when $\phi'=\phi-B_f(q,\lambda)$. The map is invertible from its triangular matrix with diagonal the identity.

Composition of the triangular matrices gives a group $\mathcal U_f$ on the underlying vector space of pairs $(u,w)$:
$$
 (u,w)(u',w')=
 \big(u+u',\,w+w'+\delta_f(u)u'\big).
$$
It is a two-step unipotent group, since the $w$-subgroup is central and the quotient is additive. It is smooth over the cubic base, with its underlying scheme a vector bundle. The map to $(q,\lambda)$ is an additive homomorphism. Denote its kernel by $\mathcal H_f$. This is again smooth, with underlying vector-bundle rank
$$
 n\binom{n+1}{2}+1+(n+1)\binom{n+2}{3}.
$$

For the general graded change of basis $G=\operatorname{GL}(V)\times\mathbb G_m$, write $(S,a)$ for the action on $V$ and $z$ respectively. Its action on the coordinates is
$$
 f'=a^{-3}\operatorname{Sym}^3(S)f,\qquad
 \phi'=a^{-1}\operatorname{Sym}^3(S)\phi S^{-1}.
$$
Indeed the normalized map must preserve the relations $z^3=f$ and $zv=\phi(v)$. The linear maps on the quadratic and cubic parts then follow from multiplication. Every isomorphism factors uniquely as such a graded change followed by a map inducing the identity in the new graded coordinates. On the lift parameters, conjugation by the graded change sends
$$
 q\longmapsto a^{-1}\operatorname{Sym}^2(S)q,\qquad
 \lambda\longmapsto a^2\lambda S^{-1}.
$$
This makes $B_f$ equivariant with the displayed action on $\phi$ and preserves the kernel subgroup $\mathcal H_f$.

The framed objects with arrows just computed present the full filtered stack after fppf descent. Every object has a local framed normal form, and every isomorphism of two framed objects is precisely one of these arrows. Descent of the algebras is effective because it is descent for finite locally free modules and their multiplication, identity and augmentation maps.

Now send an arrow to its graded change of basis and its two lift coordinates $(q,\lambda)$. This gives a morphism of groupoids and, by descent, a morphism to the stack
$$
 \left[
    [\, (P\times\Phi)/(Q\oplus V^*)\,]/G
 \right].
$$
The first quotient is relative to $P$ by the displayed translation action; the second uses the equivariant graded action. Every object lifts locally, and each arrow between framed objects lifts by taking the other coordinates of $u,w$ freely. The lifting category over a local framed object has automorphism group $\mathcal H_f$, so locally it is the classifying stack of that smooth group. This proves that the projection is a smooth gerbe and identifies its removed inertia explicitly.

## The quotient on the two cubic strata

If $f$ has at least one unit coefficient locally, $B_f$ is a split injection locally on the base. It is enough to prove injectivity in every residue field. If $qv+\lambda(v)f=0$ and $\lambda\neq0$, take nonzero $v\in\ker\lambda$, which exists for $n\geq2$. Multiplication by $v$ on the polynomial ring is injective, giving $q=0$. Then $\lambda=0$ since $f\neq0$. The case $\lambda=0$ also forces $q=0$. Full-rank minors give local left inverses over the base. The translation stack is therefore the vector bundle $\operatorname{coker}B_f$, before taking the quotient by $G$. Over the graded moduli description with $U=V\otimes L^{-1}$, the translation complex is intrinsically the tensor product by $L$ of
$$
 \operatorname{Sym}^2 U\oplus U^*
 \longrightarrow \operatorname{Hom}(U,\operatorname{Sym}^3 U).
$$
For instance the defect has source $L\otimes V$ and target $\operatorname{Sym}^3 V$, giving this twist. The split laws are precisely the zero section on this open set.

At the zero cubic, $q\mapsto(v\mapsto qv)$ is injective, and $\lambda$ acts trivially on $\phi$. The relative quotient is the product of the cokernel of this $q$-map with the classifying stack of the additive $V^*$, before descent by $G$. The identity-on-graded automorphism group is $\mathcal H_0\times V^*$. The product here is a group product, since the composition cross term involving the $\lambda$-shift factors through $\delta_0(u)(z^2)=0$.

## The inertia scheme and its blow-up

The full identity-on-graded automorphism group of any framed law is the subgroup of $\mathcal U_f$ with $(q,\lambda)\in\ker B_f$. Its underlying scheme is the product of the affine $\mathcal H_f$ coordinates and that kernel. Let $J\subset\Phi$ be the embedded image of $Q$, so the kernel scheme is equivalently
$$
 Z=\{(f,\lambda):[\lambda(\,\cdot\,)f]=0\ \text{in }\Phi/J\}.
$$
The coordinate $q$ is uniquely recovered. If $\lambda$ has a unit coefficient, one can choose a basis in which it is a coordinate functional. Applying the kernel equation to another basis vector gives $q=0$, since multiplication by that variable is injective over every ring. Applying it to the first basis vector gives $f=0$. Combined with the nonzero cubic calculation, this identifies the two axes scheme-theoretically off their intersection.

Over an algebraically closed field the reduction of $Z$ is the union of the $f$-axis and the $\lambda$-axis. The defining equations are bilinear, and their linear span in bidegree $(1,1)$ has codimension $\dim Q$ in the space of all mixed bilinear monomials. Indeed the linear map $P\otimes V^*\to\Phi/J$ is the quotient of the standard identification $P\otimes V^*=\Phi$. Thus some mixed bilinear monomials are nonzero in the coordinate ring of $Z$, although they vanish on its reduction. This proves nonreducedness at the intersection. Nonflatness occurs even at the identity above the origin. In the coordinate equation $qx_i=-\lambda_i f$, the coefficient of $x_j^3$ for $j\neq i$ gives $f_{x_j^3}\lambda_i=0$. At the identity, $\lambda_i$ is nonzero in the local ring because its image on the $\lambda$-axis is a coordinate. The base element $f_{x_j^3}$ is nonzero in the local domain of the universal cubic space. Thus the local algebra of the kernel has base torsion and cannot be flat.

For an explicit nilpotent example with $n=2$, take a base algebra with unit, four radical generators $A,B,L_1,L_2$, and one further vector $\tau$, with $L_1A=L_2B=\tau$ and all other products of these five vectors zero. It is associative because $\tau$ annihilates the radical. Set $f=A x^3+B x^2y$, $\lambda(x)=L_1$, $\lambda(y)=L_2$, and $q=-\tau x^2$. Then $qv+\lambda(v)f=0$ for both basis vectors, with $q\neq0$. This gives an actual identity-on-graded automorphism that retains a nonzero $q$-shift over a nonreduced base.

On a blow-up chart of the cubic space at its zero section, write $f=t u$ with one coefficient of $u$ equal to one. The kernel equation is $B_u(q,t\lambda)=0$. The primitive case proved above gives
$$
 q=0,\qquad t\lambda=0
$$
for the full scheme pullback. In group composition the only possible new term involving a lift supported in $\lambda z^2$ is $2\rho f\lambda$, which vanishes by these equations. Thus the pullback automorphism group really is the product of $\mathcal H_f$ and the central additive group on $t\lambda=0$. Over a field, the latter scheme is reduced on this chart: the ideal generated by the $t\lambda_i$ is $(t)\cap(\lambda_1,\ldots,\lambda_n)$, an intersection of prime ideals in the chart polynomial ring. It has the zero section and the full $\lambda$-bundle over the exceptional divisor as its two components. The same chart argument calculates the closure of the generic residual inertia as the zero section, so the horizontal automorphism group is $\mathcal H_f$.

## Recovering the blow-up from the translation planes

Write $D=\Phi/J$. On nonzero cubics, reduction of $B_f$ modulo $J$ gives a rank-$n$ plane $E_f\subset D$, the image of $b_f: \lambda\mapsto[\lambda(\cdot)f]$. Scaling $f$ leaves the plane fixed. The subbundle map $V^*\otimes\mathcal O(-1)\to D\otimes\mathcal O$ on $\mathbb P(P)$ therefore defines
$$
 \iota:\mathbb P(P)\longrightarrow \operatorname{Gr}(n,D),\qquad [f]\longmapsto E_f .
$$
This map is a closed immersion, over $\mathbb Z$ and after base change.

First work at geometric points. If $E_f=E_g$ there is an invertible linear map $A$ of $V^*$ such that $b_g(\lambda)=b_f(A\lambda)$ for every $\lambda$. Over the algebraically closed residue field, take an eigenvector of $A$ with eigenvalue $\eta$. This gives $\lambda(\cdot)(g-\eta f)\in J$. If $g-\eta f\neq0$ this map has rank one, while every nonzero member of $J$ is multiplication by a nonzero quadratic and has rank $n\geq2$. Thus the projective points agree.

A tangent direction represented by $g\bmod K f$ maps to the homomorphism $E_f\to D/E_f$ given by $b_f(\lambda)\mapsto b_g(\lambda)\bmod E_f$. This follows by writing the image of $b_{f+\varepsilon g}$ over the dual numbers as the graph of its first-order off-diagonal part. If the homomorphism vanishes, there is again a linear endomorphism $A$ with $b_g=b_f A$. An eigenvector gives $g\in Kf$ by the same rank argument, including when the eigenvalue is zero. Hence the relative geometric tangent kernels vanish. Finite presentation implies unramifiedness by the fiber criterion for relative differentials. The morphism is proper and universally injective, so it is a closed immersion. [The Stacks Project, closed immersion criterion](https://stacks.math.columbia.edu/tag/04XV)

Over any field, the closure of the graph of $f\mapsto E_f$ is now the blow-up of the origin. Indeed the closure of the graph of $f\mapsto[f]$ is the tautological incidence $f\in K u$ for $[u]\in\mathbb P(P)$, and composing with the closed immersion preserves this graph closure. Thus the modification used to split the inertia is recovered from the translation image planes themselves. Equivalently it is the blow-up of the maximal-minor ideal of $b_f$, by the graph description of a blow-up applied in Plücker coordinates. The exceptional divisor distinguishes every limiting projective direction of the cubic.

## Relation to the literature

Poonen presents the general moduli stack of commutative algebras using based multiplication tables and change of basis. Abramovich, Corti and Vistoli develop rigidification of algebraic stacks by removing specified automorphisms. Here the groupoid presentation is explicit for this filtered family, and its arrow projection constructs the gerbe directly. It exhibits the smooth subgroup, the surviving nonflat inertia, and the effect of the blow-up over zero. [Poonen, The moduli space of commutative algebras of finite rank](https://doi.org/10.4171/jems/131) · [Abramovich, Corti and Vistoli, Twisted bundles and admissible covers](https://doi.org/10.1081/AGB-120022434)

Grochow and Qiao relate cubic equivalence and algebra isomorphism by tensor isomorphism reductions. The calculation here gives a family-level moduli theorem for the cubic-anchor construction, including nonreduced test rings and nontrivial anchor line bundles. It concerns augmented algebras satisfying the stated graded conditions. Geometry.py checks the triangular composition law and 10,890 multiplication identities over the fields of orders 2, 3, and 5. It also checks all 211 projective binary cubic image planes and 100,980 tangent choices over those fields. The proof is in prose, without a Lean verification or a literature-priority claim. [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110)
