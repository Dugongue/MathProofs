# Recovering a projective scheme from its unmarked first rank-drop scheme

Fix a field $k$ and an integer $m\ge3$. Put $n_m=m(m-1)/2$. For a projective $k$-scheme $T$, let $\mathcal D_m(T)$ be the first rank-drop scheme in the size-$m$ construction with $h=m-1$, using the symmetric matrix space that realizes $T$ in the preceding theorem. That theorem gives
$$
 \mathcal D_m(T)\simeq T\times_k \operatorname{OGr}(m,2m)
$$
as schemes, with a split quadratic form on the right. [First rank-drop universality](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md)

**Theorem.** For any two projective $k$-schemes $T,T'$ of dimension less than $n_m$, their abstract first rank-drop schemes are isomorphic over $k$ if and only if $T\simeq_k T'$. This includes nonreduced and disconnected projective schemes, over every characteristic. Any pair of projective schemes is covered by choosing a common $m$ with $n_m>\max(\dim T,\dim T')$.

More precisely, the projection from the abstract rank-drop scheme to $T\sqcup T$ is characterized, up to unique isomorphism, by its universal property for maps to projective schemes of dimension less than $n_m$. This projection is recognized by every isomorphism of the rank-drop schemes, with the full scheme structure on its base. The two copies of $T$ determine its isomorphism class by connected-component multiplicities. For arbitrary coefficient base change, the same projection recovery holds for isomorphisms over the new base. We also describe the vertical automorphisms and the action of every base automorphism on them.

## Geometry of the split fiber

Write $U_0=k^m$, $W=U_0\oplus U_0^*$, and $q(x,\ell)=\ell(x)$. Let $\mathcal G=\operatorname{OGr}(m,W)$ be the projective scheme of maximal totally isotropic summands. The fibers used here are defined using the quadratic polynomial, including in characteristic two. We show that $\mathcal G$ is the disjoint union of two $k$-isomorphic smooth geometrically integral schemes of dimension $n_m$, each with Picard group $\mathbb Z$ over every field extension.

Stratify $\mathcal G$ by $r=\dim(L\cap U_0^*)$ for an isotropic plane $L$. On this stratum, put $K=L\cap U_0^*$. The projection of $L$ to $U_0$ is the annihilator $K^\circ$. In the polar quotient by $K$, the subspace $L/K$ is a graph of an alternating map
$$
 K^\circ\longrightarrow U_0^*/K=(K^\circ)^*.
$$
Here alternating means that its corresponding bilinear form has zero diagonal as a polynomial. Conversely each alternating map gives such a graph. The same description on the fixed-rank locus works on test schemes by choosing a locally split projection. Thus the stratum is the total space of the indicated alternating-form bundle on $\operatorname{Gr}(r,U_0^*)$. It is geometrically integral of dimension
$$
 r(m-r)+\frac{(m-r)(m-r-1)}{2}
       =n_m-\frac{r(r-1)}{2}.
$$

At any geometric point of the stratum, choose a basis adapted to $K$ in $U_0^*$. Subtracting an alternating graph map extending the given one, by a hyperbolic shear fixing $U_0^*$, turns $L$ into the span of $e_1,\ldots,e_{m-r}$ and $f_{m-r+1},\ldots,f_m$ in a hyperbolic basis $(e_i,f_i)$. Take the complementary isotropic plane spanned by the other member of each pair. In the chart of graphs from $L$ to this complement, the quadratic equations say that the graph matrix is alternating. These charts prove smoothness and dimension $n_m$ everywhere. In such a chart the dimension of intersection with $U_0^*$ is the nullity of the alternating $r$-by-$r$ submatrix in the final $r$ positions. Indeed the first $m-r$ coefficients of a vector in the graph must vanish for it to belong to $U_0^*$, and the remaining $U_0$-coordinates are precisely given by that submatrix. Since an alternating form has even rank in every characteristic, the parity of the intersection dimension is locally constant. The parity loci are defined by unions of the rank strata over $k$, and their open and closed property descends from an algebraic closure.

In the even parity piece the only stratum of dimension $n_m$ has $r=0$, and it is the affine space of alternating maps $U_0\to U_0^*$. In the odd piece the only stratum of that dimension has $r=1$, and it is a vector bundle over $\mathbb P(U_0^*)$. Every component of each smooth piece has dimension $n_m$, so each piece is geometrically integral by the irreducibility of its unique top stratum. Swapping $e_m$ with $f_m$ carries the even component to the odd component, since it carries the $r=0$ coordinate plane $U_0$ to an $r=1$ plane. Let $S$ be the even component and fix this swap to identify $\mathcal G\simeq S\sqcup S$.

Over any extension field, the affine open stratum of $S$ has trivial Picard group and its complement has exactly one prime divisor, the closure of the stratum $r=2$. In fact $r=2$ gives one irreducible stratum of codimension one, and all larger even $r$ have codimension at least two. A line bundle has a rational trivialization on the affine open, hence its divisor class is supported on the boundary. Regularity of $S$ lets us use Cartier classes and Weil classes interchangeably. Thus $\operatorname{Pic}(S)$ is cyclic, and is infinite because the Plücker bundle is ample on a positive-dimensional projective variety. Its generator can be chosen ample, since a positive tensor power of that generator is an ample Plücker bundle. This computes the required geometric Picard groups without a characteristic restriction. For comparison, Hudson, Martirosian and Xie compute the Picard group of spinor varieties in their quadratic-form setup, and van Geemen and Marrani study spinor embeddings in characteristic two. [Hudson, Martirosian and Xie, Proposition 2.18](https://doi.org/10.1112/plms.12479) · [Van Geemen and Marrani](https://arxiv.org/abs/1903.01228)

## An intrinsic projection over every coefficient base

Every morphism from $S_K$ to a projective $K$-scheme of dimension less than $n_m$ is constant when $K$ is algebraically closed. Indeed pull back a very ample bundle on the target. The pullback is globally generated and is a tensor power of the ample generator of $\operatorname{Pic}(S_K)$. Its exponent is nonnegative, since negative powers have negative degree on the closure of a line in the open affine stratum. If the exponent is zero, all projective coordinates of the morphism are global sections of the trivial bundle and hence constants. If it is positive, the pullback is ample. The dimension inequality forces a positive-dimensional fiber of the morphism, and restriction of the pullback to this fiber is trivial, contradicting ampleness.

Let $R$ be any commutative $k$-algebra and let $Y$ be a projective $k$-scheme of dimension less than $n_m$. For any $R$-scheme $X$, every $R$-morphism
$$
                  f:X\times_R S_R\longrightarrow Y_R
$$
factors uniquely through the projection $\pi:X\times_R S_R\to X$. For each $x\in X$, the morphism on the geometric $S$-fiber is constant by the dimension argument. Its image on the original fiber is therefore contained in a single underlying target point. Choose an affine neighborhood of this point in $Y_R$. Properness of $\pi$ gives a neighborhood of $x$ over which the image of $f$ lies in that affine: remove the closed image of the inverse image of its complement. On this neighborhood $f$ factors since $\pi_*\mathcal O=\mathcal O_X$. This sheaf equality holds with all nilpotents. Indeed $S$ is geometrically integral and proper with a $k$-point, hence $\Gamma(S,\mathcal O_S)=k$. On an affine open of $X$, tensoring a finite affine-cover equalizer for $S$ with that open's $k$-algebra is exact and proves the equality. The local maps glue uniquely, for example by restricting to the constant section of $\pi$ at the coordinate plane $U_0$. The factorization thus applies even when $R$, $X$, or $Y$ is nonreduced. [Stacks Project, factorization for morphisms with connected fibers](https://stacks.math.columbia.edu/tag/057H)

Denote $B_T=T\sqcup T$. After using the swap between the two orthogonal components, the preceding rank-drop theorem gives $\mathcal D_m(T)\simeq B_T\times S$. Its projection to $B_T$ induces a natural bijection
$$
 \operatorname{Hom}_R((B_T)_R,Y_R)
     \ \simeq\
 \operatorname{Hom}_R(\mathcal D_m(T)_R,Y_R)
$$
for every such $Y$. Since $B_T$ itself is projective of dimension less than $n_m$, the representing base and its projection are intrinsic. In particular an abstract isomorphism of the rank-drop schemes induces an isomorphism of the doubled bases, using the induced map of the inverse as inverse. Over $k$, each finite-type projective scheme has a finite decomposition into open and closed connected components. An isomorphism of doubled bases preserves the multiplicity of each connected $k$-scheme isomorphism type. These multiplicities in each doubled scheme are twice those of the corresponding original scheme. Dividing the multiplicities by two gives $T\simeq_k T'$. Conversely an isomorphism of the bases gives an isomorphism of the rank-drop schemes by taking the product. This recovers the isomorphism class of $T$ from the abstract scheme without selecting a copy.

The strict dimension inequality gives the indicated universal property. At dimension $n_m$, the exchange involution on $S\times S$ exchanges the two projections to $S$.

## All automorphisms in the stated dimension range

Let $G=\operatorname{Aut}_k(S)$ denote the automorphism functor of the split component. It is represented by an affine group scheme. One can see this directly using the anticanonical embedding. The tautological subbundle $\mathcal U$ has $W/\mathcal U\simeq\mathcal U^*$ by the polar pairing. The tangent space of the ordinary Grassmannian is given by maps $\mathcal U\to W/\mathcal U$. Preserving $q$ means that the polar pairing of $u$ with its first-order change vanishes as a quadratic polynomial in $u$. Therefore $T_S\simeq\bigwedge^2\mathcal U^*$, including in characteristic two. It follows that
$$
 \omega_S^{-1}=(\det\mathcal U^*)^{m-1}
$$
is very ample, as a positive tensor power of the Plücker bundle. Under every base change an automorphism preserves the relative anticanonical line and acts on its sections. Their formation commutes with base change from $k$ by the same finite-cover argument for global sections. Conversely a projective linear transformation preserving the closed anticanonical image restricts to an automorphism. The full space of sections in this embedding ensures uniqueness of its projective linear extension, also over test rings: a transformation restricting to the identity acts on the restricted line by a global unit, hence a scalar, and the sections identify those of the ambient $\mathcal O(1)$ with those of the restricted embedding line. The stabilizer is closed in the projective linear group by the homogeneous ideal conditions, which can be checked after faithfully flat local linear lifts. This gives the asserted affine group scheme. [Demazure, automorphisms and deformations of flag varieties](https://doi.org/10.1007/BF01390108)

For the product of $T$ with the connected fiber $S$, set $A_T=\Gamma(T,\mathcal O_T)$. Every automorphism over $R$ descends to an automorphism of $T_R$ by the projection result. The kernel consists of $T_R$-automorphisms of $T_R\times_R S_R$, hence maps $T_R\to G_R$. Because $G$ is affine, these are exactly $G(A_T\otimes_k R)$, by the identification of global functions after base change. Each base automorphism acts trivially on the $S$-factor to split the projection of groups. Thus
$$
 \operatorname{Aut}_R(T_R\times_R S_R)
    \simeq G(A_T\otimes_k R)\rtimes\operatorname{Aut}_R(T_R),
$$
where the base action on the vertical group is precomposition by the inverse base automorphism. When $T$ is geometrically integral and projective, $A_T=k$, so this is a direct product, functorially. The same description with $B_T$ in place of $T$ gives all automorphisms of the full first rank-drop scheme. It includes base automorphisms permuting the two copies and the connected components. When $T=\operatorname{Spec} k[\epsilon]/(\epsilon^2)$, for example, the vertical functor uses $G(R[\epsilon]/(\epsilon^2))$ on each copy. It retains the information in the infinitesimal base.

## Scope and verification

Fujita treats cancellation for complete varieties, and Bansal, Sarkar and Vats study recovery of projective-bundle structures under a dimension comparison. The result here uses a split maximal orthogonal Grassmannian to recover the entire scheme that the tensor construction encodes at its first rank drop, including its nilpotents. The relative description of automorphisms is independent of the chosen projective presentation of $T$. The passage to rank-drop schemes combines this with the preceding tensor-isomorphism construction in the Grochow–Qiao framework. [Fujita, Cancellation problem of complete varieties](https://doi.org/10.1007/BF01393936) · [Bansal, Sarkar and Vats, Theorem 3.9](https://arxiv.org/html/2311.00999v1) · [Grochow and Qiao, Part IV](https://arxiv.org/abs/2306.16317)

An exact finite control enumerated all $1,395$ three-planes in $\mathbb F_2^6$ and all $33,880$ three-planes in $\mathbb F_3^6$. For $r=0,1,2,3$, the isotropic stratum counts were respectively $(8,14,7,1)$ and $(27,39,13,1)$, matching the graph formulas and giving equal counts in the two parities. The proof is in prose. Lean verification and publication priority for the rank-drop reconstruction statement are unestablished.
