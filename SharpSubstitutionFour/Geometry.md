# Arbitrary projective schemes at the first detecting substitution size

**Theorem.** Let $k$ be any field, let $h\ge2$, and write $m=h+1$. For every projective $k$-scheme $T$, there is a three-tensor input to the sharp matrix-substitution construction with the following properties.

- In the marked family of centered substitutions supported on the first block row, the schemes of extra rank relations are empty in all sizes $j\le h$.
- At size $m$, the rank-drop scheme on the Grassmannian of first-row direction spans is isomorphic over $k$ to
  $$
              T\times_k \operatorname{OGr}(m,2m),
  $$
  where $\operatorname{OGr}(m,2m)$ parameterizes totally isotropic $m$-planes of the split quadratic form $\sum_{i=1}^m x_i y_i$.
- Restricting the directions at size $m$ to the marked first half of the active variables gives a rank-drop scheme isomorphic to $T$ itself.

These are scheme isomorphisms, including the nonreduced structure of $T$. The theorem uses the ordinary pencil and also applies to the normalized symmetric-matrix variant on the same marked substitutions. The first-row family uses unrestricted coefficient matrices. The matrix-substitution comparison for general small coefficient arrays is the preceding theorem. [Sharp matrix-substitution construction](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md)

## The first-row rank-drop schemes

Let $M\subseteq\operatorname{Hom}(E,F)$ be the matrix space spanned by the input slices, with $d=\dim E+\dim F$. Use the construction with $Z=E\oplus F$ and
$$
 B(x,y,A)=[xI_Z+\widetilde A,\ yI_Z],\qquad A\in M,
$$
where $\widetilde A$ maps $E$ to $F$ and kills $F$. Use $m$ copies of this block, with disjoint variable spaces $X_0,Y_0$ of dimensions $md,2md$, and put $V=X_0\oplus Y_0\oplus k e_*$. The corresponding linear subspace $H\subset C=\operatorname{Sym}^2 V$ consists of the quadrics $q_B=X^{\mathsf T}B^{\oplus m}Y$. The multiplication coefficient in the pencil is $\beta(u,v)=[uv]\in C/H$, with the inert padding omitted from the notation.

On $G_j=\operatorname{Gr}(j,V)$ let $\mathcal U$ be the tautological $j$-plane and
$$
 \mathcal P_j=\ker\big(C\otimes\mathcal O
              \longrightarrow \operatorname{Sym}^2(V/\mathcal U)\big).
$$
This is a subbundle of rank $r_j=j\dim V-j(j-1)/2$. Locally split $V=\mathcal U\oplus\mathcal U'$ to see that it consists of the degree-two products involving at least one entry of $\mathcal U$, with fiber $UV$. Let $\mathcal D_j\subset G_j$ be defined by the maximal minors testing injectivity of $\mathcal P_j\to(C/H)\otimes\mathcal O$. The relation incidence $\mathcal I_j\subset G_j\times \mathbb P(H)$ is the zero scheme of the universal quadratic line mapped to $\operatorname{Sym}^2(V/\mathcal U)$. It represents pairs $(U,[q])$ with $q$ in $UV$, over arbitrary test schemes by pullback.

On the space of ordered bases $u_1,\ldots,u_j$ of $U$, set the scalar coefficient to zero and put the $u_i$ in the first block row of the size-$j$ substitution. Its nonzero block row in the ordinary pencil is the map
$$
                V^j\longrightarrow C/H,\qquad
                  (v_i)_i\longmapsto \sum_i \beta(u_i,v_i).
$$
The map to $\mathcal P_j$ before quotienting by $H$ is surjective onto a vector bundle. It splits locally, so the rank-drop minors at rank $r_j$ give the pullback of $\mathcal D_j$. The transpose portion in the normalized symmetric pencil contributes a direct block of constant rank $\dim V$: even one nonzero $u_i$ gives a surjective $\beta(u_i,-)^{\mathsf T}$, because $\beta(u_i,-)$ is injective. Eliminating a full-rank minor in this extra block gives the same determinantal ideal, with the rank threshold shifted by $\dim V$.

Every $q_B\ne0$ has polarization rank $2m\operatorname{rank}B\ge2m$, over every extension field and in every characteristic. The polar of an element of $UV$ has rank at most $2j$. Thus $\mathcal P_j\to(C/H)\otimes\mathcal O$ is injective on every geometric fiber for $j<m$. The minors generate the unit ideal locally, proving $\mathcal D_j=\mathcal I_j=\varnothing$ as schemes. This assertion concerns extra relations among full first-row direction spans on $G_j$.

## The first relation scheme is an orthogonal Grassmannian

Assume $d\ge3$. Define the projective rank-one scheme
$$
 \Sigma_M=\mathbb P(M)\cap
   \operatorname{Seg}\big(\mathbb P(F)\times\mathbb P(E^*)\big).
$$
Equivalently it is cut out inside $\mathbb P(M)$ by the $2$-by-$2$ minors of $A$. There is a canonical isomorphism from $\mathcal I_m$ to a relative split maximal orthogonal Grassmannian over $\Sigma_M$. We prove this on arbitrary test rings so that the conclusion gives the scheme structure.

First show that the projection to $\mathbb P(H)$ factors through $\Sigma_M$. Locally split $U$ and choose a generator $q_B$ of its quadratic line. The equation $q_B\in UV$ implies that the polar matrix has zero lower-right block in a basis of $V^*$ whose last coordinates span $U^\perp$. It follows that all $(2m+1)$-minors vanish over the test ring: the matrix factors through a free module of rank $2m$, by writing the portion in the first $m$ rows separately from the portion in the first $m$ columns and remaining rows. On any geometric point, this forces $\operatorname{rank}B\le1$. The point of $\mathbb P(H)$ is nonzero, so $\operatorname{rank}B=1$, and its anchors are zero because any nonzero anchor makes the rank $d$. Thus the test scheme is covered by opens with some data entry $A_{ij}$ a unit, with pivot row $i\in F$ and pivot column $j\in E$.

On a pivot open, eliminate the pivot of $B$ by invertible row and column operations. Write $B_{\mathrm{rem}}$ for the Schur complement leftover. The polar matrix of $q_B$ is, up to permutations, the direct sum of $m$ copies each of $B$ and $B^{\mathsf T}$, with the extra zero direction. The elimination gives a $2m$-by-$2m$ invertible diagonal block and separate copies of $B_{\mathrm{rem}}$ and its transpose. The minors extending this block by one row and column force every entry of $B_{\mathrm{rem}}$ to vanish. This uses only invertible changes of bases and unit division. It proves the rank-one equations of $B$ over the entire test ring.

For $y$, use the entry in row $k\ne i$ and the $k$-th column of the second block, where the pivot row has zero entry. In the Schur complement that entry is $y$, so $y=0$. For $x$ choose $k$ different from both $i,j$, possible because $d\ge3$. In the first-block diagonal entry of row and column $k$, the Schur correction vanishes: if $k$ lies in $E$, the entry in row $k$, column $j$ vanishes, and if $k$ lies in $F$, the entry in row $i$, column $k$ vanishes. The leftover entry is $x$, so $x=0$. The remaining rank-one equations are those of $A$. This proves factorization through the rank-one scheme, including over nonreduced test rings.

Over $\Sigma_M$, the locally chosen generator $A$ of the rank-one line factors as one column times one row, both with a unit coordinate locally. Its repeated quadric has support $\mathcal L=\mathcal L_X\oplus\mathcal L_Y$ in $V\otimes\mathcal O$. The two halves are the $m$ copies of the column and row lines, respectively. They are rank-$m$ subbundles in $X_0$ and $Y_0$. On $\mathcal L^*$ the universal quadratic is split hyperbolic after locally trivializing its coefficient line.

For completeness, the condition $q_B\in UV$ forces $U\subseteq\mathcal L$ over test rings as well. Set $P=U^\perp\subset V^*$ and project $P$ to $\mathcal L^*$. Over a geometric point, the radical of the ambient hyperbolic form is $\operatorname{Ann}(\mathcal L)$, of codimension $2m$. Since $P$ has dimension $\dim V-m$ and its projection is isotropic of dimension at most $m$, the projection has dimension exactly $m$. Locally on the test scheme choose $m$ vectors in $P$ whose projections span a rank-$m$ direct summand $K\subset\mathcal L^*$. They can be chosen by a unit minor. They span a totally isotropic summand. Its polar orthogonal complement has rank $m$, and equals $K$, since the pairing is perfect and the inclusion of these summands is an equality on each geometric fiber. The projection of every vector in $P$ is orthogonal to $K$, hence lies in $K$. Then $P$ equals the full preimage of $K$: the inclusion is between rank-$(\dim V-m)$ direct summands and is an isomorphism on geometric fibers. It follows that $U$ lies in $\mathcal L$ and that its annihilator in $\mathcal L^*$ is $K$. Conversely any totally isotropic rank-$m$ summand $K$ of $\mathcal L^*$ gives $U$ by annihilation, and $q_B\in UV$ because its restriction to $U^\perp$ is zero as a quadratic polynomial. These inverse constructions are natural under base change and give the claimed scheme isomorphism.

Locally on $\Sigma_M$ this is a product with the split orthogonal Grassmannian, smooth of relative dimension $m(m-1)/2$. One can check smoothness of the split fiber in all characteristics by passing to an algebraic closure and taking an isotropic complement to any maximal isotropic subspace. The chart of subspaces transverse to that complement is the space of graphs of alternating matrices, with skew off-diagonal entries and zero diagonal. These are exactly the conditions from the split quadratic polynomial and require no division by two.

When $d=2$, the possibilities are $a=b=1$ and $M=0$ or $M=k$. The first incidence is empty for $M=0$. Otherwise use the projective pivot chart with data entry $1$. The first block is $\left(\begin{smallmatrix}x&0\\1&x\end{smallmatrix}\right)$, and the second is $yI_2$. Its rank-one equations give the ideal $(y,x^2)$. The support argument works unchanged over that chart, and the hyperbolic support has a global frame there. This gives $\mathcal I_m\simeq\operatorname{Spec}k[x]/(x^2)\times_k\operatorname{OGr}(m,2m)$, exhibiting an actual nilpotent relation direction.

## From the incidence to the determinantal scheme

On the open of $G_m$ where $\mathcal P_m\to C/H$ has a unit $(r_m-1)$-minor, eliminate that minor. The defining rank-drop minors impose that the remaining single column is zero in the residual rows. Over this closed locus the kernel is a rank-one subbundle, with a unique projective relation line, and the kernel-line incidence is isomorphic to the rank-drop scheme. This gives an isomorphism on the defect-one part with its determinantal scheme structure, without requiring the scheme to be reduced. In the $d=2$ example with $M=k$, every geometric detecting plane has only the single data relation, so this also identifies the entire first rank-drop scheme there.

In the description above, a relation line for a geometric $U$ forces $U$ into the repeated column-plus-row support of its $A$. For two distinct rank-one projective matrices, these two support spaces intersect in zero if both their columns and rows differ. If one line agrees, their intersection is exactly the repeated rank-$m$ pure half for that line. Consequently any detecting $U$ whose projections to $X_0,Y_0$ are both nonzero has exactly one relation line. Defect there is one, so the incidence and rank-drop schemes agree on this open.

## Realizing arbitrary projective schemes

For the empty scheme take $M=0$ with $a=b=2$, so the rank-one data scheme and the first relation scheme are empty. Otherwise embed $T$ as a closed subscheme of $\mathbb P^n_k$ and choose a degree $e$ at least the degrees of homogeneous ideal generators. The degree-$e$ part of the ideal gives linear conditions in the $e$-th Veronese space. Indeed on the chart where coordinate $z_i$ is nonzero, each generator of degree $b\le e$ is represented by its degree-$e$ multiple by $z_i^{e-b}$, and the multiplier is a unit after dehomogenizing. Thus these linear conditions cut out $T$ scheme-theoretically within the Veronese image. The Veronese ideal is generated by quadratic monomial exchanges. To see generation, monomials in the Veronese coordinates with the same image correspond to different partitions of the same multiset of variables into blocks of size $e$. Swapping an entry of one block with an entry of another is a quadratic binomial, and repeated swaps connect any two partitions. Grouping terms by their images proves generation of the ideal. Eliminating the linear equations, this realizes $T$ inside a projective space $\mathbb P^{b-1}$ as the zero scheme of quadrics. We can take $b\ge2$ by retaining extra linear equations or padding the ambient coordinates. [Eisenbud, Reeves and Totaro, high Veronese presentations](https://arxiv.org/abs/alg-geom/9310007) · [Shibuta, quadratic Gröbner bases for high Veronese subrings](https://arxiv.org/abs/0906.5129)

Take $a=b$ in the matrix input format, using $b$-by-$b$ symmetric matrices. Impose the linear conditions on their entries corresponding to the quadrics for $T$: a term $z_i z_j$ becomes the single entry in position $ij$, with $i\le j$. Call the resulting linear space $M$, and give its basis as tensor slices. For a zero matrix space use one zero slice to keep the format positive. The rank-one symmetric scheme is the diagonal in the Segre scheme. On the Segre, the equations $u_i v_j=u_j v_i$ impose equality of the two lines scheme-theoretically: locally with $u_i$ a unit they make $v$ a multiple of $u$, and that multiplier is a unit because $v$ represents a projective line. The remaining linear equations are exactly the defining quadrics of $T$ on the diagonal. Hence $\Sigma_M\simeq T$ over $k$, in characteristic two as well.

For two distinct geometric points of this diagonal, both factor lines differ, so their repeated support spaces are disjoint. Every detecting $U$ therefore has only one relation line. The open with a unit $(r_m-1)$-minor covers the whole rank-drop scheme, and the preceding elimination gives $\mathcal D_m\simeq\mathcal I_m$. On the diagonal the two support halves are both $\mathcal O_T(-1)\otimes k^m$, and the hyperbolic quadratic has the associated common line twist. Tensoring an isotropic summand by this line or its dual identifies the relative isotropic Grassmannian with the constant split product. This proves $\mathcal D_m\simeq T\times_k\operatorname{OGr}(m,2m)$.

Finally the scheme condition $U\subseteq X_0$ forces $U\subseteq\mathcal L_X$ in the incidence description, over arbitrary test rings. Both have rank $m$, so $U=\mathcal L_X$, giving precisely a section over $T$. This proves the exact marked pure-rank locus claim.

## A nonreduced example and finite checks

Take $T$ to be the double point $z_1^2=0$ in $\mathbb P^1$. The matrix space consists of $\left(\begin{smallmatrix}u&t\\t&0\end{smallmatrix}\right)$. On the chart $u=1$, the rank-one equation is $t^2=0$. Thus the marked pure rank-drop locus has one geometric point and its nonzero tangent direction survives in the determinantal scheme. The full first rank-drop locus is the split orthogonal Grassmannian over that double point.

An exact finite control enumerated the $2$-by-$2$ minors of the anchored matrices over the dual-number rings of $\mathbb F_2$ and $\mathbb F_3$. It checked all 97 coefficient pairs for the $d=2$ exceptional chart against $(y,x^2)$, and all 793 coefficient triples for the double-point chart against $(x,y,t^2)$. It also checked 793 alternating-graph instances in the split orthogonal chart with $m=3$.

## Comparison with prior work

Ordinary Grassmannian incidence for rank degeneracy is classical. Reineke and Hille establish quiver-Grassmannian universality. Ringel extends the realization to fixed wild acyclic quivers, and Lorscheid–Weist give an explicit scheme-level statement in Corollary 3.7. Vakil studies universality of local singularity types in deformation and moduli problems. The result here realizes arbitrary projective schemes at a prescribed first matrix-substitution size in the common-profile pencils. The special form of the scheme comes from repeated polar pivots, an intrinsic maximal isotropic support, and a rank-one section of a symmetric matrix space. It is compatible with the existing transporter-preserving construction in Grochow and Qiao's tensor-isomorphism framework. [Reineke, Every projective variety is a quiver Grassmannian](https://arxiv.org/abs/1204.5730) · [Hille, Moduli of representations, quiver Grassmannians, and Hilbert schemes](https://arxiv.org/abs/1505.06008) · [Lorscheid and Weist, Corollary 3.7](https://doi.org/10.1112/blms.12272) · [Ringel, Quiver Grassmannians for wild acyclic quivers](https://arxiv.org/abs/1703.08782) · [Vakil, Murphy's Law in algebraic geometry](https://arxiv.org/abs/math/0411469) · [Grochow and Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Ivanyos, Qiao and Subrahmanyam, matrix blow-ups and noncommutative rank](https://arxiv.org/abs/1512.03531)

The universality construction is effective from homogeneous equations and may enlarge the format with the Veronese degree. The proof is in prose. Publication priority and Lean verification are unestablished.
