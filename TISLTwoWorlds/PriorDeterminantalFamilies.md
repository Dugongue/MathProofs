# Special-linear tensor isomorphism and determinantal hypersurface equivalence

## The computational equivalence

Let $F$ be a field and let the geometric zero set of a polynomial mean its zero set after extension to an algebraic closure of $F$. In projective-linear equivalence, the change of coordinates itself must be defined over $F$. We consider reduced geometric zero sets, so repeated polynomial factors do not carry information.

**Theorem.** Over every field, special-linear three-tensor isomorphism on a common positive tensor format has a deterministic objectwise many-one reduction to projective-linear equivalence of reduced geometric zero sets of homogeneous determinant pencils. A homogeneous determinant pencil is a square matrix whose entries are homogeneous linear forms, supplied by its coefficient matrices. Both pencils have polynomial dimensions. On the explicitly specified family constructed below there is a reverse polynomial reduction, even when the input pencils use different representations of their determinant polynomials. This gives polynomial bit-time reductions over explicitly represented finite fields, in particular a same-field equivalence over $\mathbf F_3$.

For general tensor pairs, unequal formats and zero-dimensional formats can first be decided directly. For the reverse reduction, the family is specified by one common positive tensor format, the variable orders, and the promise that the determinant equals a nonzero scalar times the constructed polynomial with an arbitrary positive power on one specified linear factor. This presentation allows changes of the linear matrix representation and of that multiplicity. The decision problem itself only uses reduced geometric zero sets.

Thus the stated family is complete for ordinary tensor isomorphism under deterministic polynomial many-one reductions if and only if $\mathsf{TI}_{\mathrm{SL}}\le_m^{\mathrm P}\mathsf{TI}$. The forward implication uses the two reductions of the theorem. The reverse implication also uses $\mathsf{TI}\le_m^{\mathrm P}\mathsf{TI}_{\mathrm{SL}}$, obtained by adjoining a one-dimensional null complement in each mode. An ordinary transporter can use this complement to repair each determinant, and any transporter descends to an ordinary isomorphism of the original tensors by restriction to their mode supports and extension across the unused coordinates. A reduction for unrestricted reduced determinant-hypersurface equivalence to ordinary TI would suffice for the collapse. The equivalence here is with the explicitly constructed family. A separate construction below gives the same family-level equivalence for abstract isomorphism of absolutely irreducible projective hypersurfaces supplied by affine-linear determinant pencils. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5), [Kayal, polynomial equivalence](https://epubs.siam.org/doi/10.1137/1.9781611973082.108)

## Determinant anchors on vector variables

Write $n_1,n_2,n_3$ for the positive mode dimensions. For each mode $i$ take $n_i+1$ copies of the vector variable in $F^{n_i}$, written $x_{i,1},\ldots,x_{i,n_i+1}$. Write $x$ for all these coordinates. For each $i,j$ the determinant anchor is
$$
D_{i,j}(x)=\det(x_{i,1},\ldots,\widehat{x}_{i,j},\ldots,x_{i,n_i+1}).
$$
The data form $L_A(x)$ evaluates the trilinear tensor $A$ on the first copy from each mode. The usual covariant tensor action gives these trilinear identities after inverse transposes, which preserve determinant one.

For a polynomial $P$ on a vector space, its translation radical is the space of vectors $v$ for which $P(x+uv)=P(x)$ as a formal polynomial identity with a new scalar variable $u$. Its annihilator in the space of coordinate linear forms is determined by $P$ up to nonzero scalar. The determinant on the space of square matrices has zero translation radical. Indeed, put any nonzero matrix direction in the form $\operatorname{diag}(I_a,0)$ by invertible row and column operations, then translate the matrix $\operatorname{diag}(0,I_{n-a})$ by this direction at parameter $1$. Its determinant changes from zero to one. The change of row and column coordinates scales both polynomial determinants by the same unit.

The radical of $D_{i,j}$ is therefore the direct sum of the omitted column copy and all copies from the other groups. A linear variable substitution that preserves all anchor polynomials preserves each of these radicals. Intersecting the radical of $D_{i,j}$ with all the radicals indexed by each other group gives exactly the omitted copy $x_{i,j}$ as a vector subspace. It follows that a substitution preserving the anchors acts on each copy by a separate invertible matrix $P_{i,j}$.

For $n_i\ge2$, every pair of columns is present in at least one of the omitted-column determinants. Put equal vectors in those two columns and let the other columns vary freely. The original determinant vanishes. After the substitutions it vanishes for every choice of the other columns, which still vary freely. Hence the two transformed copies of a common nonzero vector are proportional. The quotient of the two matrices fixes every vector line, so it is scalar by checking a basis and its pairwise sums. Write the matrices in this mode as $\lambda_j P_i$. The determinant omitting copy $j$ then gives $\det(P_i)\prod_{k\ne j}\lambda_k=1$. Comparing omissions forces all $\lambda_j$ equal, hence the matrices are exactly equal and their common determinant is one. For $n_i=1$ the two anchors are the individual coordinate linear forms and force identity on both copies. Conversely a common determinant-one matrix on all copies of each mode preserves all anchors. This proves the exact stabilizer of the ordered anchor list over every field.

## A homogeneous core with separated coefficients

List all $D_{i,j}$ and the entry $L_A$ as $F_j^A(x)$ for $j=1,\ldots,J$. Use degree $3$ for the data entry even if $A=0$. Sort by their assigned homogeneous degrees $e_j$, breaking ties by a fixed order independent of the tensor data. Put
$$
D=\max_j e_j+J+3,\qquad b_j=j+1,\qquad c_j=D-e_j-b_j.
$$
The $b_j$ are strictly increasing, the $c_j$ strictly decreasing, and both are at least $2$. In two new variables $s,t$, put
$$
G_A(s,t,x)=s^D+t^D+s^{D-1}t+\sum_{j=1}^J s^{b_j}t^{c_j}F_j^A(x).
$$
This is homogeneous of degree $D$ and has a nonzero coefficient at $s^D$. We record its coefficient recovery when the $s$ and $t$ coordinate lines are respected. Suppose
$$
G_B(\lambda s,\mu t,Rx+us+vt)=\rho G_A(s,t,x)
$$
with $\lambda,\mu,\rho\in F^\times$ and $R$ invertible. The coefficients of $s^D$ and $s^{D-1}t$ give $\lambda^D=\rho$ and $\lambda^{D-1}\mu=\rho$. Each tagged term initially has $t$ exponent at least two, which the shears cannot decrease. Thus $\mu=\lambda$, and homogeneity lets us scale the whole substitution by $\lambda^{-1}$ to arrange $\lambda=\mu=\rho=1$. After this normalization the coefficient of $s^{b_j}t^{c_j}$ is $F_j^B(Rx)$ on the left and $F_j^A(x)$ on the right. No other tag pair is coordinatewise below it, and the scalar-only terms have at least one exponent below two. Any use of a shear in its own tag strictly increases at least one exponent. The anchor argument now gives the three determinant-one matrices and the data entry gives $A\cong_{\mathrm{SL}}B$.

## Recovering the coordinate lines from reduced factors

Add variables $z,w$ and set
$$
C_A(s,t,x,z,w)=G_A(s,t,x)+z w^{D-1}.
$$
This polynomial is absolutely irreducible. Viewed as a polynomial in $z$ over the polynomial ring in the other variables over any extension field, it is linear and primitive, since $G_A$ is nonzero and independent of $w$. Gauss's lemma and irreducibility over the fraction field then apply.

For each $\ell$ in the ordered list $s,t,z,w$, add two pairs of private variables $a_{\ell,j},d_{\ell,j}$ for $j=1,2$. Assign the eight distinct degrees $D+1,\ldots,D+8$ in this order and write the assigned degree as $f_{\ell,j}$. Define eight markers
$$
M_{\ell,j}=\ell^{f_{\ell,j}}+
a_{\ell,j}^{\,f_{\ell,j}-1}d_{\ell,j}.
$$
Every marker is absolutely irreducible by the same primitive linear argument in $d_{\ell,j}$. Its essential coordinate-linear-form space, the annihilator of its translation radical, is exactly $\langle\ell,a_{\ell,j},d_{\ell,j}\rangle$. To prove this, test a translation in its three variables by $(\alpha,\beta,\gamma)$ with formal parameter $v$. The coefficient of $d_{\ell,j}$ gives $(a_{\ell,j}+v\beta)^{f_{\ell,j}-1}=a_{\ell,j}^{f_{\ell,j}-1}$, forcing $\beta=0$ by comparing the highest power of $v$. The difference in the other terms then equals
$$
(\ell+v\alpha)^{f_{\ell,j}}-\ell^{f_{\ell,j}}+v\gamma a_{\ell,j}^{f_{\ell,j}-1}.
$$
Its highest $v$ coefficient forces $\alpha=0$, after which $\gamma=0$. This argument works even when the characteristic divides the assigned degree.

Use the squarefree homogeneous polynomial
$$
P_A=s\,C_A\prod_{\ell\in\{s,t,z,w\}}\prod_{j=1}^2 M_{\ell,j}.
$$
Its irreducible factors are absolutely irreducible of distinct degrees $1,D,D+1,\ldots,D+8$. The factor $s$ does not divide the core or any marker. In particular $P_A$ defines a geometrically reduced proper projective hypersurface. Its total degree is $9D+37$, linear in $\sum_i n_i$, and it has $20+\sum_i n_i(n_i+1)$ variables.

If an $F$-linear change gives projective equivalence of the reduced geometric zero sets of $P_A$ and $P_B$, it identifies their affine cones. The equality of their radical principal ideals over the algebraic closure gives
$$
P_B(S\cdot)=\sigma P_A
$$
for a nonzero scalar $\sigma$, by squarefreeness and unique factorization. Since the coefficients and $S$ are over $F$, this scalar belongs to $F$. Thus the unique degrees identify the two core factors and each named marker individually up to scalar. A change sending a marker to a scalar multiple preserves its translation radical and hence its essential coordinate-linear-form space. For each $\ell$, intersect its two essential three-spaces to recover the line spanned by $\ell$. Their total span contains exactly $s,t,z,w$ and all private variables. Therefore the substitution preserves each of the four special coordinate lines and the whole space of marker linear forms. On the quotient of the coordinate-linear-form space by the marker space it induces an invertible matrix $R$ on the classes of $x$.

Restrict the substituted core identity by setting $z,w$ and all private variables to zero. Both special variables $z,w$ remain zero after substitution because their lines are fixed. The other variables have the form $s'=\lambda s$, $t'=\mu t$, $x'=Rx+us+vt$, with $R$ invertible. The restriction is precisely the coefficient-recovery identity for $G_A,G_B$, with a nonzero core multiplier. It yields a special-linear tensor transporter. In the converse direction, let the special-linear maps act on all copies in their groups, and use the identity on $s,t,z,w$ and private variables. This maps the two data forms, preserves all anchors, and preserves all markers. It identifies the two reduced hypersurfaces. In particular the proof uses the distinct degrees of reduced components, with no multiplicity information.

## Explicit determinant pencils and inverse reconstruction

A polynomial-size algebraic branching program for $P_A$ can be constructed uniformly over $F$. Each anchor determinant has such a program by the signed clow-sequence dynamic program of Mahajan and Vinay. The other terms are monomials or sums of explicit trilinear monomials. Addition and multiplication of the displayed polynomial pieces are implemented by disjoint branching and serial concatenation. Include a branch for every trilinear coefficient, including zero, so the topology and program size depend only on the format. An algebraic branching program here is a directed acyclic graph with affine linear edge labels, a source and a sink. Its polynomial is the sum of the products of labels along source-to-sink paths. [Mahajan and Vinay, Determinant: Combinatorics, Algorithms, and Complexity](https://scholar.lib.vt.edu/ejournals/CJTCS/cjtcs/articles/1997/5/cj97-05.pdf)

Let $M$ be the strictly upper triangular adjacency matrix in topological order, whose entries sum the parallel edge labels. If $i,j$ index the source and sink, the entry $(i,j)$ of $(I-M)^{-1}=I+M+\cdots$ is the path polynomial $P_A$. Consequently the affine pencil
$$
K_A=\begin{pmatrix}I-M&e_j\\-e_i^{\mathsf T}&0\end{pmatrix}
$$
has determinant $P_A$ by the block determinant identity and $\det(I-M)=1$. Let $k$ be its size and $d=\deg P_A=9D+37$. Then $k\ge d$, since an affine $k$ by $k$ pencil has determinant degree at most $k$.

Replace each constant term of $K_A$ by that term times the already existing coordinate $s$, preserving all homogeneous linear terms. This constructs a homogeneous linear pencil in the same variables, without field divisions or extra variables. In the localization at $s$ the new matrix is $sK_A(1,t/s,x/s,z/s,w/s,\ldots)$. Its determinant is $s^{k-d}P_A$ by homogeneity, and the identity holds in the polynomial ring. Because $s$ is already one of the reduced factors, the geometric reduced zero set is unchanged. This gives the claimed forward reduction for homogeneous pencils even if their determinant has an extra power of $s$. All sizes and arithmetic construction costs are polynomial in the explicit tensor dimensions and coefficients.

For inverse reconstruction suppose a supplied homogeneous pencil has determinant
$$
\rho s^\kappa C_A \prod_{\ell,j}M_{\ell,j}
$$
for some $\rho\in F^\times$, $\kappa\ge1$, with the written mode sizes and coordinate order. Its matrix size is the degree of this nonzero determinant. Hence $\kappa$ is the size minus $9D+36$. Set $z=w=0$. For the $s$ and $t$ markers set both private variables to zero, so these markers become the written powers of $s,t$. For the $z,w$ markers set both private variables to $1$, so they become $1$. The substituted determinant is then
$$
\rho s^{A_s+\kappa}t^{A_t}G_A(s,t,x)
$$
where $A_s,A_t$ are the known sums of the two marker degrees associated with $s,t$. First set $x=0$ and extract the coefficient of $s^{A_s+\kappa+D}t^{A_t}$ to recover $\rho$. For each trilinear entry, set the three first vector copies to its indicated basis vectors and every other copy to zero, then extract $s^{A_s+\kappa+b_{j_*}}t^{A_t+c_{j_*}}$ for the assigned data tag $j_*$. Dividing by $\rho$ gives precisely that entry. Extract each bidegree by evaluating the determinant in the truncated polynomial ring that kills powers above the respective desired exponents. A division-free determinant algorithm operates in that ring, whose dimension over $F$ is polynomial. This works for any pencil satisfying the presentation promise, independent of its linear determinantal representation. It completes the reverse reduction. [Berkowitz, division-free determinant](https://cs.uwaterloo.ca/~r5olivei/courses/2021-winter-cs487/berkowitz-paper.pdf)

## Absolutely irreducible projective hypersurfaces from affine-linear pencils

There is also an exact equivalence for a family of absolutely irreducible hypersurfaces supplied by affine-linear determinant pencils whose determinant is homogeneous. This is a separate presentation from the homogeneous-entry pencils for reduced zero sets. It works even for abstract isomorphism of the projective schemes over the ground field.

Let $X$ now stand for all old coordinates of $P_A$, and put $d=\deg P_A$. Add variables $y,\xi$ and use
$$
\widehat P_A(X,y,\xi)=P_A(X)+y\xi^{d-1}.
$$
It is linear and primitive in $y$ over the polynomial ring in $X,\xi$ even after any field extension. The leading coefficient $\xi^{d-1}$ and constant term $P_A(X)$ are coprime because $P_A$ is nonzero and independent of $\xi$. Thus it is absolutely irreducible and homogeneous of degree $d$.

Its geometric singular locus is contained in $\xi=0$, since its partial derivative with respect to $y$ is $\xi^{d-1}$ in every characteristic. It spans that hyperplane. Every old coordinate axis lies in the zero sets of at least six of the eight old marker factors: each special coordinate occurs in two markers, each private coordinate occurs in one, and each data coordinate occurs in none. A marker omitting the only nonzero coordinate vanishes by positive homogeneity. A point lying on two distinct factors of $P_A$ has every first partial derivative of $P_A$ equal to zero by the product rule. At $\xi=0$ the first derivatives of $y\xi^{d-1}$ also all vanish, since $d\ge3$. Thus all old coordinate axes and the $y$ axis are singular. The latter uses $P_A(0)=0$ and the vanishing of its positive-degree derivatives at zero. These axes are rational over the ground field, and the span of the geometric singular points is exactly the stated hyperplane.

The translation radical of $P_A$ on its old variables is zero. Indeed, suppose translation by a direction with an indeterminate parameter leaves $P_A$ invariant. Work over the rational function field in that parameter. The absolutely irreducible factors stay irreducible, and the translation preserves their distinct degrees, so each factor goes to a scalar multiple of itself. Its leading homogeneous part in $X$ is unchanged by translation, forcing that scalar to be one. The marker radicals then force zero components in $s,t,z,w$ and all private directions, by their essential coordinate spaces. The core translation identity is therefore a translation of the $x$ variables alone. Its individual tag coefficients force translation invariance of every determinant anchor. Each column copy appears in at least one anchor and the determinant on those selected columns has zero translation radical. The direction is zero also in every $x$ copy, as claimed.

A projective-linear transformation over $F$ between the irreducible hypersurfaces therefore preserves the hyperplane $\xi=0$. The pullback of one defining form equals a nonzero scalar multiple of the other, by irreducibility and the same affine-cone argument as before. On the preserved hyperplane the restriction is $P_A(X)$, with translation radical precisely the $y$ direction by the preceding paragraph. The transformation of the hyperplanes preserves this radical and descends to an invertible $F$-linear transformation on the old quotient coordinates carrying $P_A$ to a scalar multiple of $P_B$. This is the previous reduced hypersurface equivalence, hence a special-linear tensor equivalence. Conversely if a linear change on the old coordinates gives $P_B(SX)=\rho P_A(X)$, extend it by $y\mapsto \rho y$ and $\xi\mapsto\xi$. This gives $\widehat P_B\mapsto\rho\widehat P_A$.

In fact the conclusion holds for abstract projective $F$-isomorphisms of these hypersurfaces. Their dimension is at least three. The Grothendieck–Lefschetz theorem for projective complete intersections makes the Picard group free on the class of $\mathcal O(1)$, without a smoothness assumption and over the base field. An isomorphism pulls back the ample generator to the ample generator. For a degree-$d$ hypersurface with $d>1$, restriction identifies ambient linear forms with its global sections of $\mathcal O(1)$, by the hypersurface exact sequence and the vanishing of the first cohomology of line bundles on projective space of dimension at least two. The complete linear system therefore extends such an isomorphism to a projective-linear map over $F$. In particular passing to abstract isomorphism introduces no ground-field ambiguity. [Grothendieck and Raynaud, SGA 2, Exposé XII, Corollary 3.7](https://arxiv.org/abs/math/0511279), [Exposé XII English translation](https://jcreinhold.github.io/sga/ii/12-projective-algebraic-schemes.html)

The branching program for $P_A$ gains one extra monomial branch for $y\xi^{d-1}$. The same block determinant construction with $I-M$ therefore gives an affine-linear pencil with determinant exactly $\widehat P_A$, without entry homogenization. Its size remains polynomial and depends only on the tensor format. Conversely, for any affine-linear pencil promised to have determinant a nonzero scalar times $\widehat P_A$ in the designated coordinates, set $y=\xi=0$. The previous coefficient extraction with $\kappa=1$ reconstructs the underlying tensor. Both reductions therefore apply to the family even when one asks for abstract isomorphism of the projective schemes. No irreducibility assertion is made for a homogeneous-entry pencil obtained by multiplying the determinant by an extra coordinate factor.

## Scope and consequences in the collapse hypothesis

The hypothesis that arbitrary reduced determinant-hypersurface equivalence lies in ordinary TI is stronger than needed by this proof. Even restricted to pairs of proper reduced determinant hypersurfaces, the arbitrary problem contains commutative symbolic determinant identity testing. To see this, take a symbolic determinant $g(x)$ of a homogeneous linear pencil, use one tagged entry of its assigned degree, and construct the same irreducible cores and marker factors for $g$ and for zero. Keep the data branch in both programs so the matrix sizes agree. The scalar terms and irreducibility argument ensure both outputs are proper hypersurfaces. The factor and coefficient comparisons above give equivalence exactly when $g(Rx)=0$ for some invertible $R$, equivalently when $g=0$. This containment does not prove that the $\mathsf{TI}=\mathsf{TI}_{\mathrm{SL}}$ hypothesis puts unrestricted reduced determinant-hypersurface equivalence or symbolic determinant identity testing in ordinary TI. [Ivanyos, Mittal and Qiao, Symbolic Determinant Identity Testing and Non-Commutative Ranks of Matrix Lie Algebras](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2022.87)

The use of geometric zero sets with an $F$-rational transporter is essential to the field statement. For example take $F=\mathbf F_3$ and the matrix pencil $A(x)=\operatorname{diag}(x_1,x_2I_2,(x_1+x_2)I_3)$. Put $f_0=\operatorname{diag}(-1,1)$ and $h_0=\operatorname{diag}(-1,1,1,1,1,1)$, and set $B(y)=h_0A(f_0^{-1}y)$. There is an ordinary transporter $(f_0,I,h_0)$ in the matrix-map convention $B(fx)g=hA(x)$. Distinct factor multiplicities $1,2,3$ in $\det A$ force the label of an ordinary automorphism of $A$ to fix the two coordinate forms and their sum projectively, hence to be $\lambda I_2$. Its row and column determinant ratio must be $\lambda^6$. Composing with the given transporter, a determinant-one label requires $\lambda^2=-1$. If that equation holds, the automorphism $(\lambda I_2,I,\lambda I_6)$ repairs both determinants because $\lambda^6=-1$. This is possible over $\mathbf F_9$ and impossible over $\mathbf F_3$. The constructed reduced hypersurfaces have the corresponding projective equivalence distinction. Equality of finite sets of $F$-rational points alone is a different comparison and is not used here.

This is a paper proof. The exact equivalences concern the stated presentation families. Unrestricted determinantal hypersurface equivalence remains a separate algorithmic target.
