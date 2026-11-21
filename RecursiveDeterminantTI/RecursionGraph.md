# Determinants of unordered signed graph modules

Over $F=\mathbb F_3$, the determinant test for a recognizable class of scalar-residue commutative cube-zero algebras reduces to a single ordinary three-tensor isomorphism instance. This class has scalar centroids on the multiplication and relation sides, and can have quadratic label and relation dimensions. It permits arbitrarily many repeated color signatures, with an arbitrary number of indistinguishable modules. The construction combines positive linear switches with an exact treatment of the parity of the module permutation.

## 1. The graph and its independent modules

Use the recoverable multicolored presentation of the graded bimap of a based algebra $A$, with $U=J/J^2$, $W=J^2$, and $L=\beta^*(W^*)\subseteq\operatorname{Sym}^2 U^*$. It has
\[
 U^*=X\oplus Y,qquad
 L=L_0\oplus\bigoplus_{c}FQ_c
\]
in frames $(\ell_i)$ of the two parts of even dimensions $a,b\ge4$. The space $L_0$ is the sum of all diagonal square lines and the full cross space $X\otimes Y$, embedded symmetrically. Each $Q_c$ is supported on internal off-diagonal edges, with nonzero weights $w_{ij}\in\{1,-1\}$. Distinct colors have disjoint supports and every color occurs in both parts. Use the three minor and star witness conditions of the multicolored presentation theorem. [Multicolored presentation and witness conditions](MulticolorDeterminantRecords.md). These are the two-edge minor condition for every pair of colors, the two one-edge witness conditions at every vertex and color, and the bound of $d-3$ on the number of incident colors in a part of dimension $d$. No distinct-signature or canonical edge-set hypothesis is imposed here.

For clarity, the recovery under these witness conditions does not use color signatures. The linearized rank-one minors force all quadratic coordinates involving a color variable to be zero, by the two-edge and one-edge witnesses. The support of their symmetric kernel is exactly $L_0$ since the rank-one elements of $L_0$ span it. The pair adjoint of $L_0^\perp$ gives the two part projectors, and the pure diagonal pieces of $L_0$ give the coordinate lines. Grouping the internal coefficient functionals on $L/L_0$ into projective row lines recovers the quotient colors. The same minor and star theorem shows that the bimap and its dual relation bimap have scalar centroids and zero common radical. Indeed the original pair adjoint is scalar from the complete cross support. In the relation space the stars at every vertex have at least two independent choices, forcing the paired adjoints to be diagonal and scalar separately on each part. The shared color equations then equate the two scalars for a centroid.

A transporter must carry the parts to the parts, the coordinate lines to coordinate lines, and the colors to colors. For a chosen alignment of the two parts, write its map on $U^*$ as
\[
 \ell_i\longmapsto s_i\ell'_{\pi(i)}, \qquad s_i\in F^\times
\]
and its map on quotient color lines as $q_c\mapsto\sigma_c q'_{\rho(c)}$. The local edge condition is
\[
 w_{ij}s_i s_j=\sigma_c w'_{\pi(i)\pi(j)}
 \qquad(ij\in E_c).
 \tag{1}
\]
Conversely signed permutations preserving the graphs and colors and satisfying (1) give exactly graded algebra transporters, since their action respects $L_0$ and the span of the $Q_c$. They lift to algebra transporters by choosing complements of $J^2$ in $J$. The unipotent shears in such lifts have determinant one.

Make an incidence graph whose nodes are vertices and colors, joining a vertex to the colors of its incident internal edges. Define modules as the connected components of this incidence graph. Every internal edge is entirely in one module, and every color and all its edges stay in one module. Once the part alignment is fixed, arbitrary independent local transporters and any bijection of the modules extend to an original transporter exactly when each local map satisfies (1). Indeed the vertex and color maps assemble by direct sum. There are no cross-module internal edges, and the universal cross space belongs to $L_0$ and imposes no additional condition on the assembled maps. This is exact independence of modules even though the original algebra is not a direct product.

Choose arbitrary orders of modules, color lines within each module, and coordinate lines. Use the diagonal, cross and ordered color bases of $L$ and the resulting dual basis of $W$, together with lifts of the dual coordinate basis of $U$ and the unit, as the adapted basis of $A$. Let $S_A$ be its column matrix in the raw basis. For a module transporter $f$ put
\[
 \chi(f)=\det(f\text{ on its color space})\prod_{i\text{ in its vertex set}}s_i.
 \tag{2}
\]
These signs multiply under composition. A global transporter matching modules by $\lambda$ has raw determinant
\[
 \det_{\rm raw} f
 =
 \frac{\det S_{A'}}{\det S_A}\,
 \tau^\delta\,
 (-1)^{I(\lambda)}\prod_i \chi(f_i).
 \tag{3}
\]
Here $\tau=-1$ only when equal-sized parts are exchanged, $\delta=a(a-1)/2\bmod 2$ in the equal-sized case and zero otherwise. The exponent $I(\lambda)$ counts inversions of the induced matching of the modules of odd color dimension, in their chosen orders. Indeed the sign of the full coordinate permutation cancels its copy on the diagonal basis of $L_0$, and its coordinate scalars remain in (2). The cross determinant powers are both even, except for the flip permutation of pairs when the parts are exchanged, of sign $\tau^\delta$. Permuting two color blocks of dimensions $r,s$ gives the factor $(-1)^{rs}$, leaving just the inversions among odd blocks. The use of inverse dual maps on $U^*$ and $W^*$ does not change signs over $F$.

## 2. Local signed comparisons with large vertex sets

Let $L_{\mathrm{in}}\ge2$ be the dense input bit length and fix a constant $C_0$. The following two local compiler tests suffice. Each incidence module can be recognized by either test.

1. Its number of vertices and colors are both at most $C_0\log_2 L_{\mathrm{in}}$.
2. Its number of colors is at most $C_0\log_2 L_{\mathrm{in}}$, with no bound on its number of vertices, and its edge weights can be normalized to $+1$ by switching signs on vertices and rescaling the color generators.

Normalization is tested by binary linear equations. Write $w_{ij}=(-1)^{b_{ij}}$, then solve $b_{ij}=u_i+u_j+v_c\pmod2$ on the edges of color $c$. Taking $(-1)^{u_i}\ell_i$ and $(-1)^{v_c}q_c$ as frames makes every edge weight positive. This condition is invariant under all transporters satisfying (1). Use the resulting frames when computing $S_A$. Different successful normalizations just choose different adapted bases.

Here is an ordinary local tensor-system comparison. Keep the coordinate algebras of vertices, edges, and colors, with basis their primitive idempotents and with coordinatewise multiplication. Attach the signed vertex, edge and color spaces by their respective projection actions. Keep the vertex-to-part mark, with the target part names supplied by the chosen alignment. The linear maps from the edge coordinate algebra to the vertex and color coordinate algebras send its primitive idempotents to the sum of their endpoints and to their color, respectively. This forces the induced permutations to respect the incidence graph. Link the signed color space to the signed edge space by sending each color basis element to the sum of its edges in their signed edge bases. This forces every map on the edge line to have the same scalar as its color. Use the symmetric bilinear map on signed vertex lines that sends the basis pair of edge $ij$ to $w_{ij}$ times the signed edge basis and all other pairs to zero. Its preservation gives (1), since all nonzero scalars square to one. Conversely these graph permutations and signs extend to the records. Their number is fixed and their sizes polynomial. A zero-edge isolated vertex module can either be compared directly, or omitted by the free correction described next.

If a connected component of the vertex-only internal graph has odd size, there is an automorphism of sign $-1$ on that incidence module. Negate all its signed vertex vectors and fix all other vertices and every color. Edge products are unchanged, and (2) changes sign. Thus both signed local queries are just the ordinary local query whenever this condition holds on the target. In the remaining case each such vertex component has even size.

For test 1 one can compute (2) by the product of the determinant on the signed vertex space, the determinant on the vertex coordinate algebra, and the determinant on the color space. The first two determinants multiply to the product of the vertex scalars. Attach full exterior algebras in these three dimensions, each using its multiplication and degree-one inclusion as single records. Their top lines give the exact sign on every transporter, with a polynomial basis size due to the logarithmic dimension bound.

For test 2 use the normalized weights. In each component of the vertex-only graph choose an edge set whose mod-two boundary is all its vertices. Such a set exists because the component is even. For an elementary proof take a spanning tree and successively select the leaf edge when needed to meet the remaining demand at that leaf. The final root demand is zero because the total demand is even. Write $P$ for the union of the resulting edges on the source module. This is just a choice of computation, and need not be respected by the transporter. Under normalized weights, multiplying (1) over these source edges gives
\[
 \prod_i s_i=\prod_c\sigma_c^{|P\cap E_c|}.
 \tag{4}
\]
There is no target weight ratio because every edge weight is one in both systems.

Let $C_P$ be the subset of source colors of odd incidence in (4). On the color space $Q$ attach its exterior algebra and the commutative algebra of squarefree monomials
\[
 F[z_c:c\in C]/(z_c^2:c\in C),
 \qquad Q=\operatorname{span}_F\{z_c:c\in C\}\text{ in degree one}.
\]
The linked monomial map of the color space extends uniquely to this second algebra, sending a product of distinct color generators to its transported product times their scalar product. On the tensor product of the top exterior line with this squarefree algebra, the vector consisting of the volume element tensored with $\prod_{c\in C_P}z_c$ acquires exactly the multiplier in (2). The tensor product is attached by its bilinear map and all transported factors are linked. Branch over the at most $2^{\dim Q}$ target subsets for the image of $C_P$, and in a branch mark the corresponding target tensor product vector times the desired sign. This forces exactly that sign and the stated image subset. Every signed transporter satisfies a branch. Each algebra has dimension $2^{\dim Q}$. The branches and the individual tensor-system compilations are polynomial under the logarithmic rank bound. They can be combined by one positive OR over ordinary comparisons. There is no enumeration of color permutations.

These constructions give uniform ordinary TI instances for local comparison at either sign and with the part names fixed, as well as ordinary local instances with the sign unmarked. All local systems have a constant number of records of order at most three. A positive OR of polynomially many ordinary instances is a special case of the positive linear switch used below. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

## 3. Assembling unordered modules without a branching bound

The following argument works for any independent module decomposition with local sign tests as above and permutation weight given by each module's parity. Fix a candidate global part alignment, of which there are at most two. Use one ordinary guard for the full un-oriented comparison with that alignment. It is expressible by the full version of the local graph records. We keep this guard in the final test.

There are two positive ways for the target to have a sign-changing automorphism preserving the parts.

- Some module has a local negative automorphism, tested by the signed module query against itself.
- Two odd-weight target modules are ordinarily isomorphic, tested by their unmarked local query. Swap them by an isomorphism and its inverse. Their two local signs multiply to one, but the permutation of their odd-dimensional blocks is odd.

If any such query is YES, both signs occur whenever the guard is true. In the remaining case, every target module has only positive local automorphisms and the odd target module types are pairwise distinct. We do not need to compute the answers to these free-correction queries. They only form an ordinary positive disjunction.

Write $Q_{ij,s}$ for the ordinary instance for source module $i$ to target module $j$ with local sign $(-1)^s$, and $Q_{ij}$ for the ordinary unmarked instance. Make binary variables $x_{ij,s}$, enabled by $Q_{ij,s}$. Require each source row and target column to have sum one over $\mathbb F_2$. These are parity equations and do not force a literal bijection. For the odd module permutation use the following extra variables. For each odd source pair $i<k$ and each pair of distinct odd target indices $j,l$, enable $y_{ik;jl}$ by the ordinary conjunction $Q_{ij}\wedge Q_{kl}$. Require the sum of these variables over $j,l$ to be one for each $i,k$. Impose the final linear equation
\[
 \sum_{ij,s}s\,x_{ij,s}
  +\sum_{i<k,\ j>l} y_{ik;jl}
  = b ,
 \tag{5}
\]
where $b$ is the prescribed sign bit after the known frame and part-flip factors in (3).

Completeness follows by selecting a genuine module matching and the corresponding inversion pairs. For soundness assume that the guard is true and neither free correction applies. Each odd source type has a unique compatible target. Thus each odd pair row has exactly one enabled inversion variable and its required sum forces it to be one. For the local sign contribution, fix any isomorphism type common to the two module lists. Without computing them, choose isomorphisms from its source modules to a representative and from the representative to its target modules. For available $(i,j)$ the local sign bit then has the form $u_i+v_j$ from these two maps. It is independent of the chosen transporter between $i,j$, because target automorphisms all have positive sign. By the odd row and column sums, the contribution from this type in the first term of (5) is exactly $\sum_i u_i+\sum_j v_j$. This is the same value as for a literal bijection in that type. The guard ensures the multiplicities do match, so a literal matching exists. Every such actual matching has the computed sign and hence satisfies the prescription if (5) holds. This argument is valid even when even-weight modules have arbitrarily many possible images.

By the linear-switch construction, a system of binary linear equations in variables enabled by explicit ordinary TI comparisons is itself one ordinary comparison. This uses the two-element shift structure over $F$ and a centrally indecomposable algebra for each query object. The coefficient field of the linear constraints is $\mathbb F_2$, while the compiled tensor field is $\mathbb F_3$. The ordinary guard, the free-correction disjunction and the system (5) are combined as guard AND (free OR linear), again by positive linear switches. For example an OR enforces sum one among its enabled binary variables, and an AND forces each enabled variable to be one. Take an OR over the at most two alignments. The number of inversion candidates is polynomial in the number of modules. The compilation layers have constant depth, so the final size is polynomial even if the individual steps have polynomial rather than linear size overhead. This does not require recursive substitution of already compiled large instances. [Linear-switch compiler](LinearSwitchCompiler.md)

## 4. Repeated modules with a genuine sign constraint

Use $k$ copies of the following two-color module, with fresh colors for each copy. In the first part take a path on six vertices, with edge colors alternating red and blue starting at red. In the second part take a path on ten vertices, alternating starting at blue, with the same two colors. All weights are positive. These paths are connected, and both colors occur in both parts and hence give a single incidence module. The local color counts are $(3,4)$ and $(2,5)$ in the two parts, so each local automorphism fixes both colors. The unique all-odd boundary set on an even path is its perfect matching. It has three red edges in the first part and five blue edges in the second, so (4) makes each local sign positive. Add one more module with one color, using two disjoint matching edges in the first part and three in the second. It also has positive local sign, and its odd weight is unique.

All side dimensions are even and unequal. The minor witnesses hold. Within each part every color is a matching of at least two edges. Two colors from different modules give disjoint edges and no cross alternatives. Within a module, equal-color edges are disjoint and distinct colors have disjoint choices with a missing alternative, as one checks on the two alternating paths. For the one-edge witnesses at a vertex, a color has at least four endpoints whereas the vertex and its neighbors have size at most three. Thus some endpoint is a nonneighbor and an edge avoids the vertex. The incident-color count is at most two. Therefore the original and relation centroids are scalar, and the dimensions of $W$ and its relation space are quadratic in the number of generators. The total color dimension is $2k+1$, giving even total algebra dimension.

The $k$ path modules can be permuted arbitrarily. All of those permutations are neutral because each module has two colors. All other local automorphisms are also sign-neutral, so every raw algebra automorphism has determinant one. Reflecting one target output basis vector gives ordinary isomorphism but only negative transporters. With $k\ge2$ the global color signatures repeat and the effective module permutation group has even order, while the present compiler still applies. The bounded local color ranks require no bound on the number of equivalent modules. Replacing the two paths by even paths of arbitrarily growing lengths with odd matching counts in the corresponding starting colors also gives modules with arbitrarily many vertices and the same two-color local compiler.

This is a written sufficient theorem for the stated graph modules. It permits arbitrary branching among independent components, and it does not supply a decomposition or local compiler for an arbitrary connected hard block of large color dimension. The unrestricted ternary reduction remains open. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
