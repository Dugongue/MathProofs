# Tangent directions and smoothness of layered branching-program spaces

## GP-0542. Generic tangent vectors preserve the depth

Fix a layered homogeneous commutative ABP format over an algebraically closed field of characteristic zero. Each layer is a rectangular matrix whose entries belong to specified finite-dimensional linear spaces of homogeneous edge polynomials, for example linear forms in one prescribed variable block. The output is the scalar product of the layer matrices. At every point in a dense open subset of the Zariski closure of the outputs, **every** tangent vector has an ABP in the same layer format of at most twice the original width and exactly the original depth. If the original format is sparse, the construction copies its edges and adds parallel derivative edges, giving constant-factor size overhead. The assertion also holds after a fixed degree-preserving linear projection, in the projected model, with the projection applied to the tangent ABP.

Indeed let $\Phi$ be the polynomial output map from the affine space of layer parameters to the coefficient space, followed by the projection if present, and let $X$ be the closure of its image. The map is dominant onto $X$. In characteristic zero generic smoothness gives a dense open subset of the parameter space where $X$ is smooth at the image and the differential onto its tangent space is surjective. The image of that open set is dense constructible and contains a nonempty open subset of $X$. At one such parameter point write the layer matrices as $M_1,\ldots,M_d$. A parameter tangent is a list of matrices $D_i$ in the same layer spaces. Its unprojected differential is
$$
\sum_{i=1}^{d}M_1\cdots M_{i-1}D_i M_{i+1}\cdots M_d .
$$
Use at layer $i$ the block matrix
$$
\begin{pmatrix}M_i&D_i\\0&M_i\end{pmatrix}.
$$
The upper-right corner of the product is the displayed differential. Use the appropriate start and finish state, discarding unused endpoint copies. There are two copies of every vertex and at most three copies of every allowed edge, including a derivative copy in the top-right block. Every path still traverses exactly one entry per layer, so prescribed layer degree and depth are preserved. The projected differential is the corresponding linear projection applied to this ABP output. Conversely at any such parameter preimage these directions fill the tangent space by surjectivity. Thus this determines which generic tangent vectors lift to the depth-preserving model.

More generally, if the layer parameters are given as truncated series through order $h$, a block upper-triangular Toeplitz construction with $h+1$ copies of each state extracts the $h$th output coefficient. The block from order $a$ to $b\ge a$ is the layer coefficient of order $b-a$. Multiplying the matrices and selecting the block from $0$ to $h$ is precisely the convolution rule for Taylor coefficients. Its depth is unchanged and size overhead at most $(h+1)^2$. This is a finite-jet statement and allows an arbitrary specified jet order.

[ABP varieties and debordering context](https://arxiv.org/abs/2003.04834)

## GP-0543. Complete smooth-locus criterion for fixed-order set-multilinear ABPs

Let the physical vector spaces be $V_1,\ldots,V_d$ with $\dim V_i=n_i$, and prescribe positive width bounds $r_1,\ldots,r_{d-1}$. Set $r_0=r_d=1$. With a fixed variable-block order the coefficient tensors of set-multilinear ABPs of these widths are exactly the tensor-train variety $X$ of tensors whose prefix flattening ranks are at most $r_i$. In particular this model is already closed. The following criterion includes width constraints that happen to be redundant.

For a tensor $T\in X$, retain the cuts $i$ at which its flattening rank equals $r_i$. Include $0,d$ as endpoints. Let $l<h$ be consecutive retained indices. For every cut $l<i<h$ define
$$
B_i=\min\left(r_l\prod_{j=l+1}^{i}n_j,\quad r_h\prod_{j=i+1}^{h}n_j\right).
$$
Then $T$ is smooth in $X$ **if and only if $r_i\ge B_i$ at every unretained cut**. The test uses just the minimal tensor-train widths of $T$ and the prescribed caps. It covers arbitrary length, all physical dimensions, and repeated or excessive caps. It does not decide smoothness of unrestricted commutative ABP varieties with no block order.

Here is a proof. Given a tensor, its exact prefix support $U_i$ is the image of the contraction onto the first $i$ factors. These satisfy $U_i\subset U_{i-1}\otimes V_i$. Choose bases of the support spaces and use these inclusions and the final tensor coefficients as cores. This yields the train representation with widths equal to the prefix ranks, and padding gives every larger representation. The reverse bound follows by cutting the product at a bond. It follows that $X$ is the closed rank-condition locus and is irreducible as a polynomial image of the core space.

Let $Y$ be the analogous variety that enforces only the retained caps, viewing the corresponding intervals as supermodes. Its full-rank locus is smooth. One explanation is the tower of Grassmannians that first chooses $U_i$ of the stated dimension inside the preceding support tensored with the next supermode, and then chooses the last tensor in the resulting vector bundle. On the full-rank open set these support spaces are uniquely recovered from the tensor and their assignment is regular on the usual pivot charts. Thus the vector bundle construction is an isomorphism on that open locus. In particular $T$ is a smooth point of $Y$.

For a missing cut in one supermode, its full flattening is the flattening of that core multiplied on the two sides by the left and right interface injections. On the full-rank locus both interface maps are injective, because the retained widths are minimal there. Its rank is therefore the core flattening rank. For every tensor in $Y$ the rank at that cut is bounded by $B_i$ by the same factorization, without requiring injectivity. Also, the rank $B_i$ is attained somewhere in $Y$. Hold the other cores of the full-rank tensor $T$ fixed. The interface injections for this core do not depend on its own coefficients. Choose core coefficients giving a full-rank matrix at the missing cut. The resulting flattening attains $B_i$. It follows that $X=Y$ precisely when every missing cap is at least $B_i$. That implication already proves smoothness in the redundant case.

It remains to show singularity in the other case. At a full-width representation of $T$ for the retained-cut train, the differential of the collapsed core parametrization surjects onto $T_TY$. To see this without a genericity assumption, locally choose bases of the canonical support subspaces using fixed nonzero minors. Expressing the inclusions and the final tensor in those bases gives a regular local right inverse, and its derivative splits the output differential. For a different choice of bases, make a fixed invertible gauge change at each retained cut.

For each collapsed core, its variations are spanned by pure tensors across all its physical factors and its two bond spaces. Vary only this core along such a pure tensor direction. At a missing cut inside the selected core, the matrix of the addition has rank at most one. The original rank was strictly below its cap, so the whole line of variations stays within the cap. At a missing cut inside another core, that other core is unchanged. Its flattening had the actual rank of $T$ by the interface injection argument. Changing boundary contractions can only decrease its rank from this bound. Retained caps always hold in the collapsed format, so every one of these variation lines lies in $X$. Their velocities span the image of the differential, hence $T_T X=T_T Y$.

If any missing cap is strictly less than $B_i$, then $X$ is a proper closed subset of the irreducible $Y$ and has smaller dimension. Its Zariski tangent at $T$ has dimension $\dim Y$, so $T$ is singular. This proves the criterion, including the possibility of multiple simultaneous drops. The proof uses the variety tangent of the reduced locus and requires no assertion that an intersection of determinantal ideals is already radical.

[Tensor-train tangent-cone context](https://arxiv.org/abs/1705.10152)
