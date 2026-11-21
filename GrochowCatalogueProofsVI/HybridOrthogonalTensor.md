# The hybrid orthogonal and general-linear tensor problem

## GP-0177

Consider rational three-tensors, with the positive-definite orthogonal action in the first mode and general-linear actions in the other two. Fix the acting field $F$ to be either $\mathbb Q$ or $\mathbb R$. Bipartite graph isomorphism with the sides labeled reduces to this problem, and this problem reduces by a polynomial-bit many-one map to ordinary three-tensor isomorphism over the same acting field $F$. Both reductions output rational coefficient arrays. A transporter in the ordinary instance yields a hybrid transporter over its own acting field. Rational and real hybrid witnesses can give different answers on the same rational data. These results give a complexity comparison in both settings. [Classical-group tensor actions and the remarks on mixed models](https://arxiv.org/html/2306.03135v2#S5)

### A marked bilinear reduction

Write the input as a bilinear map $f:X\times Y\longrightarrow Z$ in coordinate spaces. Three-tensor isomorphism uses inverse transpose in the two input modes in this convention. This distinction is harmless for the first orthogonal mode and does not change the allowed group in the second.

Use the following named spaces, preserving each separately in each mode. On the left take $X,Y_0,F a$ with $Y_0$ a coordinate copy of $Z$. On the right take $Y,X',F b$ with $X'$ a coordinate copy of $X$. In the output take $Z,X_0,F c$ with $X_0$ another copy of $X$. Use these blocks of a bilinear map:
$$
\begin{array}{rcl}
X\times Y&\longrightarrow Z & f,\\
Y_0\times F b&\longrightarrow Z & (z,\eta b)\mapsto\eta z,\\
X\times F b&\longrightarrow X_0 & (x,\eta b)\mapsto\eta x,\\
F a\times X'&\longrightarrow X_0 & (\xi a,x')\mapsto\xi x',\\
F a\times F b&\longrightarrow F c & (\xi a,\eta b)\mapsto\xi\eta c,\\
X\times X'&\longrightarrow F c & (x,x')\mapsto(x^{\mathsf T}x')c.
\end{array}
$$
The unlisted blocks vanish. Every output block is the image of a designated pairing, including when $f$ fails to span $Z$.

Let a block transporter have scalar actions $\lambda$ on $a$ and $\mu$ on $b$, and let the maps on $X,X'$ be $A,A'$. The two bridges to $X_0$ give $\mu A=\lambda A'$. The first $c$ block gives scalar $\lambda\mu$ on its output, so the second $c$ block gives $A^{\mathsf T}A'=\lambda\mu I$. Combining the identities gives $A^{\mathsf T}A=\lambda^2 I$. Thus $A/\lambda$ is genuinely orthogonal over $F$. In the transported data block, divide the map on $Z$ by $\lambda$ to obtain the exact hybrid transporter. Conversely, any hybrid transporter extends to the marked map with $\lambda=\mu=1$, identical actions on the $X$ copies, and the output action copied on $Y_0$. This proof forces a square algebraically, without deciding rationality of a square root.

### Removing the marks over either acting field

For completeness, the mark removal uses ranks of contractions, and therefore works over arbitrary fields. For a block map $B:L\times R\to C$ of this kind, add two guard lines on the right for each named left block, and two on the left for each named right block. Each right guard $j$ pairs with its designated left block and a private left space of dimension $M2^j$, by sending them identically into two private output sectors when the guard coordinate is one. Use an independent analogous construction for the left guards. Zero blocks may be retained with their zero rank. All other new pairings are zero. Choose $M$ greater than the sum of original mode dimensions and the number of guards.

On each side the subspace of original data and private spaces has contraction rank less than $M$. Its contraction uses only the original output or the other side's guard lines. A vector with any nonzero guard component has rank at least $M$ by pairing its component with the corresponding independent private space. Hence those subspaces are intrinsic, and their mutual pairing spans the original output. Quotient the output by it. The contraction of a right guard combination against the unguarded left subspace now has rank
$$
M\sum_{j:t_j\ne0}2^j+\epsilon,\qquad 0\le\epsilon\le\dim L<M.
$$
This holds because the private-space images are direct and the only other images come from $L$. The quotient guard lines are therefore intrinsic individually, by the binary expansion of the integer part after division by $M$. The same argument recovers the opposite lines.

On either unguarded subspace, the private space of one guard is the intersection of all other opposite guards' kernels. The second guard on its paired data block ensures that no data block survives this intersection. Quotient by all private spaces, then recover each data block by intersecting the guard kernels for all other blocks. The restricted original pairing recovers every output block by the given designated pairings. Thus an ordinary transporter induces precisely a marked transporter and is effectively restricted and projected in the known coordinates. Conversely a marked transporter extends by the same maps on paired copies and the identity on private spaces and guards. There are constantly many guards here, so the resulting ordinary tensor has polynomial dense size. [Earlier guard method over finite rings](https://github.com/Dugongue/MathProofs/blob/a32630798eebd129ef621986ca4e0b8ce5edfcf3/GrochowCatalogueProofsV/PresentedModuleTensorReduction.md)

### Bipartite graph isomorphism as a lower bound

For a bipartite graph $G\subseteq[m]\times[n]$, let $\mathcal S_G$ be the coordinate matrix space spanned by its edge matrices $E_{ij}$, each having one nonzero entry equal to one. Use these edge matrices as an orthonormal labeled slice basis for the first tensor mode, with the row and column axes in the two general-linear modes. Unequal side sizes or edge counts are rejected before construction by outputting a fixed negative instance. A side-preserving graph isomorphism acts by permutations on the row and column spaces and permutes the edge basis. Its slice action is orthogonal over both $\mathbb Q$ and $\mathbb R$.

Conversely a hybrid transporter implies left-right equivalence of the coordinate matrix spaces. Work over $\mathbb C$, to which the transporter extends from either acting field. Let $D$ be the product of the full row and column diagonal tori, and let $H$ be the algebraic stabilizer of $\mathcal S_{G'}$ in $\mathrm{GL}_m\times\mathrm{GL}_n$. The group $H$ contains $D$, because every edge matrix is a diagonal weight vector. If $g\mathcal S_G=\mathcal S_{G'}$, then $gDg^{-1}\subseteq H$ as well. Both tori are connected and lie in $H^\circ$. They are maximal because they are already maximal in the ambient product. Conjugacy of maximal tori in the connected algebraic group $H^\circ$ gives $h\in H^\circ$ with $hgD(hg)^{-1}=D$. The normalizer of $D$ consists of two monomial matrices. Their action on coordinate matrix lines is exactly a row and column permutation. Hence $G$ and $G'$ are side-preserving isomorphic. Bipartite graph isomorphism with sides labeled is GI-complete by passing to the vertex-edge incidence graph of an ordinary graph. The constructed arrays are polynomial in the graph size.

### Rational and real witnesses differ

In format $(2,1,1)$, take first-mode vectors $(1,0)$ and $(1,1)$. Real orthogonal change of coordinates and a nonzero scalar from either one-dimensional general-linear mode suffice to match them. A rational matching would require a rational scalar whose square is $2$, by taking squared norms. No such scalar exists. The common-field reduction above respects both answers.
