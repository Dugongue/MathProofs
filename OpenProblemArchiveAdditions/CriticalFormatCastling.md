# Tensor isomorphism hardness in concise critical formats

**Theorem.** For $\delta\in\{0,4\}$, ordinary three-tensor isomorphism reduces by polynomial-time many-one reductions to ordinary TI and to special-linear TI on concise tensors of formats satisfying
$$
\Delta(a,b,c)=a^2+b^2+c^2-abc=\delta.
$$
Thus ordinary TI on either concise format family has the degree of unrestricted ordinary TI. The special-linear statement is a hardness result in the TI-to-SL-TI direction. These are exact field-arithmetic reductions over any field, and polynomial bit-time reductions over a fixed finite field. This informal proof uses the archived sentinel-and-castling construction and builds on the castling machinery already in MathProofs. [Determinant Cosets from Castling and Normalized Matrix Pencils](../DeterminantCosetsByCastling/PROOF.md)

## Determinant calibration and conciseness

Let $E,F,H$ have dimensions $a,b,c$, and let $T\in E\otimes F\otimes H$ have injective flattening $\phi_T\colon H^*\to E\otimes F$. For $0<c<ab$, set $K_T=\ker \phi_T^*$ and form the tensor of the inclusion $K_T\hookrightarrow E^*\otimes F^*$ in $E^*\otimes F^*\otimes K_T^*$. Isomorphism is preserved and reflected. A first- and second-mode pair sends the image of $\phi_T$ to that of $\phi_S$ exactly when its inverse dual sends $K_T$ to $K_S$. In each case the last mode map is then forced by the injective flattening.

Fix coordinate volume on $E^*\otimes F^*$ and $H$. Choose a basis of $K_T$ whose concatenation with lifts of the standard basis of $H$ has determinant $1$. This is achieved by rescaling one kernel vector and does not depend on the choice of lifts. Choose the basis for $K_S$ by the same rule. Under a transporter $(g,h,k)$ for $T,S$, the map on the ambient dual tensor product is $g^{-T}\otimes h^{-T}$, and the induced map on the quotient $H$ is $k$. Taking determinants in the resulting block triangular map gives
$$
\det(z)=(\det g)^{-b}(\det h)^{-a}(\det k)^{-1}
$$
for the matrix $z$ on the kernel. The third mode of the castled tensor transforms by $z^{-T}$. Thus castling also preserves and reflects simultaneous determinant one. The construction uses Gaussian elimination and a single rescaling.

If $c<\min(a,b)$, the new tensor is concise. The third flattening is injective by construction. A proper first slot support would place $K_T$ in a subspace of dimension at most $(a-1)b$, whereas $\dim K_T=ab-c>(a-1)b$. The same argument using $c<a$ proves full second slot support.

## From an arbitrary input to an oriented padded input

Trim each nonzero input to its three intrinsic slot supports. This preserves and reflects ordinary TI when the original ambient dimensions agree, since any isomorphism on supports can be extended to the original modes. Unequal support dimensions decide a NO instance. Equal zero inputs decide a YES instance. The resulting nonzero concise tensors have common format $(d_1,d_2,d_3)$, after reordering modes so $d_3=n=\max_i d_i$.

For $c>n$, add $r=c-n$ scalar direct summands, each the tensor $(1)$ in a separate one-dimensional block in all three modes. The sum is concise and has third dimension $c$. Direct-sum cancellation holds for concise three-tensors. Their centroids are commutative, the primitive idempotents give the indecomposable summands, and any isomorphism permutes the summands by transport of the centroid. Thus a common multiset of scalar blocks cancels. [Centroid blocks and tensor transporters](../SLDeterminantAssembly/PROOF.md)

Pad the first two modes with zeros to dimensions $a,b$ both strictly larger than $c$. A GL transporter of the trimmed tensors extends to these padded tensors with all three determinants $1$. Its third determinant is corrected on one added scalar block by a nonzero multiplier in the third mode and the inverse multiplier in the first mode. The free complementary directions independently correct the first and second determinants. Conversely a transporter of the padded tensors restricts to the support sums and implies a GL transporter for the trimmed tensors by cancellation. The same reasoning without determinant correction gives ordinary orbit equivalence of the padded tensors.

## Choosing the integer formats

The replacement $(a,b,c)\mapsto(a,b,ab-c)$ preserves $\Delta$. For $\delta=4$, take
$$
c=\max(n+1,3),\qquad a=c^2-2,\qquad b=c^3-3c .
$$
Substitution gives $\Delta=4$ and $a,b>c$. For $\delta=0$, start at $(3,6,15)$ and repeat $(x,y,z)\mapsto(y,z,yz-x)$ until the smallest coordinate $x$ exceeds $n$. At each step $x<y<z$ and $yz-x>z$. The invariant $\Delta$ stays zero. Starting with $y\le x^2$ and $z\le y^2$, each iteration preserves these inequalities because $yz-x\le z^2$. Thus the first $x>n$ is $O((n+1)^2)$, and the subsequent coordinates are polynomially bounded in $n+1$. Take $(c,a,b)=(x,y,z)$. Both constructions permit every padded dimension and satisfy the conciseness inequalities for castling. The output dense array has polynomial size.

To implement the already-decided cases within each output promise, use $(c,a,b)=(3,6,15)$ for $\delta=0$ or $(3,7,18)$ for $\delta=4$. In the $a$ by $b$ matrix space take one three-dimensional span of independent rank-one matrix units and one three-dimensional space of alternating matrices supported in a $3$ by $3$ corner. The latter contains only rank-two nonzero matrices, including in characteristic two. The two subspaces cannot be left-right equivalent because their rank sets differ. Their castled tensors furnish a fixed concise NO pair for both target actions. Two identical copies of either tensor furnish a fixed YES pair. This completes the reductions on every input.
