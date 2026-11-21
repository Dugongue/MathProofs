# A determinant-preserving reduction on every ternary input

**Theorem.** Given any two ordered ternary three-tensors of a common format, one can transform each independently to a tensor with the following properties.

1. The set of three simultaneous transporter determinant values between the two outputs equals that between the two inputs. This includes ordinary TI, signed TI, and all seven other prescribed sign tests.
2. In each output mode, the stabilizer contains an element of order 13 that cannot permute the lines of any ternary basis. This holds even for the determinant-one stabilizer.
3. If the largest input side is $D$, each output side is $O(D+1)$. The map is deterministic polynomial time on dense inputs and also has an explicit sparse description.

Consequently the unrestricted same-field containment $\mathrm{TI}_{\rm SL}(\mathbb F_3)\le_m^P\mathrm{TI}(\mathbb F_3)$ is equivalent to the corresponding promise reduction on inputs having no stabilizer-invariant ternary basis of lines in any mode. In the promise version an ordinary unrestricted TI pair is required as output. The forward implication is restriction. For the reverse implication compose the transformation below with the promised reduction. The theorem gives a worst-case reformulation and preserves the determinant constraints. The desired transformation that removes those constraints remains open. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Transformation

Choose the smallest even $k\ge4$ such that $k^2>D$ and put $A=M_k(\mathbb F_3)$. Use the matrix-unit bases. Append the trilinear form $R(X,Y,Z)=\operatorname{tr}(XYZ)$ as a direct summand in three fresh coordinate blocks. Thus the output is $T\oplus R$ with every mixed term zero. Passing between forms and covariant tensors transposes or inverts the mode maps according to convention, preserving each sign over the ternary field. The new entries of value one occur at precisely the $k^3$ triples $((i,j),(j,l),(l,i))$ in the new blocks. Since $k$ grows by increments of two, $k^2=O(D+1)$. [Executable transformation](pad.py)

## Why the block is intrinsic

Work on the minimal support spaces in the covariant tensor convention. They are the spans of all contractions in the other two legs. They are equivariant under arbitrary isomorphisms. The matrix summand is concise by nondegeneracy of the trace pairing. Hence the support spaces of the output are the direct sums of the corresponding old supports and the three full matrix blocks.

For a concise tensor its centroid consists of triples of linear maps whose separate actions on the tensor are equal. Each projection is faithful by conciseness. Composition is closed and commutative: for two centroid operators, move their actions from the same mode onto the two distinct other modes, commute them there, then move them back in reverse order. Equality of actions and faithfulness give the asserted identities. For a direct sum of two concise tensors every centroid triple is block diagonal. Indeed, acting off-diagonally on one mode creates a component with just that leg in a different block. An action on another leg cannot produce that same pattern from either diagonal summand. Conciseness forces each off-diagonal map to vanish. The centroid of the direct sum is therefore the product of the two centroids.

For $R$ the centroid is just the scalars. In form notation the equality of the first two actions gives $f(X)Y=Xg(Y)$ by the trace pairing. Setting $X$ or $Y$ equal to the identity gives $f(X)=Xa$ and $g(Y)=aY$ for one matrix $a$. Comparing with the third leg gives $aYZ=Yh(Z)$, hence $h(Z)=aZ$ and $aY=Ya$ for every $Y$. Thus $a$ is scalar.

The projector onto $R$ is accordingly a primitive centroid idempotent. Every other primitive idempotent lies in the old-support factor of this product and its images have dimension at most $D$. The matrix projector has rank $k^2>D$ in all modes. Any transporter conjugates the two centroids and so carries this unique large primitive projector to its counterpart. This proves that all three matrix subspaces are preserved even when the original tensors are nonconcise. For zero input the matrix projector is the entire concise-support identity, with the same conclusion.

## Why no determinant changes

An ordered autotopism of the matrix summand gives three invertible linear maps $f,g,h$ with $f(X)g(Y)=h(XY)$, using the trace pairing to take the inverse dual map on the output. Write $a=f(1)$ and $b=g(1)$. The equations $h(X)=f(X)b$ and $h(Y)=ag(Y)$ imply that $a,b$ are units, since the indicated multiplication maps are onto. Then $\phi(X)=a^{-1}f(X)=g(X)b^{-1}$ is a unital linear algebra automorphism, as substitution into the product identity shows. Every such automorphism is inner: its images of the standard diagonal matrix units are complementary primitive rank-one idempotents, and applying the images of $E_{i1}$ to a nonzero vector in the first image supplies a basis in which every image of $E_{ij}$ is the standard matrix unit.

Left or right multiplication on $M_k$ has determinant the $k$-th power of the determinant on the defining $k$-space, by acting separately on columns or rows. Thus all left and right multiplications by units have determinant one over $\mathbb F_3$ when $k$ is even. This applies also to inner conjugation and gives determinant one on all three legs of the matrix autotopism.

Every original transporter extends by the three identity maps. Conversely a transporter of the outputs preserves the matrix subspaces by the projector argument, and its restrictions there form an autotopism of $R$: on the concise supports the other primitive blocks also map into the old supports, so they contribute nothing to the matrix component. Quotienting the ambient modes by the three matrix subspaces sends the output tensors back to the original tensors. The induced quotient maps are therefore original transporters. The block triangular determinant identity gives exactly their three original determinant values, because the three restrictions have determinant one. This quotient argument includes unused ambient coordinates and all shears on them.

## Why a mode frame cannot exist

Take $B$ acting by multiplication by a primitive thirteenth root in the three-dimensional space $\mathbb F_{27}$ over $\mathbb F_3$. Its minimal polynomial has degree three since 3 has order three modulo 13. Extend by the identity to $P$ on the $k$-space. The simultaneous actions $X\mapsto PX$, $Y\mapsto Y$, $Z\mapsto ZP^{-1}$ preserve $R$ by cyclicity of trace, and act identically on the old blocks. The first mode operator has order 13 and has minimal polynomial dividing $(t-1)f(t)$ for one cubic $f$, by its action on columns. Dualizing retains this degree bound. Cyclic rotation gives such an element on each mode.

If this operator permuted a basis of lines, its permutation would have cycles of lengths one or 13. Its order forces a 13-cycle, because fixing all lines would give a diagonal ternary operator of order at most two. On a 13-cycle the successive images of a spanning vector through the first thirteen powers are linearly independent, as they occupy distinct basis lines. This contradicts the degree-four annihilating polynomial. The argument holds in arbitrary ambient dimension, including after adding all the old coordinates.

The reduction and its proof are informal. The local control verifies the order-13 action on all 27 vectors of its defining three-space. The [companion result](Proof.md) gives an executable SL canonization algorithm for a separate family where the rank-two contraction geometry does determine a frame.
