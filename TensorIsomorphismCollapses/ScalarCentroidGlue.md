# A determinant-preserving scalar-centroid embedding

Over $\mathbb F_3$, the full special-linear 3-tensor problem is many-one equivalent to each of the previous candidates 7 (balanced concise), 8 (absolutely indecomposable), 9 (scalar centroid), 13 (two summands with unequal formats) and 14 (two summands with equal formats). The comparison for 9 uses an exact embedding of the determinant set and preserves every sign, even on a negative instance.

## 1. Reduce to concise balanced tensors of even side length

Consider two input tensors of the same format. Compare the dimensions of their three supports; unequal dimensions exclude ordinary equivalence. Unless both are zero, compact to the support bases, using the original basis in every full-support mode. The original ambient sign set equals the compact sign set plus the independent coordinate signs in deficient modes. This is because a free complement can adjust its own determinant arbitrarily; basis-calibration factors in deficient modes are absorbed by that same freedom. For each deficient mode add a concise tensor with the corresponding one-coordinate sign subgroup, distinguished by an oversized format. The even-sided Kronecker padding pencil of the previous determinant-subgroup construction supplies precisely this gadget. This restores the original sign set on concise inputs. [Sign subgroup comparison](SignComparison.md)

If the current parities are mixed, every odd-coordinate sign is already in the scalar sign subgroup: there are at most two odd modes, and the scalar in an even mode can be chosen to satisfy the product-one condition. Add sign pads of shape $(3,N,N)$ to turn just those odd sides even, without changing the sign set. A pad in its short mode is a pencil on three labels whose normalized blocks are single Jordan blocks with even distinct lengths. Its four determinant factors are $x,y,z,x+y+z$, of those distinct lengths, with common nilpotent term vanishing at the anchor $(1,1,2)$. Fixing each projective hyperplane forces a scalar label action; it contributes an arbitrary sign in dimension three. With label fixed, its centralizer units have determinant one by the even Jordan lengths. A scalar label action extends by a scalar on one even matrix mode. Thus the pad contributes just that short-mode sign. It is indecomposable by the scalar-label argument for the earlier Jordan pads.

If all sides are odd, add a larger odd cube given by the non-Frobenius-invariant directed-path pencil of the earlier sign proof. The graph-pencil classification forces scalar stabilizers with scalars of product one; its determinant image is the even-total plane in odd dimensions. This plane was already realized by scalar automorphisms of the original tensor, so its addition preserves the sign set and all sides become even. If all sides were even, no parity adjustment is needed. All pads can be kept distinct, using individual oversized sides.

Finally add three determinant-trivial Jordan pencils of shapes $(2,N_i,N_i)$ with short sides in the respective modes $i$. Their determinant image is trivial: the three distinct projected lines fix label action scalar, and each distinct even-length Jordan centralizer has determinant one. They too are indecomposable. For current even sizes $n_i$ set $N_i=C+n_i$, for a sufficiently large even $C$. The new size in mode $i$ is
$$
                 n_i+2+\sum_{j\ne i}N_j
                 =2+2C+\sum_j n_j .
$$
This is a common even size. The pads' long sides exceed all prior side sizes, so distinct ordered formats still isolate them. These reductions work on any sign membership question and on the whole determinant set. Trivial constant cases can be sent to fixed yes and no instances. This proves the first endpoint collapse, candidate 7.

## 2. Attach a marker pencil without acquiring determinant slack

Write a concise input as $M:W\to\operatorname{Hom}(V,U)$. Take $C=F^2$, and a fixed square pencil $G(c):B\to A$ with the three projective determinant factors $x,y,x+y$, Jordan blocks of distinct even lengths, and common normalized anchor as above. Choose each length bigger than $\dim U$. Then for every nonzero $c$, over any algebraic extension, at least two blocks are invertible and $G(c)$ has rank greater than $\dim U$. Every transporter of $G$ fixing that same pencil has determinant one in all three modes, and $G$ is concise. The proof uses the distinct multiplicities to fix the three lines individually and force its label transformation scalar. Its even Jordan normalized centralizers and even mode lengths give the three determinant ones.

Define the new pencil with labels $W\oplus C$, domain $V\oplus Q\oplus B$ for $Q=U\otimes C^*$, and output $U\oplus A$ by
$$
 \widehat M(w,c)=\begin{pmatrix}
         M(w)& \operatorname{ev}_c &0\\
         0&0&G(c)
                 \end{pmatrix},
   \qquad \operatorname{ev}_c(u\otimes \ell)=\ell(c)u .
$$
This pencil is concise by the original conciseness, faithfulness of the evaluation, and conciseness of the marker. Any transporter preserves the following intrinsic flags, with the same symbols on a target.

* $W$ is the set of labels with rank at most $\dim U$.
* $U$ is the span of images of those labels and $K=Q\oplus B$ is their common kernel.
* $Q$ is the common kernel of the restrictions $K\to (U\oplus A)/U$ of the whole pencil.

These follow immediately from the two blocks and hold after field extension. Thus a transporter restricts to the original tensor on $W,(V\oplus K)/K,U$ and to a transporter of $G$ on $C,K/Q,A$. Let $\alpha$ be the induced label map on $C$, and $h_U$ the map on $U$. The induced map on $Q$ is $h_U\otimes\alpha^{-\mathsf T}$ by comparing evaluations. It has determinant one because $\dim C=2$ and $\det\alpha=1$. The other added quotient actions have determinant one by the choice of tag. Therefore the new tensor has precisely the old determinant triples, by the filtration determinant rule and the fixed raw concatenation order. Conversely every original transporter extends using its map on $U$ in the evaluation factor and identity on all marker spaces. Both directions preserve individual signs and require no search.

The centroid of the new tensor is scalar, even over the algebraic closure. To prove it, temporarily work over that closure. Any centroid triple preserves the intrinsic flags. Indeed for a generic scalar $t$, $I+t$ times a centroid element in one mode and the inverse corresponding map in another give a tensor automorphism, since the single-mode actions agree. Hence the linear parts preserve the flags. Use the centroid equalities on the evaluation quotient $C\times Q\to U$: comparing the $U$ and $C$ actions shows that both are the same scalar, because evaluation is the full product pairing. It forces the diagonal action on $Q$ to be that scalar. The original and marker tensor conciseness, using the already fixed scalar on $U$ or $C$ respectively, make all diagonal actions the same scalar. Subtract it. The remaining centroid actions can only be a label shear $C\to W$, an output shear $A\to U$, and input shears $V\to Q\oplus B$ and $B\to Q$. On a marker label $c$, the label shear acts through $M(W)$, supported on $V\to U$. The output shear acts through $G(c)$, supported on $B\to U$. These supports are disjoint, so their equality makes both zero. Injectivity of the label slice map and the full span of the marker images kill those two shears. After that, equality with the input action and the zero common kernels of $G$ and evaluation kill both input shears. Hence the centroid contains only the common scalars.

This proves the comparison with 9. A scalar geometric centroid implies absolute indecomposability, so it also proves the comparison with 8. The conclusions use the previous polynomial recognition tests for these two structural families for the easy upper directions.

## 3. Two summands with either format profile

For the unequal-format problem 13, append a common determinant-trivial absolutely indecomposable Jordan pad of different format to the tensor in Section 2. The geometric primitive centroid blocks isolate the two tensors by their formats. Thus the sign set stays unchanged. The output passes the required two-summand recognition.

For equal formats (14), start Section 2 with the even cubic inputs of Section 1. Let $D$ be the even cubic rigid path pencil of the same input side length, with non-Frobenius-invariant edge color and therefore zero determinant subgroup. Choose the common size sufficiently large for this template. Apply the same marker construction to $D$ and call the resulting fixed tensor $Z$. It is absolutely indecomposable, of exactly the same ordered format as the two encoded data tensors, and its determinant subgroup is trivial. Each of its sides is even because the tag has even sizes and the original cube is even. Append one copy of $Z$ to both sides. There are exactly two geometric summands, even if they are geometrically isomorphic, as their centroid is the product of two scalar algebras.

In a block-preserving match, the fixed block contributes no signs. If an isomorphism swaps the blocks instead, it gives maps from the first data tensor to $Z$ and $Z$ to the second data tensor. Their composition gives an actual data transporter, with determinant equal to the product of the two corresponding determinants. Exchanging two equal even-dimensional blocks in any mode contributes sign one. Thus even an exchanging determinant-one isomorphism gives a determinant-one data transporter. Conversely use the identity on the fixed block when an appropriate data map exists. This proves the equal-format collapse without requiring the two summands to have different isomorphism types.

These are informal determinant-preserving reductions over $\mathbb F_3$. Upper reductions use the exact definitions of the previous twenty candidates and reject malformed inputs by a fixed no instance.
