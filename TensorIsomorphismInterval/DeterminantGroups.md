# A determinant-subgroup order inside the TI to SL-TI interval

Work over $F=\mathbb F_3$. The complete problems are decision problems on explicitly encoded 3-tensor pairs. A class is the set of languages polynomial-time many-one reducible to the stated complete problem. We use arbitrary rectangular formats and compare equal formats. Write $\Gamma=(\mathbb F_3^\times)^3$ additively as $\mathbb F_2^3$, sending a negative determinant to $1$. For a subgroup $H\le\Gamma$, define $P_H(T,S)$ to ask for an ordinary transporter whose determinant triple belongs to $H$. Consequently $P_\Gamma=\mathrm{TI}$ and $P_0=\mathrm{SL\text{-}TI}$.

## The subgroup reduction theorem

For every $H\subseteq K\subseteq\Gamma$,
$$
                    P_K\ \le_m^p\ P_H .
$$
All the reductions are deterministic. The theorem realizes the entire sign-subgroup inclusion order in reverse as a system of reductions. Complexity classes at different positions may coincide.

For the lower endpoint one can also use a direct reduction. Append one empty coordinate in each mode of both tensors. Every ordinary transporter extends to an ambient transporter with determinant one by adjusting the new complements. Any ambient transporter restricts to one on the intrinsic supports (the images of the three contractions on the other two factors) and extends back to the original dimensions. For clarity, the subgroup padding below works on nonconcise inputs too.

## 1. Auxiliary tensors realizing sign subgroups

The centroid of a concise tensor is the algebra of triples whose mode actions on the tensor agree. It is commutative: move two actions to different modes to commute them and use conciseness to recover equality of the component maps. Under ordinary transport the centroids are conjugate. Nontrivial central idempotents split the tensor into independent blocks, and primitive idempotents recover its indecomposable blocks. This follows by decomposing each mode into the images of the orthogonal idempotents, since the tensor has zero components with two distinct block indices. Ordinary transport permutes these intrinsic blocks. These observations can be made over the base field.

**Coordinate line.** One empty coordinate in the corresponding mode gives an independent sign in that mode and no additional signs in the other modes. An intrinsic support is always preserved, so its complement gives a genuine, freely adjustable determinant contribution.

**Two-coordinate line.** The following concise pencil has shape $(2,N,N)$, and realizes the sign line $\langle(0,1,1)\rangle$:
$$
       M(x,y)=\operatorname{diag}(x I_{m_1},\, y I_{m_2},\, (x+y) I_{m_3}).
$$
Use distinct positive $m_i$ of even sum $N$, with $N$ larger than any input side. The pencil has an invertible slice at $(1,1)$. Its determinant polynomial has three distinct linear factors with three different multiplicities. Any ordinary automorphism of the tensor scales this determinant polynomial and hence its first-mode projective action fixes each of those three lines. A linear map on a two-dimensional space fixing three distinct projective points is scalar. The first determinant is therefore one. The invertible slice then shows that the two matrix-mode determinants are equal, because the scalar from the label action is raised to the even power $N$. One reflection on a chosen block, applied compatibly to both matrix modes, realizes the nonzero sign pair. The pencil is indecomposable as a tensor. Indeed a centroid idempotent $e$ supplies an automorphism acting by $I+e$ on the label and the inverse of $I+e$ on one of the other modes, since the single-mode centroid actions agree. The label map being scalar forces the label idempotent to be scalar, and conciseness then forces the original idempotent to be zero or the identity. Permuting modes supplies the other two-coordinate lines.

**Three-coordinate line.** Let $E=\mathbb F_9$, $\sigma(z)=z^3$, and $m\ge2$ be even, with $N=m+2$ larger than any input side. In the contraction frame $(x,z)\in F^m\oplus E$, with trace coordinates on the last two quotient modes, use the pencil
$$
 M(x,z)=\begin{pmatrix}
 \operatorname{diag}(x)+\operatorname{Tr}(z)J &
 \mathbf1\operatorname{Tr}(\sigma(z)\,\cdot)\\
 \sigma(z)\mathbf1^{\mathsf T}&[w\mapsto zw]
 \end{pmatrix}.
$$
Here $J$ is the directed path matrix, with one in positions $(i,i+1)$. This is the previous rank-one graph-pencil construction with a Frobenius-invariant path color. Its only rational rank-one labels are the $m$ axes for $x$, since at $z\ne0$ the bottom block has rank two. The pencil is concise, using these axes and the invertible quotient at $z=1$. Any automorphism permutes the matched axes across the three modes and preserves their spans. In the two physical matrix-mode quotients, use the trace pairing to write the quotient equation as $A K(z) B^*=K(Cz)$, where $K$ denotes multiplication by $z$. At $z=1$, $AB^*=K(c)$, where $c=C(1)\ne0$. Hence $A K(z) A^{-1}=K(c^{-1}Cz)$. It follows that $C=c\tau$, $A=a\tau$, $B=b\tau$, where $\tau\in\{1,\sigma\}$, $a,b\in E^\times$ and $ab=c$.

For the mixed terms compare the independent linearized monomials $z$ and $z^3$ over $E$. Upper output shears contribute only a $z$ term in the mixed row and input shears only a $z$ term in the mixed column. Against the target coefficient $\sigma(c)$ of $\sigma(\tau z)$, this forces both shears to vanish, and forces the top-axis scalars $a_i,b_i\in F^\times$ to satisfy $a_i b=c^3$, $b_i a=c^3$. Thus $a_i b_i=c^5\in F^\times$. Fifth power is an automorphism on $E^\times$ of order eight, so $c\in F^\times$, and then $a_i=a$ and $b_i=b$ with $a,b\in F^\times$. The top diagonal equality kills the label shear. The remaining equation requires a graph automorphism of the directed path, since the nonzero color is Frobenius-invariant. The permutation is the identity. Conversely each common $\tau$ and the two freely chosen scalars $a,b$ gives such an automorphism. The normalized determinants of the three maps are all $\det_F\tau$, since $N$ is even. This yields exactly the line $\langle(1,1,1)\rangle$. This tensor is indecomposable: with the entire label mode fixed, its two remaining actions are common scalars. A centroid idempotent would supply an automorphism fixing the label by using $I+e$ and its inverse in the two matrix modes, so its two components and then the entire idempotent must be scalar.

The graph-pencil calculation also gives raw yes-set separation for the different $H$'s. Replace every nonzero path color by $\operatorname{Tr}(\ell z)$ for one $\ell\in E\setminus F$, keeping the mixed terms unchanged. The same calculation leaves only $\tau=1$, since Frobenius changes the color. Thus the stabilizer sign image is zero. Reflecting arbitrary modes gives pairs with singleton sign cosets of every possible sign triple. Different groups $H$ really impose different tensor conditions, without deciding complexity-class separation.

## 2. Padding by an arbitrary sign subgroup

Choose a basis of $K$, and for each basis vector use the appropriate line construction. For noncoordinate basis vectors choose distinct auxiliary shapes, with the large side greater than all input dimensions. Direct-sum the auxiliary tensors onto each side of the input, and add the coordinate slack in the designated ambient modes. Work first in the intrinsic supports. In the concise support tensor, each attached block is distinguished by its ordered dimensions from every input block and from each other attached block. Therefore every ordinary transporter restricts to transport on the input support and separately to automorphisms on the added blocks. The original input ambient complement may contribute any determinant when nonzero, independently of the support action. Those same contributions are present in the padded instance, with independently adjustable additional signs in the designated empty slots. With the fixed coordinate decompositions used on both sides, determinant multiplication gives exactly
$$
     \{\text{padded transporter signs}\}
       = \{\text{input transporter signs}\}+K .
$$
The empty set is preserved. A shear between the support and its complement contributes determinant one. Conversely any desired support and complement actions extend by blocks, so the equality includes both directions even for singular inputs. All added sides are polynomially bounded. Testing membership of the padded sign set in $H$ is equivalent to membership of the original sign set in $K$ when $H\subseteq K$. This proves the subgroup theorem.

## 3. Six sign candidates and the three character tests

Modulo mode permutation there are three nonzero line types, according as their generator has weight one, two or three, and three plane types, according as their defining linear functional has weight one, two or three. Thus there are six sign candidates other than the two endpoint presentations. For example the line $\langle e_1\rangle$ requires the other two modes individually to have determinant one, while $\langle e_1+e_2\rangle$ requires those two signs to agree and the third mode to be oriented. The three plane problems impose one sign equation each.

For a fixed input with some ordinary transporter, its sign set is an affine coset $a+G$, with $G$ the source stabilizer sign group. Then $P_H$ is equivalent to $a\in G+H$. The latter holds exactly when for each hyperplane $L\supseteq H$, the query $P_L$ answers yes. Indeed, if $a\notin G+H$, a linear functional zero on $G+H$ and nonzero on $a$ yields an excluding hyperplane. The empty sign set yields no on every character query; $H=\Gamma$ is the ordinary test itself. Thus full SL-TI over $F$ is a fixed conjunction of the seven single-character queries, which have three types up to permutation.

In particular, if each of the three character types many-one reduces to ordinary TI, then full SL-TI does as well. A constant number of ordinary TI comparisons can be combined by taking all their tensors as a tensor system on independent vector spaces, then applying the fixed-signature tensor-system compiler. This is a sufficient strategy for the endpoint equality. Under polynomial-time Turing reducibility the same conjunction gives an immediate upper bound in the join of the character classes. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1 and Open Question 1.9](https://arxiv.org/html/2306.03135v2#S4)

## 4. A variant over other fixed finite fields

For an ordinary determinant subgroup of $(F^\times)^3$ over a fixed finite field, the rectangular evaluation tensor $\sum_{ij} e_{ij}\otimes u_i\otimes v_j$, of shape $(ab,a,b)$, is one simple family of slack blocks. Its action in the first mode is forced to be the inverse dual of the product action on the last two. Its automorphism determinant set is
$$
 (D^{-b}E^{-a},D,E),\qquad D,E\in F^\times.
$$
The centroid is scalar, since $C_2\otimes I=I\otimes C_3$ on the full product space forces both matrices to be the same scalar. Taking $a,b$ in fixed residue classes modulo $q-1$ and growing them above all input dimensions makes this an exact pad for the single character $\det(g_1)\det(g_2)^b\det(g_3)^a=1$. This remark is independent of the full subgroup realization over $\mathbb F_3$.

These are informal reductions. The definitions of the problem classes are proposals. Every asserted interval containment has a proof, and strict containments and publication priority are open.
