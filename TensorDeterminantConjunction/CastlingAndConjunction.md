# Castling and independent sign queries

Work over $F=\mathbb F_3$ with explicit rectangular 3-tensors and deterministic polynomial-time reductions. Write a det-$-1$ as the bit one. Write $A_1,A_2,A_3$ for the three one-character problems from the interval list, with conditions respectively $d_1=1$, $d_1d_2=1$, and $d_1d_2d_3=1$. Write $R_1,R_2,R_3$ for the three line-subgroup problems from that list, numbered 4–6. The endpoints and definitions are in [the interval packet](https://github.com/Dugongue/MathProofs).

## 1. The three character problems are many-one equivalent

If there is an unused support direction in any mode appearing in a tested character, an arbitrary sign on that complement corrects the character and the decision reduces to ordinary TI. Likewise a scalar automorphism $(\lambda_1 I,\lambda_2 I,\lambda_3 I)$, $\lambda_1\lambda_2\lambda_3=1$, can correct a tested character if its vector of participating dimension parities is neither all zero nor all one. These branches may be mapped to any orientation problem by the established TI lower reduction using unused coordinates. Below all required first modes are therefore concise. Modes may be permuted.

For a tensor $T\in U\otimes V\otimes W$ concise in $U$, identify $U^*$ with its image $L_T$ in $P=V\otimes W$. Replace the tensor by the inclusion of the annihilator $L_T^\perp\subseteq P^*$, expressed in a basis, with the other modes $V^*,W^*$. This is the standard castling operation. Assume the annihilator has positive dimension. To calibrate determinants, start the basis of $P$ with the ordered image of the raw basis of $U^*$, then choose its complement basis so the entire matrix has determinant one. This is possible by rescaling its last vector. Use the induced dual complement basis for the new label. Apply this procedure independently to $T,S$.

An old transporter $(a,b,c)$ carries $L_T$ to $L_S$ by $b\otimes c$, with restricted matrix $a^{-\mathsf T}$ in the chosen image bases. Its induced map on the quotient $P/L_T$ has determinant
$$
  \det a\,(\det b)^{\dim W}(\det c)^{\dim V}.
$$
This follows from the block triangular matrix in the two calibrated bases. On the annihilators the action is inverse dual to the quotient action, and the new label transformation is itself inverse dual to that induced on the annihilator. Conversely an isomorphism of annihilator tensors uniquely determines the old label action from the induced map on the original image, by double annihilator. Therefore castling gives exact correspondence of ordinary transporters and transforms their determinant bits by
$$
 (x,y,z)\ \longmapsto\
 (x+(\dim W\bmod2)y+(\dim V\bmod2)z,\; y,\; z).
 \tag{1}
$$
The two dualizations in the unchanged modes do not affect signs. Extracting calibrated bases and carrying out castling takes polynomial time. [Castling and orbit correspondence](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/maximum-likelihood-estimation-for-tensor-normal-models-via-castling-transforms/FF03C608CF421F399C16127F8476538F)

To reduce $A_1$ to the two-mode product problem, append unused directions to make $\dim V$ odd and $\dim W$ even, and make $\dim V\dim W>\dim U$. These modes were unconstrained. On the transformed tensor, the product of the first and third determinants is exactly the old first determinant by (1). Conversely, for a two-mode product test on the first and third modes the decision is ordinary whenever either tested mode is odd or unused, by the initial correction observation. Otherwise the third mode is even. Make the second mode odd and sufficiently large by unused directions and use (1), so that the new first determinant alone tests the old two-mode product. This proves $A_1\equiv_m^p A_2$.

To reduce $A_1$ to $A_3$, pad the two untested modes to be odd and large, and use (1). The new total sign is the old first sign. Conversely, for a nontrivial total-sign query the dimensions all have the same parity and there are no unused support directions. We can take them all odd while preserving the total sign. To do so use an odd-sided evaluation tensor of shape $(ab,a,b)$, $a,b$ odd and larger than every input side, whose nonzero entries express the identity on $F^a\otimes F^b$. Its centroid is scalar and its stabilizer sign bits are exactly the even-total plane: the two small maps have arbitrary signs and the large map is their inverse dual tensor product. Add one such block when all three dimensions are even, and two distinct such blocks when they are already odd. Their sizes distinguish them from every input support summand and from each other, and their signs change only the even-total plane. All three padded dimensions are odd. Cross terms in the tensor product of modes ensure the first-side annihilator has positive dimension. Now castling makes the new first determinant test exactly the old total. It follows that all three $A_i$'s are many-one equivalent.

## 2. A concise tensor preserves one chosen sign and makes the other two trivial

Transform a hard total-sign instance to concise all-odd dimensions as above. Regard it as a bilinear map $m:U\times V\to W$. Form the finite-dimensional associative unital local algebra
$$
 B=F\,1\oplus U\oplus V\oplus W,
$$
with unit $1$, and with $uv=m(u,v)$ the only nonzero product between its radical summands. Since triple products inside the radical vanish, it is associative. The radical is $J=U\oplus V\oplus W$, $J^2=W$ by conciseness, and the induced product on $J/J^2$ recovers $U,V$ as its right and left annihilator, respectively. On those spaces and $J^2$, all algebra isomorphisms induce precisely the original tensor transporters. Conversely each such transporter extends by the identity on $1$. All filtration shears have determinant one. Hence the determinant of an algebra isomorphism is exactly the total determinant of the corresponding tensor transporter, since signs equal their inverses. The dimension $b=\dim B$ is even.

Encode $B$ by the action tensor of $B$ on $M=B\oplus B$, given by left multiplication. This tensor is concise, since the action is faithful and includes the identity slice. Any transporter of action pencils takes the regular image algebra to the target by conjugation with its matrix input action $g$, after allowing an invertible left factor $u\in B'$ on the target slices. More explicitly if $s,h$ are the label and output maps, the input $1$ gives $L_u=hg^{-1}$, and
$$
       L_{s(a)}=L_u g L_a g^{-1}.
$$
Thus $\phi(a)=u^{-1}s(a)$ is an algebra isomorphism and $g$ is semilinear along it. Conversely any algebra isomorphism $\phi$ gives such a transporter with $u=1$ and $g=\phi\oplus\phi$. The unit factor has $\det L_u=\rho(u)^b=1$, where $\rho$ is the scalar residue, because the remaining parts raise the radical filtration and $b$ is even.

The same filtration proves that an arbitrary $B'$-linear isomorphism of the free module $(B')^2$ has determinant $\det \beta^{b}=1$, where $\beta$ is its top action on $(B'/J')^2$: on each grade it acts by $\beta$ on the free index and the identity on the algebra grade. This holds for a noncommutative $B'$ as well by using right multiplication on left-module coefficients. The $\phi\oplus\phi$ part also has determinant one. Hence the exact transporter sign set of the action tensor consists of $(\det\phi,1,1)$ for the preceding algebra isomorphisms.

For an ordinary centroid triple of this action tensor, denote the label action by $c$ and write the equal matrix actions as $k$, identified using the identity slice. The identity slice makes $k=L_{c(1)}$ on $M$. Moving $k$ across an arbitrary slice forces $c(1)$ to be central, and the label action is multiplication by that central element. Thus the centroid is isomorphic to the center of $B$, which need not be scalar. It is local, however, since a central idempotent in the local algebra is zero or one. Indeed the center has scalar residue and nilpotent kernel. Therefore the action tensor is absolutely indecomposable. Its format is $(b,2b,2b)$ and all sides are even.

To handle the ordinary branches in the total-sign question, first embed the corresponding ordinary TI pair into a concise balanced family with determinant-one witnesses, using the previous optimal-max-rank construction. Then make the three sides odd using the evaluation pad. The resulting total-sign answer is precisely the ordinary answer on the branch. For any fixed number of such sign queries one can choose all resulting $b$'s distinct and in disjoint ranges by choosing the sizes of the evaluation pads, which also let one choose arbitrarily large odd auxiliary dimensions. This tags each indecomposable axis tensor by format.

## 3. Comparison consequences

Let $A=A_1$ and let $A^{\wedge k}$ be the decision problem consisting of $k$ independently encoded $A$-instances all of which must have answer yes, for constant $k$. Use the axis construction in two distinct modes and direct sum its two tagged tensors. Transporters now have the two independent signs in a fixed coordinate plane. For any of the three nonzero line types $H$ one can choose this plane so that it intersects $H$ only in zero, by omitting any coordinate on which the generator is nonzero. Thus
$$
             A^{\wedge 2}\le_m^p R_i\qquad (i=1,2,3).
$$
With all three axes present one obtains $A^{\wedge 3}\le_m^p\mathrm{SL\text{-}TI}$. This is exact even on a negative ordinary branch because the distinct formats prevent exchanges, and any individual ordinary failure makes the entire pair fail.

Conversely each $R_i$ is a conjunction of three character queries, by the three hyperplanes containing its allowed sign line. Each full SL-TI instance is a conjunction of seven character queries. Replacing those queries by $A$ via castling gives
$$
 R_i\le_m^p A^{\wedge3},\qquad
 A^{\wedge3}\le_m^p\mathrm{SL\text{-}TI}\le_m^p A^{\wedge7}.
$$
In particular all six sign-constrained classes and SL-TI have the same polynomial-time Turing closure. The displayed conjunction bounds concern many-one reductions; a conjunction of several $A$-instances is its own specified complete problem.

These are informal reductions. They preserve the actual determinant constraints through the indicated transformations.
