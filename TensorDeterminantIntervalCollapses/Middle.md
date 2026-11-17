# Middle tiers: shared references and odd stabilizers

Over $\mathbb F_3$, write $O$ for ordinary tensor isomorphism, $A$ for determinant-one isomorphism in the first mode, and $B$ for determinant-one isomorphism in both first and second modes on a common transporter. Put $J=A\wedge A$, with independently encoded comparisons. Let $R$ be the shared-reference triple M3, asking for $A(X,Y)\wedge A(X,Z)$, and let $F(X)$ ask for an ordinary automorphism of $X$ with negative first determinant. Then M4 is $A\wedge F$ on independent data and M5 has the same degree. Reductions below are deterministic and many-one. Tensor coordinates and any supplied matrices are explicit.

## 1. One shared-reference instance on the equal-flexibility promise

For a tensor pair $(X,Y)$, the first determinants of its ordinary transporters, if any, form one coset of the first-determinant image of the source stabilizer. Thus $F(X)$ holds exactly when both first signs are available whenever $O(X,Y)$ holds.

Take two independent comparisons $(X_1,Y_1)$ and $(X_2,Y_2)$. Use the previous exact sign projection and scalar-centroid glue to turn the first pair into $(P_1,Q_1)$ and the second into $(P_2,Q_2)$. The two encodings preserve ordinary equivalence and the full first-sign profiles, with other signs zero. They act on absolutely indecomposable even-sided tensors. Use two distinct block formats. Whenever an ordinary transporter exists, equality of the relative sign profiles implies equality of their direction subgroups, which are the first-determinant images of the source stabilizers. If no ordinary transporter exists, the proposed comparison below fails regardless of the encoded stabilizer.

Define the triple
$$
  X'=P_1\oplus P_2,\qquad
  Y'=Q_1\oplus P_2,\qquad
  Z'=P_1\oplus Q_2.
$$
The primitive centroid summands select exactly the matching format in each comparison. In $X'\to Y'$, the second block can correct the first sign precisely when $F(X_2)$, provided the first pair has an ordinary transporter. The analogous statement holds in $X'\to Z'$. Write $O_i=O(X_i,Y_i)$, $A_i=A(X_i,Y_i)$ and $F_i=F(X_i)$. The exact verdict of $R(X',Y',Z')$ is
$$
 O_1\land O_2\land(A_1\lor F_2)\land(A_2\lor F_1)
 =
 O_1\land O_2\land\big((A_1\land A_2)\lor F_1\lor F_2\big).
$$
The equality uses $O_i\land F_i\Rightarrow A_i$. In particular this is an exact one-instance reduction $J\to R$ under the promise $F_1=F_2$. It applies both when both sources are sign-rigid and when both are sign-flexible. If it is efficiently certified that either source is flexible, $J$ instead reduces to one $A$ instance by absorbing that ordinary comparison into the other signed comparison with the established neutral conjunction.

An exact false-positive mechanism remains in the unrestricted input. If exactly one source is flexible and both ordinary comparisons hold, the construction accepts even when the other pair is sign-rigid with negative relative sign. Such inputs exist. For the flexible pair one can take a same-tensor comparison of a zero tensor; for the other take a tensor of trivial determinant image and its first-mode rebase by a reflection. One example of a tensor of trivial determinant image is the multiplication tensor of $\operatorname{Mat}_2(\mathbb F_3)$. Every isotopy of this unital algebra is an algebra automorphism followed by left and right multiplication by units. The algebra automorphism is inner, and the left and right unit actions on the four-dimensional algebra each have determinant a square, by the two column or row copies. Thus every tensor stabilizer has positive determinant in all three modes.

Consequently the common-source direct-sum construction does not prove $J\le_m^p R$ on arbitrary input. It proves that a polynomial-time procedure which either certifies $F_1=F_2$ or identifies one flexible source suffices for $J\le_m^p R$. The latter branches use $A\le_m^p R$ by duplicating the target. In particular $F\in P$ suffices for $J\equiv_m^p R$, using the known $R\le_m^p J$. The case of certifiably unequal flags is not a promise of easy ordinary isomorphism, but the above use of an ordinary comparison handles it without an isomorphism oracle in the reduction.

## 2. The exact supplied-transporter variant is M4

Consider $J$ with one additional piece of explicit data: an ordinary transporter $g:U\to V$ for its second comparison. Reject an invalid certificate. This variant is equivalent to $A\wedge F$.

If $\det(g_1)=+1$, the certified second comparison is already positive. If $\det(g_1)=-1$, that comparison has a positive transporter precisely when $U$ has a negative first-mode stabilizer. This follows by writing every transporter as $g$ composed with a source automorphism. Thus in the first case use a fixed positive $F$ instance, and in the second case use $F(U)$ as the second conjunct. Invalid inputs go to a fixed negative output. Conversely, given $A(X,Y)\wedge F(U)$, use $(U,R_1U)$ and its explicit reflection $R_1$ as the certified ordinary transporter in the second pair. This supplies the other many-one direction. In particular the certificate removes exactly the ability of the second signed test to compare two unrelated ordinary orbits.

## 3. The unary odd-stabilizer problem lies between ordinary TI and one-sign TI

The upper reduction is the reflection test $(U,R_1U)$ above. For the lower direction, use the earlier optional-swap construction's odd-dimensional helper encoding. Given $(C,D)$, form equal-format, absolutely indecomposable tensors $H(C)$ and $H(D)$, with all mode dimensions odd, whose individual stabilizers have total determinant $+1$. They are ordinarily isomorphic exactly when $O(C,D)$. This is a dependency from the previous proof of optional correction, constructed by neutral amplification, parity padding and scalar-centroid glue.

The tensor $W=H(C)\oplus H(D)$ has an automorphism of negative total determinant exactly when its two helpers can exchange. Any automorphism preserving each component has total determinant $+1$. If exchange is possible, use any isomorphism between the helpers together with its inverse in the other direction. Their local determinants cancel. The block transposition contributes a negative determinant in all three odd-dimensional modes, hence a negative total determinant. Its possibility is exactly $O(C,D)$. For wrong input formats use a fixed negative unary instance. Apply the earlier exact linear sign projection to the self-comparison $(W,W)$, with the total sign projected to the first mode. The resulting nonempty relative sign profile is a subgroup, since its input profile was a stabilizer sign image. Its direction is therefore the whole profile and is the stabilizer sign image of its encoded source. Testing $F$ on that source proves $O\le_m^p F$, even without requiring the two output descriptions to be identical.

The exact same type of argument proves that a polynomial list of unary odd-stabilizer questions can be combined as a single disjunction in $F$: isolate the live sign on one common physical axis, make the objects indecomposable and even-sided, choose distinct formats, and take the direct sum. The full first-determinant image is the sum of the independent images. It contains the negative bit if and only if some component has it. Pairwise distinct formats keep unrequested exchanges out. All marker lengths can be chosen from distinct polynomially bounded ranges sized to the combined input. This proves disjunction, without an analogous claim for conjunction.

If $F\le_m^p O$, then M4 and M5 reduce to $A$ by neutral conjunction, and their known lower reduction makes this a collapse to $A$. If $A\le_m^p F$, then M4 and M5 are instead equivalent to $J$, by substituting this reduction in the second component. Neither premise is established here. The first would identify the unary problem with ordinary TI, and the second would identify it with one-sign TI.

## 4. Residual cases for the two-sign question

Let $D\subseteq\mathbb F_2^2$ be the relative two-bit profile of one comparison, and $H$ the projected stabilizer sign subgroup. Empty profiles reject. If a witness $h\ne0$ in $H$ is given, then testing the one character annihilating $h$ decides $B$, as in M7. The separate-witness version M2 behaves differently. When the supplied $h$ is diagonal $(1,1)$, each coordinate can be corrected separately, so M2 equals ordinary isomorphism. The ordinary coset may nevertheless be the opposite diagonal line and fail $B$. When the given $h$ is a coordinate direction, M2 and $B$ both reduce to the remaining coordinate sign. For rigid sources $H=0$, M2 and $B$ agree on every relative pair, since there is at most one possible sign vector.

These statements give exact restricted collapses and isolate a concrete obstruction in the shared-reference construction. They do not prove $J\le_m^p A$, $B\le_m^p J$, or $B\le_m^p A$. For the ambient tensor-system compiler see [Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2#S4). All proofs are informal.
