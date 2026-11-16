# Tensor isomorphism within a fixed deformation family

## Theorem

Let $R$ be a commutative local ring, let $I\subset R$ be a nilpotent ideal, and let $0\ne t\in I$. Set $S=R/\operatorname{Ann}_R(t)$. For any three ranks $a,b,c\ge2$, free three-tensor isomorphism over $S$ reduces to free three-tensor isomorphism over $R$, with linear side lengths, in a family with a common reduction modulo $I$. The common reduction is concise. Over a field its stabilizer is the connected reductive group
$$
\mathrm{GL}_a\times\mathrm{GL}_b\times\mathrm{GL}_c\times \mathbb G_m^3.
$$
The reduction uses one fixed tensor and a distinct-summand block for the input data. Every transporter is block diagonal and its restrictions recover a transporter of the original pair over $S$.

For example, take $R=\mathbb Z/p^e\mathbb Z$ or $k[\epsilon]/(\epsilon^e)$, with $e\ge2$, and $t=p$ or $\epsilon$. Then the entire preceding coefficient length is already present in one fixed reduction modulo $p$ or $\epsilon$. At $e=2$, ordinary tensor isomorphism over the residue field is equivalent to isomorphism in this constructed fixed-reduction family. The analogous flat associative-algebra deformation problem is also exactly tensor isomorphism. In that model one can identify the entire Hochschild deformation space.

## 1. A concise base tensor with three arms

Take free coordinate modules $A,B,C$ of ranks $a,b,c$, their coordinate duals, and three scalar lines $L_i=R\ell_i$. Use the spaces
$$
P=A\oplus L_1\oplus C^*,\qquad
Q=A^*\oplus B\oplus L_2,\qquad
U=L_3\oplus B^*\oplus C .
$$
The summands in each space are ordered by labels $1,2,3$. Let $T_0\in P\otimes_R Q\otimes_R U$ have the three identity-pairing tensors in label triples $(1,1,1),(2,2,2),(3,3,3)$:
$$
T_0=\sum_i a_i\otimes a_i^*\otimes\ell_3
      +\sum_j \ell_1\otimes b_j\otimes b_j^*
      +\sum_k c_k^*\otimes\ell_2\otimes c_k .
$$
Here each displayed list uses paired bases. Every output mode has full support, with its basis vectors witnessed by coordinate contractions against the other modes. The data submodule $E=A\otimes_R B\otimes_R C$ occupies label triple $(1,2,3)$. For an input $\bar T$ over $S$, output
$$
\mathcal L(\bar T)=T_0+tT\in P\otimes Q\otimes U
$$
where $T\in E$ is any lift. Since $t\operatorname{Ann}(t)=0$, the result is independent of the lift. Its reduction modulo $I$ equals $T_0$. The minor witnessing full mode support there lifts to a unit minor over $R$, since $I$ is nilpotent. Thus the output is also concise in the sense of surjective support flattenings.

## 2. Recognizing the arms intrinsically

Over any nonzero commutative base ring, the centroid of $T_0$ consists of triples of endomorphisms whose actions in their respective single modes give the same tensor. It is exactly $R^3$ acting by the same scalar in all three modes of each arm.

Indeed for distinct $i,j$, an off-diagonal map from arm $j$ to arm $i$ in the first mode contributes to the label triple $(i,j,j)$. The single action in the second mode contributes zero there. The first contribution displays the entries of the off-diagonal map in separate coordinates because the third and second factors of arm $j$ provide full first-mode support. Hence that block of the map vanishes. Applying this argument in each mode proves block diagonality. In each arm an endomorphism acts on its scalar line by a scalar. The centroid equations, using the full support in the other two modes, force those endomorphisms to be that same scalar times the identity.

An automorphism of $T_0$ conjugates the centroid and therefore permutes the three arms over every residue field. The positions of the rank-one summands distinguish the arms, since $a,b,c\ge2$. Consequently the induced automorphism of $R^3$ fixes its standard idempotents modulo every maximal ideal. An idempotent of $R$ vanishing modulo every maximal ideal is zero, and an idempotent equal to one modulo every maximal ideal is one. So the centroid idempotents are fixed over the base ring itself. These idempotents are the projections determining all three mode decompositions.

The stabilizer now has an explicit description. On arm 1 choose $g_A$ on $A$ and a unit $\lambda_3$ on $L_3$, and act by $\lambda_3^{-1}g_A^{-T}$ on $A^*$. On arm 2 choose $g_B$ on $B$ and a unit $\lambda_1$ on $L_1$, with $\lambda_1^{-1}g_B^{-T}$ on $B^*$. On arm 3 choose $g_C$ on $C$ and a unit $\lambda_2$ on $L_2$, with $\lambda_2^{-1}g_C^{-T}$ on $C^*$. This description is functorial under change of the base ring. In particular the group scheme over any field is the stated product. Its action on $E$ is $g_A\otimes g_B\otimes g_C$, without any of the three scalar parameters.

## 3. Every transporter of the deformations preserves the arms

Suppose a triple $G$ of invertible matrices carries $\mathcal L(\bar T)$ to $\mathcal L(\bar T')$. Modulo $I$, it stabilizes $T_0$, hence is block diagonal by Section 2. Inductively suppose $G$ is block diagonal modulo $I^j$, for $j\ge1$. Modulo $I^j$ its action preserves the direct-sum decomposition by label triples. The three same-label components of the transport equation therefore imply that $G$ fixes $T_0$ modulo $I^j$.

Use the stabilizer description to lift this reduction of $G$ to an exact stabilizer $\widehat G$ over $R$. All small group parameters lift, since $I^j$ is nilpotent. Then $G=\widehat G(1+X)$, where the three matrices $X$ have entries in $I^j$. Modulo $I^{j+1}$, terms with two factors of $X$ vanish, and terms applying $X$ to the coefficient-$t$ part vanish. The change of $T_0$ is therefore the sum of the three single-slot actions of $X$. The components with two equal arm labels and a third different one must vanish. In each such component the only term is a single off-diagonal block of one $X$ applied to one identity arm. The same coordinate-contraction argument as in Section 2 gives that this block is zero modulo $I^{j+1}$. Thus $G$ is block diagonal modulo $I^{j+1}$. Nilpotence completes the induction.

It follows that $G$ fixes $T_0$ exactly and its remaining equation, on $E$, is
$$
 t(g_A\otimes g_B\otimes g_C)T=tT'.
$$
This is the input transporter equation over $S$, since multiplying by $t$ has kernel $\operatorname{Ann}(t)$. Conversely lift the three input matrices to invertible matrices over $R$ and take all $\lambda_i=1$. The proper ideal $\operatorname{Ann}(t)$ lies in the maximal ideal, so a lift of an invertible matrix over $S$ has unit determinant. Over a nonlocal base ring the same argument identifies output transporters with lifts of input transporters.

If $R$ is finite local, this gives a counting reduction as well. Every transporter over $S$ yields exactly
$$
|R^\times|^3|\operatorname{Ann}(t)|^{a^2+b^2+c^2}
$$
transporters of the output, counting all choices of parameters. Witness recovery just restricts to the indicated three blocks and reduces them. The dense output only copies $T$ with a coefficient $t$ and writes fixed identity arms. Its side lengths are $a+c+1,a+b+1,b+c+1$. Over the indicated finite principal local rings all operations take polynomial bit time in the explicit coefficients and the description of the modulus. Over these principal local rings, cases with a mode of rank less than two can be decided by matrix equivalence via Smith normal form, or by shape comparison in an empty mode, and mapped to fixed positive or negative examples of rank at least two.

Over dual numbers, the data submodule $E$ is also a stabilizer-invariant direct summand of the first-order normal space to the orbit of $T_0$. The image of the differential of the group action has support only in label triples with at least two equal entries. The action of the stabilizer preserves every label triple, giving the direct summand claim. This identifies the entire ordinary three-mode action in a transverse part of the first-order deformation space.

### Fixed Gram matrices at a square-zero coefficient

When $t^2=0$, all three transpose-Gram matrices of $\mathcal L(\bar T)$ equal those of $T_0$ over $R$ itself. Indeed in any mode flattening, the support columns of the identity arms carry two equal arm labels, while the payload columns carry two distinct labels. Thus both cross terms in $F_i(\mathcal L(\bar T))F_i(\mathcal L(\bar T))^T$ vanish. The payload self-product vanishes by $t^2=0$.

In these coordinate bases the three Gram matrices of $T_0$ are diagonal, with ones on the paired-space coordinates and the arm dimensions on the respective scalar lines. For dual numbers over any field or for $\mathbb Z/p^2\mathbb Z$, the unrestricted residue-field input can be padded with at most one zero coordinate in each mode after the rank-one cases, so the three active dimensions are nonzero in the residue field. Such field padding preserves tensor equivalence: witnesses restrict to the images of the flattenings and then extend in each original mode. The resulting Gram matrices are invertible and are identical for every lift of the given format. This is a statement about ordinary tensor isomorphism on these inputs and about the equality of the displayed matrix descriptors. [MathProofs, Problem 1.8](https://github.com/Dugongue/MathProofs/tree/main/Problem18)



## 4. All algebra deformations of a three-vertex square-zero algebra

Let $k$ be a field. There is a complementary realization with no unused components in the associative-algebra deformation space. Define $D_0=k^3\oplus J$ with three diagonal idempotents and off-diagonal corners $e_0Je_1=X$, $e_1Je_2=Y$, and $e_0Je_2=Z$, of positive dimensions $a,b,c$. Give $J$ zero multiplication. Diagonal elements act at the indicated endpoints.

Let $R$ be a local Artinian principal ring with residue field $k$ and maximal ideal $(t)\ne0$. Consider unital associative $R$-algebras that are finite free and reduce to $D_0$. We compare the algebras without requiring that an isomorphism preserve a chosen identification of the reduction. Lift the three diagonal idempotents simultaneously. For a square-zero kernel this follows by correcting an approximate idempotent $u$ with $u+(1-2u)(u^2-u)$, then lifting the other idempotents in its complementary corner. Iteration along the powers of the nilpotent ideal proves the general case. The Peirce decomposition is a direct sum of finite projective, hence free, $R$-modules. Their ranks are the dimensions of the corresponding residue corners. Thus each diagonal is $Re_i$, all backward corners vanish and all forward corners have the prescribed ranks. There is exactly one potentially nonzero product of two off-diagonal corners, $X\times Y\to Z$. Its coefficients lie in $(t)$. Every choice of these coefficients is associative because any product of three strict corners vanishes.

Consequently every such lift is determined up to a choice of corner bases by $tM$, where $M:X\times Y\to Z$ is a bilinear tensor over $S=R/\operatorname{Ann}(t)$. To compare two lifts, observe that the commutator ideal is exactly the off-diagonal ideal $J_R$. Each strict corner element $x$ equals $[e_i,x]$ for its left endpoint, and the diagonal quotient is commutative. A lift isomorphism induces a permutation of the diagonal vertices over the local ring. The residue directed corner pattern with three positive forward arrows forces that permutation to fix the three vertices. Conjugation by $\sum_i f_i e_i$, for the image idempotents $f_i$ in the target, aligns the idempotents. This element is a unit congruent to $1$ modulo $J_R$ and satisfies $f_i u=u e_i$. After alignment the only equation is the bilinear transport of $tM$, equivalent to transport of $M$ over $S$. Conversely every $S$-transporter lifts. This classifies every finite free lift in the prescribed family.

For effective recovery from a raw table, reduce modulo the maximal ideal, form the span $J$ of commutators, and compute the quotient $D_0/J$. Since $J^2=0$, the quotient acts on $J$ on both sides. The left annihilator of $J$ in the quotient is exactly $k e_2$, and the right annihilator is exactly $k e_0$. Thus linear equations find those lines. If $v\ne0$ on one of the lines satisfies $v^2=\alpha v$, then $\alpha\ne0$ and $v/\alpha$ is its vertex idempotent. Subtracting the two recovered idempotents from $1$ gives $e_1$. Lift this system through the preimage of $J$ in the raw algebra, a nilpotent ideal since its square lies in $t$ times the algebra. Use the idempotent correction above. In each lifted corner, project the input basis vectors using the two idempotents, and choose a subset forming a basis modulo the maximal ideal. Nakayama's lemma and freeness give a basis of the corner. Divide the resulting coefficients of the single corner product by $t$ to read their classes over $S$.

This computes the inverse reduction deterministically in polynomial bit time for $\mathbb Z/p^e\mathbb Z$ and for the standard truncated polynomial rings over explicitly encoded finite fields. Each idempotent correction squares the current defect ideal, so only logarithmically many corrections in the nilpotence index are needed. Choosing all three corners requires finite-field linear algebra, with the idempotents found from annihilators even when the field size varies. Over the indicated rings division by $t$ is ordinary coordinate division or coefficient shifting.


For $R=k[\epsilon]/\epsilon^2$ the space of normalized first-order deformations is the whole of $\mathrm{HH}^2(D_0)$. Indeed use normalized Hochschild cochains relative to the separable diagonal $k^3$. The only nonzero two-fold composable tensor of strict corners is $X\otimes_kY$, whose output corner is $Z$. All three-fold compositions of strict corners vanish already in the relative cochains. The differential from degree one lands in zero because strict corner products in $D_0$ are zero and relative one-cochains preserve each corner. Thus
$$
\mathrm{HH}^2(D_0)=\operatorname{Hom}_k(X\otimes_kY,Z),
\qquad \mathrm{HH}^q(D_0)=0\quad(q\ge3).
$$
The base automorphism group acts on this space through the ordinary three independent corner maps. Inner automorphisms act trivially on Hochschild cohomology. Equivalently, conjugating idempotents before comparison puts every map into its corner form, as above. Deformations with marked base identification are represented by the individual elements of this space. Forgetting the identification takes their ordinary tensor orbits. This is an explicit case in which an unobstructed deformation space has an isomorphism comparison problem as general as unrestricted tensor isomorphism.

## Sources and status

This is an AI-assisted informal proof. The common-reduction tensor construction uses the same intrinsic centroid method as the earlier MathProofs derived-equivalence and ring constructions. The algebra side uses the classical description of first-order associative deformations by Hochschild cohomology and the relative bar resolution for a separable diagonal. Grochow–Qiao–Stange–Sun analyze five tensor actions over commutative rings, and the earlier MathProofs prime-power theorem embeds field TI in tensors that reduce to zero. The present tensor construction makes the common reduction concise with a specified smooth reductive stabilizer and proves exact recovery of every transporter. Publication priority for these refinements remains unverified. [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/html/2611.00735v1) · [Grochow–Qiao, Part I](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full) · [Huang–Lu–Ye–Zhang, Centers of multilinear forms and applications](https://arxiv.org/abs/2110.07915) · [Cibils et al., Hochschild cohomology of bound quiver algebras](https://arxiv.org/abs/2404.06916) · [Prime-power tensor isomorphism](https://github.com/Dugongue/MathProofs/tree/main/PrimePowerTensorIsomorphism)
