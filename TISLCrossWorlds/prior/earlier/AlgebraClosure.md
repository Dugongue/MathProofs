# Exact parity reductions with one-sided cube maps and ordered operators

[Prior regular form and group constructions](baseline/baseline/AlgebraWorlds.md) · [Atlas algebra entries](baseline/expansion/Algebra.md)

Work over \(\mathbb F_3\). Let \(H\) mean deterministic polynomial-time many-one \(\mathsf{TI}_{SL}\le_m\mathsf{TI}\) for dense three-tensors. All ordered frames in this note are part of the representations. The proof uses the unmarked alternating character construction and the symmetric typed character construction in the staged 234-entry atlas, especially the alternating construction in *Regular forms, extraspecial quotients, and determinant corrections*, the cube-zero compiler, and entries 82, 100–103, 107, 111–112 and 230 of the atlas. The two group reductions below require no ordinary alternating-group or graph-parity theorem.

## 1. Compact groups and the parity formula

An alternating bimap \(\gamma:Y\times Y\to Z\) with spanned output and zero common radical, together with a linear map \(\pi:Y\to Z\), defines a compact class-two three-group. Present it on ordered lifts of a basis of \(Y\) and an elementary abelian central \(Z\) by the commutators \(\gamma\) and cubes \(\pi\). Explicitly, in coordinates \((a,z)\in\{0,1,2\}^{\dim Y}\times Z\), the product has first coordinate \(a+b\bmod 3\), second coordinate \(z+w+c(a,b)\), where
\[
 c(a,b)=\sum_i\left\lfloor(a_i+b_i)/3\right\rfloor\pi(e_i)
   +\sum_{i>j}a_i b_j\gamma(e_i,e_j).
\]
Both the carry and bilinear terms satisfy the central two-cocycle equation. The commutator is \(\gamma\), and the cube of \((a,z)\) is \(\pi(a)\). The center and derived subgroup are exactly \(Z\) by the two bracket conditions. If \(\pi\ne0\) the group has exponent nine.

A group isomorphism induces \(g:Y\to Y'\), \(h:Z\to Z'\) satisfying \(h\gamma=\gamma'(g,g)\) and \(h\pi=\pi'g\). Conversely these conditions make the images of the generators respect the presented relations, and an induced quotient and center isomorphism gives a group isomorphism. On coordinate-ordered elements a group isomorphism has permutation sign \(\det g\,\det h\). It permutes the central fibers over \(g\), each of odd size, and acts on each fiber by \(h\) followed by a translation depending on its first coordinate. The translations are even, and there are an odd number of fibers. For an invertible map of a ternary coordinate space, transvections are even and negating one coordinate exchanges an odd number of pairs. Those maps generate the linear group, proving the formula.

Ordinary comparison of \((\gamma,\pi)\) reduces to ordinary TI by the fixed-arity typed compiler. Use duplicate input roles joined by an identity when encoding the repeated role of \(\gamma\). Its even comparison reduces to SL-TI by the exact character compiler, with weights one on \(Y,Z\) and zero on all auxiliary roles. These statements include the restrictions on \(\pi\) below. [Ordinary tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2) · [Group and tensor reductions](https://doi.org/10.1137/21M1441110)

## 2. Two new equivalent settings for H

**Theorem.** Each of the following compact group classes has ordinary isomorphism many-one equivalent to ternary TI. In either class, even isomorphism reduces to ordinary isomorphism if and only if \(H\) holds.

- Exponent-nine class-two groups with elementary abelian center equal to the derived group and **surjective** cube map \(G/Z\to Z\).
- Exponent-nine class-two groups with elementary abelian center equal to the derived group and **injective** cube map \(G/Z\to Z\).

No center, line, additive basis, or extraspecial quotient is fixed by isomorphisms. The coordinate basis only defines the represented group and the sign. The maps below preserve exactly which determinant signs occur. Thus an ordinary comparison that distinguishes every pair in either outward class would close the original problem.

The seed for both maps is the unmarked alternating character construction. For any one specified character of a ternary three-tensor, it produces a spanned alternating bracket \(\beta:X\times X\to W\) with zero common radical and exact total determinant \(\det g_X\det h_W\) equal to the character on the original transporter set. Its ambient dimension \(\dim X\) is even, as it is the sum of the main role space, its dual, and symplectic blocks. The high-rank marker construction permits increasing the marker ranks by any sufficiently large even increments. Its parity congruences only concern the individual block half-ranks, output-copy count, and the product scalars. In particular the number of markers can be even: add an otherwise unused marker whose half-rank is odd. The old requirement that the number of markers be odd made an associated unital algebra even-dimensional, which is unnecessary in this group seed. Since the nonmarker output dimension is even, one can freely require \(\dim W\) even. Every marker line is individually intrinsic by the subset sums of the distinct scalar-slice ranks. This uses boundedly many markers and linear dimension overhead for fixed arity and fixed field.

A nonempty ordinary transporter determinant set is an affine coset in the three ternary signs. It contains the identity tuple if and only if every determinant character attains \(1\), by separation in the quotient by its determinant stabilizer. The trivial character detects the empty set. Thus a constant conjunction of exact character queries suffices. Once the queries are ordinary, apply ordinary TI AND. For the ordinary lower reductions use only the trivial character.

### Surjective cube map

Take a seed \(\beta:X\times X\to W\) with \(w=\dim W\) even and a specified intrinsic marker line \(\mathbb F_3 z_0\). Put
\[
 Y=X\oplus W^*\oplus W,\qquad Z=W.
\]
Let \(\pi\) be the identity from the last \(W\) to \(Z\) and zero elsewhere. Define \(\gamma\) to be \(\beta\) on \(X\times X\), the evaluation \(\gamma(r,s)=r(s)z_0\) for \(r\in W^*\), \(s\) in the last \(W\), and zero on the other blocks, using skew symmetry. The bracket spans \(Z\) and has zero common radical. The asserted surjectivity and nonzero exponent follow immediately.

For every transporter, \(K=\ker\pi=X\oplus W^*\) is intrinsic and the common radical of the restriction \(\gamma|_{K\times K}\) is \(R=W^*\). On \(K/R\) and \(Z\) the induced maps \(g_X,h\) transport the original bracket. The products of \(R\) with \(Y\) span precisely \(\mathbb F_3z_0\), so its scale is some \(\alpha\in\{\pm1\}\). The quotient map on \(Y/K\) agrees with \(h\) via \(\pi\). The map on \(R\) is \(\alpha h^{-\mathsf T}\) by evaluation, of determinant \(\det h\) as \(w\) is even. The determinant on \(Y\oplus Z\) is therefore
\[
 \det g_X\cdot(\det h)\cdot(\det h)\cdot(\det h)=\det g_X\det h .
\]
The formula uses compatible ordered frames and remains true with off-diagonal maps by multiplicativity in this flag. Conversely any seed transporter sends the intrinsic marker line to the target marker line and lifts with these three block maps and \(h\) on \(Z\). All target ordinary and even comparisons therefore reflect and lift exactly.

### Injective cube map

Take a seed \(\beta:X\times X\to W\) with \(n=\dim X\) even and \(n>\dim W+1\), ensured by increasing anchor ranks. Write
\[
 Y=X\oplus\mathbb F_3 c\oplus\mathbb F_3 u\oplus\mathbb F_3 v,
 \qquad
 Z=Y'\oplus W\oplus X',
\]
where \(Y'\) and \(X'\) are ordered copies. Let \(\pi:Y\to Y'\subset Z\) be the identity. The bracket projected to \(W\oplus X'=Z/\pi(Y)\) is \(\beta\) on \(X\times X\), \(\overline{\gamma}(c,x)=x'\), and zero elsewhere, extending by skew symmetry. Its \(Y'\)-component is
\[
 \gamma_{Y'}(u,x)=x',\qquad
 \gamma_{Y'}(u,v)=c',\qquad
 \gamma_{Y'}(c,u)=u',\qquad
 \gamma_{Y'}(c,v)=v',
\]
where each prime in these four \(Y'\)-component equations means the copy in \(Y'\). The remaining components are zero. The displayed products spanning \(Y'\) have zero projection in \(W\oplus X'\), and the products spanning the latter have zero \(Y'\)-component. Thus the full image spans \(Z\). The projected bracket has common radical \(\langle u,v\rangle\). In the full bracket a nonzero \(u\)-coefficient is detected by pairing with \(X\), and a nonzero \(v\)-coefficient thereafter by pairing with \(u\). Thus the full common radical is zero.

The radical \(\langle u,v\rangle\) of the projected bracket is intrinsic, leaving the quotient \(X\oplus\mathbb F_3 c\). In this quotient \(X\) is exactly the set whose multiplication slice has rank at most \(\dim W+1\). For \(x\in X\), the slice maps \(X\) into \(W\), and the extra \(c\)-column increases the rank by at most one. For \(x+a c\) with \(a\ne0\), the restriction to \(X\) already surjects onto \(X'\) modulo \(W\). Hence an ordinary group transporter induces a seed transporter \(g_X,h_W\), with \(W\) recovered as the image of \(X\times X\). On the remaining \(X'\) quotient the transporter is \(\tau g_X\), where \(\tau\) is its scale on the \(c\)-line modulo \(X\). Its determinant is \(\det g_X\) because \(n\) is even. Finally the action on \(\pi(Y)\) equals that on \(Y\); their two determinants square to one in the parity formula. The group determinant is precisely \(\det h_W\det g_X\). Every seed transporter lifts: act as \(g_X\) on \(X\), fix \(c,u,v\), act by the same \(Y\)-map on \(Y'\), and by \(h_W,g_X\) on \(W,X'\). All defining equations then hold.

These formulas prove both group equivalences. They also refute the weaker proposed lemma that a surjective or injective cube map alone always absorbs the orientation. Take the seed with trivial character, so every transport of the self-pair has total sign \(+1\). Apply a single reflection to the output coordinates away from the selected marker vector. The ordinary relative isomorphism exists and every relative sign is negative. The two constructions give this same negative sign in either group family. The coordinate matrix of the cube map is identical at both endpoints. In contrast, if the cube map is **both** surjective and injective, then every group transporter has sign \(+1\) in \(\pi\)-aligned frames, because the determinant factors are identical. A small-defect version is the earlier logarithmic exterior-algebra criterion.

## 3. A one-query sufficient criterion from ordered operator modules

**Theorem.** For any fixed-arity ternary tensor system with specified commuting-to-target **ordered linear operator constraints**, one weighted determinant-character comparison reduces to ordinary TI under the condition below. The operator constraints may be arrows between different roles. There is no bound on the total dimension of even determinant-contributing modules.

Make \(M\) the direct sum of tested and auxiliary roles. Regard all role idempotents and ordered linear arrows as operators on \(M\), acting by zero on the unused blocks. Let \(R\) be the algebra they generate in \(\operatorname{End}(M)\). A transporter has to commute to the same ordered generator, not just send the algebra collectively to the other algebra. Find one reference isomorphism of the two ordered operator modules by constructive module isomorphism, or reject if none. Use this reference to identify them with a common \(M\), recording its weighted determinant in the original role frames.

Put \(E=\operatorname{End}_R(M)\) and \(E/\operatorname{rad}E=\prod_i M_{a_i}(K_i)\). Lift one primitive idempotent \(e_i\) from each block and set \(P_i=e_iM\). Its multiplicity is \(a_i\). If the desired weight of role \(v\) is \(b_v\in\mathbb Z/2\), define \(d_i=\sum_v b_v\dim_{K_i}(P_i)_v\). The dimensions make sense after a lift of \(K_i\) into the corner \(e_i E e_i\), whose existence follows from separability. The hypothesis is \(a_i=O(\log L)\) for every \(i\) for which \(d_i\) is odd, with \(L\) the written input length and fixed implicit constant.

Here are the determinant computation and the ordinary compiler. An allowed unknown on \(M\) is \(h\in E^\times\). Write \(Q=E/\operatorname{rad}E\) and \(\bar h_i\) for its chosen simple quotient maps. Its weighted determinant equals
\[
 \prod_i N_{K_i/\mathbb F_3}(\det_{K_i}\bar h_i)^{d_i}.
\]
Indeed \(1+\operatorname{rad}E\) is unipotent on each role. In each simple quotient factor, lift full matrix units in \(E\) and a finite-field section in the first diagonal corner. Elementary transvections are then lifted by \(1+T\) with \(T^2=0\) and determinant one. A generator acting by a scalar \(\delta\) on one lifted copy of \(P_i\), identity elsewhere, gives determinant \(N(\delta)^{\dim_{K_i}(P_i)_v}\) on each role. These lifts generate the determinants in the quotient and establish the formula.

The \(K_i^{a_i}\) multiplicity module is intrinsic for this ordered-operator model:
\[
 M_i=\operatorname{Hom}_R(P_i,M)/(\operatorname{rad}E)e_i
       \cong Q\bar e_i.
\]
Extend a map \(P_i\to M\) by zero on the complementary summand of \(M\) to identify the numerator with \(E e_i\). The unknown acts by postcomposition, and the residue field acts on the right by precomposition. Include each \(P_i\) as a fixed auxiliary space, its evaluation with \(\operatorname{Hom}_R(P_i,M)\), and the known subspace and quotient maps defining \(M_i\). These are linear and bilinear tensor constraints. Evaluation forces the indicated action on the same unknown \(h\) used for the original tensor constraints. It makes no requirement that \(h\) fix an arbitrarily chosen matrix-unit system on \(M\). For each odd \(d_i\) include \(\bigwedge_{K_i} M_i\) and its top line. Their dimensions over \(\mathbb F_3\) are bounded by \([K_i: \mathbb F_3]\,2^{a_i}\). Link all Frobenius copies of the top line by the \(\mathbb F_3\)-linear coordinate maps \(x\mapsto x^{3^j}\), and multiply them along a binary tree. The induced scalar is its norm to \(\mathbb F_3\). Include the scalar subline and multiply the resulting \(\mathbb F_3\) lines. A point mark imposes exactly the required product sign, calibrated by the initial reference.

All auxiliary algebras are constructed explicitly in polynomial time by finite-field algebra algorithms. Use separate labels for the polynomially many occurrences; the atlas's two-fixed-operator packing puts them in a constant tensor signature. The usual tensor-system compiler then gives one ordinary TI instance. Any original weighted transporter extends to the typed system by all the specified induced maps. Any ordinary transporter of the diagram obeys the exact weighted formula on the original roles. This proves both directions. The single arrow \(\pi:Y\to Z\) gives the previous kernel/cokernel condition as a special case: the nonzero-rank indecomposable arrow has two copies in the weighted determinant and cancels. [Brooksbank and Luks, constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf) · [Ivanyos and Qiao, finite-field algebra decomposition](https://arxiv.org/html/1708.03495) · [Ordinary compiler](https://arxiv.org/html/2306.03135v2)

### A sufficient missing construction and a falsifier of the immediate version

It would suffice to give an explicit polynomial recoding of the marked regular alternating carrier into a tensor system with ordered linear operators, for each one output-sign comparison, retaining the exact output-sign transporter set under the recoding and having logarithmic multiplicities at every odd contribution. The previous theorem would compile the recoded pair to ordinary TI, and the fixed character conjunction would prove \(H\). This condition is about supplied operators that really intertwine with the original transporters or with certified lifts. Arbitrarily choosing a convenient flag and discarding other transporters gives no such certificate.

The version that simply adds intrinsic commuting operators on the **same** output role without losing any ordinary transporters is false, even on orientation-rigid carriers. Let \(V\) be an even-dimensional standard symplectic space over \(\mathbb F_3\). Feed the alternating typed compiler the nonsingular form on \(V\), with its scalar output line fixed by field multiplication. Use one copy of \(V\) in the weighted output and even copy counts for any auxiliary variable roles. If a second copy of \(V\) is needed as a distinct input role to the alternating template, its identity link makes its map the same, and its even output-copy count does not alter the following argument. Take the regular mark. Every typed transporter induces a symplectic \(V\)-map, so all marked output determinants are \(+1\). The explicit lifts of \(\operatorname{Sp}(V)\) act on the output as an odd number of copies of their natural module and a collection of trivial lines.

Any endomorphism commuting with all these lifts must preserve that direct sum. The element \(-I_V\) forbids off-block maps between natural and trivial components. The centralizer on the natural module is scalar, as commuting with each symplectic transvection preserves its one-dimensional displacement image, and an operator preserving every line is scalar. Thus on the natural isotypic block the added operators act as \(I_V\otimes A_j\) on \(V\otimes P\) with \(\dim P\) odd. Some indecomposable operator-module summand of \(P\) has odd \(\mathbb F_3\)-dimension, hence odd \(\dim_{K_i}P_i\). In \(V\otimes P\) it occurs at least \(\dim V\) times as an ordered operator module. The logarithmic bound fails. An odd output-basis conjugation with the covector correspondingly conjugated gives a genuine relative signed NO in this same family, while ordinary marked transport exists. This also explains the failure of replacing the output by a uniform nilpotent-chain replication: an even chain kills its sign, and an odd chain leaves the same unbounded multiplicity.

The two exponent-nine equivalences and the ordered-operator criterion do not establish \(H\). Square-zero relational parity from the atlas is an exact parity transfer, and its graph oracle computations are adaptive; it supplies no ordinary many-one elimination for the remaining module action. The new group carriers isolate the obstruction on just the kernel or just the cokernel of an elementary abelian cube map, and the operator criterion gives an unconditional ordinary reduction wherever the stated multiplicity bound holds.


## 4. Low-degree natural volume decorations cannot give the missing construction

**Proposition.** Let \(V=\mathbb F_3^n\). For a subquotient \(M\) of a finite direct sum of mixed tensor powers \(V^{\otimes a}\otimes(V^*)^{\otimes b}\) with \(a+b<n\), one has \(M^{\mathrm{SL}(V)}=M^{\mathrm{GL}(V)}\). Here the powers and subquotients carry their prescribed natural actions.

Let \(D\cong(\mathbb F_3^\times)^n\) be the diagonal signs in a basis. Its representations split into weights because its order is prime to \(3\). A tensor word contributes a sign character with a coordinate parity vector recording occurrences of that basis index, equally for dual positions. Since the total occurrence count is less than \(n\), no weight vector can have all coordinates odd. The characters trivial on \(D\cap\mathrm{SL}(V)\) are exactly the all-zero and all-odd vectors, by pairing positions with two sign flips. Thus an \(\mathrm{SL}(V)\)-fixed vector is also fixed by all of \(D\). The same weight bound passes to submodules and quotients, since the diagonal representations are semisimple. Together \(D\) and \(\mathrm{SL}(V)\) generate \(\mathrm{GL}(V)\), by multiplying any odd determinant by a single coordinate reflection.

In particular, suppose a proposed universal marking mechanism allows every even matrix to act on auxiliary roles by the induced natural actions of mixed degree at most \(d\). Suppose it imposes all new markings by fixed tensors of order at most three in these roles and their duals. Each marking is then an invariant in a subquotient of mixed degree at most \(3d\). If \(3d<n\), retaining all even actions automatically retains odd coordinate reflections. Therefore such markings do not enforce the universal orientation, even with arbitrarily many low-degree natural occurrences. This condition does not apply to arbitrary auxiliary actions or transporter-dependent lifts.

## 5. Bounded controls

For the two new group maps, I tested a six-dimensional bracket with two distinct marker ranks into a two-dimensional output, all four combinations of the independent block similitude signs, and both choices of cube-map direction. The eight lifts passed 724 bracket identities, 76 cube-map identities, and eight exact determinant comparisons, with spanned output and zero common radical in every case. For the injective construction, the rank criterion gave the claimed \(X\) on all \(3^7=2{,}187\) vectors of the projected seven-dimensional quotient. This tests the new algebraic maps, rather than the unrestricted decision problem.
