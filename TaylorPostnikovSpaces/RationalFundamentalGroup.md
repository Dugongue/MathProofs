# A complete characterization for simple two-types with rational fundamental group

**PROVED — let \(W\) be a pointed connected simple CW complex with \(\pi_iW=0\) for \(i>2\), let \(V=\pi_1W\) be any rational vector space, and let \(B=\pi_2W\) be any abelian group. Then normalized Taylor, H-space, vanishing Postnikov invariant, and splitting as \(K(V,1)\times K(B,2)\) are equivalent. No finite-generation hypothesis or localization input is used. Confidence: 0.98.**

All constructions and arguments specific to this theorem are written below. The numbered foundational results imported are stated where used and collected at the end.

## 1. Statement and normalization

All spaces and homotopies are pointed. An H-structure is a map \(\mu:W^2\to W\) whose restriction to \(W\vee W\) is pointed homotopic to the fold.

A normalized \(r\)-ary operation, for \(r\geq1\), is a map \(t:W^r\to W\) with \(t\Delta_r\simeq\operatorname{id}_W\). For a word \(\alpha\in\{x,y\}^r\), define \(d_\alpha:W^2\to W^r\) by selecting the indicated coordinate projection at each input. The operation is Taylor if, for every input \(i\), there exist words \(\alpha,\beta\) with \(\alpha_i\ne\beta_i\) and \(td_\alpha\simeq td_\beta\).

**Theorem 1.1 — PROVED below; confidence 0.98.** Under the hypotheses in the opening statement, the following are equivalent:

1. \(W\) admits a normalized Taylor operation.
2. \(W\) admits an H-structure.
3. Its principal Postnikov invariant \(k\in H^3(K(V,1);B)\) is zero.
4. \(W\simeq K(V,1)\times K(B,2)\).

**PROVED clarification; confidence 1.00.** The normalization is necessary in condition 1: without it, a constant operation satisfies all the stated variable-identification identities on every space.

## 2. Homology of a rational abelian group, including infinite dimension

We first establish the required natural homology calculation, with no restriction on the dimension of \(V\).

**Lemma 2.1 — PROVED; confidence 0.99.** For every rational vector space \(V\) and every \(j\geq1\), there is a natural isomorphism
\[
H_j(K(V,1);\mathbb Z)\cong\Lambda_{\mathbb Q}^jV.
\tag{2.1}
\]
The homology group in degree zero is \(\mathbb Z\).

**Proof.** We use an explicit functorial classifying-space model. For an abelian group \(A\), its bar simplicial set has \(n\)-simplices \(A^n\). Its faces are
\[
d_0(a_1,\ldots,a_n)=(a_2,\ldots,a_n),\quad
d_n(a_1,\ldots,a_n)=(a_1,\ldots,a_{n-1}),
\]
and, for \(0<i<n\),
\[
d_i(a_1,\ldots,a_n)
=(a_1,\ldots,a_i+a_{i+1},\ldots,a_n).
\]
Its degeneracies insert a zero coordinate. This is the bar construction \(\overline W K(A,0)\); May (1967), Theorem 23.2, identifies it as a simplicial \(K(A,1)\), and Theorem 16.6 identifies the homotopy groups of its realization. We denote the realization by \(BA\). By May (1967), Theorem 14.1, it is a CW complex with one cell for each nondegenerate simplex. Its normalized cellular chain group in degree \(n\) is therefore free on the tuples \((a_1,\ldots,a_n)\) having no zero coordinate, with boundary the alternating sum of the faces just displayed, omitting degenerate terms. Every group homomorphism induces the corresponding map on these chain complexes.

Let \(\mathcal L(V)\) consist of subgroups generated over \(\mathbb Z\) by a finite rationally linearly independent list in \(V\), ordered by inclusion. Each such subgroup is explicitly free abelian on that list. Every finite set of vectors lies in one such subgroup: choose a rational basis of their finite-dimensional span and divide those basis vectors by a common denominator for all the coordinates in the finite set. The same construction applied to the two finite bases of any two members gives a larger member containing both. Thus \(\mathcal L(V)\) is directed and covers \(V\). The normalized bar chain complex of \(V\) is consequently the directed union of the bar chain complexes of these free subgroups.

Homology commutes with this directed union in the present explicit sense. A cycle is a finite sum of bar simplices, so all its entries belong to one \(L\); it is already a cycle there, since the boundary formulas do not leave that subgroup. If its class becomes zero in the full complex, a finite chain witnessing this also uses only finitely many entries and therefore belongs to a larger member of \(\mathcal L(V)\). These two observations prove
\[
H_j(BV;\mathbb Z)=\underset{L\in\mathcal L(V)}{\operatorname{colim}}H_j(BL;\mathbb Z).
\tag{2.2}
\]

For a free abelian group \(L\) of finite rank \(s\), the torus \(T^s\) is a \(K(L,1)\), after choosing a basis: its universal cover is \(\mathbb R^s\). There is a map \(BL\to T^s\) inducing this identification of fundamental groups. One can construct its coordinates by \(H^1\)-representability, May–Ponto (2012), Equation (3.4.1), and the natural UCT, Hatcher (2002), Theorem 3.2. It is a homotopy equivalence by Whitehead's theorem, Hatcher (2002), Theorem 4.5.

The torus cellular chain complex has a cell for each subset of its circle factors, with all differentials zero. Its integral cohomology is the exterior algebra on its degree-one coordinate classes: the coordinate squares vanish because they pull back from \(H^2(S^1;\mathbb Z)=0\), and products over distinct coordinates are a basis by the integral cohomological Künneth theorem under its finite-free hypothesis, Hatcher's cited online edition, Theorem 3.15. This also proves naturality of the corresponding homology calculation. Indeed, a homomorphism between two free abelian groups is realized by the torus map whose circle coordinates are the integer monomials specified by its matrix. It acts on degree-one cohomology by the transpose matrix and hence on products by its exterior powers. Dualizing these finite free groups gives its exterior-power action on homology. Maps between the corresponding \(K(L,1)\)'s are homotopic if they induce the same fundamental-group map, by the same \(H^1\)-representability and UCT. We have therefore obtained the natural identification
\[
H_j(BL;\mathbb Z)=\Lambda_{\mathbb Z}^jL.
\tag{2.3}
\]

Exterior powers over \(\mathbb Z\) commute with these directed unions. To see surjectivity directly, a wedge uses finitely many group elements and thus belongs to one subgroup. To see injectivity, an equality between finite expressions in the exterior power is generated by finitely many multilinearity and alternating relations; all elements in such a witness belong to a larger member of \(\mathcal L(V)\). Equations (2.2) and (2.3) consequently identify \(H_j(BV;\mathbb Z)\) with \(\Lambda_{\mathbb Z}^jV\). This identification is natural: a homomorphism of rational vector spaces sends the finite basis of any member of \(\mathcal L(V)\) into a finite set contained in a member of the corresponding target family, and (2.3) is natural for that homomorphism between free abelian subgroups.

Finally, the canonical map
\[
\Lambda_{\mathbb Z}^jV\longrightarrow\Lambda_{\mathbb Q}^jV
\tag{2.4}
\]
is an isomorphism for \(j\geq1\). It is enough to verify this for finite-dimensional rational subspaces: every wedge and every finite relation involves only finitely many vectors. For \(U=\mathbb Q^s\), the lattices \(L_n=(1/n!)\mathbb Z^s\) are cofinal among finitely generated subgroups. Inside \(\Lambda_{\mathbb Q}^jU\), their exterior powers are
\[
(1/(n!)^j)\mathbb Z^{\binom{s}{j}}.
\]
Their union is the full rational vector space, since any fixed denominator divides \((n!)^j\) for sufficiently large \(n\). This proves (2.4) in finite dimension and then for arbitrary \(V\) by the finite-subspace argument. Every identification used the canonical maps induced by inclusions or group homomorphisms, so (2.1) is natural. \(\square\)

## 3. Two natural algebraic identifications

For an abelian group \(C\), define
\[
E_C=\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,C),
\qquad
J_C=\operatorname{Hom}_{\mathbb Z}(\mathbb Q,C).
\]

**Lemma 3.1 — PROVED; confidence 0.99.** Both \(E_C\) and \(J_C\) are canonically rational vector spaces, with multiplication by \(a\in\mathbb Q\) defined by precomposition with multiplication by \(a\) on \(\mathbb Q\). For every rational vector space \(U\), there are natural isomorphisms
\[
\operatorname{Ext}^1_{\mathbb Z}(U,C)
\cong\operatorname{Hom}_{\mathbb Q}(U,E_C),
\tag{3.1}
\]
and
\[
\operatorname{Hom}_{\mathbb Z}(U,C)
\cong\operatorname{Hom}_{\mathbb Q}(U,J_C).
\tag{3.2}
\]

**Proof.** We give the free-resolution details used in (3.1). Let \(F_{\mathbb Q}=\bigoplus_{n\geq1}\mathbb Ze_n\), with \(e_n\mapsto1/n!\) under its surjection to \(\mathbb Q\). Its kernel is free on
\[
u_n=e_n-(n+1)e_{n+1}.
\]
For generation, reduce a finite sum supported through \(e_N\) by these relations to a multiple of \(e_N\); if its rational image is zero, that multiple is zero. For independence, a finite nonzero relation among the \(u_n\)'s has a largest index \(N\), whose coefficient of \(e_{N+1}\) cannot vanish. Thus this is a free resolution of length one.

For \(U\) with a rational basis \((u_i)_{i\in I}\), take the direct sum over \(I\) of this resolution. Write it as \(0\to K_U\to F_U\to U\to0\). The Ext group is the cokernel
\[
\operatorname{Ext}^1(U,C)
=\operatorname{coker}\bigl(\operatorname{Hom}(F_U,C)
\longrightarrow\operatorname{Hom}(K_U,C)\bigr).
\tag{3.3}
\]
This is the free-resolution definition of Ext used in the UCT.

We record explicitly the additivity and naturality in the first argument. A homomorphism \(f:U\to U'\) lifts to \(F_U\to F_{U'}\) because \(F_U\) is free. It maps \(K_U\) into \(K_{U'}\), and restriction followed by precomposition defines \(f^*\) on (3.3). Two choices of lift differ by a homomorphism \(F_U\to K_{U'}\). Precomposition with this difference represents a homomorphism on \(K_U\) that extends to \(F_U\), so it is zero in the cokernel. This proves independence of the lift. Lifting a composite by the composite of lifts proves functoriality. Lifting \(f+g\) by the sum of two lifts proves \((f+g)^*=f^*+g^*\). Applying the same construction to identity maps between two free resolutions shows that the construction is independent of the chosen resolution.

Let \(\mu_a:\mathbb Q\to\mathbb Q\) multiply by \(a\). Define \(a\xi=\mu_a^*\xi\) on \(E_C\). Additivity, functoriality, and \(\mu_1=\operatorname{id}\) verify the rational-module laws. In particular multiplication by a nonzero integer has inverse induced by its reciprocal. The same argument for the contravariant additive functor \(\operatorname{Hom}(-,C)\) gives the asserted rational structure on \(J_C\).

For \(u\in U\), let \(\alpha_u:\mathbb Q\to U\) send \(a\) to \(au\). Define
\[
\Theta_U(\xi)(u)=\alpha_u^*\xi.
\]
Since \(\alpha_{u+v}=\alpha_u+\alpha_v\) and \(\alpha_{au}=\alpha_u\mu_a\), the established additivity and functoriality show that \(\Theta_U(\xi)\) is rational linear.

To prove \(\Theta_U\) is an isomorphism, use the basis chosen above. The Hom groups in (3.3) become products of their one-dimensional counterparts. The image of the resulting product map is the product of the images: a preimage for each coordinate can be selected independently. Therefore its cokernel is the product of the coordinate cokernels. This identifies
\[
\operatorname{Ext}^1\left(\bigoplus_{i\in I}\mathbb Q,C\right)
=\prod_{i\in I}E_C.
\]
Under this identification, \(\Theta_U\) sends a class to its values on the basis \(u_i\). These are exactly the unrestricted coordinates specifying an element of \(\operatorname{Hom}_{\mathbb Q}(U,E_C)\). Thus \(\Theta_U\) is an isomorphism. Its definition using \(\alpha_u\) is independent of the basis, and
\[
\Theta_U(f^*\xi)(u)=\Theta_{U'}(\xi)(f(u))
\]
proves naturality.

For (3.2), send \(h:U\to C\) to the map
\[
\Phi_U(h)(u)(a)=h(au),\qquad a\in\mathbb Q.
\]
It is rational linear in \(u\) with the stated rational structure on \(J_C\). Its inverse evaluates at \(1\): given \(\theta:U\to J_C\), put \(h(u)=\theta(u)(1)\). Rational linearity gives
\[
\theta(u)(a)=\theta(au)(1)=h(au),
\]
so both composites are identities. The defining formula also proves naturality. \(\square\)

## 4. Splitting an arbitrary coefficient group

**Lemma 4.1 — PROVED; confidence 0.99.** Every abelian group \(B\) admits a direct-sum decomposition
\[
B=D\oplus R
\tag{4.1}
\]
such that \(D\) is divisible and injective, \(\operatorname{Hom}(\mathbb Q,R)=0\), and \(\operatorname{Ext}^1(U,D)=0\) for every rational vector space \(U\).

**Proof.** Let \(D\) be the sum of all divisible subgroups of \(B\). This sum is divisible: an element is a finite sum of elements of divisible subgroups, and an \(n\)-th root can be chosen in each such subgroup and then added. Thus \(D\) contains every divisible subgroup and is itself divisible.

We prove injectivity directly. Suppose \(A\subseteq C\) are abelian groups and \(f:A\to D\) is a homomorphism. Partially order its extensions \(g:A'\to D\), where \(A\subseteq A'\subseteq C\), by extension. The union of a chain is an extension, so Zorn's lemma gives a maximal one. If \(c\in C\setminus A'\), the subgroup \(\{n\in\mathbb Z:nc\in A'\}\) is either zero or \(d\mathbb Z\) for a positive integer \(d\). In the zero case choose \(y=0\). In the second case choose \(y\in D\) with \(dy=g(dc)\), using divisibility. In both cases define
\[
g'(a+nc)=g(a)+ny,\qquad a\in A',\ n\in\mathbb Z.
\]
If two expressions agree, their difference has \((n-n')c\in A'\). In the zero case this forces \(n=n'\). In the second case \(n-n'=kd\), and
\[
g((n-n')c)=k g(dc)=kdy=(n-n')y,
\]
which proves well-definedness. The formula gives a homomorphism extending \(g\) to the strictly larger group \(A'+\mathbb Zc\), a contradiction. Hence \(f\) extends to all of \(C\). This proves injectivity.

Apply this extension property to \(\operatorname{id}_D:D\to D\) along \(D\subseteq B\). It gives a retraction \(\rho:B\to D\). With \(R=\ker\rho\), every \(b\in B\) is the sum \(\rho(b)+(b-\rho(b))\), and \(D\cap R=0\). This proves (4.1).

If \(h:\mathbb Q\to R\), its image is divisible: an \(n\)-th root of \(h(a)\) is \(h(a/n)\). Its image is therefore a subgroup of \(D\), by the definition of \(D\), and also a subgroup of \(R\). Hence it is zero. Finally, any map \(K_U\to D\) in the resolution (3.3) extends to \(F_U\) by injectivity. The cokernel in that formula is zero, proving the last assertion. \(\square\)

No canonical splitting in (4.1) is claimed or needed. Choose one for the remainder of the proof.

## 5. The two forms encoding the Postnikov invariant

Put \(X=K(V,1)\). Hatcher (2002), Theorem 2A.1, identifies \(H_1(W;\mathbb Z)\) with the abelianization of \(\pi_1W\), which here is \(V\). A map \(q:W\to X\) inducing the given identification of fundamental groups consequently exists by \(H^1\)-representability and the degree-one UCT. Its homotopy fiber has only one nonzero homotopy group, namely \(B\) in degree two, by the homotopy-fiber exact sequence, May–Ponto (2012), Corollary 2.2.3. It is therefore \(K(B,2)\). Simplicity of \(W\) says the action on this fiber group is trivial. May–Ponto (2012), Lemma 3.4.2, then gives a classifying map
\[
k:X\longrightarrow K(B,3)
\]
and a fiberwise equivalence \(W\simeq\operatorname{hofib}(k)\) over \(X\). We use the same symbol \(k\) for its class in \(H^3(X;B)\). The explicit path-fiber model consists of \((x,\gamma)\), where \(\gamma\) runs from \(k(x)\) to the basepoint.

**PROVED lifting criterion; confidence 0.99.** For any pointed \(a:T\to X\), a pointed lift up to homotopy through \(q\) exists if and only if \(a^*k=0\).

**Proof.** A lift makes \(ka\) nullhomotopic because \(kq\) is nullhomotopic by the path defining the fiber. Conversely, if \(a^*k=0\), representability makes \(ka\) pointed nullhomotopic. A chosen nullhomotopy \(N\) gives the lift \(t\mapsto(a(t),N(t,-))\) in the path-fiber model. Transport across the chosen equivalence gives the required lift to \(W\). \(\square\)

The splitting \(B=D\oplus R\) gives \(k=(k_D,k_R)\). Cohomology respects this finite direct sum because its cochain Hom groups do so. By Lemma 2.1 and the natural UCT in degree three,
\[
0\to\operatorname{Ext}^1(\Lambda_{\mathbb Q}^2V,C)
\to H^3(X;C)
\to\operatorname{Hom}(\Lambda_{\mathbb Q}^3V,C)\to0.
\tag{5.1}
\]
For \(C=R\), the right group is zero: restrict a homomorphism to each rational line and use \(\operatorname{Hom}(\mathbb Q,R)=0\). For \(C=D\), the left group is zero by Lemma 4.1. Lemma 3.1 therefore supplies natural identifications
\[
H^3(X;R)\cong
\operatorname{Hom}_{\mathbb Q}(\Lambda_{\mathbb Q}^2V,E_R),
\qquad E_R=\operatorname{Ext}^1(\mathbb Q,R),
\tag{5.2}
\]
and
\[
H^3(X;D)\cong
\operatorname{Hom}_{\mathbb Q}(\Lambda_{\mathbb Q}^3V,J_D),
\qquad J_D=\operatorname{Hom}(\mathbb Q,D).
\tag{5.3}
\]
Write the corresponding alternating forms as
\[
\omega_2:V^2\to E_R,\qquad
\omega_3:V^3\to J_D.
\tag{5.4}
\]
Both forms are rational multilinear. In particular, the target of the trilinear form is the rational vector space \(J_D\), not the possibly torsion group \(D\).

**Lemma 5.1 — PROVED; confidence 0.99.** The following probes and lifts have the stated properties.

(a) Every map \(a_u:K(\mathbb Q,1)\to X\) induced by \(s\mapsto su\) lifts through \(q\).

(b) For \(a_{u,v}:K(\mathbb Q^2,1)\to X\) induced by \((s,t)\mapsto su+tv\), the pullback \(a_{u,v}^*k_R\) is the element \(\omega_2(u,v)\) under the natural identification
\[
H^3(K(\mathbb Q^2,1);R)=E_R.
\]

(c) If \(k_R=0\), every such \(a_{u,v}\) lifts through \(q\).

(d) For \(a_{u,v,w}:K(\mathbb Q^3,1)\to X\), the pullback \(a_{u,v,w}^*k_D\) is \(\omega_3(u,v,w)\) under
\[
H^3(K(\mathbb Q^3,1);D)=J_D.
\]

**Proof.** Lemma 2.1 gives \(H_2(K(\mathbb Q,1);\mathbb Z)=H_3(K(\mathbb Q,1);\mathbb Z)=0\). The UCT makes its degree-three cohomology zero for every coefficient group. The lifting criterion proves (a).

For (b), the map on second homology sends the basis \(e_1\wedge e_2\) to \(u\wedge v\), by the naturality in Lemma 2.1. Pullback in the natural UCT is therefore the Ext pullback along \(s\mapsto s(u\wedge v)\). By the definition of \(\Theta\) in Lemma 3.1, this is exactly \(\omega_2(u,v)\).

For (c), the \(R\)-component pulls back to zero by its assumed global vanishing. The \(D\)-component pulls back to zero because the source has \(H_3=0\) and because \(\operatorname{Ext}^1(H_2,D)=0\). Thus the entire pulled-back \(B\)-class vanishes, and the lifting criterion applies.

For (d), the map on third homology sends \(s(e_1\wedge e_2\wedge e_3)\) to \(s(u\wedge v\wedge w)\). Naturality of (5.1) and the definition of \(\Phi\) identify the pullback with the homomorphism \(s\mapsto k_D(s(u\wedge v\wedge w))\) in \(J_D\), which is exactly \(\omega_3(u,v,w)\). \(\square\)

## 6. Mixed-input vanishing for arbitrary operations

Let \(t:W^r\to W\) be any pointed operation. Write its fundamental-group homomorphism as
\[
t_*(v_1,\ldots,v_r)=\sum_{i=1}^rF_i(v_i).
\tag{6.1}
\]
Each \(F_i:V\to V\) is rational linear: group homomorphisms commute with integer multiplication and with the unique division by each nonzero integer in rational vector spaces.

**Lemma 6.1 — PROVED; confidence 0.99.** For distinct inputs \(i,j\),
\[
\omega_2(F_i u,F_j v)=0\qquad(u,v\in V).
\tag{6.2}
\]
If \(k_R=0\), then for distinct \(i,j\),
\[
\omega_3(F_i u,F_i v,F_j w)=0,
\tag{6.3}
\]
and for pairwise distinct \(i,j,h\),
\[
\omega_3(F_i u,F_j v,F_h w)=0.
\tag{6.4}
\]

**Proof.** For (6.2), choose the two line lifts from Lemma 5.1(a). Insert the lift of \(a_u\) in input \(i\), using the first variable of \(K(\mathbb Q,1)^2\), and the lift of \(a_v\) in input \(j\), using its second variable. Set all other inputs equal to the basepoint. This gives \(L:K(\mathbb Q,1)^2\to W^r\).

The composite \(g=qtL\) induces \((s,t)\mapsto sF_i u+tF_jv\) on fundamental groups. Maps to \(X=K(V,1)\) are classified by their fundamental-group homomorphisms, by \(H^1\)-representability and the degree-one UCT. Thus \(g\) is homotopic to the corresponding map \(a_{F_i u,F_jv}\). But \(g\) lifts through \(q\), namely by \(tL\), so \(g^*k=0\). Its \(R\)-component and Lemma 5.1(b) give (6.2).

Now assume \(k_R=0\). For (6.3), choose a lift of the plane map \(a_{u,v}:K(\mathbb Q^2,1)\to X\) using Lemma 5.1(c), and a lift of the line map \(a_w:K(\mathbb Q,1)\to X\). Insert them in inputs \(i,j\), respectively, and set all other inputs to the basepoint. The source is \(K(\mathbb Q^2,1)\times K(\mathbb Q,1)\), a \(K(\mathbb Q^3,1)\). The composite through \(t\) and \(q\) induces the three columns \(F_i u,F_i v,F_j w\), and it lifts through \(q\). Lemma 5.1(d) therefore gives (6.3).

For (6.4), choose three line lifts, put them in inputs \(i,j,h\), and use the three variables of \(K(\mathbb Q,1)^3\). The same calculation now gives the columns \(F_i u,F_jv,F_hw\). Its pullback of \(k_D\) vanishes because it lifts, proving (6.4). \(\square\)

## 7. Taylor identities force both forms to vanish

**Proposition 7.1 — PROVED; confidence 0.98.** A normalized Taylor operation on \(W\) forces \(k=0\).

**Proof.** Let \(t\) be such an operation, with the linear maps \(F_i\) in (6.1). Normalization gives
\[
\sum_{i=1}^rF_i=\operatorname{id}_V.
\tag{7.1}
\]
For a fixed input \(i\), choose its Taylor identity \(td_\alpha\simeq td_\beta\). Put
\[
\delta_j=
\begin{cases}1&\alpha_j=x\\0&\alpha_j=y\end{cases}
-
\begin{cases}1&\beta_j=x\\0&\beta_j=y.\end{cases}
\]
Then \(\delta_j\in\{-1,0,1\}\), \(\delta_i=\pm1\), and equality of the induced maps on the first copy of \(V\subseteq V^2\) gives
\[
\sum_{j=1}^r\delta_jF_j=0.
\tag{7.2}
\]

Fix \(u,v\in V\). By rational bilinearity and (7.2),
\[
0=\omega_2\left(F_i u,\sum_j\delta_jF_jv\right)
=\sum_j\delta_j\omega_2(F_i u,F_jv).
\]
All terms with \(j\ne i\) vanish by (6.2). Since \(\delta_i=\pm1\), we obtain
\[
\omega_2(F_i u,F_i v)=0.
\tag{7.3}
\]
This holds for every \(i\). Expanding both arguments by (7.1) now gives
\[
\omega_2(u,v)=\sum_{i,j}\omega_2(F_i u,F_jv)=0,
\]
using (6.2) for distinct indices and (7.3) for equal indices. Decomposable wedges span \(\Lambda_{\mathbb Q}^2V\), so the homomorphism in (5.2) is zero. That identification is an isomorphism, hence \(k_R=0\).

We can consequently use (6.3) and (6.4). They show that every trilinear term whose three input indices are not all equal vanishes. Indeed, if exactly two indices agree, alternation moves those arguments into the first two positions of (6.3), with a sign; if all three differ, (6.4) applies.

For a fixed \(i\), apply its relation (7.2) to the third argument:
\[
0=\omega_3\left(F_i u,F_i v,\sum_j\delta_jF_jw\right)
=\sum_j\delta_j\omega_3(F_i u,F_i v,F_jw).
\]
Equation (6.3) kills every term with \(j\ne i\). Since \(\delta_i=\pm1\), this gives
\[
\omega_3(F_i u,F_i v,F_i w)=0.
\tag{7.4}
\]
Finally, expand all three arguments by (7.1):
\[
\omega_3(u,v,w)=
\sum_{i,j,h}\omega_3(F_i u,F_jv,F_hw)=0.
\]
The mixed terms vanish by (6.3)–(6.4), and the equal-index terms vanish by (7.4). Decomposable triple wedges span \(\Lambda_{\mathbb Q}^3V\), so (5.3) gives \(k_D=0\). Both coefficient components vanish, and hence \(k=0\). \(\square\)

**Corollary 7.2 — PROVED; confidence 0.98.** In the same class of simple two-types, the normalization in the implication \(1\Rightarrow3\) can be weakened as follows. Suppose a pointed map \(t:W^r\to W\) satisfies the stated Taylor identities and its diagonal composite \(t\Delta_r:W\to W\) induces a surjection on \(\pi_1W\). Then \(k=0\), and therefore \(W\simeq K(V,1)\times K(B,2)\).

**Proof.** Write \(t_*=\sum_iF_i\) as in (6.1), and put \(S=\sum_iF_i\). The assumption is that \(S:V\to V\) is onto; it need not be the identity. For every input \(i\), its Taylor identity still gives (7.2), with \(\delta_i=\pm1\).

Equation (6.2) kills \(\omega_2(F_i u,F_jv)\) for \(i\ne j\). Applying (7.2) in the second argument gives
\[
0=\omega_2\left(F_i u,\sum_j\delta_jF_jv\right)
=\delta_i\omega_2(F_i u,F_iv),
\]
so the equal-index terms vanish as well. Consequently
\[
\omega_2(Su,Sv)=\sum_{i,j}\omega_2(F_i u,F_jv)=0.
\]
Since \(S\) is onto, every pair in \(V^2\) is \((Su,Sv)\) for some \(u,v\). Thus \(\omega_2=0\) and \(k_R=0\).

All plane lifts are now available by Lemma 5.1(c). Equations (6.3) and (6.4), together with alternation, kill every trilinear term with input indices not all equal. For an equal-index term, (7.2) gives
\[
0=\omega_3\left(F_i u,F_i v,\sum_j\delta_jF_jw\right)
=\delta_i\omega_3(F_i u,F_iv,F_iw),
\]
so these terms vanish too. Hence
\[
\omega_3(Su,Sv,Sw)=
\sum_{i,j,h}\omega_3(F_i u,F_jv,F_hw)=0.
\]
Surjectivity of \(S\) makes this the vanishing of \(\omega_3\) on every triple, so \(k_D=0\). Therefore \(k=0\); the splitting follows from the nullhomotopy-fiber construction in Proposition 9.1 below. \(\square\)

## 8. H-structures also force vanishing, without associativity

**Proposition 8.1 — PROVED; confidence 0.99.** An H-structure on \(W\) forces \(k=0\).

**Proof.** Apply Lemma 6.1 to \(t=\mu\). Its two unit homotopies imply \(F_1=F_2=\operatorname{id}_V\). Equation (6.2) immediately gives \(\omega_2(u,v)=0\) for all \(u,v\), and therefore \(k_R=0\).

With that established, (6.3) for \(i=1,j=2\) gives \(\omega_3(u,v,w)=0\) for all triples. Thus \(k_D=0\) as well. No associativity or commutativity was used. \(\square\)

## 9. Splitting and explicit normalized Mal'cev operations

**Proposition 9.1 — PROVED; confidence 0.99.** If \(k=0\), then \(W\simeq K(V,1)\times K(B,2)\). This product has an H-structure and a normalized Taylor operation.

**Proof.** Choose a pointed nullhomotopy \(N_x\) of the map \(k:X\to K(B,3)\), viewed as a path from \(k(x)\) to the basepoint. In the path-fiber model, the formulas
\[
(x,\gamma)\longmapsto(x,N_x^{-1}*\gamma),\qquad
(x,\omega)\longmapsto(x,N_x*\omega)
\]
give homotopy inverse maps between \(\operatorname{hofib}(k)\) and \(X\times\Omega K(B,3)\). Contracting each consecutive path followed by its reverse gives the two inverse homotopies. The loop space has only \(\pi_2=B\), so it is \(K(B,2)\). This proves the splitting.

Write \(G=K(V,1)\times K(B,2)\). Let \(\iota_1\in H^1(G;V)\) and \(\iota_2\in H^2(G;B)\) be the classes represented by its two coordinate projections. Cohomology representability constructs \(m:G^3\to G\) by requiring, in each of these two target coordinates,
\[
m^*\iota_s=
\operatorname{pr}_1^*\iota_s-\operatorname{pr}_2^*\iota_s
+\operatorname{pr}_3^*\iota_s,\qquad s=1,2.
\tag{9.1}
\]
This is the operation \(x-y+z\) in the abelian Eilenberg–Mac Lane group structure, expressed through representing cohomology classes so that no restriction on the cardinalities of \(V\) or \(B\) is needed.

Pulling (9.1) back by \(x\mapsto(x,x,x)\) gives \(\iota_s-\iota_s+\iota_s=\iota_s\). Thus \(m(x,x,x)\simeq x\). Pulling back by \((x,y)\mapsto(x,y,y)\) gives \(\operatorname{pr}_1^*\iota_s\), so \(m(x,y,y)\simeq x\). Pulling back by \((x,y)\mapsto(y,y,x)\) gives the same class, so \(m(y,y,x)\simeq x\). Representability in both coordinates turns these class equalities into the stated pointed homotopies.

The identities
\[
m(x,x,x)\simeq m(y,y,x),\qquad
m(x,x,x)\simeq m(x,y,y)
\]
are Taylor identities: the first distinguishes inputs one and two, and the second distinguishes inputs two and three. Together with the normalization already verified, they make \(m\) a normalized Taylor operation. The map \(\mu(x,z)=m(x,*,z)\) has both homotopy units by the two Mal'cev identities and is an H-structure.

Finally, if \(e:W\to G\) is a pointed homotopy equivalence with inverse \(h\), define \(t=h\,m\,e^3\) and \(\mu_W=h\,\mu\,e^2\). The relations just proved, together with \(he\simeq\operatorname{id}_W\), transport normalization, the Taylor identities, and the two unit identities to \(W\). \(\square\)

**Conclusion of Theorem 1.1 — PROVED; confidence 0.98.** Proposition 7.1 proves \(1\Rightarrow3\). Proposition 8.1 proves \(2\Rightarrow3\). Proposition 9.1 proves \(3\Rightarrow4\) and \(4\Rightarrow1,2\). These implications establish all four equivalences.

## 10. Scope and relation to the explicit counterexample

**PROVED consequence; confidence 0.99.** The conclusion applies to arbitrary-dimensional rational \(V\) and arbitrary abelian \(B\), including divisible torsion coefficient groups. It uses no finite generation, no finite-type CW assumption, and no given local-to-global theorem. The only height hypothesis is that \(W\) is a two-type.

**PROVED consequence; confidence 0.99.** The explicit nonsplit example with \(V=\mathbb Q^2\), \(B=\mathbb Z\), and a nonzero locally invisible \(k\)-invariant has no normalized Taylor operation. Its nonzero invariant lies in the bilinear component (5.2), which Proposition 7.1 forces to vanish whenever such an operation exists.

**PROVED statement of scope; confidence 1.00.** This characterization does not settle normalized Taylor \(\Rightarrow\) H for arbitrary simple spaces of higher or infinite Postnikov height. Its finite list of bilinear and trilinear obstruction forms is a property of the two-type situation.

## 11. Precise references used

- J. Peter May (1967), *Simplicial Objects in Algebraic Topology*: Theorem 14.1, CW structure on realization; Theorem 16.6, comparison of simplicial and realized homotopy groups; Theorem 23.2, the bar construction on a discrete group as \(K(A,1)\). Author PDF: <https://www.math.uchicago.edu/~may/BOOKS/Simp.pdf>. Searchable copy of the same primary text: <https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/May-simp-ocr.pdf>.
- Allen Hatcher (2002), *Algebraic Topology*: Theorem 2A.1, first homology as the abelianization of the fundamental group; Theorem 3.2, the natural cohomology universal coefficient theorem and its Ext term; Theorem 4.5, Whitehead's theorem; Theorem 3.15 in the cited Cornell online edition, the cohomological Künneth theorem with its finite-free hypothesis. Some earlier copies number this last theorem 3.16. Author chapters: <https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf>, <https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf>, and <https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf>.
- J. P. May and K. Ponto (2012), *More Concise Algebraic Topology: Localization, Completion, and Model Categories*: Corollary 2.2.3, homotopy-pullback exact sequence; Equation (3.4.1), cohomology representability; Lemma 3.4.2, principal classification of Eilenberg–Mac Lane fibrations with trivial fundamental-group action. Author PDF: <https://www.math.uchicago.edu/~may/BOOKS/KateBookFinal.pdf>.

## 12. Adversarial self-audit

**PROVED assessment; confidence 0.98.** The most delicate logical transition is from the vanishing reduced-coefficient component to the existence of lifts of all rational planes. Such plane lifts are not asserted at the beginning: their reduced obstruction can be nonzero. They are introduced only after the line tests and the Taylor identities have proved \(k_R=0\). At that point the divisible-coefficient component restricts to zero because a rational plane has \(H_3=0\) and divisible coefficients have zero Ext. This verifies the entire obstruction, in the original coefficient group \(B=D\oplus R\), before any plane is used. If those plane lifts were used before \(k_R\) vanished, the trilinear part of the argument would be unjustified.
