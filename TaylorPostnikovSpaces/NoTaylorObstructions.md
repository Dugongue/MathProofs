# The explicit height-two local-H example admits no normalized Taylor operation

**PROVED — every normalized operation on the space \(U\) below induces a coordinate projection on \(\pi _1U\); consequently \(U\) admits no normalized Taylor operation. Confidence: 0.99.**

This note concerns the example \(U\) used to show that the auxiliary implication “all prime localizations are H-spaces implies an integral H-space” fails without finite generation. It strengthens the qualification attached to that example: the example does not merely lack a known Taylor operation; a normalized Taylor operation on it is impossible. Nothing here changes the conditional finite-type, finite-height theorem proved previously.

## 1. Precise normalization and Taylor identities

**Definition.** A normalized \(r\)-ary operation on a pointed connected space \(Z\), where \(r\geq1\), is a pointed map \(t:Z^r\to Z\) such that \(t\Delta_r\simeq\operatorname{id}_Z\) through pointed maps.

For a word \(\alpha=(\alpha_1,\ldots,\alpha_r)\in\{x,y\}^r\), let \(d_\alpha:Z^2\to Z^r\) have its \(i\)-th coordinate equal to the first projection when \(\alpha_i=x\), and to the second projection when \(\alpha_i=y\).

**Definition.** A normalized Taylor operation is a normalized operation \(t\) such that, for every \(i\in\{1,\ldots,r\}\), there are words \(\alpha,\beta\in\{x,y\}^r\) with \(\alpha_i\ne\beta_i\) and \(t d_\alpha\simeq t d_\beta\).

**PROVED clarification, confidence 1.00.** Normalization is indispensable to this formulation: a constant pointed map satisfies every identity involving only its values, but it cannot satisfy \(t\Delta_r\simeq\operatorname{id}_Z\) unless \(Z\) is contractible. The argument below uses normalization exactly in the equation \(\sum_iF_i=\operatorname{id}_{\mathbb Q^2}\).

## 2. The general obstruction used in the proof

**Lemma 2.1 — PROVED; confidence 0.99.** Let \(Y=K(\mathbb Q,1)\), \(X=K(\mathbb Q^2,1)\), and let \(q:Z\to X\) be a pointed map such that:

1. \(q_*\) identifies \(\pi _1Z\) with \(\mathbb Q^2\).
2. For every \(u\in\mathbb Q^2\), the map \(a_u:Y\to X\) inducing \(a_u(s)=su\) on fundamental groups has a pointed lift up to homotopy through \(q\).
3. The map \(q\) has no pointed homotopy section.

Then every normalized operation \(t:Z^r\to Z\) induces a coordinate projection
\[
t_*:(\mathbb Q^2)^r\longrightarrow\mathbb Q^2.
\]

**Proof.** Write \(V=\mathbb Q^2\), using the identification supplied by \(q_*\). Let \(F_i:V\to V\) be the restriction of \(t_*\) to the \(i\)-th factor. Every group homomorphism between rational vector spaces is \(\mathbb Q\)-linear: it commutes with multiplication by integers, and, since division by a nonzero integer is unique, it commutes with division by integers as well. Thus every \(F_i\) is \(\mathbb Q\)-linear. Since \(t_*\) is a group homomorphism out of a direct product of abelian groups, it satisfies
\[
t_*(v_1,\ldots,v_r)=\sum_{i=1}^r F_i(v_i).
\]
Normalization gives
\[
\sum_{i=1}^rF_i=\operatorname{id}_V. \tag{2.1}
\]

We first prove that, whenever \(i\ne j\), no vector in \(\operatorname{im}F_i\) is linearly independent of a vector in \(\operatorname{im}F_j\). Suppose instead that \(u,v\in V\) make \(F_i(u)\) and \(F_j(v)\) independent. Choose lifts \(\ell_u,\ell_v:Y\to Z\) of \(a_u,a_v\). Define
\[
L:Y^2\longrightarrow Z^r
\]
by using \(\ell_u\) of the first input in position \(i\), \(\ell_v\) of the second input in position \(j\), and the basepoint in every other position. Then
\[
g=qtL:Y^2\longrightarrow X
\]
induces the homomorphism
\[
g_*:\mathbb Q^2\longrightarrow\mathbb Q^2,\qquad
(s,t)\longmapsto sF_i(u)+tF_j(v).
\]
The assumed independence makes \(g_*\) an isomorphism.

Both \(Y^2\) and \(X\) are Eilenberg–Mac Lane spaces of type \(K(\mathbb Q^2,1)\). The map \(g\) therefore has a pointed homotopy inverse \(h:X\to Y^2\). This conclusion can be obtained without an unnumbered classification assertion: cohomology representability, May–Ponto (2012), Equation (3.4.1), and the degree-one universal coefficient theorem, Hatcher (2002), Theorem 3.2, give
\[
[T,K(A,1)]\cong H^1(T;A)\cong\operatorname{Hom}(H_1(T;\mathbb Z),A)
\]
for any connected \(T\) and abelian \(A\), because \(H_0(T;\mathbb Z)=\mathbb Z\) has zero Ext. Represent the two coordinate homomorphisms of \(g_*^{-1}\) to construct \(h\), and use the same classification to show \(gh\simeq\operatorname{id}_X\) and \(hg\simeq\operatorname{id}_{Y^2}\).

But then \(s=tLh:X\to Z\) satisfies \(qs=gh\simeq\operatorname{id}_X\), contradicting hypothesis 3. This proves the asserted dependence of all vectors coming from different inputs.

Suppose every \(F_i\) has rank at most one. Equation (2.1) guarantees that some \(F_i\) is nonzero. Let \(L_0=\operatorname{im}F_i\), a one-dimensional subspace, and choose \(u\) with \(F_i(u)\ne0\). For every \(j\ne i\), a vector in \(\operatorname{im}F_j\) outside \(L_0\) would be independent of \(F_i(u)\), contradicting the preceding paragraph. Hence \(\operatorname{im}F_j\subseteq L_0\) for every \(j\). The image of \(\sum_jF_j\) is then contained in \(L_0\), contradicting (2.1). Therefore some \(F_i\) has rank two.

For this \(i\), suppose \(F_j(v)\ne0\) for some \(j\ne i\). Surjectivity of \(F_i\) allows us to choose \(u\) such that \(F_i(u)\) is independent of \(F_j(v)\). This again contradicts the dependence already proved. Thus every \(F_j\) with \(j\ne i\) is zero. Equation (2.1) now says \(F_i=\operatorname{id}_V\). This is exactly the claimed projection. \(\square\)

**Corollary 2.2 — PROVED; confidence 0.99.** Under the hypotheses of Lemma 2.1, \(Z\) admits no normalized Taylor operation.

**Proof.** Suppose \(t:Z^r\to Z\) is such an operation. By Lemma 2.1, \(t_*\) is the projection to some input \(i\). The Taylor condition at that input supplies words \(\alpha,\beta\) with \(\alpha_i\ne\beta_i\) and a pointed homotopy \(td_\alpha\simeq td_\beta\). On \(\pi _1(Z^2)=V^2\), one composite is the first projection and the other is the second projection. These homomorphisms are distinct: their values on \((v,0)\), for \(v\ne0\), are \(v\) and \(0\). Homotopic pointed maps induce equal homomorphisms, a contradiction. \(\square\)

## 3. The explicit nonzero class defining \(U\)

The following construction makes the application concrete. It also records exactly which parts of the earlier counterexample are needed.

Put
\[
B=\prod_p\mathbb Z_{(p)},\qquad C=B/\Delta\mathbb Z.
\]

**Lemma 3.1 — PROVED; confidence 1.00.** The group \(C\) is uniquely divisible.

**Proof.** If \(nb=\Delta m\), every coordinate of \(b\) is \(m/n\). Membership in every \(\mathbb Z_{(p)}\) forces \(m/n\in\mathbb Z\), so \(b\) is diagonal and multiplication by \(n\) on \(C\) is injective.

For \(b=(b_p)\in B\), choose \(z\in\mathbb Z\) satisfying \(z\equiv-b_p\pmod {p^{v_p(n)}}\) at each prime \(p\mid n\). Reduction is defined because \(b_p\) has denominator prime to \(p\), and the CRT applies to these finitely many congruences. Then \((b_p+z)/n\in\mathbb Z_{(p)}\) at every prime. Consequently multiplication by \(n\) on \(C\) is onto. These unique divisions define its rational vector-space structure. \(\square\)

Let \(c\in C\) be represented by the tuple equal to \(1\) at \(p=2\) and \(0\) elsewhere. It is nonzero. Define \(j:\mathbb Q\to C\) by \(j(s)=sc\), and define
\[
E=\{(b,s)\in B\times\mathbb Q:[b]=j(s)\}.
\]
There is an exact sequence
\[
0\longrightarrow\mathbb Z\longrightarrow E\longrightarrow\mathbb Q\longrightarrow0,
\qquad m\longmapsto(\Delta m,0),\quad(b,s)\longmapsto s.
\]

**Lemma 3.2 — PROVED; confidence 1.00.** This extension defines a nonzero class \(\xi\in\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,\mathbb Z)\).

**Proof.** A homomorphism \(\mathbb Q\to\mathbb Z_{(p)}\) is zero, since each image element lies in \(p^a\mathbb Z_{(p)}\) for every \(a\), and the intersection of these subgroups is zero. Hence \(\operatorname{Hom}(\mathbb Q,B)=0\). A section of \(E\to\mathbb Q\) would supply a homomorphism \(\mathbb Q\to B\) lifting the nonzero map \(j\), which is impossible. The extension is nonsplit.

Here the extension interpretation of Ext can be verified directly. Map \(F=\bigoplus_{n\ge1}\mathbb Ze_n\) onto \(\mathbb Q\) by \(e_n\mapsto1/n!\). Its kernel is freely generated by \(u_n=e_n-(n+1)e_{n+1}\): generation follows by reducing a finite sum to its last basis vector, and independence follows by inspecting the last basis vector in a putative relation. Choose lifts to \(E\) of all \(1/n!\). Their differences on the \(u_n\) define \(\alpha\in\operatorname{Hom}(\ker(F\to\mathbb Q),\mathbb Z)\). Its class in the cokernel defining Ext is zero precisely when \(\alpha\) extends to \(F\), precisely when the chosen lifts can be adjusted to descend to a section \(\mathbb Q\to E\). Thus the nonsplitting gives \(\xi\ne0\). \(\square\)

**Lemma 3.3 — PROVED; confidence 0.99.** With \(Y=K(\mathbb Q,1)\) and \(X=K(\mathbb Q^2,1)\),
\[
H^3(Y;\mathbb Z)=0,\qquad H^3(X;\mathbb Z)\cong\operatorname{Ext}^1(\mathbb Q,\mathbb Z).
\]

**Proof.** Construct \(K(\mathbb Q^d,1)\), for \(d=1,2\), as the telescope of the tori \(T^d\) under the maps multiplying every circle coordinate successively by \(2,3,4,\ldots\). Maps and homotopies from compact sources lie in finite initial subtelescopes, each of which retracts to its last torus. Thus the homotopy groups are the corresponding colimits: the fundamental group is \(\mathbb Q^d\), and all higher homotopy groups vanish.

The bounded-height observation also applies to finite singular chains and chains witnessing boundaries, so homology is the corresponding colimit. In dimension one the transition maps multiply \(H_1(T^d)\) by the indicated integer. For \(T^2\), the map multiplying both coordinates by \(a\) has covering degree \(a^2\), and therefore multiplies \(H_2\) by \(a^2\). The resulting colimits are \(H_1(Y)=\mathbb Q\), \(H_i(Y)=0\) for \(i>1\), and \(H_1(X)=\mathbb Q^2\), \(H_2(X)=\mathbb Q\), \(H_i(X)=0\) for \(i>2\). Apply the natural cohomology universal coefficient exact sequence of Hatcher (2002), Theorem 3.2, in degree three. \(\square\)

Let \(0\ne k\in H^3(X;\mathbb Z)\) correspond to \(\xi\). Represent it by a based map \(k:X\to K(\mathbb Z,3)\), using May–Ponto (2012), Equation (3.4.1). Let
\[
U=\operatorname{hofib}(k),\qquad q:U\to X.
\]
A path model has points \((x,\gamma)\), where \(\gamma\) starts at \(k(x)\) and ends at the basepoint. A CW model is understood whenever needed; the maps are transported in the pointed CW homotopy category.

## 4. Verification of all hypotheses of the obstruction lemma

**Theorem 4.1 — PROVED; confidence 0.99.** Every normalized operation \(t:U^r\to U\) induces a projection on \(\pi _1U=\mathbb Q^2\). In particular \(U\) admits no normalized Taylor operation.

**Proof.** The homotopy-fiber sequence
\[
K(\mathbb Z,2)\longrightarrow U\xrightarrow q X\xrightarrow k K(\mathbb Z,3)
\]
gives an isomorphism \(q_*:\pi _1U\to\pi _1X=\mathbb Q^2\). Indeed, the adjacent fiber groups \(\pi_1K(\mathbb Z,2)\) and \(\pi_0K(\mathbb Z,2)\) vanish. The exact homotopy sequence here is the homotopy-pullback sequence of May–Ponto (2012), Corollary 2.2.3.

For any \(u\in\mathbb Q^2\), let \(a_u:Y\to X\) induce \(s\mapsto su\). Lemma 3.3 gives \(H^3(Y;\mathbb Z)=0\), so \(ka_u\) is based nullhomotopic. Choose a pointed nullhomotopy \(N_u\). The formula
\[
\ell_u(y)=(a_u(y),N_u(y,-))
\]
defines a lift to the homotopy-fiber path model. It gives a pointed lift up to homotopy to the chosen CW model. This verifies hypothesis 2 of Lemma 2.1 for every vector \(u\).

Finally, \(q\) has no homotopy section. The paths in the homotopy-fiber model give \(kq\simeq *\). If \(s:X\to U\) satisfied \(qs\simeq\operatorname{id}_X\), then \(k\simeq kqs\simeq *\), contradicting \(k\ne0\). All hypotheses of Lemma 2.1 hold. Apply that lemma and Corollary 2.2. \(\square\)

**PROVED consequence, confidence 0.99.** More generally, every nonzero \(k\in H^3(K(\mathbb Q^2,1);B_0)\), with arbitrary abelian coefficient group \(B_0\), gives the same no-normalized-Taylor conclusion for \(\operatorname{hofib}(k)\). The proof uses \(H^3(K(\mathbb Q,1);B_0)=0\), which follows from the homology calculation in Lemma 3.3 for every coefficient group, and uses no special property of \(\xi\) beyond nonvanishing. The special class constructed above is needed only for the simultaneous prime-local splitting in the earlier local-H counterexample.

## 5. References and scope

- Allen Hatcher (2002), *Algebraic Topology*, Theorem 3.2: natural universal coefficient theorem for cohomology. Author PDF: <https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf>.
- J. P. May and K. Ponto (2012), *More Concise Algebraic Topology: Localization, Completion, and Model Categories*, Corollary 2.2.3: homotopy exact sequence for a homotopy pullback; Equation (3.4.1): cohomology representability by Eilenberg–Mac Lane spaces. Author PDF: <https://www.math.uchicago.edu/~may/BOOKS/KateBookFinal.pdf>.

**PROVED scope statement, confidence 1.00.** This theorem excludes the explicit non-finite-type example from serving as a counterexample to normalized Taylor \(\Rightarrow\) H. It does not settle that implication for arbitrary spaces without either finiteness condition. In particular no conclusion about Taylor operations on Pan's phantom-map example is imported into this proof.

## Adversarial self-audit

**PROVED assessment, confidence 0.99.** The step most vulnerable to an unnoticed obstruction would be the claimed lifts of all rational one-dimensional subgroup maps. They exist because their obstruction is the pullback of the actual defining \(k\)-class, and the entire group \(H^3(K(\mathbb Q,1);B_0)\) is zero. Once those lifts are in hand, the decisive contradiction uses only a homotopy section: if two distinct inputs contribute independent vectors, their product creates a lift of a homotopy equivalence \(K(\mathbb Q^2,1)\to K(\mathbb Q^2,1)\). No assertion about determinant actions on Ext, classification of all maps of two-types, or higher-operation compatibility is required.
