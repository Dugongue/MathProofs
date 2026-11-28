# Taylor operations and unbounded Postnikov towers: a compactness theorem

**Verdict — PROVED under the finite-deviation hypothesis below; confidence 0.98.** Finite Postnikov height is unnecessary when all the integral groups that parameterize relative multiplication lifts are finite. This includes the case in which every higher homotopy group is finite, with an arbitrary finitely generated abelian fundamental group. It also includes some spaces with nonzero rational homotopy in infinitely many degrees.

This note proves the compactness assertion independently of the particular method used to construct multiplications on the finite Postnikov sections. To apply it to Taylor operations, one may use the finite-height theorem already proved in `LC/LC_FullProof.md`, together with the stipulated Taylor local step. The unrestricted statement without a finiteness or compatibility hypothesis is not asserted here.

## 1. Definitions, precise input, and main statement

We use pointed spaces and pointed maps. Products and mapping spaces are taken in compactly generated spaces. A relative CW pair is a pair obtained by attaching cells to its subspace. The notation \([X,Y]_A\), when a map \(a:A\to Y\) has been fixed, means homotopy classes relative to \(A\) of maps whose restriction is exactly \(a\).

Let \(W\) be a connected simple CW complex. Write

\[
 A_n=\pi_nW,\qquad X=W\times W,\qquad A=W\vee W,
 \qquad a:A\longrightarrow W
\]

for the fold map. Since \(W\) is simple, \(A_1\) is abelian. For \(n\ge 2\), put

\[
 E_n(W)=H^n(X,A;A_n).
 \tag{1.1}
\]

All cohomology in this note has constant coefficients. Simplicity is what permits this choice of coefficients in the Postnikov lifting problem.

The following foundational statements are used with their precise references.

* **Established input, confidence 0.99:** a connected simple space has a Postnikov tower of principal fibrations. This is May–Ponto (2012), Theorem 3.2.1. We choose models \(P_n\), maps \(q_n:W\to P_n\), and fibrations \(p_n:P_n\to P_{n-1}\) such that \(p_nq_n=q_{n-1}\), \(q_n\) is an isomorphism on \(\pi_i\) for \(i\le n\), and \(\pi_iP_n=0\) for \(i>n\). The fibre of \(p_n\) is \(K(A_n,n)\). The total space can be taken to be the homotopy fibre of a map \(P_{n-1}\to K(A_n,n+1)\). These models can be chosen simultaneously for the countable tower.
* **Established input, confidence 0.99:** a nilpotent space with finitely generated homotopy groups is weakly equivalent to a CW complex with finite skeleta and has finitely generated integral homology groups. This is May–Ponto (2012), Theorem 4.5.2, assertions (i), (iii), and (v). A weak equivalence between CW complexes is a homotopy equivalence, by Hatcher (2002), Theorem 4.5. Thus, when degreewise finite generation is assumed, we may replace \(W\) by a CW model with finite skeleta.
* **Established input, confidence 0.99:** \(\widetilde H^j(Z;M)\) is represented by \(K(M,j)\); this is Hatcher (2002), Theorem 4.57. The cohomological universal coefficient theorem is Hatcher, Theorem 3.2. The field cohomological Künneth theorem is Hatcher, Theorem 3.15 in the current author-hosted edition.
* **Established input, confidence 0.99:** Serre fibrations have the relative homotopy lifting property for CW pairs, and a Serre fibration that is a weak homotopy equivalence has the right lifting property with respect to every relative CW inclusion. These are consequences of the precise generating cofibrations and generating acyclic cofibrations in May–Ponto (2012), Theorem 17.2.2, and its proof on printed pages 345–346. The proof there explicitly obtains lifting for \(S^{d-1}\hookrightarrow D^d\); attaching the cells one dimension at a time gives the assertion for relative CW pairs. For the relative homotopy lifting assertion, each new cell requires lifting against
  \[
  (D^d\times\{0\})\cup(S^{d-1}\times I)\hookrightarrow D^d\times I.
  \]
  The proof of that theorem identifies this pair with a disk-cylinder pair defining a Serre fibration. The monoidal assertion in the same theorem guarantees that \(W\vee W\hookrightarrow W\times W\) is a cofibration of the required kind. One may instead use the product CW structure after choosing the countable CW model above.
* **Established input, confidence 0.99:** the homotopy limit of a tower has the Milnor homotopy exact sequences, and the inverse limit of a tower of fibrations is equivalent to its homotopy limit. These are May–Ponto (2012), Propositions 2.2.9 and 2.2.11. The exact sequence, including its component version, will be stated explicitly where used.

No claim of novelty is made for these inputs or for the finite-homotopy-group special case below. In particular, Stephan Klaus (2003), Theorem 1 of *H-space structures and Postnikov approximations*, already proves that a connected space whose homotopy groups are all finite is an H-space if every Postnikov approximation is an H-space. Our proof uses relative cohomological finiteness, which also permits an infinite abelian fundamental group and the rational patterns described below.

**Theorem 1.1 — PROVED; confidence 0.98.** Suppose that \(W\) is a connected simple CW complex, every finite Postnikov section \(P_nW\) is an H-space, and every group \(E_n(W)\) in (1.1) is finite. Then \(W\) is an H-space. Neither finite generation of its homotopy groups nor a bound on its Postnikov height is required for this statement. The conclusion includes a representative multiplication whose restriction to the wedge is exactly the fold map.

Degreewise finite generation will be assumed only for the finiteness tests and rational criteria in Sections 7–10. The compactness argument uses only the finiteness of the specified relative cohomology groups, the principal tower, and the relevant CW lifting properties.

**Lemma 1.2 — PROVED; confidence 0.99.** Arbitrary abelian groups, including uncountable groups, admit strict topological abelian Eilenberg–MacLane models in compactly generated spaces. The compactly generated product of two CW complexes has the product CW structure, and the wedge inclusion is a relative CW inclusion.

**Proof.** First observe that a compact subset of a CW complex is contained in a finite subcomplex. Otherwise it meets infinitely many distinct open cells; choose one point in each of a countably infinite collection of those intersections. The resulting point set, and every subset of that set, is closed in the CW complex: the closure of any cell meets only finitely many of its points, and the weak topology of the CW complex tests closedness on those closed cells. Thus this is a closed infinite discrete subspace of the given compact set, which is impossible. The compact set therefore meets only finitely many cells, whose closures lie in a finite subcomplex by closure finiteness.

Give the Cartesian product of two CW complexes its product cells and their weak CW topology. Each product cell is a disk, its boundary is assembled from lower product cells, and the closure-finiteness condition follows from that of the two factors. The identity from this CW product to the usual product is continuous on each cell, hence continuous. A continuous map from a compact Hausdorff space to the usual product has both coordinate images in finite subcomplexes, by the preceding paragraph. Its image therefore lies in a product of finite CW complexes, where the product CW topology equals the usual topology. It is consequently continuous into the weak CW product. The definition of compact generation now identifies that weak CW product with the compactly generated Cartesian product. The cells in the wedge are precisely the product cells with one factor the basepoint cell, so the wedge is a subcomplex. We may choose the basepoint to be a zero-cell in each factor.

For an arbitrary abelian group M define the simplicial abelian group \(\mathcal K(M,n)\) by

\[
 \mathcal K(M,n)_q=Z^n(\Delta[q];M).
\]

The cochains are normalized simplicial cochains; operators are pullback along order-preserving vertex maps, and addition is pointwise. May (1967), Theorem 23.9, proves that this has simplicial homotopy group M in degree n and zero in other degrees. Theorems 16.1 and 16.6 identify these with the homotopy groups of its realization. Theorem 14.1 makes that realization a CW complex.

For simplicial sets S and T, May (1967), Theorem 14.3, gives the natural continuous bijection \(|S\times T|\to |S|\times|T|\), with a continuous inverse when the target has its product CW topology. The previous paragraph about products supplies exactly that topology after compact generation. Equivalently, the inverse is continuous on every product of finite subcomplexes, and every compact test map factors through such a product, so it is continuous in the compactly generated category. Realization therefore preserves finite products there without a countability hypothesis. Realizing the addition, inverse, and zero of \(\mathcal K(M,n)\) gives continuous operations on its realization. Every abelian-group identity holds strictly because it held as an identity of simplicial maps and finite products are preserved. This gives the required model. \(\square\)

## 2. Relative lifting and the number of possible multiplication classes

Set \(a_n=q_na:A\to P_n\). Let

\[
 T_n=\{f:X\to P_n\mid f|_A=a_n\}/\simeq_A.
 \tag{2.1}
\]

Composition with \(p_n\) gives a function

\[
 \rho_n:T_n\longrightarrow T_{n-1}.
 \tag{2.2}
\]

No surjectivity of \(\rho_n\) is assumed.

**Lemma 2.1 — PROVED; confidence 0.99.** Each \(T_n\) is nonempty.

**Proof.** Choose an H-space multiplication \(\nu_n:P_n\times P_n\to P_n\). By its unit property, the restriction of \(\nu_n(q_n\times q_n)\) to \(A\) is pointed homotopic to \(a_n\). The wedge inclusion is a cofibration. Its homotopy extension property extends this homotopy over \(X\), beginning at \(\nu_n(q_n\times q_n)\). The final map is an element of the set of strict extensions in (2.1). Hence \(T_n\ne\varnothing\). \(\square\)

**Lemma 2.2 — PROVED; confidence 0.99.** \(T_1\) consists of one element.

**Proof.** The target is \(P_1=K(A_1,1)\). The relative cohomology group \(H^1(X,A;A_1)\) is zero. To check this, the maps on degree-zero homology induced by \(A\hookrightarrow X\) are isomorphisms because both spaces are connected. The map on degree-one homology is also an isomorphism: both groups are naturally \(H_1(W;\mathbb Z)\oplus H_1(W;\mathbb Z)\), and the inclusion maps each summand identically to the corresponding product factor. The homology exact sequence therefore gives

\[
 H_0(X,A;\mathbb Z)=H_1(X,A;\mathbb Z)=0.
\]

The universal coefficient theorem gives \(H^1(X,A;A_1)=0\). Relative extensions into \(K(A_1,1)\), once one extension is fixed, are classified by this group: subtract the fixed extension in the topological abelian model of Lemma 1.2, factor the difference through \(X/A\), and apply cohomology representability. Lemma 2.1 supplies an extension. Consequently there is exactly one relative homotopy class. No cardinality restriction on \(A_1\) was used. \(\square\)

**Lemma 2.3 — PROVED; confidence 0.98.** For \(n\ge2\), every fibre of \(\rho_n:T_n\to T_{n-1}\) has cardinality at most \(|E_n(W)|\).

**Proof.** Fix a class \([g]\in T_{n-1}\), and choose a representative \(g:X\to P_{n-1}\) with \(g|_A=a_{n-1}\). First consider strict lifts \(f\) of this particular map, so \(p_nf=g\), with \(f|_A=a_n\).

Write the principal stage as the homotopy fibre of a map

\[
 \kappa_n:P_{n-1}\longrightarrow K(A_n,n+1).
\]

Thus a lift of \(g\) is a continuous family of paths from \(\kappa_ng(x)\) to the basepoint. Its restriction on \(A\) is the family of paths already specified by \(a_n\). If there is no lift, the fibre in question is empty after the transport argument below. Suppose that one such lift \(f^0\) exists, with path family \(H^0(x,t)\). Use the strict topological abelian model for \(K(A_n,n+1)\). For another lift with path family \(H(x,t)\), the difference

\[
 D(x,t)=H(x,t)-H^0(x,t)
\]

vanishes for \(t=0\), for \(t=1\), and for \(x\in A\). Therefore it is a based map

\[
 X/A\longrightarrow\Omega K(A_n,n+1).
\]

Conversely any such based map gives a path-family difference, and adding it to \(H^0\) gives a lift with the prescribed boundary. These constructions are inverse at the level of maps and respect vertical homotopies fixed on \(A\). Loop-suspension adjunction identifies based homotopy classes from \(X/A\) into \(\Omega K(A_n,n+1)\) with those from \(\Sigma(X/A)\) into \(K(A_n,n+1)\). Cohomology representability and the suspension isomorphism identify these with

\[
 \widetilde H^n(X/A;A_n)=H^n(X,A;A_n)=E_n(W).
 \tag{2.3}
\]

For completeness, the suspension isomorphism here is obtained from the cohomology exact sequence of the contractible cone on \(X/A\), relative to \(X/A\); its quotient is the suspension. Thus vertical homotopy classes of strict lifts, if nonempty, form a torsor under \(E_n(W)\).

Now let \([h]\in T_n\) map to \([g]\). Choose a homotopy \(H:X\times I\to P_{n-1}\), fixed on \(A\), from \(p_nh\) to \(g\). Lift this homotopy through \(p_n\), starting with \(h\) and keeping the lift equal to \(a_n\) on \(A\times I\). The relative homotopy lifting property stated in Section 1 supplies this lift. Its endpoint \(h'\) is a strict lift of \(g\), has the required boundary, and represents the same class in \(T_n\) as \(h\). Every class in the fibre of \(\rho_n\) is therefore represented by a strict lift of \(g\). Passing from vertical homotopy to arbitrary homotopy relative to \(A\) can only identify classes. The fibre is a quotient of the set in (2.3), proving the cardinality bound. \(\square\)

**Corollary 2.4 — PROVED; confidence 0.99.** Under the hypotheses of Theorem 1.1, every \(T_n\) is a finite nonempty set.

**Proof.** Nonemptiness is Lemma 2.1. Lemma 2.2 starts the induction with \(|T_1|=1\). Lemma 2.3 gives

\[
 |T_n|\le |T_{n-1}|\,|E_n(W)|.
\]

The right-hand side is finite at every finite stage. \(\square\)

## 3. The exact compactness argument

**Lemma 3.1 — PROVED; confidence 0.999.** An inverse sequence of finite nonempty sets

\[
 S_1\longleftarrow S_2\longleftarrow S_3\longleftarrow\cdots
\]

has a nonempty inverse limit. Its bonding maps need not be onto.

**Proof.** For \(m\ge n\), let \(I_{m,n}\) be the image of \(S_m\) in \(S_n\). For fixed \(n\), these are nested nonempty subsets of a finite set, so their intersection

\[
 S'_n=\bigcap_{m\ge n}I_{m,n}
\]

is nonempty and equals \(I_{m,n}\) for all sufficiently large \(m\).

The bonding map sends \(S'_{n+1}\) into \(S'_n\). It is onto: given \(s\in S'_n\), choose \(m\) large enough that the images in both \(S_n\) and \(S_{n+1}\) have stabilized. Since \(s\in I_{m,n}\), choose \(u\in S_m\) mapping to \(s\). Its image in \(S_{n+1}\) belongs to \(I_{m,n+1}=S'_{n+1}\) and maps to \(s\).

Choose \(s_1\in S'_1\). Having chosen \(s_n\), use the surjectivity just proved to choose \(s_{n+1}\in S'_{n+1}\) mapping to it. The resulting sequence is an inverse-limit element. \(\square\)

Apply this lemma to \(T_n\). We obtain classes \(t_n\in T_n\) satisfying \(\rho_n(t_n)=t_{n-1}\) for every \(n\ge2\).

## 4. Rectifying compatible classes to compatible maps

**Lemma 4.1 — PROVED; confidence 0.99.** There are strict representatives \(f_n:X\to P_n\) of the classes \(t_n\) such that

\[
 p_nf_n=f_{n-1},\qquad f_n|_A=a_n
 \quad(n\ge2).
 \tag{4.1}
\]

**Proof.** Choose any representative \(f_1\). Suppose \(f_{n-1}\) has been chosen. Take any representative \(g_n\) of \(t_n\). Compatibility of the classes means that \(p_ng_n\) is homotopic to \(f_{n-1}\) relative to \(A\). Lift a chosen such homotopy through \(p_n\), starting at \(g_n\) and with the constant prescribed boundary \(a_n\) throughout. The endpoint is a representative \(f_n\) of \(t_n\) satisfying (4.1). This construction does not change any earlier \(f_j\). Induction produces the entire countable sequence. \(\square\)

Let

\[
 L=\varprojlim_nP_n.
\]

The compatible maps in (4.1) define a continuous map

\[
 F:X\longrightarrow L,\qquad F(x)=(f_1(x),f_2(x),\ldots).
 \tag{4.2}
\]

Continuity follows from the defining property of the subspace of the product that is the inverse limit. The compatible maps \(q_n\) define \(q:W\to L\), and the boundary condition in (4.1) gives the exact identity

\[
 F|_A=qa.
 \tag{4.3}
\]

## 5. Convergence and transfer of the unit

**Lemma 5.1 — PROVED; confidence 0.99.** The map \(q:W\to L\) is a weak homotopy equivalence.

**Proof.** By May–Ponto (2012), Proposition 2.2.11, the inverse limit of the fibrations \(p_n\) is homotopy equivalent to their homotopy limit. Proposition 2.2.9 gives, for \(i\ge1\), the exact sequence

\[
 0\longrightarrow\varprojlim{}^1_n\pi_{i+1}(P_n)
 \longrightarrow\pi_i(L)
 \longrightarrow\varprojlim_n\pi_i(P_n)
 \longrightarrow0.
 \tag{5.1}
\]

Its component version says that the fibre over the unique element of \(\varprojlim\pi_0(P_n)\) is \(\varprojlim{}^1\pi_1(P_n)\).

For fixed \(i\), the sequence \(\pi_i(P_n)\) is constant with value \(A_i\) and identity transition maps after identifying the groups using \(q_n\), as soon as \(n\ge i\). Thus its inverse limit is \(A_i\). The \(\varprojlim^1\) term for each eventually constant group sequence is trivial. Here is the algebraic check, including nonabelian groups. For a sequence \(G_n\) with bonding maps \(\gamma_n:G_{n+1}\to G_n\), define \(\varprojlim^1G_n\) as the orbit set for the action

\[
 (x_n)\cdot(g_n)
   =(g_n^{-1}x_n\gamma_n(g_{n+1}))_n.
 \tag{5.2}
\]

Suppose all \(\gamma_n\) are isomorphisms for \(n\ge N\). Given \((x_n)\), set \(g_N=1\). For \(n\ge N\), solve

\[
 \gamma_n(g_{n+1})=x_n^{-1}g_n
\]

recursively, which is possible because \(\gamma_n\) is onto. For the finitely many indices below \(N\), define

\[
 g_n=x_n\gamma_n(g_{n+1})
\]

in descending order. Equation (5.2) then sends \((x_n)\) to the sequence of identity elements. There is one orbit.

Consequently (5.1) identifies \(\pi_i(L)\) with \(A_i\). These identifications are induced by the projections to sufficiently high stages, so \(q_*\) is the isomorphism in question. The component version gives that \(L\) is path connected. Hence \(q\) is a weak homotopy equivalence. \(\square\)

It would be unjustified to apply the CW Whitehead theorem directly to \(q:W\to L\) without addressing the topology of \(L\): an inverse limit of CW complexes need not have CW homotopy type. The next argument avoids that issue.

**Lemma 5.2 — PROVED; confidence 0.99.** There is a map \(\mu:X\to W\) whose restriction to \(A\) is exactly \(a\).

**Proof.** Form the mapping-path space

\[
 E_q=\{(w,\gamma)\in W\times L^I:
                   \gamma(0)=q(w)\},
\]

with maps

\[
 r:E_q\to W,\quad r(w,\gamma)=w,
 \qquad p:E_q\to L,\quad p(w,\gamma)=\gamma(1).
\]

The map \(p\) is the mapping-path fibration of \(q\); path concatenation supplies its homotopy lifting property. The map

\[
 j:W\to E_q,\quad j(w)=(w,\text{constant path at }q(w))
\]

satisfies \(rj=\operatorname{id}_W\), and the homotopy

\[
 (w,\gamma)\longmapsto
   (w,\,[t\mapsto\gamma(st)])\qquad(0\le s\le1)
\]

joins \(jr\) to \(\operatorname{id}_{E_q}\). Thus \(j\) and \(r\) are inverse homotopy equivalences. Since \(pj=q\), Lemma 5.1 implies that \(p\) is a weak homotopy equivalence. It is therefore an acyclic Serre fibration.

Consider the lifting square with top map \(ja:A\to E_q\), bottom map \(F:X\to L\), and left map the wedge inclusion. It commutes exactly by (4.3). The acyclic-fibration lifting property of May–Ponto, Theorem 17.2.2, gives \(\widetilde F:X\to E_q\) with

\[
 p\widetilde F=F,
 \qquad\widetilde F|_A=ja.
\]

Define \(\mu=r\widetilde F\). Then

\[
 \mu|_A=rja=a.
\]

This is the required multiplication, with a strict unit on the chosen representative. \(\square\)

**Completion of the proof of Theorem 1.1 — PROVED; confidence 0.98.** Lemmas 2.1–2.3 make every \(T_n\) finite and nonempty. Lemma 3.1 supplies compatible classes. Lemma 4.1 supplies compatible representatives. Lemmas 5.1 and 5.2 turn them into a multiplication on \(W\) with the required unit. \(\square\)

## 6. The exact compatibility criterion and the role of \(\varprojlim^1\)

**Theorem 6.1 — PROVED; confidence 0.99.** For a simple CW complex with the tower and boundary maps above, the following statements are equivalent:

1. \(W\) is an H-space.
2. \(\varprojlim_nT_n\ne\varnothing\).

For this equivalence, no finiteness of the sets \(T_n\) is needed. If every \(T_n\) is nonempty and the images \(\operatorname{im}(T_m\to T_n)\) stabilize as \(m\to\infty\) for every fixed \(n\), then both statements hold.

**Proof.** A multiplication on \(W\) can be made equal to the fold on \(A\) by the homotopy extension property. Its composites with \(q_n\) form compatible elements of \(T_n\), proving the first implication. Starting from an inverse-limit element, Sections 4 and 5 construct a multiplication; their arguments did not use finiteness. Finally, stabilization of the images is exactly the property used in the proof of Lemma 3.1. That proof works without finite sets when stabilization is assumed, and gives a nonempty inverse limit. \(\square\)

**Observation 6.2 — PROVED; confidence 0.999.** The stabilization condition is sufficient, not necessary, for a nonempty inverse limit.

**Proof.** The sequence \(\mathbb Z\xleftarrow{\times2}\mathbb Z\xleftarrow{\times2}\cdots\) has the coherent element consisting of zeros. Its images in the first copy of \(\mathbb Z\) are \(2^m\mathbb Z\), which never stabilize. \(\square\)

**Proposition 6.3 — PROVED using the exact reference stated; confidence 0.98.** Once a compatible sequence of relative multiplication classes has been chosen, there is no additional \(\varprojlim^1\) obstruction to existence. The \(\varprojlim^1\) term describes the ambiguity between realizations of that compatible sequence.

**Proof.** Choose compatible representatives \(f_n\) by Lemma 4.1 and let \(\mathcal M_n\) be the space of maps \(X\to P_n\) whose restriction is exactly \(a_n\), based at \(f_n\). Restriction of \(p_n\) gives maps \(\mathcal M_n\to\mathcal M_{n-1}\). Their relative homotopy lifting property follows by adjunction from the same CW-pair lifting argument used in Lemma 4.1. The spaces may be replaced by their homotopy-equivalent mapping-path fibrant models without changing their components or homotopy groups.

Apply May–Ponto (2012), Proposition 2.2.9, to the tower of these based spaces, with domain the pointed zero-sphere. It gives a surjection

\[
 \pi_0\operatorname{holim}_n\mathcal M_n
   \longrightarrow\varprojlim_n\pi_0\mathcal M_n.
 \tag{6.1}
\]

The fibre over the chosen compatible components is the orbit set

\[
 \varprojlim{}^1_n\pi_1(\mathcal M_n,f_n).
 \tag{6.2}
\]

This is a nonabelian \(\varprojlim^1\) in general, defined by the orbit action (5.2); no abelian-group structure is asserted. One can see the formula directly in the mapping-microscope model. A point in that model consists of points in the \(\mathcal M_n\) and paths between consecutive images. Choosing paths from those points to \(f_n\) replaces all points by the basepoints and leaves a sequence of loops. Changing the chosen paths changes that sequence by (5.2). Homotopies produce precisely this equivalence relation, as recorded by Proposition 2.2.9. In particular the sequence of trivial loops always exists, so (6.2) cannot obstruct the existence of a realization once the compatible components have been selected. The nontrivial existence issue is the possible emptiness of \(\varprojlim T_n\) before such a choice. \(\square\)

## 7. Finiteness of the relative groups

**Lemma 7.1 — PROVED; confidence 0.99.** If \(W\) is simple and each \(A_i\) is finitely generated, then every group \(H_j(X,A;\mathbb Z)\) is finitely generated. Consequently \(H^n(X,A;C)\) is finite whenever \(C\) is finite, and it is finitely generated whenever \(C\) is finitely generated.

**Proof.** May–Ponto, Theorem 4.5.2, gives finite generation of every \(H_j(W;\mathbb Z)\). It also applies to \(X=W\times W\), whose homotopy groups are \(A_i\oplus A_i\) and which is simple. Thus each \(H_j(X;\mathbb Z)\) is finitely generated. For positive \(j\), the reduced homology of \(A=W\vee W\) is the direct sum of the two copies of \(\widetilde H_j(W;\mathbb Z)\); in degree zero \(A\) is connected. The homology exact sequence of \((X,A)\) expresses \(H_j(X,A;\mathbb Z)\) as an extension of a quotient of \(H_j(X;\mathbb Z)\) by a subgroup of \(H_{j-1}(A;\mathbb Z)\). Subgroups, quotients, and extensions of finitely generated abelian groups are finitely generated.

The universal coefficient sequence is

\[
 0\to\operatorname{Ext}^1_{\mathbb Z}
       (H_{n-1}(X,A;\mathbb Z),C)
 \to H^n(X,A;C)
 \to\operatorname{Hom}_{\mathbb Z}
       (H_n(X,A;\mathbb Z),C)\to0.
 \tag{7.1}
\]

For a finitely generated abelian group \(B\), write \(B\cong\mathbb Z^r\oplus\bigoplus_i\mathbb Z/d_i\). Then

\[
 \operatorname{Hom}(B,C)
   \cong C^r\oplus\bigoplus_i C[d_i],
 \qquad
 \operatorname{Ext}^1(B,C)
   \cong\bigoplus_i C/d_iC.
\]

These groups are finite when \(C\) is finite, and finitely generated when \(C\) is finitely generated. The same conclusions hold for the middle group of (7.1). \(\square\)

**Corollary 7.2 — PROVED; confidence 0.99.** Suppose that \(W\) is simple, \(\pi_1W\) is finitely generated abelian, and \(\pi_nW\) is finite for every \(n\ge2\). If every finite Postnikov section is an H-space, then \(W\) is an H-space, regardless of its height.

**Proof.** Lemma 7.1 makes each \(E_n(W)\) finite. Theorem 1.1 applies. No assumption that \(\pi_1W\) is finite occurred: Lemma 2.2 gives the single initial class even when \(\pi_1W=\mathbb Z^r\oplus T\) with \(r>0\). \(\square\)

**Lemma 7.3 — PROVED; confidence 0.99.** For every connected CW complex W, every abelian group M, and every \(n\ge2\), the Postnikov map induces an isomorphism

\[
 \widetilde H^n(P_{n-1}W\wedge P_{n-1}W;M)
 \xrightarrow{\;\cong\;}
 \widetilde H^n(W\wedge W;M).
 \tag{7.2}
\]

Thus \(E_n(W)\) depends only on the lower stage \(P_{n-1}W\) and the coefficient group \(A_n\).

**Proof.** Use a connected CW model with one zero-cell. Such a model is obtained by collapsing a maximal tree in the one-skeleton; the tree is a contractible subcomplex and its collapse is a homotopy equivalence by the homotopy extension property. Construct a model B for \(P_{n-1}W\) from W by attaching cells to kill \(\pi_n\), then \(\pi_{n+1}\), and then successive higher groups. To kill a class in \(\pi_j\), attach a \((j+1)\)-cell along a representative sphere. Attaching these cells does not alter lower homotopy groups. All new cells therefore have dimensions at least \(n+1\). The resulting map is a Postnikov map, and other chosen Postnikov models are equivalent under W, so the cohomology claim can be checked in this model.

The smash product \(B\wedge B\) has a non-basepoint cell for every product of two non-basepoint B-cells, with dimension the sum of their dimensions. A new cell outside \(W\wedge W\) uses at least one new B-cell of dimension at least \(n+1\). The other non-basepoint factor has dimension at least one, since the model has only one zero-cell. Hence every cell of the relative CW pair \((B\wedge B,W\wedge W)\) has dimension at least \(n+2\). Its relative cellular cochain groups in degrees at most \(n+1\) are zero for arbitrary M. The relative cohomology groups in degrees n and \(n+1\) are therefore zero. The cohomology exact sequence gives (7.2). Finally \(X/A=W\wedge W\), so (1.1) is the right-hand side with \(M=A_n\). \(\square\)

## 8. The exact rational criterion for the finite-deviation hypothesis

Write \(V_n=A_n\otimes\mathbb Q\) and let \(G=W_{\mathbb Q}\).

**Lemma 8.1 — PROVED; confidence 0.99.** Under degreewise finite generation, the group \(E_n(W)\) is finite if and only if

\[
 D_n=\widetilde H^n(G\wedge G;V_n)=0.
 \tag{8.1}
\]

**Proof.** By Lemma 7.1, \(E_n(W)\) is finitely generated. A finitely generated abelian group is finite exactly when its tensor product with \(\mathbb Q\) is zero.

Apply the explicit decompositions in the proof of Lemma 7.1 to the universal coefficient sequence. Its \(\operatorname{Ext}\) term is torsion and vanishes after tensoring with \(\mathbb Q\). For a finitely generated group \(B\), the canonical map

\[
 \operatorname{Hom}(B,A_n)\otimes\mathbb Q
 \longrightarrow\operatorname{Hom}(B,V_n)
\]

is an isomorphism: on the free summand it is \(A_n^r\otimes\mathbb Q\cong V_n^r\), and both torsion-summand contributions vanish. Thus coefficient change gives

\[
 E_n(W)\otimes\mathbb Q
 \cong H^n(X,A;V_n).
 \tag{8.2}
\]

The rationalization \(W\to G\) is an isomorphism on rational homology by May–Ponto, Theorem 6.1.2. The field homological Künneth theorem makes the product map an isomorphism on rational homology. The wedge map also has this property because positive reduced homology of a wedge is a direct sum. The exact sequences of the two pairs and exactness of vector spaces therefore make

\[
 (W\times W,W\vee W)\longrightarrow
 (G\times G,G\vee G)
\]

an isomorphism on relative rational homology. Over a field, cohomology with a vector-space coefficient group is the vector-space dual Hom of homology with that coefficient group; the \(\operatorname{Ext}\) term is zero. Hence the map is an isomorphism on relative cohomology with coefficients \(V_n\). Finally, the quotient of the product by the wedge is the smash product, and cohomology of a cofibration pair is the reduced cohomology of its quotient. Combining this with (8.2) gives the canonical isomorphism

\[
 E_n(W)\otimes\mathbb Q\cong D_n.
\]

The equivalence follows. \(\square\)

**Theorem 8.2 — PROVED; confidence 0.98.** Let \(W\) be simple with degreewise finitely generated homotopy groups. Suppose every \(P_nW\) is an H-space and

\[
 \widetilde H^n(W_{\mathbb Q}\wedge W_{\mathbb Q};
                  \pi_nW\otimes\mathbb Q)=0
 \quad\text{for every }n\ge2.
 \tag{8.3}
\]

Then \(W\) is an H-space, with no finite-height assumption.

**Proof.** Lemma 8.1 gives the hypothesis on \(E_n(W)\) in Theorem 1.1. \(\square\)

The next formulation is useful when the rational splitting in the Taylor local step has been supplied.

**Proposition 8.3 — PROVED; confidence 0.99.** Suppose \(G\simeq\prod_{i\ge1}K(V_i,i)\), with \(\dim_{\mathbb Q}V_i<\infty\) for every \(i\). Define

\[
 J=\{n\ge1:V_n\ne0\},\qquad
 C=\{d>0:H^d(G;\mathbb Q)\ne0\}.
\]

Then (8.3) is equivalent to

\[
 J\cap(C+C)=\varnothing.
 \tag{8.4}
\]

Here \(C+C=\{a+b:a,b\in C\}\), with both summands positive.

**Proof.** In a fixed degree, all homology and cohomology groups are finite-dimensional. This follows either from May–Ponto, Theorem 6.1.4, or by discarding the factors \(K(V_i,i)\) with \(i\) larger than that degree and applying the theorem to the finite product. Factors with \(i>d\) have no positive homology in degrees at most \(d\), so discarding them does not change cohomology in those degrees.

Field Künneth and the wedge restriction identify the positive cross terms as

\[
 \widetilde H^n(G\wedge G;V_n)
 \cong V_n\otimes_{\mathbb Q}
       \bigoplus_{\substack{a+b=n\\a,b>0}}
           H^a(G;\mathbb Q)\otimes_{\mathbb Q}H^b(G;\mathbb Q).
 \tag{8.5}
\]

To justify the omission of a relative connecting term, restriction from product cohomology to wedge cohomology is onto in each positive degree: a pair \((u,v)\) is the restriction of \(\operatorname{pr}_1^*u+\operatorname{pr}_2^*v\). Thus relative cohomology injects into product cohomology, with image its cross-term kernel. Formula (8.5) follows. A tensor product of two nonzero vector spaces is nonzero, and a direct sum is zero precisely when every summand is zero. If \(V_n\ne0\), the right-hand side vanishes precisely when \(n\notin C+C\). If \(V_n=0\), it vanishes without further conditions. Degree one is never in \(C+C\), so including it in \(J\) causes no extra restriction. This proves (8.4). \(\square\)

**Proposition 8.4 — PROVED; confidence 0.99.** Assume degreewise finite generation and that every finite Postnikov section of W is an H-space. Put

\[
 G_{<n}=\prod_{1\le i<n}K(V_i,i).
\]

Then

\[
 E_n(W)\otimes\mathbb Q
 \cong\widetilde H^n(G_{<n}\wedge G_{<n};V_n)
 \cong V_n\otimes_{\mathbb Q}
 \bigoplus_{\substack{a+b=n\\a,b>0}}
 H^a(G_{<n};\mathbb Q)\otimes H^b(G_{<n};\mathbb Q).
 \tag{8.6}
\]

No assertion about a global splitting of \(W_{\mathbb Q}\) is needed for this formula.

**Proof.** Lemma 7.3 with rational coefficients identifies the right-hand side of (8.2) with the degree-n cohomology of \(P_{n-1}W\wedge P_{n-1}W\), with coefficients \(V_n\). The space \(P_{n-1}W\) is an H-space by hypothesis. Rationalization preserves finite products, by May–Ponto (2012), Proposition 6.2.3. Rationalizing a multiplication and its unit homotopy therefore makes \((P_{n-1}W)_{\mathbb Q}\) an H-space. It has finite-dimensional rational homotopy groups and finite height. May–Ponto (2012), Theorem 9.1.1, identifies this rational H-space with the finite rational Eilenberg–MacLane product \(G_{<n}\). The rational homology and cohomology comparison used in Lemma 8.1 gives the first isomorphism in (8.6). The product, wedge, and cross-term calculation in (8.5) gives the second. \(\square\)

The degree-pattern tests below can consequently be made in these finite products, before a global rational splitting is selected. Equivalently, one may form the formal GEM \(\mathcal G=\prod_iK(V_i,i)\). In positive cohomological degrees smaller than n its cohomology agrees with that of \(G_{<n}\), because the omitted factors are at least \((n-1)\)-connected. Thus the criterion \(J\cap(C+C)=\varnothing\), with C computed in this formal GEM, is a valid test under the assumptions of Proposition 8.4.

## 9. Concrete rational degree patterns

In this section assume degreewise finite generation and that every finite Postnikov section is an H-space. We use the finite rational products in Proposition 8.4; no global rational splitting is an additional hypothesis.

**Corollary 9.1 — PROVED; confidence 0.99.** In Theorem 8.2, condition (8.3) holds if the rational homotopy is concentrated in one degree \(d\ge1\).

**Proof.** For \(n\ne d\), the coefficient space \(V_n\) in (8.6) is zero. For \(n=d\), the lower rational product \(G_{<d}\) is a point because there are no lower rational homotopy groups. Its positive cohomology is zero, so (8.6) is zero. If all rational homotopy groups vanish, every coefficient space is zero. Lemma 8.1 gives (8.3). \(\square\)

**Corollary 9.2 — PROVED; confidence 0.99.** More generally, suppose the nonzero rational homotopy degrees lie in a finite interval \([m,M]\) with \(M<2m\). Then (8.3) holds.

**Proof.** Each finite lower rational product in (8.6) has no positive cohomology below m: every nontrivial factor is \((m-1)\)-connected, and finite-product Künneth preserves this vanishing. Two positive cohomological degrees therefore add to at least \(2m\), whereas every n with \(V_n\ne0\) is at most \(M<2m\). All cross terms in (8.6) vanish. Lemma 8.1 gives (8.3). \(\square\)

This corollary allows infinitely many nonzero integral homotopy groups above \(M\), provided those groups are finite and the degreewise finite-generation hypothesis is retained.

**Proposition 9.3 — PROVED; confidence 0.99.** There are rational degree patterns of unbounded height satisfying (8.3). One such pattern is

\[
 V_n=\begin{cases}\mathbb Q,&n=3^k\text{ for some }k\ge0,\\
                  0,&\text{otherwise}.
       \end{cases}
 \tag{9.1}
\]

The index set may instead start at \(k=1\), thereby removing rational fundamental group.

**Proof.** Every degree \(3^k\) is odd. Rational cohomology of \(K(\mathbb Q,d)\) for odd \(d\) is exterior on one generator of degree \(d\), by May–Ponto (2012), Proposition 6.7.2. Field Künneth makes rational cohomology of each lower product \(G_{<n}\) exterior on its displayed generators.

Fix \(n=3^k\). A nonzero cross term in (8.6) would be a tensor of two positive-degree monomials in the lower product with total degree \(3^k\). Each lower generator can occur at most once in each exterior monomial and thus at most twice in the tensor. The total degree of any such tensor is consequently at most

\[
 2\sum_{i=0}^{k-1}3^i=3^k-1.
\]

This is smaller than \(n\), a contradiction. For \(k=0\), there are no lower positive-degree generators and the same contradiction is immediate. Thus \(D_{3^k}=0\). For all other \(n\), the coefficient space \(V_n\) is zero. Hence (8.3) holds. \(\square\)

**Proposition 9.4 — PROVED; confidence 0.99.** A more general sufficient pattern has nonzero rational homotopy only in increasing odd degrees \(d_0<d_1<\cdots\), of ranks \(r_i\), with

\[
 d_k>2\sum_{i<k}r_i d_i
 \quad\text{for every }k\ge1.
 \tag{9.2}
\]

**Proof.** Rational cohomology of \(G_{<d_k}\) is exterior on \(r_i\) generators of degree \(d_i\), for \(i<k\). Each occurs at most twice across two tensor factors. The total possible degree is at most the right-hand side of (9.2), strictly smaller than \(d_k\). Therefore no degree-\(d_k\) cross term exists. The argument for the first degree has no lower generators. Formula (8.6) proves the assertion in every degree. \(\square\)

## 10. Application to Taylor operations

**Corollary 10.1 — PROVED relative to the stipulated local step and the completed finite-height theorem; confidence 0.98.** Suppose \(W\) has a Taylor operation of the kind in the question, is of degreewise finite homotopy type, and satisfies (8.3). Then \(W\) is an H-space without any finite Postnikov height assumption.

In particular, this conclusion holds when \(\pi_1W\) is any finitely generated abelian group and every \(\pi_nW\), \(n\ge2\), is finite. It also holds for the rational patterns in Section 9.

**Proof.** The given Taylor simplicity lemma makes \(W\) simple. For every \(n\), its Postnikov section is simple, has finitely generated homotopy groups, and has finite height. A Taylor operation descends to \(P_nW\). To see the factorization without assuming a strict Postnikov functor, construct \(P_nW\) from \(W\) by attaching cells in dimensions at least \(n+2\). The product \((P_nW)^r\) is obtained from \(W^r\) by attaching cells in dimensions at least \(n+2\), because cells in the other factors have nonnegative dimension. Every map from \(W^r\) to an n-type extends over those cells: the obstruction to extending over a d-cell lies in \(\pi_{d-1}\) of the n-type, which is zero when \(d\ge n+2\). Such extensions are unique up to homotopy because the corresponding homotopy-extension obstructions lie in \(\pi_d\), also zero. Therefore composition of the Taylor map with \(q_n\) determines a unique homotopy-class operation on \(P_nW\). Each Taylor identity is an equality between maps from a finite product, and uniqueness of these extensions transfers that equality to the Postnikov section. Any normalization identity present in the original operation is transferred by the same argument.

Apply the given local step to \(P_nW\), then the completed finite-height LC theorem. It follows that \(P_nW\) is an H-space for every \(n\). Condition (8.3) and Theorem 8.2 now imply that \(W\) is an H-space. The higher-finite special case uses Corollary 7.2. The rational patterns use Section 9. \(\square\)

The hypothesis “every finite Postnikov section is an H-space” can instead be supplied by any independent argument. The compactness theorem does not use a Taylor operation after that point.

## 11. What remains and an adversarial audit

**Example 11.1 — PROVED; confidence 0.99.** Finiteness of all \(E_n(W)\) is sufficient but not necessary for the existence of an H-space structure. Let

\[
 W=K(\mathbb Z,2)\times K(\mathbb Z,4).
\]

Coordinate addition in the models of Lemma 1.2 is an H-space multiplication. On the other hand, \(V_4=\mathbb Q\), and \(G_{<4}=K(\mathbb Q,2)\). Its degree-two cohomology is \(\mathbb Q\), by May–Ponto, Proposition 6.7.2. The term with \(a=b=2\) in (8.6) gives

\[
 E_4(W)\otimes\mathbb Q\cong\mathbb Q.
\]

Thus \(E_4(W)\) is infinite even though W is already an H-space. \(\square\)

**Scope statement — PROVED as a description of the argument; confidence 0.999.** The proof removes finite height when the degreewise multiplication-lift groups are finite. It does not prove that arbitrary Taylor spaces satisfy this extra condition, and it does not resolve the unrestricted normalized Taylor-to-H implication without finite type. Rational GEMs can have nonzero cross-term spaces, so the vanishing condition cannot be inferred merely from rational splitting.

**Audit — confidence 0.98.** The point most likely to be mishandled is the passage from nonempty finite-stage multiplication sets to a compatible system. No transition map was assumed onto. Lemma 3.1 first passes to the stabilized image subsets, proves their transition maps onto, and only then chooses a compatible sequence. Without finiteness or an independently established stabilization condition, this argument fails exactly there; finite-stage H-structures alone do not supply a coherent sequence.

A second topological hazard is to regard the ordinary inverse limit of Postnikov stages as a CW complex. The proof makes no such claim. Lemma 5.1 only gives a weak equivalence to that limit, and Lemma 5.2 uses an acyclic mapping-path fibration to transport the multiplication with its wedge boundary intact.

## 12. References used

1. **J. P. May and K. Ponto (2012), _More Concise Algebraic Topology: Localization, Completion, and Model Categories_.** Theorem 3.2.1 (simple spaces and principal Postnikov towers); Theorem 4.5.2 (degreewise finite generation and finite CW type); Theorem 6.1.2 (localization on homotopy and homology); Theorem 6.1.4 (localized finite type); Proposition 6.2.3 (localization of products); Proposition 6.7.2 (rational Eilenberg–MacLane cohomology); Theorem 9.1.1 (rational H-space splitting); Propositions 2.2.9 and 2.2.11 (homotopy limits and inverse limits of fibrations); Theorem 17.2.2 (the Serre model structure and the precise lifting properties used above). Author PDF: <https://www.math.uchicago.edu/~may/BOOKS/KateBookFinal.pdf>.
2. **Allen Hatcher (2002), _Algebraic Topology_.** Theorem 3.2 (cohomological universal coefficients); Theorem 3.15 in the current author-hosted edition (cohomological Künneth theorem); Theorem 4.5 (CW Whitehead theorem); Theorem 4.57 (cohomology representability). Author PDF: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.
3. **J. Peter May (1967), _Simplicial Objects in Algebraic Topology_.** Theorems 14.1 and 14.3, Theorems 16.1 and 16.6, and Theorem 23.9, for the strict topological abelian Eilenberg–MacLane models used in Lemmas 1.2, 2.2, and 2.3. Author scan: <https://www.math.uchicago.edu/~may/BOOKS/Simp.pdf>. Searchable primary-text scan: <https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/May-simp-ocr.pdf>.
4. **Stephan Klaus (2003), “H-space structures and Postnikov approximations,” _Mathematical Proceedings of the Cambridge Philosophical Society_ 135(1), 133–135, Theorem 1.** DOI: <https://doi.org/10.1017/S0305004103006728>. Cited to acknowledge the established finite-homotopy-group special case, not as an input to the proof above.
