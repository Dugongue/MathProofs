---
title: "Taylor operations on rational two-stage spaces"
subtitle: "Complete proofs, explicit arithmetic obstructions, and a torsion gluing theorem"
date: "27 November 2026"
geometry: "margin=1in"
fontsize: 10pt
colorlinks: true
toc: true
toc-depth: 1
numbersections: false
header-includes:
  - '\usepackage{amsmath,amssymb}'
  - '\allowdisplaybreaks'
  - '\emergencystretch=3em'
---

**PROVED — a simple two-stage space with arbitrary rational lower homotopy and arbitrary abelian upper homotopy admits a normalized Taylor operation exactly when its Postnikov invariant vanishes, exactly when it is an H-space. Confidence: 0.98.**

## Executive summary

**PROVED, confidence 0.98.** The principal theorem covers every pair of degrees \(1\le d<n\), with no finite generation, cardinality, or rational-dimension restriction. It extends the earlier rational fundamental-group two-type result to arbitrary two-stage degrees. The proof uses products of rational homology-sphere telescopes to detect every integral obstruction, including Ext classes invisible under rational coefficients. Mixed-input terms vanish because the relevant probes lift; Taylor identities eliminate the remaining terms. The coefficient components are removed in the order required to justify every lift.

**PROVED, confidence 0.99.** An explicit factorial-resolution class produces examples in every lower degree whose prime localizations and rationalization split, although the original spaces are not H-spaces. Every normalized operation on these examples induces a coordinate projection on the lower homotopy group. They therefore admit no normalized Taylor operation.

**PROVED, confidence 0.99.** A separate chapter proves a finite-prime local-to-global H-space theorem without finite type or finite Postnikov height, when one fixed finite set of primes supports all higher homotopy groups. Its fundamental group may be an arbitrary abelian group.

No historical priority claim is made. No proof-assistant verification is claimed. The exact arithmetic checks are supplementary computations; the infinite assertions have written proofs.

## Conventions, status, and scope

A normalized operation \(t:W^a\to W\) satisfies \(t\Delta_a\simeq\operatorname{id}_W\). This is an explicit assumption: variable-identification identities by themselves are satisfied by constant maps. All Taylor statements in the new work either include this normalization or state the weaker diagonal-surjectivity hypothesis they actually use.

Each theorem and lemma carries a status and confidence. Every intermediate assertion inside a proof inherits that proof's **PROVED** label and confidence. A cited foundation is imported only at its precise numbered location. Definitions do not make an empirical confidence claim. A **COMPUTATIONAL** label denotes only a finite calculation actually run, and not a proof of the full topological assertion.

All products are compactly generated, all maps and homotopies are pointed, and all spaces are taken in the CW homotopy category when a CW replacement is required. An H-structure has a homotopy unit; no associativity is assumed. Numbered lemmas and equations are local to each chapter. The proof of the main theorem is independent of the previous finite-type local-to-global theorem and independent of the stipulated Taylor local step.

The accompanying cumulative archive preserves the earlier research deliverables unchanged. The present manuscript contains the full new work, rather than a compressed description of it.



# Part I. The complete two-stage characterization

**PROVED; confidence 0.98.** Let \(1\le d<n\). Let \(W\) be a pointed connected simple CW complex whose only possibly nonzero homotopy groups are
\[
\pi_dW=V,\qquad \pi_nW=B,
\]
where \(V\) is an arbitrary rational vector space and \(B\) is an arbitrary abelian group. Then the following conditions are equivalent:

1. \(W\) admits a normalized Taylor operation.
2. \(W\) admits a multiplication with a homotopy unit.
3. Its Postnikov invariant \(k\in H^{n+1}(K(V,d);B)\) vanishes.
4. \(W\simeq K(V,d)\times K(B,n)\).

No finite generation, countability, or finite rational dimension is required. The proof covers even \(d\), where rational Eilenberg–MacLane spaces have nonzero homology in arbitrarily high degrees.

## 1. Conventions and precise imported results

All maps and homotopies are pointed. Products are formed in compactly generated spaces; when cellular arguments are used, they have their CW product topology. This convention does not change the homotopy classes or homology of the products in the argument. A normalized operation of arity \(a\ge1\) is a map \(t:W^a\to W\) satisfying \(t\Delta_a\simeq\mathrm{id}_W\). For a word \(\alpha\in\{x,y\}^a\), let \(d_\alpha:W^2\to W^a\) select the indicated coordinate in each position. The Taylor condition is that, for every \(i\in\{1,\ldots,a\}\), there are words \(\alpha,\beta\) with \(\alpha_i\ne\beta_i\) and \(td_\alpha\simeq td_\beta\).

**PROVED foundational inputs, used by precise citation; confidence 0.99.** We use the following results in their pointed CW formulations.

* Hatcher (2002), Theorem 3.2: the natural cohomology universal coefficient exact sequence.
* Hatcher (2002), Theorem 3B.6: the natural homology Künneth exact sequence.
* Hatcher (2002), Theorem 4.32: the Hurewicz isomorphism in the first nonzero degree of a simply connected space. In degree one we use Theorem 2A.1, identifying \(H_1\) with the abelianization of \(\pi_1\).
* Hatcher (2002), Theorem 4.5: a weak equivalence between CW complexes is a homotopy equivalence.
* Hatcher (2002), Proposition A.1: a compact subset of a CW complex lies in a finite subcomplex. Theorem A.6 identifies the weak CW product topology with the compactly generated product topology.
* May–Ponto (2012), Equation (3.4.1): reduced cohomology is represented by pointed maps to Eilenberg–MacLane spaces.
* May–Ponto (2012), Corollary 2.2.3: the homotopy groups of a map and its homotopy fiber fit into the homotopy-fiber exact sequence.
* May–Ponto (2012), Lemma 3.4.2: a fibration with Eilenberg–MacLane fiber and trivial fundamental-group action is the homotopy fiber of its principal classifying map.
* May–Ponto (2012), Theorem 5.2.8: if the coefficient group is rational, the reduced integral homology of its Eilenberg–MacLane space is rational.
* May–Ponto (2012), Proposition 6.7.2: the rational cohomology algebra of \(K(\mathbb Q,d)\) is polynomial on its fundamental class for even \(d\), and exterior on that class for odd \(d\).

The arguments special to the theorem, including all passages to infinite-dimensional vector spaces, are proved below. The exact UCT used is
\[
0\longrightarrow\operatorname{Ext}^1_{\mathbb Z}(H_{j-1}(X;\mathbb Z),C)
\longrightarrow H^j(X;C)
\longrightarrow\operatorname{Hom}_{\mathbb Z}(H_j(X;\mathbb Z),C)
\longrightarrow0.
\tag{1.1}
\]
No natural splitting of this sequence is asserted.

## 2. The rational Pontryagin algebra of the base

For a rational vector space \(V\), put
\[
S_d^r(V)=
\begin{cases}
\operatorname{Sym}_{\mathbb Q}^r(V),&d\text{ even},\\
\Lambda_{\mathbb Q}^r(V),&d\text{ odd}.
\end{cases}
\]
The elements of \(V\) have degree \(d\). The products of their degree-\(d\) homology classes are Pontryagin products induced by addition on \(K(V,d)\).

**Lemma 2.1 — PROVED; confidence 0.99.** For every rational vector space \(V\), there is a natural isomorphism of graded algebras
\[
H_*(K(V,d);\mathbb Q)\cong\bigoplus_{r\ge0}S_d^r(V),
\tag{2.1}
\]
where \(S_d^r(V)\) lies in degree \(rd\). For every positive degree \(j\), the coefficient map
\[
H_j(K(V,d);\mathbb Z)\longrightarrow H_j(K(V,d);\mathbb Q)
\]
is an isomorphism. In particular
\[
H_j(K(V,d);\mathbb Z)=0\quad(d\nmid j),\qquad
H_{rd}(K(V,d);\mathbb Z)\cong S_d^r(V)\quad(r\ge1).
\tag{2.2}
\]

**Proof.** First consider \(V=\mathbb Q\). Let \(u\in H^d(K(\mathbb Q,d);\mathbb Q)\) be the class corresponding to the identity on \(\mathbb Q\). By the cited Proposition 6.7.2, its powers form a basis when \(d\) is even, and only \(1,u\) are nonzero when \(d\) is odd. The universal coefficient theorem over the field \(\mathbb Q\) identifies cohomology with the linear dual of rational homology. If a homology group contained two independent vectors, extend them to a basis and take the two coordinate functionals; its dual would have dimension at least two. Since the computed cohomology has dimension at most one in each degree, rational homology does too. Thus these finite-dimensional homology groups are the duals of the computed cohomology groups.

Here and below, addition on \(K(C,d)\) is obtained by representing the sum of the two pulled-back fundamental classes. Both triple bracketings of this addition represent the sum of the three fundamental classes, interchanging two inputs leaves the two-term sum unchanged, and setting either input to the basepoint leaves the other fundamental class. Representability therefore proves associativity, commutativity, and the unit law up to pointed homotopy. Its induced Pontryagin product is consequently an associative graded-commutative unital product on homology.

The addition map \(\mu:K(\mathbb Q,d)^2\to K(\mathbb Q,d)\) satisfies
\[
\mu^*u=u\otimes1+1\otimes u.
\tag{2.3}
\]
Indeed, both sides represent the homomorphism \((x,y)\mapsto x+y\) in degree \(d\). Representability and (1.1), together with Hurewicz, identify maps into \(K(\mathbb Q,d)\) by that homomorphism. If \(d=1\), the same conclusion follows from degree-one representability and abelianization.

When \(d\) is even, choose the homology class \(z_r\) dual to \(u^r\). Expanding \((u\otimes1+1\otimes u)^{r+s}\) and pairing with \(z_r\otimes z_s\) gives
\[
z_rz_s=\binom{r+s}{r}z_{r+s}.
\]
Consequently \(z_1^r=r!z_r\). Since \(r!\) is invertible over \(\mathbb Q\), the Pontryagin algebra is freely polynomial on \(z_1\). When \(d\) is odd, there are no positive homology groups beyond degree \(d\), so \(z_1^2=0\); the algebra is exterior. This proves (2.1) in dimension one.

For \(V=\mathbb Q^m\), the finite product \(K(\mathbb Q,d)^m\) has exactly the homotopy groups of \(K(V,d)\). The Hurewicz/UCT construction in degree \(d\) produces a map inducing the specified isomorphism on \(\pi_d\); its source and target have no other nonzero homotopy groups. Whitehead's theorem makes it an equivalence. The Künneth theorem over \(\mathbb Q\) identifies its homology algebra with the tensor product of \(m\) copies of the preceding one-generator algebra. The interchange of factors introduces the sign \((-1)^{d^2}\), so the result is the symmetric algebra when \(d\) is even and the exterior algebra when \(d\) is odd.

For arbitrary \(V\), choose a basis \((e_i)_{i\in I}\), and let \(Y_i\) be a pointed CW model of \(K(\mathbb Q,d)\) with one zero-cell. Form the weak product \(Y\): it is the union of the products \(Y_J=\prod_{i\in J}Y_i\), over finite subsets \(J\subset I\), with cells the finite products of cells of the factors and with the weak CW topology. This gives a CW complex. Every cell has finitely many nonbasepoint coordinates, and its closure is contained in a finite product of finite subcomplexes, so closure finiteness holds. The weak topology is the one prescribed by these characteristic maps.

Any map from a sphere, any homotopy between two such maps, and any singular simplex has compact image. By Proposition A.1 its image is contained in a finite subcomplex of \(Y\), which in turn uses only finitely many coordinates. It is therefore contained in one \(Y_J\). It follows directly that
\[
\pi_q(Y)=\mathop{\mathrm{colim}}_{J\text{ finite}}\pi_q(Y_J),
\qquad
H_q(Y;\mathbb Q)=\mathop{\mathrm{colim}}_{J\text{ finite}}H_q(Y_J;\mathbb Q).
\tag{2.4}
\]
For the homology assertion, a cycle is a finite sum of singular simplices and lies in some \(Y_J\). A chain witnessing that it is a boundary also lies in a possibly larger finite product. These are the surjectivity and injectivity statements needed for (2.4).

The first equality in (2.4) identifies \(\pi_dY\) with \(\bigoplus_{i\in I}\mathbb Q=V\) and all other homotopy groups with zero. Thus \(Y\) is a model of \(K(V,d)\). The second equality identifies its Pontryagin algebra with the union of the free graded-commutative algebras on all finite subsets of the basis. Every algebraic monomial and relation uses finitely many basis vectors, so this union is exactly the algebra in (2.1).

The resulting identification is natural in \(V\). A homomorphism \(F:V\to V'\) is rational linear because division by each nonzero integer is unique. The map \(K(F,d)\) is an H-map up to homotopy: its composite with addition and the sum of its two composites induce the same map \((v,w)\mapsto F(v+w)=F(v)+F(w)\) on \(\pi_d\), and maps from \(K(V,d)^2\) into \(K(V',d)\) are determined by that degree-\(d\) homomorphism, as above. Therefore it preserves Pontryagin products. It acts on the generators as \(F\), so it acts in degree \(rd\) as \(S_d^r(F)\). This proves basis independence and naturality.

Finally, Theorem 5.2.8 says that each positive integral homology group is a rational vector space. Tensoring a free chain complex with \(\mathbb Q\) commutes with its homology. To see this directly, write a rational chain with a common positive denominator as \(c/m\), with \(c\) integral. If \(c/m\) is a cycle, then \(\partial c=0\), since the integral chain groups are torsion-free. If an integral cycle \(c\), viewed with denominator \(m\), is a boundary \(\partial(b/k)\), then \(kc=m\partial b\), so its class is already zero after rationalizing integral homology. These statements give the surjectivity and injectivity of the canonical map from rationalized integral homology to rational homology. Tensoring a rational vector space with \(\mathbb Q\) leaves it unchanged, proving (2.2). \(\square\)

## 3. Coefficient groups and natural multilinear forms

**Lemma 3.1 — PROVED; confidence 0.99.** Every abelian group \(B\) decomposes as
\[
B=D\oplus R,
\tag{3.1}
\]
where \(D\) is divisible and injective and \(R\) has no nonzero divisible subgroup. Hence \(\operatorname{Hom}(\mathbb Q,R)=0\), and \(\operatorname{Ext}^1(U,D)=0\) for every abelian group \(U\).

**Proof.** Let \(D\) be the sum of all divisible subgroups of \(B\). Every element of this sum is a finite sum. To divide it by a positive integer, divide its summands inside their respective divisible subgroups and add the resulting elements. Thus \(D\) is divisible.

We prove its injectivity. Given an inclusion \(A\subset C\) and a homomorphism \(f:A\to D\), consider all extensions of \(f\) to intermediate subgroups, ordered by extension. The union along a chain is a homomorphism on the union of its domains, so Zorn's lemma gives a maximal extension \(g:A'\to D\). If \(c\in C\setminus A'\), let \(I=\{m\in\mathbb Z:mc\in A'\}\). This ideal is either zero or \(h\mathbb Z\) for an integer \(h>0\). In the zero case set \(z=0\); in the other case choose \(z\in D\) with \(hz=g(hc)\). Define
\[
g'(a+mc)=g(a)+mz.
\]
If \(a+mc=a'+m'c\), then \((m-m')c\in A'\). In the zero case \(m=m'\). In the other case \(m-m'=qh\), and \(g((m-m')c)=qg(hc)=(m-m')z\). In both cases the displayed definition is well-defined. It extends \(g\) to \(A'+\mathbb Zc\), contradicting maximality. Thus \(A'=C\), proving injectivity.

Extend \(\mathrm{id}_D:D\to D\) along \(D\subset B\) to a retraction \(\rho:B\to D\), and put \(R=\ker\rho\). This gives (3.1). Any divisible subgroup of \(R\) is a divisible subgroup of \(B\), so it lies in \(D\cap R=0\). The image of any map \(\mathbb Q\to R\) is divisible and is therefore zero. A free resolution computes \(\operatorname{Ext}^1(U,D)\) as a cokernel of restriction into \(D\), and injectivity says that restriction is onto. Thus the Ext group vanishes. \(\square\)

Define the rational vector spaces
\[
E_R=\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,R),\qquad
J_D=\operatorname{Hom}_{\mathbb Z}(\mathbb Q,D),
\tag{3.2}
\]
with scalar multiplication induced by precomposition on \(\mathbb Q\).

**Lemma 3.2 — PROVED; confidence 0.99.** For every rational vector space \(U\) and abelian group \(C\), there are natural isomorphisms
\[
\operatorname{Ext}^1(U,C)\cong
\operatorname{Hom}_{\mathbb Q}(U,\operatorname{Ext}^1(\mathbb Q,C)),
\tag{3.3}
\]
\[
\operatorname{Hom}_{\mathbb Z}(U,C)\cong
\operatorname{Hom}_{\mathbb Q}(U,\operatorname{Hom}_{\mathbb Z}(\mathbb Q,C)).
\tag{3.4}
\]

**Proof.** A free resolution of \(\mathbb Q\) has middle group \(F=\bigoplus_{j\ge1}\mathbb Ze_j\), map \(e_j\mapsto1/j!\), and kernel freely generated by \(e_j-(j+1)e_{j+1}\). Generation follows by reducing any relation supported through \(e_N\) to a multiple of \(e_N\); its rational image forces that multiple to be zero. Independence follows by taking the largest index in a proposed finite relation: the coefficient of \(e_{N+1}\) is nonzero. Taking direct sums of this resolution over a rational basis of \(U\) gives a length-one free resolution of \(U\).

Write the resulting resolution as \(0\to L_U\to F_U\to U\to0\). By the free-resolution definition,
\[
\operatorname{Ext}^1(U,C)
=\operatorname{coker}\bigl(\operatorname{Hom}(F_U,C)
\longrightarrow\operatorname{Hom}(L_U,C)\bigr).
\tag{3.9}
\]
Given \(f:U\to U'\), freeness lifts it to \(\widetilde f:F_U\to F_{U'}\), and that lift carries \(L_U\) into \(L_{U'}\). Precomposition defines pullback on the displayed cokernel. If \(\widetilde f_1\) and \(\widetilde f_2\) lift the same map, their difference \(h\) has image in \(L_{U'}\). For any \(\lambda:L_{U'}\to C\), the difference between the two pullbacks of \(\lambda\) is the restriction to \(L_U\) of the map \(\lambda h:F_U\to C\). This difference is zero in (3.9). Thus pullback is independent of the lift. Lifting a sum by the sum of chosen lifts proves additivity; lifting a composite by the composite proves functoriality. Comparison maps between resolutions, obtained by lifting identity maps, show independence of the particular free resolution.

Precomposition by the scalar map \(q\mapsto aq\) gives the rational vector-space operations on \(\operatorname{Ext}^1(\mathbb Q,C)\): additivity gives the additive law, functoriality gives the multiplicative law, and precomposition by a reciprocal inverts multiplication by every nonzero rational. The same verification applies to Hom, where no resolution is needed because composition of homomorphisms is already well-defined.

For \(u\in U\), let \(\alpha_u:\mathbb Q\to U\) send \(q\) to \(qu\). The map
\[
\xi\longmapsto (u\longmapsto\alpha_u^*\xi)
\]
is rational linear because \(\alpha_{u+v}=\alpha_u+\alpha_v\) and \(\alpha_{au}=\alpha_u\circ\mu_a\). It is an isomorphism: on a rational basis of \(U\), the chosen free resolution is a direct sum, its Hom complex is a product, and its cokernel is the product of the one-dimensional cokernels. The image of a product of homomorphisms is the product of their images, because preimages may be chosen independently in each coordinate. Thus the cokernel is precisely the unrestricted family of values on that basis, as required. The definition by \(\alpha_u\), rather than by the basis, proves naturality.

For (3.4), send \(h:U\to C\) to the map \(u\mapsto(q\mapsto h(qu))\). Its inverse evaluates the resulting Hom element at \(1\in\mathbb Q\). Rational linearity ensures that these two constructions are inverse, and their formulas prove naturality. \(\square\)

Put \(X=K(V,d)\). The coefficient splitting gives \(k=(k_R,k_D)\). By (1.1), Lemmas 2.1, 3.1, and 3.2, there are natural identifications
\[
H^{n+1}(X;R)\cong
\operatorname{Hom}_{\mathbb Q}(H_n(X;\mathbb Z),E_R),
\tag{3.5}
\]
\[
H^{n+1}(X;D)\cong
\operatorname{Hom}_{\mathbb Q}(H_{n+1}(X;\mathbb Z),J_D).
\tag{3.6}
\]
For (3.5), every homomorphism from a rational vector space into \(R\) is zero: restrict to each rational line and apply Lemma 3.1. For (3.6), the Ext group is zero because \(D\) is injective.

**Corollary 3.3 — PROVED; confidence 0.99.** If \(d\nmid n\), then \(k_R=0\). If \(n=rd\), where necessarily \(r\ge2\), then \(k_R\) is determined by the rational multilinear form
\[
\omega_R(v_1,\ldots,v_r)
=\kappa_R(v_1\cdots v_r)\in E_R,
\tag{3.7}
\]
where \(\kappa_R:H_n(X;\mathbb Z)\to E_R\) is its image in (3.5) and the product is the Pontryagin product. The form is symmetric for even \(d\) and alternating for odd \(d\), and \(k_R=0\) exactly when \(\omega_R=0\).

If \(d\nmid n+1\), then \(k_D=0\). If \(n+1=sd\), where necessarily \(s\ge2\), the corresponding statement holds with
\[
\omega_D(v_1,\ldots,v_s)
=\kappa_D(v_1\cdots v_s)\in J_D.
\tag{3.8}
\]

**Proof.** The homology groups in (3.5) and (3.6) vanish in the indicated nondivisible degrees by Lemma 2.1. In a divisible degree, products of degree-\(d\) classes span the homology group, so the linear functional is determined by its values on those products. The product relations give the stated symmetry, and multilinearity follows from bilinearity of the Pontryagin product and rational linearity of \(\kappa_R\) or \(\kappa_D\). Since \(n>d\), a nonzero quotient \(n/d\) or \((n+1)/d\) in this situation is at least two. \(\square\)

## 4. Rational homology-sphere probes

**Lemma 4.1 — PROVED; confidence 0.99.** For each \(d\ge1\), there is a pointed connected CW complex \(T_d\) with
\[
H_0(T_d;\mathbb Z)=\mathbb Z,\qquad H_d(T_d;\mathbb Z)=\mathbb Q,
\qquad \widetilde H_j(T_d;\mathbb Z)=0\ (j\ne d).
\tag{4.1}
\]
For \(d\ge2\), it is \((d-1)\)-connected. For any finite set \(J\),
\[
H_{qd}(T_d^J;\mathbb Z)\cong
\bigoplus_{\substack{I\subseteq J\\|I|=q}}\mathbb Q\quad(q>0),
\tag{4.2}
\]
and every positive homology group in a degree not of this form is zero. For any list \((v_j)_{j\in J}\) of elements of \(V\), there is a map
\[
a_{\mathbf v}:T_d^J\to X
\tag{4.3}
\]
whose induced map on \(H_d\) sends the \(j\)-th coordinate generator to \(v_j\). Its effect on the top product class is
\[
(a_{\mathbf v})_*(z_1\times\cdots\times z_{|J|})
=v_1\cdots v_{|J|}.
\tag{4.4}
\]

**Proof.** Take the mapping telescope of the based degree maps
\[
S^d\xrightarrow{2}S^d\xrightarrow{3}S^d\xrightarrow{4}\cdots.
\tag{4.5}
\]
The telescope is made by gluing the mapping cylinders along their end spheres. Choose cellular degree maps, give it the induced CW structure, and use the initial sphere's basepoint as its basepoint. We retain the uncollapsed telescope throughout.

The height map to \([1,\infty)\) sends compact subsets into bounded intervals. Thus every singular chain and every chain witnessing a boundary lies in a finite subtelescope. A finite subtelescope deformation retracts onto its last sphere, and the map from one such retract to the next induces multiplication by its indicated degree on \(H_d\). Homology is therefore the direct limit of \(\mathbb Z\xrightarrow2\mathbb Z\xrightarrow3\cdots\) in degree \(d\), is \(\mathbb Z\) in degree zero, and is zero elsewhere. The displayed direct limit is \(\mathbb Q\), by identifying the generator at stage \(j\) with \(1/j!\). This proves (4.1). A sphere or a homotopy from a sphere in any degree below \(d\) is also contained in a finite subtelescope; its image becomes nullhomotopic in the retract \(S^d\). This proves the connectivity assertion.

The group \(\mathbb Q\) is flat: it is the directed union of the free rank-one groups \((1/j!)\mathbb Z\), and tensoring an injection with this union remains injective because every alleged kernel element and every relation witnessing its vanishing are already witnessed at a finite stage. Thus all Tor terms in the integral Künneth sequence for products of \(T_d\)'s vanish. Iterating the Künneth isomorphism gives (4.2), because a positive-degree contribution selects degree \(d\) from a subset of the factors and degree zero from the remaining ones. Products of copies of \(\mathbb Q\) under tensor over \(\mathbb Z\) are again \(\mathbb Q\), via multiplication of scalars.

By (1.1), \(H^d(T_d;V)=\operatorname{Hom}(\mathbb Q,V)\): if \(d>1\) the preceding homology group is zero; if \(d=1\) it is \(\mathbb Z\), whose Ext group is zero. Representability yields a map \(a_v:T_d\to X\) corresponding to \(q\mapsto qv\). Define (4.3) to be the sum, under addition of \(X\), of the maps \(a_{v_j}\) from the separate factors. This gives its stated map on \(H_d\). The definition of the Pontryagin product gives (4.4), by applying the iterated addition map to the external product of the degree-\(d\) classes. \(\square\)

**Lemma 4.2 — PROVED; confidence 0.99.** A pointed map \(a:T\to X\) lifts through \(q:W\to X\), up to pointed homotopy, if and only if \(a^*k=0\).

**Proof.** To construct \(q\), first suppose \(d\ge2\). Hurewicz identifies \(H_d(W;\mathbb Z)\) with \(V\), while \(H_{d-1}(W;\mathbb Z)=0\). The UCT therefore identifies \(H^d(W;V)\) with \(\operatorname{Hom}(V,V)\). Represent the identity by a pointed map \(q:W\to X\). If \(d=1\), abelianization gives \(H_1(W;\mathbb Z)=V\), and \(\operatorname{Ext}^1(H_0(W;\mathbb Z),V)=\operatorname{Ext}^1(\mathbb Z,V)=0\); the same construction in degree one gives \(q\). Thus \(q\) induces the identity on \(\pi_d\). The homotopy-fiber exact sequence shows that its fiber has the sole nonzero homotopy group \(B\) in degree \(n\): in degree \(d\), the map between the two copies of \(V\) is the identity, and in every other degree the only nonzero term is the copy of \(B\) in degree \(n\).

The action of \(\pi_1X\) on \(B\) is trivial. For \(d>1\), the group \(\pi_1X\) is zero. For \(d=1\), the map \(q\) identifies \(\pi_1W\) with \(\pi_1X\), and simplicity of \(W\) makes the action on its group \(\pi_nW=B\) trivial. Lemma 3.4.2 now identifies \(W\), over \(X\), with the homotopy fiber of a representative \(k:X\to K(B,n+1)\). Explicitly that fiber consists of pairs \((x,\gamma)\) where \(\gamma\) is a path from \(k(x)\) to the basepoint. A lift makes \(ka\) nullhomotopic via these paths. Conversely, if \(a^*k=0\), representability gives a pointed nullhomotopy \(N\) of \(ka\), and \(z\mapsto(a(z),N(z,-))\) is a lift to the path-fiber model. Transport across the equivalence gives a lift to \(W\). \(\square\)

**Lemma 4.3 — PROVED; confidence 0.99.** Suppose \(n=rd\). Then every probe \(a_{\mathbf v}:T_d^J\to X\) with \(|J|<r\) lifts to \(W\). Suppose instead that \(k_R=0\) and \(n+1=sd\). Then every probe with \(|J|<s\) lifts to \(W\).

**Proof.** In the first assertion, all homology of the source above degree \(|J|d\) is zero. Since \(|J|d<rd=n\), its homology in degrees \(n\) and \(n+1\) is zero. The UCT makes \(H^{n+1}(T_d^J;B)=0\), and Lemma 4.2 applies.

For the second assertion, the \(R\)-component pulls back to zero by the assumed global vanishing. The source has \(H_{n+1}=0\), since \(|J|d<sd=n+1\). The UCT with injective coefficients \(D\) therefore gives \(H^{n+1}(T_d^J;D)=0\), without requiring \(H_n=0\). This kills the other component, so Lemma 4.2 again applies. \(\square\)

## 5. Operations force mixed coefficients to vanish

Let \(t:W^a\to W\) be any pointed map. Its map on the first nonzero homotopy group has the form
\[
t_*(v_1,\ldots,v_a)=\sum_{i=1}^a F_i(v_i),
\tag{5.1}
\]
for rational linear endomorphisms \(F_i\) of \(V\).

**Lemma 5.1 — PROVED; confidence 0.99.** As pointed maps into \(X=K(V,d)\),
\[
qt\simeq\sum_{i=1}^a K(F_i,d)q\operatorname{pr}_i.
\tag{5.2}
\]

**Proof.** For \(d\ge2\), \(W^a\) is \((d-1)\)-connected. Hurewicz gives \(H_d(W^a;\mathbb Z)=\pi_d(W^a)=V^a\), and \(H_{d-1}=0\). The UCT and representability identify pointed maps from \(W^a\) to \(K(V,d)\) with homomorphisms \(V^a\to V\). Both sides in (5.2) induce (5.1). When \(d=1\), simplicity makes \(\pi_1W=V\) abelian. Abelianization identifies \(H_1(W^a;\mathbb Z)=V^a\), and the UCT Ext term is \(\operatorname{Ext}^1(\mathbb Z,V)=0\). Degree-one representability gives the same identification and the same conclusion. \(\square\)

**Lemma 5.2 — PROVED; confidence 0.99.** If \(n=rd\), then for every nonconstant function \(\rho:\{1,\ldots,r\}\to\{1,\ldots,a\}\) and vectors \(v_1,\ldots,v_r\in V\),
\[
\omega_R(F_{\rho(1)}v_1,\ldots,F_{\rho(r)}v_r)=0.
\tag{5.3}
\]
If \(k_R=0\) and \(n+1=sd\), then the corresponding assertion holds for \(\omega_D\) and every nonconstant \(\rho:\{1,\ldots,s\}\to\{1,\ldots,a\}\).

**Proof.** We give the full common construction, with \(h=r\) in the first assertion and \(h=s\) in the second. For each operation coordinate \(i\), put \(J_i=\rho^{-1}(i)\). Nonconstancy of \(\rho\) means \(|J_i|<h\) for every \(i\). On \(T_d^{J_i}\), take the probe sending the generator in coordinate \(j\) to \(v_j\). Lemma 4.3 gives a lift \(b_i:T_d^{J_i}\to W\). For an empty set \(J_i\), use the basepoint map. Combining the \(b_i\)'s after projection from \(T_d^h\) gives a map
\[
b:T_d^h\longrightarrow W^a.
\]
The composite \(tb\) is an actual lift of its projection \(qtb:T_d^h\to X\). Hence \((qtb)^*k=0\), by Lemma 4.2.

By Lemma 5.1, \(qtb\) is homotopic to the probe whose \(j\)-th vector is \(F_{\rho(j)}v_j\). Formula (4.4) therefore sends the top product class to
\[
F_{\rho(1)}v_1\cdots F_{\rho(h)}v_h.
\]
In the first assertion, naturality of the UCT and of (3.3) identifies the \(R\)-component of the pulled-back class, evaluated on the generator of \(H_n(T_d^r;\mathbb Z)=\mathbb Q\), with the left side of (5.3). Since the pulled-back class is zero, this value is zero. In the second assertion, naturality of the UCT and (3.4) identifies the \(D\)-component, evaluated on the generator of \(H_{n+1}(T_d^s;\mathbb Z)=\mathbb Q\), with the indicated value of \(\omega_D\). It too is zero. These prove both assertions. \(\square\)

## 6. The algebraic Taylor cancellation

**Lemma 6.1 — PROVED; confidence 1.00.** Let \(V,E\) be rational vector spaces, \(h\ge2\), and let \(\omega:V^h\to E\) be multilinear. Let \(F_1,\ldots,F_a\in\operatorname{End}_{\mathbb Q}(V)\) satisfy:

* every mixed value \(\omega(F_{\rho(1)}v_1,\ldots,F_{\rho(h)}v_h)\) with nonconstant \(\rho\) is zero;
* for every \(i\), there are integers \(\delta_j\in\{-1,0,1\}\) with \(\delta_i=1\) or \(-1\) and \(\sum_j\delta_jF_j=0\);
* the endomorphism \(S=\sum_jF_j\) is surjective.

Then \(\omega=0\).

**Proof.** Fix \(i\) and its displayed relation. Multilinearity gives
\[
0=\omega\left(F_iv_1,\ldots,F_iv_{h-1},\sum_j\delta_jF_jv_h\right)
=\sum_j\delta_j\omega(F_iv_1,\ldots,F_iv_{h-1},F_jv_h).
\]
The \(j\ne i\) terms have a nonconstant input allocation, because \(h\ge2\); they vanish by the first condition. The remaining equality is
\[
\delta_i\omega(F_iv_1,\ldots,F_iv_h)=0.
\]
Since \(\delta_i\in\{1,-1\}\), the diagonal value is zero. Thus every allocation, constant or nonconstant, has zero value. For arbitrary \(w_1,\ldots,w_h\in V\), choose \(v_j\) with \(Sv_j=w_j\), using surjectivity separately in each coordinate. Expanding gives
\[
\omega(w_1,\ldots,w_h)
=\omega\left(\sum_iF_iv_1,\ldots,\sum_iF_iv_h\right)
=\sum_{\rho:\{1,\ldots,h\}\to\{1,\ldots,a\}}
\omega(F_{\rho(1)}v_1,\ldots,F_{\rho(h)}v_h)=0.
\]
The sum is finite because both index sets are finite. This proves the lemma. \(\square\)

**Lemma 6.2 — PROVED; confidence 1.00.** A Taylor operation \(t\) gives the relations in the second bullet of Lemma 6.1. If \(t\) is normalized, it also gives \(S=\mathrm{id}_V\).

**Proof.** For the Taylor identity \(td_\alpha\simeq td_\beta\) witnessing position \(i\), restrict to the \(x\)-axis in \(W^2\) and apply \(\pi_d\). The resulting equality is
\[
\sum_{j:\alpha_j=x}F_j=\sum_{j:\beta_j=x}F_j.
\]
Take \(\delta_j=\mathbf1_{\alpha_j=x}-\mathbf1_{\beta_j=x}\). Each \(\delta_j\) belongs to \(\{-1,0,1\}\), and \(\alpha_i\ne\beta_i\) makes \(\delta_i\in\{-1,1\}\). This proves the claimed relation. Applying \(\pi_d\) to \(t\Delta_a\simeq\mathrm{id}\) gives \(\sum_jF_j=\mathrm{id}_V\). \(\square\)

## 7. Proof of the equivalences and the stronger diagonal-surjectivity statement

**Theorem 7.1 — PROVED; confidence 0.98.** Under the opening hypotheses, if \(W\) admits a Taylor operation whose diagonal composite is surjective on \(\pi_dW\), then \(k=0\).

**Proof.** Choose \(B=D\oplus R\) as in Lemma 3.1. If \(d\nmid n\), Corollary 3.3 already gives \(k_R=0\). If \(n=rd\), then \(r\ge2\). Lemma 5.2 gives the mixed vanishing for \(\omega_R\). Lemma 6.2 gives all the required signed relations. The map on \(\pi_d\) of the diagonal composite is \(S=\sum_iF_i\), so the assumed diagonal surjectivity gives the last hypothesis of Lemma 6.1. That lemma proves \(\omega_R=0\), and Corollary 3.3 yields \(k_R=0\).

We have now established \(k_R=0\) in every case. If \(d\nmid n+1\), Corollary 3.3 gives \(k_D=0\). If \(n+1=sd\), then \(s\ge2\). The second assertion of Lemma 5.2 is now applicable, because its \(k_R=0\) hypothesis has been proved. It gives mixed vanishing for \(\omega_D\); the Taylor relations and diagonal surjectivity are unchanged. Lemma 6.1 gives \(\omega_D=0\), and Corollary 3.3 yields \(k_D=0\). Hence \(k=(k_R,k_D)=0\). \(\square\)

**Theorem 7.2 — PROVED; confidence 0.98.** An H-space \(W\) satisfying the opening hypotheses has \(k=0\).

**Proof.** Let \(\mu:W^2\to W\) have a homotopy unit. The two endomorphisms in (5.1) are both \(\mathrm{id}_V\), since restricting to either axis is homotopic to the identity.

If \(d\nmid n\), then \(k_R=0\) by Corollary 3.3. If \(n=rd\), choose the nonconstant allocation \(\rho(1)=1\) and \(\rho(j)=2\) for \(2\le j\le r\). It is nonconstant because \(r\ge2\). Lemma 5.2 makes \(\omega_R(v_1,\ldots,v_r)=0\) for every list of vectors, so \(k_R=0\).

Having established that vanishing, if \(d\nmid n+1\), then \(k_D=0\) by Corollary 3.3. If \(n+1=sd\), use the allocation \(\rho(1)=1\), \(\rho(j)=2\) for \(2\le j\le s\) in the second assertion of Lemma 5.2. It gives \(\omega_D=0\), hence \(k_D=0\). Thus \(k=0\). \(\square\)

**Completion of the opening theorem — PROVED; confidence 0.98.** A normalized Taylor operation has diagonal map equal to the identity in the homotopy category, so Theorem 7.1 proves \(1\Rightarrow3\). Theorem 7.2 proves \(2\Rightarrow3\).

If \(k=0\), choose a pointed nullhomotopy of its representative map \(X\to K(B,n+1)\). In its path-fiber model this nullhomotopy identifies a point over \(x\) with the chosen null path followed by an arbitrary loop at the basepoint. Concatenating the inverse chosen path gives the inverse equivalence. These composites are homotopic to the identities by cancellation of a path with its reverse. Thus
\[
W\simeq X\times\Omega K(B,n+1)\simeq K(V,d)\times K(B,n).
\]
The last equivalence follows from the homotopy groups of the loop space and CW replacement, followed by Whitehead's theorem. This proves \(3\Rightarrow4\).

Conversely, the product projection admits a section \(x\mapsto(x,*)\). Suppose \(e:W\to X\times K(B,n)\) is a homotopy equivalence. The map \(\operatorname{pr}_Xe\) induces an automorphism \(A\) of \(V\), since \(n>d\) makes \(\pi_dK(B,n)=0\). Replace \(e\) by \((K(A^{-1},d)\times\mathrm{id})e\); the new equivalence induces the identity on the lower group. Maps from \(W\) to \(X\) are classified by that homomorphism, as in Lemma 5.1. Consequently, composing the product section with a homotopy inverse of this new equivalence gives a homotopy section of the specified map \(q\). Lemma 4.2, applied to \(\mathrm{id}_X\), then gives \(k=0\). This proves \(4\Rightarrow3\).

To construct the operations on a product, for any abelian \(C\) and any degree \(j\ge1\), represent the cohomology class \(\operatorname{pr}_1^*\iota+\operatorname{pr}_2^*\iota\) on \(K(C,j)^2\) by a map \(\mu_C\), where \(\iota\) is its fundamental class. Its restriction to either axis represents \(\iota\), hence is homotopic to the identity. Taking the two coordinate maps yields an H-structure on \(K(V,d)\times K(B,n)\), proving \(4\Rightarrow2\).

Represent instead \(\operatorname{pr}_1^*\iota-\operatorname{pr}_2^*\iota+\operatorname{pr}_3^*\iota\) by a ternary map \(m_C\). Its diagonal represents \(\iota-\iota+\iota=\iota\), so it is normalized. The identities
\[
m_C(x,x,y)\simeq m_C(y,y,y),\qquad
m_C(x,y,y)\simeq m_C(x,x,x)
\]
follow by equality of their representing classes, respectively \(y\) and \(x\). The first identity distinguishes positions one and two; the second distinguishes position three. Thus it is Taylor. Taking the coordinatewise operation on the product proves \(4\Rightarrow1\).

Finally, transfer these structures through a pointed homotopy equivalence \(e:W\to X\times K(B,n)\) with inverse \(h\): use \(h\mu(e\times e)\) and \(hm(e\times e\times e)\). The equations \(he\simeq\mathrm{id}\) and \(eh\simeq\mathrm{id}\) verify their units, normalization, and Taylor identities after this transfer. All four conditions are equivalent. \(\square\)

## 8. Scope, degree consequences, and audit

**Corollary 8.1 — PROVED; confidence 0.99.** If \(d\ge2\) and neither \(n\) nor \(n+1\) is divisible by \(d\), every simple two-stage space with the specified groups already splits, without any operation hypothesis.

**Proof.** Corollary 3.3 gives \(k_R=0\) and \(k_D=0\) separately. Thus \(k=0\), and the product construction in the completion of the opening theorem applies. \(\square\)

**PROVED scope statement; confidence 1.00.** The result contains the earlier rational fundamental-group two-type theorem as \(d=1,n=2\), and also treats every \(d=1,n>2\). Its new even-degree mechanism is the use of \(T_d\), not \(K(\mathbb Q,d)\), as the probe. For even \(d\), the latter space has classes in all positive multiples of \(d\); an arbitrary map from it need not lift through a nonzero Postnikov invariant. The homology of \(T_d\) is concentrated in degrees zero and \(d\), and Lemma 4.3 proves each actual lift used.

**PROVED scope statement; confidence 1.00.** The proof does not treat a base with rational homotopy in several different degrees. A map of such a base can have decomposable terms on its higher coordinates. Equation (5.2), which is exact for the one-degree base \(K(V,d)\), would need replacement in that setting. No assertion about the unrestricted Taylor-to-H implication is made here.

**Adversarial self-audit — PROVED assessment of this argument; confidence 0.98.** The most vulnerable step is not the formal Taylor cancellation; it is the claim that enough probe products lift to the original \(W\). The proof establishes \(k_R=0\) before using any larger probe needed for the \(D\)-component. For \(d=1\), a product of \(s-1=n\) circles with rational homology can have \(H_n\ne0\), so arbitrary coefficients would leave an Ext obstruction. After \(k_R=0\), the only remaining coefficient group is injective \(D\), and that Ext obstruction is absent. Lemma 4.3 spells out this exact order. If the order were reversed, the proof of mixed vanishing for \(\omega_D\) would be unjustified. No invariance of the splitting \(B=D\oplus R\) under the operation is used; the operation always acts on actual lifts to \(W\).

## 9. References

1. Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002. Theorem 2A.1; Theorems 3.2 and 3B.6; Theorems 4.5 and 4.32; Proposition A.1 and Theorem A.6. Author's corrected online text: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>. Appendix: <https://pi.math.cornell.edu/~hatcher/AT/ATapp.pdf>.
2. J. Peter May and Kate Ponto, *More Concise Algebraic Topology: Localization, Completion, and Model Categories*, University of Chicago Press, 2012. Corollary 2.2.3, Equation (3.4.1), Lemma 3.4.2, Theorem 5.2.8, Proposition 6.7.2. Author's text: <https://www.math.uchicago.edu/~may/PAPERS/116.pdf>.

The cited book results provide foundations; the theorem is derived above. No claim that the theorem is new in the literature, and no claim of proof-assistant verification, is made.


# Part II. Explicit local splittings and integral obstructions

**PROVED — for every integer \(d\geq1\), the construction below gives a simple two-stage CW space \(W_d\), with nonzero homotopy groups in degrees \(d\) and \(2d\), which splits after localization at every prime and after rationalization, but which admits neither an H-structure nor a normalized Taylor operation. For \(d\geq2\) these spaces are simply connected. Every normalized operation on \(W_d\) induces a coordinate projection on its bottom homotopy group. Confidence: 0.99.**

The proof uses the homology and mixed-input lemmas proved in the accompanying main theorem. The arithmetic class is constructed here by an explicit integer sequence. No uncomputed extension class is chosen.

## 1. A factorial resolution and an explicit extension class

Put
\[
F=\bigoplus_{j\geq1}\mathbb Z e_j,\qquad
\epsilon(e_j)=\frac1{j!}\in\mathbb Q,
\qquad u_j=e_j-(j+1)e_{j+1}.
\]

**Lemma E1 — PROVED; confidence 1.00.** The map \(\epsilon:F\to\mathbb Q\) is onto, and its kernel is the free abelian subgroup on the elements \(u_j\).

**Proof.** Every rational number has a denominator dividing some factorial, so it is an integer multiple of some \(1/j!\). Thus \(\epsilon\) is onto. Each \(u_j\) belongs to its kernel. Given an element supported on \(e_1,\ldots,e_N\), successively use \(e_j\equiv(j+1)e_{j+1}\) modulo the subgroup generated by the \(u_j\). The resulting element is an integer multiple \(c e_N\). Its image is \(c/N!\); if the original element was in the kernel, \(c=0\). This proves that the \(u_j\) generate the kernel. To prove their independence, take a finite relation \(\sum_{j=1}^N c_j u_j=0\) with \(c_N\ne0\). Its \(e_{N+1}\)-coefficient is \(-(N+1)c_N\ne0\), a contradiction. \(\square\)

For every \(j\geq1\), write
\[
q_j=2^{v_2(j!)},\qquad o_j=j!/q_j.
\]
Here \(v_2\) denotes the exponent of \(2\) in a positive integer. Define \(z_j\) to be the unique integer in \([0,j!-1]\) satisfying
\[
z_j\equiv-1\pmod{q_j},\qquad z_j\equiv0\pmod{o_j}.
\tag{E1}
\]
When a modulus equals \(1\), its congruence imposes no restriction. In particular \(z_1=0\).

**Construction E2 — PROVED; confidence 1.00.** These integers are explicitly determined by
\[
z_j=0\quad(q_j=1),\qquad
z_j=o_j\bigl((-o_j^{-1})\bmod q_j\bigr)\quad(q_j>1).
\tag{E2}
\]
The inverse exists because \(o_j\) is odd. A representative between \(0\) and \(q_j-1\) in the parentheses gives a number between \(0\) and \(o_jq_j-1\), divisible by \(o_j\), and congruent to \(-1\) modulo \(q_j\). If two representatives satisfy (E1), their difference is divisible by both coprime numbers \(q_j\) and \(o_j\), and hence by their product \(j!\); the specified interval makes the representatives equal. The inverse in (E2) can be obtained by the Euclidean algorithm. This proves existence and uniqueness without an unspecified choice.

Both congruences for \(z_{j+1}\), when reduced modulo \(q_j\) and \(o_j\), are the congruences for \(z_j\), because each of those moduli divides its successor. Therefore
\[
a_j=\frac{z_j-z_{j+1}}{j!}
\tag{E3}
\]
is an integer. Define a homomorphism \(a:\ker\epsilon\to\mathbb Z\) by \(a(u_j)=a_j\). Let
\[
\xi=[a]\in
\operatorname{coker}\bigl(\operatorname{Hom}(F,\mathbb Z)
 \longrightarrow\operatorname{Hom}(\ker\epsilon,\mathbb Z)\bigr)
=\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,\mathbb Z).
\tag{E4}
\]

**Lemma E3 — PROVED; confidence 1.00.** The class \(\xi\) is nonzero. Its coefficient image in \(\operatorname{Ext}^1(\mathbb Q,\mathbb Z_{(p)})\) is zero for every prime \(p\), and its image in \(\operatorname{Ext}^1(\mathbb Q,\mathbb Q)\) is zero.

**Proof.** If \(a\) extended to \(F\), put \(x_j=a(e_j)\in\mathbb Z\) for the values of that extension. The required equations would be
\[
x_j-(j+1)x_{j+1}=a_j.
\tag{E5}
\]
Multiplying by \(j!\) and using (E3) shows that
\[
C=z_j-j!x_j
\tag{E6}
\]
is an integer independent of \(j\). The odd part of \(j!\) divides both \(z_j\) and \(j!x_j\). Thus \(3^{v_3(j!)}\mid C\) for every \(j\). The valuations \(v_3(j!)\) are unbounded; a nonzero integer has finite \(3\)-adic valuation. Consequently \(C=0\). Taking \(j=2\) in (E6) gives \(C\equiv z_2=1\pmod2\), a contradiction. Hence the extension to \(F\) does not exist, and \(\xi\ne0\).

For the prime \(2\), define
\[
x_{j,2}=\frac{z_j+1}{j!}.
\tag{E7}
\]
The numerator is divisible by the entire power of \(2\) in the denominator, by (E1). Thus \(x_{j,2}\in\mathbb Z_{(2)}\). For an odd prime \(p\), define
\[
x_{j,p}=\frac{z_j}{j!}.
\tag{E8}
\]
The numerator is divisible by \(o_j\), which contains the entire power of \(p\) in \(j!\). Thus \(x_{j,p}\in\mathbb Z_{(p)}\). Substitution gives, for every prime \(p\),
\[
x_{j,p}-(j+1)x_{j+1,p}
=\frac{z_j-z_{j+1}}{j!}=a_j;
\]
the added \(1\) in (E7) cancels. Sending \(e_j\) to \(x_{j,p}\) therefore extends the coefficient image of \(a\) to \(F\), proving that the localized Ext class is zero. Formula (E8), now regarded as a rational number without a restriction on its denominator, gives an extension with values in \(\mathbb Q\). This proves rational vanishing. \(\square\)

**Construction E4 — PROVED; confidence 1.00.** An explicit group extension representing (E4) is
\[
E=\bigl(\mathbb Z b\oplus F\bigr)
\Big/\bigl\langle u_j-a_jb:j\geq1\bigr\rangle,
\qquad
0\longrightarrow\mathbb Z\xrightarrow{1\mapsto b}E
\xrightarrow{e_j\mapsto1/j!,\ b\mapsto0}\mathbb Q\longrightarrow0.
\tag{E9}
\]

**Proof.** The displayed map to \(\mathbb Q\) respects every relation and is onto by Lemma E1. A relation belonging entirely to \(\mathbb Z b\) would come from a finite integer combination of the \(u_j\) equal to zero in \(F\). Their independence in Lemma E1 makes every coefficient zero. Thus the kernel inclusion \(\mathbb Z\to E\) is injective. If an element maps to zero in \(\mathbb Q\), its \(F\)-component lies in the subgroup generated by the \(u_j\); using the displayed relations converts it to an integer multiple of \(b\). This proves exactness.

Lifting the basis of \(F\) to the named generators \(e_j\) in \(E\) sends \(u_j\) to \(a_jb\), which is precisely the defining Ext representative. A retraction of the kernel would have to send \(e_j\) to integers solving (E5), and such integers do not exist. Conversely the formulas (E7) and (E8) define retractions after the corresponding coefficient pushouts. Hence (E9) also verifies the nonsplitting and all local splittings directly. \(\square\)

## 2. The spaces in every degree

Define
\[
V_d=\begin{cases}
\mathbb Q,&d\text{ even},\\
\mathbb Q^2,&d\text{ odd},
\end{cases}
\qquad X_d=K(V_d,d).
\tag{E10}
\]
The rational Eilenberg–Mac Lane homology calculation proved in the main theorem gives
\[
H_{2d}(X_d;\mathbb Z)=\mathbb Q,\qquad
H_{2d+1}(X_d;\mathbb Z)=0.
\tag{E11}
\]
For even \(d\), the generator in degree \(2d\) is the Pontryagin square of the generator of \(V_d\); the chosen identification sends that square to \(1\). For odd \(d\), it is the product of the two ordered basis vectors of \(V_d\), and that product is sent to \(1\). For \(d=1\), the second equality follows because \(\Lambda^3\mathbb Q^2=0\). For \(d>1\), the degree \(2d+1\) is not a positive multiple of \(d\), so that homology group is zero.

The natural cohomological universal coefficient sequence therefore gives an isomorphism
\[
H^{2d+1}(X_d;C)
\cong\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,C)
\tag{E12}
\]
for every abelian coefficient group \(C\). Define \(k_d\) to be the class corresponding to \(\xi\) under (E12), and choose a pointed representing map
\[
k_d:X_d\longrightarrow K(\mathbb Z,2d+1).
\tag{E13}
\]
Representability is Hatcher (2002), Theorem 4.57, or May–Ponto (2012), Equation (3.4.1). Let \(W_d\) be a pointed CW model of its homotopy fiber. In the path model this consists of pairs \((x,\gamma)\), with \(\gamma\) a path from \(k_d(x)\) to the basepoint. Projection gives
\[
K(\mathbb Z,2d)\longrightarrow W_d\xrightarrow{q_d}X_d
\xrightarrow{k_d}K(\mathbb Z,2d+1).
\tag{E14}
\]

**Lemma E5 — PROVED; confidence 0.99.** The space \(W_d\) is connected and simple, with
\[
\pi_jW_d=\begin{cases}
V_d,&j=d,\\
\mathbb Z,&j=2d,\\
0,&j\notin\{d,2d\},\ j\geq1.
\end{cases}
\tag{E15}
\]
Its defining class \(k_d\) is nonzero.

**Proof.** The homotopy exact sequence of (E14), May–Ponto (2012), Corollary 2.2.3, gives all the displayed groups and connectedness: both base and fiber are connected, and the two nonzero degrees are distinct. For \(d\geq2\), the fundamental group is zero, so the space is simple. For \(d=1\), the fundamental group is the abelian group \(\mathbb Q^2\). The action on the fiber group is trivial because (E14) is the pullback of a path fibration over an Eilenberg–Mac Lane space; this is precisely implication (i) to (iv) of May–Ponto (2012), Lemma 3.4.2. There are no other nonzero higher homotopy groups. Thus \(W_1\) is simple as well. Finally, (E12) is an isomorphism and \(\xi\ne0\) by Lemma E3, so \(k_d\ne0\). \(\square\)

**Theorem E6 — PROVED; confidence 0.99.** For every prime \(p\),
\[
(W_d)_{(p)}\simeq K(V_d,d)\times K(\mathbb Z_{(p)},2d),
\tag{E16}
\]
and
\[
(W_d)_{\mathbb Q}\simeq K(V_d,d)\times K(\mathbb Q,2d).
\tag{E17}
\]

**Proof.** Replace the coefficient map \(\mathbb Z\to C\), where \(C=\mathbb Z_{(p)}\) or \(C=\mathbb Q\), by the induced map between Eilenberg–Mac Lane targets. Composing (E13) with it gives a map \(k_{d,C}:X_d\to K(C,2d+1)\). Naturality of the universal coefficient isomorphism (E12) identifies its class with the coefficient image of \(\xi\), which vanishes by Lemma E3. Choose a pointed nullhomotopy \(N_C\) of this map.

Let \(Z_C=\operatorname{hofib}(k_{d,C})\). The coefficient map induces \(W_d\to Z_C\), equal to the identity on the base, and on the homotopy groups (E15) it is the identity of \(V_d\) and the coefficient map \(\mathbb Z\to C\). The long exact sequence verifies that \(Z_C\) has no other homotopy groups. It is simple by the same argument as in Lemma E5. All of its homotopy groups are local for the coefficient ring in question. By May–Ponto (2012), Theorem 6.1.1, \(Z_C\) is a local space. By Theorem 6.1.2(iii), the map \(W_d\to Z_C\) is a localization, because it localizes every homotopy group. These theorems require nilpotence, which simplicity supplies; they require neither finite generation nor finite Postnikov height.

The nullhomotopy identifies the fiber with \(X_d\times\Omega K(C,2d+1)\). Explicit maps are
\[
(x,\gamma)\longmapsto(x,N_C(x,-)^{-1}*\gamma),
\qquad
(x,\omega)\longmapsto(x,N_C(x,-)*\omega).
\tag{E18}
\]
Here paths in the first fiber run from \(k_{d,C}(x)\) to the basepoint, and \(\omega\) is a loop at that basepoint. Path concatenation followed by cancellation of a path and its reverse gives homotopies from both composites to the identity, fixed at the basepoint. Since \(\Omega K(C,2d+1)\simeq K(C,2d)\), the two claimed splittings follow. \(\square\)

## 3. Every normalized operation projects on the bottom group

Let \(t:W_d^m\to W_d\) be any pointed operation, and write its action on the bottom homotopy group as
\[
t_*(v_1,\ldots,v_m)=\sum_{i=1}^mF_i(v_i).
\tag{E19}
\]
Each \(F_i\) is rational linear. The mixed-input lemma in the main theorem applies to the length-two form representing \(k_d\). In the even case that form is
\[
\omega(u,v)=uv\,\xi\qquad(u,v\in\mathbb Q),
\tag{E20}
\]
with the Pontryagin normalization of (E11). In the odd case it is
\[
\omega(u,v)=\det(u,v)\,\xi\qquad(u,v\in\mathbb Q^2),
\tag{E21}
\]
where the determinant uses the ordered basis in (E11). The coefficient group \(\operatorname{Ext}^1(\mathbb Q,\mathbb Z)\) is a rational vector space, as proved in the main theorem. Since \(\xi\ne0\), multiplication of \(\xi\) by a rational number is zero exactly when that rational number is zero.

Consequently the mixed-input lemma gives
\[
\omega(F_i u,F_j v)=0\qquad(i\ne j).
\tag{E22}
\]
One can also verify exactly the required special case directly: the rational sphere telescope \(T_d\) has reduced integral homology \(\mathbb Q\) only in degree \(d\). Every map \(T_d\to X_d\) determined by a vector therefore has zero pulled-back class in \(H^{2d+1}(T_d;\mathbb Z)\) and lifts to \(W_d\). Put two such lifts in inputs \(i\) and \(j\) of \(t\). Their composite lifts a map \(T_d^2\to X_d\), so its pulled-back class is zero. The top product homology generator maps to the Pontryagin product \(F_i u\,F_j v\), which evaluates as (E20) or (E21). Naturality of the UCT identifies this vanishing with (E22). Thus no additional compatibility of \(t\) with a chosen principal-fiber action is being assumed.

**Theorem E7 — PROVED; confidence 0.99.** If \(t\) is normalized, precisely one \(F_i\) in (E19) is the identity and all the others are zero.

**Proof for even \(d\).** Write \(F_i(u)=a_i u\) with \(a_i\in\mathbb Q\). Equation (E22) at \(u=v=1\) gives \(a_i a_j\xi=0\), and hence \(a_i a_j=0\), for distinct indices. Normalization gives \(\sum_i a_i=1\). There is therefore at least one nonzero coefficient. Any second nonzero coefficient would contradict the product equation. The unique nonzero coefficient equals \(1\), by its sum. This proves the assertion in the even case.

**Proof for odd \(d\).** Equation (E22) says every vector in \(\operatorname{im}F_i\) is linearly dependent with every vector in \(\operatorname{im}F_j\) when \(i\ne j\). Suppose first that all \(F_i\) have rank at most one. Normalization gives \(\sum_iF_i=\operatorname{id}_{\mathbb Q^2}\), so some \(F_i\) is nonzero. Choose a nonzero vector in its image and let \(L\) be its one-dimensional span. The dependence just established forces the image of each \(F_j\), \(j\ne i\), to lie in \(L\). The image of \(F_i\) is also \(L\). Hence the image of their sum lies in \(L\), contrary to the sum being the identity on a two-dimensional space.

Thus some \(F_i\) has rank two. If \(F_j\ne0\) for an index \(j\ne i\), choose a nonzero vector in its image. The surjectivity of \(F_i\) supplies a vector in its image independent of that one, contradicting (E22). Therefore all the remaining \(F_j\) are zero. The normalization equation now gives \(F_i=\operatorname{id}\). This proves the assertion in the odd case. \(\square\)

**Corollary E8 — PROVED; confidence 0.99.** No \(W_d\) admits a normalized Taylor operation or an H-structure.

**Proof.** If a normalized operation were Taylor, choose the input \(i\) singled out in Theorem E7. A Taylor identity distinguishing that input gives two maps \(W_d^2\to W_d\) whose induced homomorphisms on the bottom group are the two distinct projections \(V_d^2\to V_d\). Indeed, every other input has zero coefficient, and the two words place different variables in input \(i\). The projections are different because \(V_d\ne0\); evaluate them at \((v,0)\) with \(v\ne0\). Pointed homotopic maps induce the same homomorphism, giving a contradiction.

If \(\mu:W_d^2\to W_d\) were an H-structure, the two unit homotopies would force both bottom-axis maps to be the identity. This contradicts (E22): in even degree evaluate (E20) on \((1,1)\), and in odd degree evaluate (E21) on the two ordered basis vectors. In either case the value is \(\xi\ne0\). Thus there is no H-structure. \(\square\)

## 4. Scope and adversarial audit

**PROVED scope; confidence 1.00.** This family disproves the auxiliary assertion that prime-local H-structures together with rational splitting force an integral H-structure without finite generation. It does not give counterexamples to Taylor implying H: the Taylor obstruction has been proved explicitly. The examples have finite Postnikov height, and are simply connected for every \(d\geq2\), so the failure cannot be attributed to an infinite fundamental group or an unbounded tower. Their bottom homotopy group is not finitely generated.

**PROVED audit; confidence 0.99.** The most delicate arithmetic point is the coexistence of integral nonsplitting and splitting at every prime. The same recurrence has been checked in both directions: an integral solution would give one integer \(C\) satisfying all incompatible limiting congruences, while each localized solution is the explicitly displayed sequence (E7) or (E8). The topological transfer then uses coefficient naturality of a UCT isomorphism, not a claimed commutation of cohomology with localization in an infinite CW complex. If that distinction were ignored, these examples could be incorrectly declared split integrally.

## References

- Allen Hatcher (2002), *Algebraic Topology*, Theorem 3.2 (cohomological UCT), Theorem 4.57 (cohomology representability). Author text: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.
- J. P. May and K. Ponto (2012), *More Concise Algebraic Topology: Localization, Completion, and Model Categories*, Corollary 2.2.3 (homotopy-fiber exact sequence), Lemma 3.4.2 (principal Eilenberg–Mac Lane fibrations and the action condition), Theorems 6.1.1 and 6.1.2 (nilpotent localizations characterized on homotopy groups). Author text: <https://www.math.uchicago.edu/~may/PAPERS/116.pdf>.


# Part III. Finite-prime gluing without type or height bounds

**PROVED — confidence 0.99.** Let \(W\) be a pointed connected simple CW complex. Suppose that there is a finite set \(S\) of primes such that, for every \(n\geq2\), every element of \(\pi_nW\) is annihilated by a positive integer whose prime divisors belong to \(S\). The fundamental group \(\pi_1W\) may be any abelian group. Then

\[
 W\text{ is an H-space}\quad\Longleftrightarrow\quad
 W_{(p)}\text{ is an H-space for every }p\in S.
\]

There is no finite-generation assumption, no bound on the Postnikov height, and no common bound on the orders of the higher homotopy groups. The proof constructs a multiplication with a strict unit on the chosen wedge. No assertion of historical novelty is made.

## 1. Definitions and exact foundational inputs

All maps and homotopies are pointed. Products are taken in the category of compactly generated spaces. Choose the basepoint of every CW space to be a zero-cell. An H-space multiplication is a map \(\mu:W\times W\to W\) whose restriction to \(W\vee W\) is homotopic to the fold. Associativity and commutativity are not required.

A space is simple when its fundamental group is abelian and its action on every higher homotopy group is trivial. Such a space is nilpotent: its fundamental group is nilpotent, and the action on each higher homotopy group has a one-step filtration with trivial quotient action.

An abelian group is **\(S\)-primary torsion** in this note when every one of its elements is annihilated by an integer all of whose prime divisors lie in \(S\). This permits different integers for different elements. Put

\[
 R=\mathbb Z[S^{-1}],\qquad R_p=\mathbb Z_{(p)},\qquad
 A_T=A\otimes_{\mathbb Z}T
\]

for an abelian group \(A\) and a localization ring \(T\).

The following foundational theorems are imported, with their precise scope. All additional lemmas needed for the result are proved below.

1. **PROVED by the cited theorem — confidence 0.99:** May–Ponto (2012), Theorems 6.1.1 and 6.1.2. A nilpotent CW space has localization at any set of primes. The localized homotopy groups are the corresponding localizations of its homotopy groups; for abelian groups these are the tensor products with the localization ring. A nilpotent space with localized homotopy groups is a local space. The localization map has the universal property for maps into local spaces. There is no finite-generation assumption in these two theorems.
2. **PROVED by the cited theorem — confidence 0.99:** May–Ponto (2012), Proposition 6.2.3. Localization of nilpotent spaces preserves finite products up to the canonical homotopy equivalence. Consequently localization takes an H-space multiplication and its unit homotopies to an H-space multiplication and its unit homotopies.
3. **PROVED by the cited theorem — confidence 0.99:** Hatcher (2002), Theorems 4.57 and 3.2. Pointed maps into \(K(M,j)\) represent reduced cohomology with coefficients in the abelian group \(M\); the cohomological universal coefficient sequence is natural. Hatcher, Theorem 4.5, is the Whitehead theorem for CW complexes. Hatcher, Theorem 2A.1, identifies \(H_1\) with the abelianization of the fundamental group. These statements impose no countability condition on \(M\).
4. **PROVED by the cited theorem — confidence 0.99:** May (1967), Theorems 23.9, 16.1, 16.6, 14.1, and 14.3. The realization of the simplicial abelian group of normalized \(j\)-cocycles on simplices is a CW \(K(M,j)\), and realization preserves finite products in the compactly generated interpretation. Its realized addition is a strict continuous abelian group operation. We always use this model when taking the difference of two maps into an Eilenberg–Mac Lane space. More explicitly, in simplicial degree \(q\) this model is \(Z^j(\Delta[q];M)\), the simplicial operators are pullback along order-preserving maps of vertices, and addition is pointwise. The identity element is the zero cocycle. Every abelian-group identity holds before realization and hence after realization.
5. **PROVED by the cited theorem — confidence 0.99:** May–Ponto (2012), Corollary 2.2.3. The path model of a homotopy pullback has the homotopy exact sequence, including the component term. In the abelian fundamental-group case, the map between the homotopy groups of the two endpoints and the common target is the difference of the two endpoint maps. We also give the relevant component description explicitly below.
6. **PROVED by the cited theorem — confidence 0.99:** May–Ponto (2012), Theorem 17.2.2 and its proof on printed pages 345–346. A Serre fibration that is a weak homotopy equivalence has the right lifting property against relative CW inclusions, and hence against their retracts. The monoidal assertion of the same theorem implies that \(W\vee W\hookrightarrow W\times W\) is a cofibration when \(W\) is a pointed CW space with zero-cell basepoint: this is the pushout product of the cofibration \(\{*\}\hookrightarrow W\) with itself. Cofibrations have the homotopy extension property.

These are the only imported topology results used in the proof, apart from the definitions of homotopy groups, the product description of fundamental groups, and the long exact homology sequence of a pair. In particular no finite-height local-to-global theorem is being invoked.

## 2. Arithmetic for arbitrary abelian groups

### Lemma 2.1: simultaneous scalar approximation

**PROVED — confidence 0.999.** If \(S\ne\varnothing\) is finite, then

\[
 R\longrightarrow\bigoplus_{p\in S}\mathbb Q/R_p,
 \qquad r\longmapsto(r+R_p)_{p\in S},
 \tag{2.1}
\]

is onto.

**Proof.** Choose a representative \(q_p\in\mathbb Q\) of each prescribed coset. Let \(s_p\geq0\) be an integer such that \(p^{s_p}q_p\in R_p\), and put \(M=\prod_{p\in S}p^{s_p}\). Thus \(Mq_p\in R_p\) for each \(p\).

If \(s_p>0\), reduction modulo \(p^{s_p}R_p\) identifies \(R_p/p^{s_p}R_p\) with \(\mathbb Z/p^{s_p}\mathbb Z\): a denominator coprime to \(p\) has a multiplicative inverse modulo \(p^{s_p}\). Choose an integer \(c_p\) representing \(Mq_p\) in this quotient. The integers \(p^{s_p}>1\) are pairwise coprime. For each of them choose an integer \(u_p\) such that

\[
 u_p(M/p^{s_p})\equiv1\pmod {p^{s_p}}.
\]

Such \(u_p\) exists by the Euclidean algorithm because \(M/p^{s_p}\) is coprime to \(p\). Set

\[
 b=\sum_{p:s_p>0}c_pu_p(M/p^{s_p}).
\]

Reduction modulo \(p^{s_p}\) gives \(b\equiv c_p\pmod {p^{s_p}}\), since every summand with another prime index is divisible by \(p^{s_p}\). Therefore \(b-Mq_p\in p^{s_p}R_p\) for every \(p\); when \(s_p=0\), this assertion just says that two elements of \(R_p\) have difference in \(R_p\). Since \(M/p^{s_p}\) is a unit in \(R_p\), division by \(M\) gives

\[
 b/M-q_p\in R_p.
\]

The number \(b/M\) belongs to \(R\). It maps to all the prescribed cosets, as required. \(\square\)

### Lemma 2.2: the finite arithmetic exact sequence

**PROVED — confidence 0.999.** For every abelian group \(A\) and every finite nonempty \(S\), the following sequence is exact:

\[
0\longrightarrow A\xrightarrow{j}
A_R\oplus\prod_{p\in S}A_{R_p}
\xrightarrow{d}\prod_{p\in S}A_{\mathbb Q}
\longrightarrow0.
\tag{2.2}
\]

Here \(j(a)\) is the tuple of the localization images of \(a\), and

\[
d(a_0,(a_p)_p)=(a_0-a_p)_p,
\]

with the entries interpreted in \(A_{\mathbb Q}\).

**Proof.** First take \(A=\mathbb Z\). An element in the kernel is a common rational number belonging to \(R\) and to each \(R_p\). Write that number in lowest terms. Membership in \(R\) says its denominator uses only primes in \(S\), whereas membership in \(R_p\) says its denominator is not divisible by \(p\). All primes are therefore excluded from the denominator, so the number is integral. Conversely every integer gives an element of the kernel. Lemma 2.1 says that, for every tuple \((q_p)_p\), there is \(a_0\in R\) with \(a_0-q_p\in R_p\). Taking \(a_p=a_0-q_p\) proves surjectivity of \(d\). Thus (2.2) is exact when \(A=\mathbb Z\).

We supply the algebraic details that justify tensoring this sequence with an arbitrary \(A\). Tensor product is right exact because it is defined by generators \(a\otimes b\) modulo bilinearity relations: taking a quotient of the second factor imposes exactly the additional relations saying that the tensors of kernel elements are zero. A localization ring \(T^{-1}\mathbb Z\) is flat. Indeed, \(A\otimes T^{-1}\mathbb Z\) is the group of fractions \(a/t\), with \(a/t=0\) exactly when some element of \(T\) kills \(a\). If \(A\hookrightarrow B\), this criterion shows that \(T^{-1}A\to T^{-1}B\) is injective. Together with right exactness it proves exactness of tensoring with the localization ring. A finite direct sum of flat groups is flat, by taking the direct sum of these exact functors. In particular \(\prod_{p\in S}\mathbb Q\), a finite direct sum of copies of \(\mathbb Q\), is flat.

For clarity, a short exact sequence \(0\to U\to V\to C\to0\) whose quotient \(C\) is flat remains injective at its left after tensoring with every \(A\). Here is a proof avoiding an unproved Tor assertion. Choose a free group \(F\) surjecting onto \(A\), with kernel \(K\). Let \(x\in A\otimes U\) map to zero in \(A\otimes V\), and choose a lift \(\widetilde x\in F\otimes U\). Its image in \(F\otimes V\) belongs to the image of \(K\otimes V\), by right exactness applied to \(K\to F\to A\to0\). Choose \(y\in K\otimes V\) mapping to that image. The image of \(y\) in \(K\otimes C\) maps to zero in \(F\otimes C\), because \(\widetilde x\) came from \(U\). Flatness of \(C\) makes \(K\otimes C\to F\otimes C\) injective; hence this image is zero. Right exactness of \(K\otimes(-)\) gives \(z\in K\otimes U\) mapping to \(y\). The images of \(z\) and \(\widetilde x\) in \(F\otimes V\) agree. The map \(F\otimes U\to F\otimes V\) is injective because \(F\) is free and \(U\to V\) is injective. Thus the image of \(z\) in \(F\otimes U\) equals \(\widetilde x\). It follows that \(x=0\) in \(A\otimes U\), as required.

Apply this observation to the sequence already proved for \(\mathbb Z\). Tensoring with \(A\) is exact, including its first injection. Tensor product commutes with finite direct sums; finite products of abelian groups are the same as finite direct sums. The resulting sequence is exactly (2.2). \(\square\)

### Lemma 2.3: higher homotopy reconstruction

**PROVED — confidence 0.999.** If \(A\) is \(S\)-primary torsion, then \(A_R=0=A_{\mathbb Q}\), and its localization map gives an isomorphism

\[
A\xrightarrow{\cong}\prod_{p\in S}A_{R_p}.
\tag{2.3}
\]

**Proof.** Given \(a\in A\), some integer supported on \(S\) kills \(a\), and that integer is invertible in \(R\). Thus \(a\otimes1=0\) in \(A_R\). Every tensor in \(A_R\) is a sum of scalar multiples of such elements, so \(A_R=0\). Every torsion element becomes zero after rationalization, proving \(A_{\mathbb Q}=0\). Substituting these two equalities into (2.2) proves (2.3). \(\square\)

## 3. Maps into an aspherical abelian target

### Lemma 3.1: degree-one classification

**PROVED — confidence 0.99.** If \(Y\) is a pointed connected CW complex and \(M\) is an abelian group, then the map that associates to \(f:Y\to K(M,1)\) its homomorphism on fundamental groups gives a bijection

\[
[Y,K(M,1)]_*\cong\operatorname{Hom}(\pi_1Y,M).
\tag{3.1}
\]

**Proof.** Cohomology representability identifies the left side with \(H^1(Y;M)\). The universal coefficient sequence identifies that group with \(\operatorname{Hom}(H_1(Y;\mathbb Z),M)\), because \(H_0(Y;\mathbb Z)=\mathbb Z\) is free and its Ext group vanishes. The degree-one Hurewicz identification gives \(H_1(Y;\mathbb Z)=\pi_1Y^{\mathrm{ab}}\). A homomorphism from \(\pi_1Y\) to an abelian group factors uniquely through this abelianization. Naturality of the representing class and the universal coefficient map identifies this bijection with the homomorphism on fundamental groups, rather than only with an abstract bijection. \(\square\)

### Lemma 3.2: relative uniqueness on a product

**PROVED — confidence 0.99.** Let \(Y\) be pointed and connected, put \(X=Y\times Y\) and \(A=Y\vee Y\), and use CW models. Then for every abelian \(M\),

\[
H^1(X,A;M)=0.
\tag{3.2}
\]

Consequently, any two maps \(u,v:X\to K(M,1)\) that are exactly equal on \(A\) are homotopic relative to \(A\).

**Proof.** Both \(X\) and \(A\) are connected, so the inclusion induces an isomorphism \(H_0(A;\mathbb Z)\to H_0(X;\mathbb Z)\). The first homology of the wedge is the direct sum \(H_1(Y;\mathbb Z)\oplus H_1(Y;\mathbb Z)\), as follows from its reduced cellular chain complex. The fundamental group of the product is \(\pi_1Y\times\pi_1Y\); abelianizing gives \(H_1(X;\mathbb Z)=H_1(Y;\mathbb Z)\oplus H_1(Y;\mathbb Z)\). Each wedge inclusion maps its first homology to the corresponding product summand by the identity. Thus \(H_1(A;\mathbb Z)\to H_1(X;\mathbb Z)\) is an isomorphism. The long exact homology sequence of \((X,A)\) now gives

\[
H_1(X,A;\mathbb Z)=H_0(X,A;\mathbb Z)=0.
\]

The universal coefficient sequence in relative degree one has these two groups as its Hom and Ext arguments, so it gives (3.2).

Use the strict abelian model for \(K(M,1)\). Since \(u=v\) on \(A\), the pointwise difference \(v-u\) vanishes on \(A\) and factors through a pointed map \(X/A\to K(M,1)\). Its homotopy class is in \(\widetilde H^1(X/A;M)=H^1(X,A;M)=0\). Thus it has a pointed nullhomotopy on the quotient. Pull this nullhomotopy back to \(X\) and add \(u\); it is a homotopy from \(v\) to \(u\), fixed on \(A\). \(\square\)

## 4. The fracture square in the present generality

Assume \(S\ne\varnothing\), and write

\[
A_1=\pi_1W,\qquad A_n=\pi_nW\quad(n\geq2).
\]

Set

\[
 G_R=K((A_1)_R,1),\qquad G=K((A_1)_{\mathbb Q},1),
 \qquad E_p=W_{(p)}.
\]

Choose the localization maps \(\ell_p:W\to E_p\). Lemma 3.1 gives a map \(\ell_R:W\to G_R\) inducing \(A_1\to(A_1)_R\) on fundamental groups. This is an \(R\)-localization of \(W\): its target is local by May–Ponto, Theorem 6.1.1; its map on \(\pi_1\) is localization; and in every degree \(n\geq2\) both the target homotopy group and \((A_n)_R\) vanish by Lemma 2.3. The homotopy-group characterization in May–Ponto, Theorem 6.1.2, therefore applies.

Let \(\rho_R:G_R\to G\) be the map induced by the coefficient map \((A_1)_R\to(A_1)_{\mathbb Q}\), using the functorial simplicial abelian models. For each \(p\in S\), choose \(\rho_p:E_p\to G\) inducing the canonical map \((A_1)_{R_p}\to(A_1)_{\mathbb Q}\); Lemma 3.1 supplies it. Define \(g=\rho_R\ell_R\). Both \(g\) and \(\rho_p\ell_p\) induce the same map \(A_1\to(A_1)_{\mathbb Q}\). Choose, using Lemma 3.1, a pointed homotopy

\[
\eta_p:g\simeq\rho_p\ell_p.
\tag{4.1}
\]

Define \(P\) explicitly to consist of tuples

\[
\bigl(y_0,(y_p)_{p\in S},(\gamma_p)_{p\in S}\bigr),
\tag{4.2}
\]

where \(y_0\in G_R\), \(y_p\in E_p\), and \(\gamma_p:I\to G\) is a path with

\[
\gamma_p(0)=\rho_R(y_0),\qquad
\gamma_p(1)=\rho_p(y_p).
\]

Give it the compactly generated subspace topology in the corresponding product of spaces and path spaces. Its basepoint has all spatial coordinates at the basepoint and all paths constant. This is the path model of

\[
\operatorname{holim}\left(
G_R\xrightarrow{\text{diagonal }\rho_R}\prod_{p\in S}G
\xleftarrow{\prod_p\rho_p}\prod_{p\in S}E_p
\right).
\tag{4.3}
\]

The common target is the product of \(|S|\) copies of \(G\); using a single copy with a product of distinct prime pieces would give a different diagram.

For a later exact unit calculation, replace each homotopy \(\eta_p\) by the path family \(\widehat\eta_p\) that is constant for the first half of the interval and follows \(\eta_p\) for its second half. Define

\[
\chi:W\longrightarrow P,\qquad
\chi(w)=\bigl(\ell_R(w),(\ell_p(w))_p,
                         (\widehat\eta_p(w,-))_p\bigr).
\tag{4.4}
\]

### Lemma 4.1: the comparison is a weak equivalence

**PROVED — confidence 0.99.** The space \(P\) is connected and \(\chi\) induces an isomorphism on every homotopy group.

**Proof.** The projection from \(P\) to

\[
 B=G_R\times\prod_{p\in S}E_p
\]

is a pullback of the endpoint path fibration of \(C=\prod_{p\in S}G\). Its fiber at the basepoint is \(\Omega C\). The space \(C\) is aspherical, so \(\pi_iC=0\) for \(i\geq2\). Consequently its homotopy pullback exact sequence identifies

\[
\pi_iP\cong\pi_iB=\prod_{p\in S}(A_i)_{R_p}
\quad(i\geq2).
\tag{4.5}
\]

Under this identification, \(\chi_*\) is the tuple of localization maps, which is an isomorphism by Lemma 2.3.

The remaining part of the exact sequence has the form

\[
0\longrightarrow\pi_1P\longrightarrow
(A_1)_R\oplus\prod_{p\in S}(A_1)_{R_p}
\xrightarrow{d}\prod_{p\in S}(A_1)_{\mathbb Q}
\longrightarrow\pi_0P\longrightarrow *.
\tag{4.6}
\]

Every displayed fundamental group is abelian. A loop in \(B\), obtained by a loop at the away piece and a loop in each prime piece, changes a path joining the endpoints by the difference of the endpoint loop classes. Thus the map in (4.6) is exactly \(d(a_0,(a_p))=(a_0-a_p)_p\). The component term is the orbit set for this translation action on \(\pi_1C\); since the acting groups are abelian, it is the quotient by the image of \(d\). Lemma 2.2 says \(d\) is onto. The orbit set therefore has one element, so \(P\) is connected. The same lemma identifies its kernel with \(A_1\), by the tuple of localization maps. This tuple is the homomorphism induced by \(\chi\), since the paths in (4.4) supply the chosen endpoint comparison and the projection to \(B\) gives the localization maps themselves. Therefore \(\chi_*:A_1\to\pi_1P\) is an isomorphism. Together with (4.5) this proves the assertion. \(\square\)

No CW homotopy-type assertion about the path space \(P\) is needed. The final construction will use the weak equivalence \(\chi\) through a mapping-path fibration.

## 5. Explicit multiplication and compatibility, including the unit

Assume each \(E_p\) has an H-space multiplication. By the homotopy extension property for \(E_p\vee E_p\hookrightarrow E_p\times E_p\), replace the chosen multiplication by a pointed homotopic map \(\mu_p:E_p\times E_p\to E_p\) whose restriction to the wedge is exactly the fold: start from its unit homotopy on the wedge, extend it to the product, and use the endpoint of the extended homotopy. Let \(\mu_R\) be strict addition on \(G_R\).

Put

\[
X=W\times W,\qquad A=W\vee W,
\]

and let \(a:A\to W\) be the fold. Define

\[
f_R=\mu_R(\ell_R\times\ell_R):X\to G_R,
\qquad f_p=\mu_p(\ell_p\times\ell_p):X\to E_p.
\tag{5.1}
\]

Their wedge restrictions are exactly \(\ell_Ra\) and \(\ell_pa\). Put

\[
u=\rho_Rf_R,\qquad v_p=\rho_pf_p.
\]

Then \(u|_A=ga\) and \(v_p|_A=\rho_p\ell_pa\). The reverse of \(\eta_pa\) is a homotopy from \(v_p|_A\) to \(u|_A\). Extend it to a homotopy

\[
B_p:X\times I\to G,\qquad B_p(-,0)=v_p,
\]

such that

\[
B_p(a',s)=\eta_p(a(a'),1-s)\quad(a'\in A).
\tag{5.2}
\]

Let \(\overline v_p=B_p(-,1)\). It agrees exactly with \(u\) on \(A\). By Lemma 3.2 there is a homotopy \(C_p:u\simeq\overline v_p\) that is stationary on \(A\). Concatenate \(C_p\) with the reverse of \(B_p\) to get

\[
H_p:u\simeq v_p.
\tag{5.3}
\]

On \(A\), the first half of this homotopy is the constant path at \(ga\), and the second half is \(\eta_pa\). Hence its path family on \(A\) is exactly \(\widehat\eta_pa\), with the convention used in (4.4).

These maps give a continuous map

\[
F:X\longrightarrow P,\qquad
F(x)=\bigl(f_R(x),(f_p(x))_p,(H_p(x,-))_p\bigr).
\tag{5.4}
\]

Its path coordinates have the endpoints required in (4.2), so it really takes values in \(P\). Its wedge restriction satisfies the exact identity

\[
F|_A=\chi a.
\tag{5.5}
\]

This is the full compatibility argument. It uses the vanishing \(H^1(W\times W,W\vee W;(A_1)_{\mathbb Q})=0\). It does not assume that a selected multiplication at one Postnikov stage extends over the next stage, does not select compatible multiplications through an infinite tower, and does not require any finiteness of deviation groups.

### Lemma 5.1: transferring a relative extension through a weak equivalence

**PROVED — confidence 0.99.** Let \(i:A\hookrightarrow X\) be a cofibration of CW spaces, let \(a:A\to W\), and let \(\chi:W\to P\) be a pointed weak equivalence. If \(F:X\to P\) satisfies \(Fi=\chi a\), then there is a pointed map \(\mu:X\to W\) with \(\mu i=a\).

**Proof.** Form

\[
E_\chi=\{(w,\gamma)\in W\times P^I:\gamma(0)=\chi(w)\}
\]

and \(q:E_\chi\to P\), \(q(w,\gamma)=\gamma(1)\). The map \(q\) is a Hurewicz fibration. To verify its homotopy lifting property directly, suppose a starting lift is \((w(z),\gamma_z)\) over \(H(z,0)\), where \(H:Z\times I\to P\) is a homotopy in the base. Keep \(w(z)\) fixed. At homotopy time \(s\), use the path

\[
\Gamma_{z,s}(t)=
\begin{cases}
\gamma_z((1+s)t),&0\leq t\leq 1/(1+s),\\
H(z,(1+s)t-1),&1/(1+s)\leq t\leq1.
\end{cases}
\]

At the dividing point the two formulas agree because \(\gamma_z(1)=H(z,0)\). The formula begins at \(\chi(w(z))\), ends at \(H(z,s)\), depends continuously on its variables in the compactly generated path topology, and equals the original path when \(s=0\). It gives the required lift.

The projection \(r:E_\chi\to W\) has section \(j(w)=(w,\text{constant path at }\chi(w))\). The deformation

\[
(w,\gamma)\longmapsto(w,t\mapsto\gamma((1-s)t)),\qquad 0\leq s\leq1,
\]

is from the identity to \(jr\), and fixes the image of \(j\). Therefore \(j\) and \(r\) are homotopy inverses. Since \(qj=\chi\) and \(\chi\) is a weak equivalence, \(q\) is a weak equivalence on all homotopy groups and components as well. It is in particular an acyclic Serre fibration.

Apply the relative lifting statement in May–Ponto, Theorem 17.2.2, to the commutative square with top map \(ja:A\to E_\chi\), left map \(i:A\hookrightarrow X\), bottom map \(F:X\to P\), and right map \(q\). Commutativity is exactly \(Fi=\chi a=qja\). Obtain \(L:X\to E_\chi\) with \(Li=ja\) and \(qL=F\). Set \(\mu=rL\). Then \(\mu i=rja=a\), proving the assertion. \(\square\)

### Completion of the theorem

**PROVED — confidence 0.99.** Apply Lemma 5.1 to (5.5) and Lemma 4.1. It produces \(\mu:W\times W\to W\) restricting exactly to the fold on \(W\vee W\). Hence \(W\) is an H-space.

For the converse, localize an H-space multiplication on \(W\). The product-localization equivalence of May–Ponto, Proposition 6.2.3, identifies the localization of its domain with \(W_{(p)}\times W_{(p)}\), and localization of the unit homotopies gives the unit homotopies for the localized multiplication. Thus every \(W_{(p)}\) is an H-space.

If \(S=\varnothing\), the support hypothesis says \(\pi_nW=0\) for \(n\geq2\). Since its fundamental group is abelian, the degree-one classifying map \(W\to K(\pi_1W,1)\) is a weak equivalence. Both spaces have CW models, so Hatcher (2002), Theorem 4.5, makes it a homotopy equivalence. Transporting strict addition from \(K(\pi_1W,1)\) proves that \(W\) is an H-space. This treats the empty set as well. \(\square\)

## 6. Exact Taylor consequence and scope

### Corollary 6.1: consequence of the stipulated local step

**PROVED conditional on the stated local-step input — confidence 0.99.** Let \(W\) satisfy the hypotheses of the theorem and admit a normalized Taylor operation. Assume the audited local implication stipulated in the research problem applies to this \(W\): for every prime \(p\), its localization \(W_{(p)}\) admits an H-space multiplication. Then \(W\) is an H-space.

**Proof.** The supplied local implication gives the required multiplications for each of the finitely many primes in \(S\). The theorem constructs the integral multiplication. \(\square\)

The qualification concerning the local-step input is deliberate. If the given local proof has independently been established only under finite-type or finite-height hypotheses, this corollary does not extend that local proof. The theorem itself is unconditional and applies whenever the indicated prime-local H-structures are known, regardless of how they are obtained.

### Proposition 6.2: where the hypotheses enter

**PROVED — confidence 0.99.** The proof uses the hypotheses as follows.

* Simplicity makes \(W\) nilpotent, makes its fundamental group abelian, and allows its localizations to have the asserted tensor-product fundamental groups. The finite arithmetic exact sequence is then a sequence of abelian groups in degree one.
* The support condition makes the away piece \(W_R\) aspherical. It also gives the isomorphism (2.3) in every higher homotopy degree.
* Finiteness of \(S\) is used in scalar simultaneous approximation, in tensoring finite products, and in forming the finite arithmetic square. No passage to an infinite product of prime-local spaces is being made.
* Neither finite type nor finite Postnikov height occurs in any argument. The fundamental group need not be finitely generated, and the orders of torsion elements need not be bounded.

**Proof.** These are direct identifications of the uses in Sections 2–5. In particular all constructions in Section 5 are maps into the full spaces \(E_p\), so there is no hidden termination argument through Postnikov stages. \(\square\)

## 7. Adversarial self-audit

**PROVED audit statement — confidence 0.99.** The step most exposed to an error is the claim that arbitrary local multiplications can be made compatible with the chosen comparison paths while preserving the unit. Merely observing that the rationalization is an H-space would not justify that claim. Here the overlap is specifically \(K((\pi_1W)_{\mathbb Q},1)\), and Lemma 3.2 proves the exact relative vanishing group. Equation (5.2) first adjusts the two maps to have identical wedge restrictions; the relative vanishing then supplies a homotopy fixed on the wedge. The final concatenation is matched to the initially chosen half-constant comparison paths. Thus (5.5) is an equality of maps, not only an equality of abstract homotopy classes. If the overlap had higher Eilenberg–Mac Lane factors, Lemma 3.2 would not supply the corresponding higher relative vanishing, and this proof would no longer establish compatibility.

## 8. References

* Allen Hatcher (2002), *Algebraic Topology*: Theorem 2A.1 (first homology and abelianization); Theorem 3.2 (cohomological universal coefficient theorem); Theorem 4.5 (CW Whitehead theorem); Theorem 4.57 (cohomology representability).
* J. Peter May (1967), *Simplicial Objects in Algebraic Topology*: Theorems 14.1 and 14.3 (realization and products, with compactly generated product topology); Theorems 16.1 and 16.6 (simplicial and realized homotopy groups); Theorem 23.9 (the simplicial Eilenberg–Mac Lane construction).
* J. Peter May and Kate Ponto (2012), *More Concise Algebraic Topology: Localization, Completion, and Model Categories*: Corollary 2.2.3 (homotopy pullback exact sequence); Theorems 6.1.1 and 6.1.2 (local spaces and localization of nilpotent spaces); Proposition 6.2.3 (localization and products); Theorem 17.2.2 and its proof, printed pages 345–346 (the Quillen model structure, relative lifting for acyclic Serre fibrations, and the monoidal cofibration statement).


# Appendix. Reproducible arithmetic checks

**COMPUTATIONAL; confidence 1.00.** The included program `verify_arithmetic.py`
was run using exact integer and rational arithmetic. It checked the factorial
congruences through index 101, all 100 recurrence steps for each of the 26 primes
from 2 through 101, membership of every local primitive in its indicated
localization, and 100 rational recurrence steps. All checks passed.

The output `arithmetic_results.json` includes the first twelve values and the
precise check bounds. These finite checks supplement Lemmas E1--E3; they do not
replace the proofs of integral nonsplitting, vanishing at every prime, or any
topological assertion. Run `python3 verify_arithmetic.py` to reproduce them.

The independent audit notes are supplied as separate text sources. They record
the checks on infinite-dimensional homology, factorial normalization, divisible
torsion coefficients, the order of probe lifting, relative unit compatibility,
and exact numbered citations.
