---
title: "Local H-structures on finite Postnikov pieces"
subtitle: "A complete proof of Theorem LC, including infinite abelian fundamental groups"
date: "27 November 2026"
geometry: "margin=1in"
fontsize: 10pt
colorlinks: true
toc: true
numbersections: false
header-includes:
  - '\usepackage{amsmath,amssymb}'
  - '\allowdisplaybreaks'
---

**PROVED — Theorem LC follows from the stipulated local step, with no extra hypothesis. Confidence: 0.98.**

## Executive summary

The proof establishes the stronger local-to-global assertion: a simple finite-type finite Postnikov piece whose rationalization is a generalized Eilenberg–Mac Lane space and whose prime localizations are H-spaces is an H-space. The finite arithmetic square has a product of rationalizations as its common target. Rational H-structures need not be unique. The compatibility problem is solved by constructing actual maps into the full local Postnikov pieces that implement finite-index lattices of corrections in one rational degree while leaving every lower degree unchanged. A power-map lemma kills all higher torsion obstructions to those correction maps. Explicit Chinese remainder approximation then matches the local multiplications, degree by degree. Relative cohomology of the product and wedge supplies the unit-preserving compatibility homotopies. Finite generation and finite Postnikov height enter at distinct, identified steps. Counterexamples below concern the auxiliary local-to-global assertion; no unverified Taylor operation is attributed to them.

# 1. Statement, conventions, and imported foundations

Every lemma, construction, and consequence proved in Sections 2–16 is labelled **PROVED**, with confidence 0.98 unless a different confidence is stated. Each intermediate assertion inside a proof inherits that proof's status and confidence. Statements quoted from a numbered external theorem are labelled **PROVED by the cited theorem**. No argument below is labelled a proof merely because it passed a finite computation.

All spaces are pointed, connected CW complexes, with homotopy limits interpreted in the CW homotopy category. Products use the compactly generated topology. A pointed H-structure on Y is a map

\[
\mu:Y\times Y\longrightarrow Y
\]

whose restriction to \(Y\vee Y\) is pointed homotopic to the fold. No associativity or commutativity is assumed.

Put \(A_i=\pi_iW\). The hypotheses are that every \(A_i\) is finitely generated, \(A_i=0\) for \(i>N\), and W is simple: \(A_1\) is abelian and its actions on \(A_i\), \(i>1\), are trivial.

A Taylor operation here has exactly the meaning stipulated in the question: a map \(t:W^n\to W\) together with a nontrivial system of Taylor identities, each an equality up to homotopy between the composites \(W^2\to W^n\xrightarrow t W\) specified by two words in \(\{x,y\}^n\), with every variable position distinguished by at least one identity whose two words differ there. The two consequences below are inputs, not assertions proved from those identities in this manuscript.

We use exactly these stipulated inputs about Taylor operations:

1. The supplied Lemma A/B says that a space with the specified Taylor operation is simple.
2. The supplied local step says that every \(W_{(p)}\) is an H-space, that \(W_{\mathbb Q}\) is an H-space, and that every rational Postnikov invariant vanishes.

The proof does not need a choice of Taylor term after these inputs have been applied. In particular, it proves the following assertion.

**Theorem 1.1 — PROVED below; confidence 0.98.** Let W be simple, with finitely generated homotopy groups and finite Postnikov height. Suppose all rational Postnikov invariants vanish and every prime localization \(W_{(p)}\) has an H-structure. Then W has an H-structure.

Here \(\mathbb Z_{(p)}\) denotes the subring of \(\mathbb Q\) consisting of fractions with denominator prime to p. It never denotes the p-adic integers.

The foundational results imported in the proof are listed precisely here. Their consequences specific to this problem are proved in the sections that follow.

* May–Ponto (2012), Lemma 3.4.2: an Eilenberg–Mac Lane fibration with trivial action is principal.
* May–Ponto (2012), Theorem 4.5.2 and Theorem 6.1.4: finite generation of nilpotent homotopy groups implies the corresponding degreewise integral or localized homology finiteness.
* May–Ponto (2012), Theorem 6.1.2: nilpotent localization has its universal property and localizes homotopy and homology groups.
* May–Ponto (2012), Propositions 6.2.3 and 6.2.5: localization preserves finite products and connected nilpotent homotopy pullbacks.
* Hatcher (2002, cited online edition), Proposition 0.16: CW pairs have the homotopy extension property; Theorems 4.5 and 4.8: Whitehead and cellular approximation; Proposition 4.13 and Example 4.16: CW models and cell-attachment Postnikov constructions; Theorem 4.57: Eilenberg–Mac Lane representability; Theorem 3.15: the cohomological Künneth theorem under its finite-free hypothesis.

The numbering of Hatcher's Künneth theorem here is that in the linked Cornell online edition: 3.15. Some earlier copies number it 3.16. Full bibliographic details appear in Section 17.

We may choose connected CW models with one zero-cell, by Hatcher, Proposition 4.13. Thus the wedge inclusions used below are cofibrations. The cohomology of a based quotient of a CW pair is relative cohomology, by the cellular cochain description: the relative chain group is the free group on cells not in the subcomplex, and these are exactly the non-basepoint cells of the quotient.

**Construction 1.2 — PROVED using the numbered May (1967) results specified here; confidence 0.99.** Whenever strict addition or subtraction in an Eilenberg–Mac Lane target is used, use the following explicit model. For a countable abelian group M, let

\[
\mathcal K(M,n)_q=Z^n(\Delta[q];M).
\]

An element is an M-valued function on the strictly increasing lists of n+1 vertices satisfying the cocycle equation

\[
\sum_{i=0}^{n+1}(-1)^i
c(v_0,\ldots,\widehat v_i,\ldots,v_{n+1})=0.
\]

Simplicial operators are pullback along order-preserving vertex maps; a list with a repeated vertex contributes zero. Addition, negation and the zero element are pointwise. This is a countable simplicial abelian group. May (1967), Theorem 23.9, identifies its simplicial homotopy groups as M in degree n and zero elsewhere. Theorems 16.1 and 16.6 identify these with the homotopy groups of its realization. Theorem 14.1 makes the realization a CW complex, and Corollary 14.6 makes its realized addition, inverse and zero a strict topological abelian group structure. We take that realization as \(K(M,n)\). Coefficient homomorphisms act pointwise on the cocycles and realize to pointed homomorphisms. All coefficient groups for which this strict model is required below are countable. In Lemma 6.2 we accordingly state the extension assertion for countable M, which covers every application.

# 2. A cohomology finiteness and base-change lemma

**Lemma 2.1 — PROVED; confidence 0.98.** Let R be a localization of \(\mathbb Z\), let X be a CW complex whose \(H_i(X;R)\) are finitely generated R-modules, and let M be a finitely generated R-module. Then every \(H^j(X;M)\) is finitely generated over R, and the coefficient map induces an isomorphism

\[
H^j(X;M)\otimes_R\mathbb Q
\xrightarrow{\cong}
H^j(X;M\otimes_R\mathbb Q).
\tag{2.1}
\]

The same conclusion holds after replacing \(\mathbb Q\) by any further localization of R. A class whose rational coefficient image is zero is torsion. For \(R=\mathbb Z_{(p)}\), such a class has finite p-power order.

**Proof.** Let \(C_*\) be the cellular chain complex with R-coefficients, and write \(Z_i=\ker d_i\), \(B_i=\operatorname{im}d_{i+1}\). A localization of \(\mathbb Z\) is a principal ideal domain. Submodules of free modules over a principal ideal domain are free, so the surjection \(C_i\to B_{i-1}\) has a splitting. Choose one. This identifies

\[
C_i=Z_i\oplus B_{i-1},\qquad d_i(z,b)=b\in Z_{i-1}\subseteq C_{i-1}.
\]

A degree-j cochain is a homomorphism on each of the two summands. It is a cocycle exactly when its component on \(Z_j\) vanishes on \(B_j\). That component then gives a homomorphism from \(H_j(X;R)\) to M. Coboundaries have zero component on \(Z_j\); their components on \(B_{j-1}\) are exactly the restrictions of homomorphisms \(Z_{j-1}\to M\). The free resolution

\[
0\longrightarrow B_{j-1}\longrightarrow Z_{j-1}
\longrightarrow H_{j-1}(X;R)\longrightarrow0
\]

therefore gives the natural short exact sequence

\[
0\longrightarrow\operatorname{Ext}^1_R(H_{j-1}(X;R),M)
\longrightarrow H^j(X;M)
\longrightarrow\operatorname{Hom}_R(H_j(X;R),M)
\longrightarrow0.
\tag{2.2}
\]

For a finitely generated R-module, use its decomposition into finitely many free summands and cyclic torsion summands. On the summands of the first argument in (2.2),

\[
\begin{aligned}
\operatorname{Hom}_R(R,M)&=M,&
\operatorname{Ext}^1_R(R,M)&=0,\\
\operatorname{Hom}_R(R/(a),M)&=\{m:am=0\},&
\operatorname{Ext}^1_R(R/(a),M)&=M/aM.
\end{aligned}
\]

These formulas prove finite generation of both end terms and hence of the middle term. They also show, summand by summand, that extension of scalars to any further localization commutes with both end terms. Localization is exact. Apply it to (2.2), compare with (2.2) for the localized coefficient module, and use the end-term isomorphisms to obtain the middle isomorphism. For rational coefficients the torsion end terms disappear. The kernel of localization of a module consists exactly of its torsion elements. A torsion element in a finitely generated \(\mathbb Z_{(p)}\)-module is killed by a power of p. This proves all assertions. \(\square\)

**Lemma 2.2 — PROVED; confidence 0.98.** A localization of a simple nilpotent space is simple, even if its fundamental group is infinite.

**Proof.** Let R be a localization of \(\mathbb Z\). Theorem 6.1.2 of May–Ponto identifies the localized homotopy groups with \(A_i\otimes R\); for \(i=1\) this applies because \(A_1\) is abelian. In particular the localized fundamental group is abelian.

Its action on \(A_i\otimes R\) is nilpotent because the localized space is nilpotent. Every automorphism of an R-local abelian group is R-linear: it commutes with multiplication by integers and with the uniquely defined division by each inverted integer. Naturality of the fundamental-group action shows that the image of \(A_1\) acts trivially on the image of \(A_i\). R-linearity then shows it acts trivially on all of \(A_i\otimes R\).

Fix an element g of \(A_1\otimes R\). Some positive integer s, invertible in R, has \(sg\) in the image of \(A_1\). Let T be the action of g on \(A_i\otimes R\). Thus \(T^s=1\). Nilpotence of the action gives a finite filtration with trivial action on the quotients; hence \(U=T-1\) satisfies \(U^c=0\) for some c. Expanding \(T^s-1\) gives

\[
0=U\left(sI+\binom{s}{2}U+\cdots+U^{s-1}\right).
\]

The factor in parentheses is invertible. After dividing by the unit s, it is \(I+V\), where V is a polynomial in U with zero constant term; V is nilpotent, and \(I-V+V^2-\cdots\) terminates and is its inverse. Therefore U=0 and T=1. Since g was arbitrary, the action is trivial. \(\square\)

# 3. The torsion invariants and the away-from-finitely-many-primes piece

**Lemma 3.1 — PROVED; confidence 0.98.** Under the hypotheses of Theorem 1.1, every integral Postnikov invariant has finite order. If \(e_0\) is the least common multiple of these orders, with order 1 assigned to a zero class, then

\[
W[1/e_0]\simeq
\prod_{i=1}^N K(A_i\otimes\mathbb Z[1/e_0],i).
\tag{3.1}
\]

**Proof.** Write \(W_j=P_jW\). Simplicity makes each stage above \(W_1=K(A_1,1)\) a principal fibration, by May–Ponto, Lemma 3.4.2. Fix classifying maps

\[
\kappa_j:W_{j-1}\longrightarrow K(A_j,j+1),\qquad 2\le j\le N,
\]

with \(W_j\) identified with their homotopy fibers. The groups \(H_i(W_{j-1};\mathbb Z)\) are finitely generated by May–Ponto, Theorem 4.5.2. Lemma 2.1 applies to \(H^{j+1}(W_{j-1};A_j)\).

The rational Postnikov invariant is zero by hypothesis. Localization on homology, together with (2.2) with rational coefficients, identifies cohomology on the rationalized base with cohomology of the original base with rational coefficients. Thus \([\kappa_j]\) has zero image in \(H^{j+1}(W_{j-1};A_j\otimes\mathbb Q)\). By Lemma 2.1 it is torsion; since the group is finitely generated, its order is finite.

There are only N-1 such classes. Their least common multiple \(e_0\) is therefore a finite positive integer. After inverting \(e_0\), the coefficient image of every \([\kappa_j]\) is zero.

We justify that this kills the localized classifying map, rather than only its pullback. For any localization R, a map \(X\to X_R\) induces an isomorphism on R-homology by May–Ponto, Theorem 6.1.2. Apply (2.2), over R, to see that it induces an isomorphism on cohomology with any R-module coefficients. Equivalently the mapping cone has zero R-homology, and (2.2) gives zero cohomology with those coefficients. Consequently the localized classifying class on \((W_{j-1})_R\) is zero if and only if its coefficient-image pullback on \(W_{j-1}\) is zero.

Localization preserves the connected homotopy-fiber diagrams by May–Ponto, Proposition 6.2.5. A null classifying map has homotopy fiber equivalent to the product of its domain and \(K(A_j\otimes R,j)\). More explicitly, in the model consisting of pairs \((x,\gamma)\) with \(\gamma\) a path from \(\kappa_j(x)\) to zero, a chosen nullhomotopy provides one such path for each x. Concatenating that path with an arbitrary loop gives a map from the product. Concatenating its reverse gives an inverse up to the path-concatenation homotopies that delete a path followed by its reverse. These homotopies keep the endpoints fixed. Applying this at each stage, starting at \(K(A_1\otimes R,1)\), proves (3.1). \(\square\)

For the rest of the proof, enlarge \(e_0\) to

\[
e=\operatorname{lcm}\bigl(e_0,\exp\operatorname{Tor}A_1,\ldots,
\exp\operatorname{Tor}A_N\bigr).
\]

Assign exponent 1 to a zero torsion group. Set

\[
S=\{p:p\mid e\},\quad R=\mathbb Z[1/e],\quad
F_i=A_i/\operatorname{Tor}A_i,\quad V_i=A_i\otimes\mathbb Q.
\]

The set S is finite. Choose bases of the free abelian groups \(F_i\), of ranks \(r_i\), and use the compatible rational bases of \(V_i\). Lemma 3.1 gives a localization model

\[
G_R=\prod_{i=1}^N K(F_i\otimes R,i),\qquad
G=\prod_{i=1}^N K(V_i,i).
\tag{3.2}
\]

The product equivalence can be chosen to induce the specified identifications on homotopy groups: at a null principal stage its fiber factor is the labelled \(K(A_j\otimes R,j)\), and the base equivalence has already been fixed. We use \(G_R\) as the model for \(W_R\), and G as its rationalization. The Eilenberg–Mac Lane factors are chosen with their abelian addition maps.

If S is empty, (3.1) makes W itself a product of Eilenberg–Mac Lane spaces, and its coordinatewise addition proves the theorem. We henceforth assume S is nonempty. The cases N=0 and N=1 are already covered: a connected zero-type is contractible, and a simple one-type is \(K(A_1,1)\) with \(A_1\) abelian.

# 4. Explicit arithmetic approximation

**Lemma 4.1 — PROVED; confidence 0.98.** For a finite set S of primes,

\[
\mathbb Z[S^{-1}]\longrightarrow
\bigoplus_{p\in S}\mathbb Q/\mathbb Z_{(p)}
\tag{4.1}
\]

is surjective, where a rational number is sent to its class in every summand.

**Proof.** Choose representatives \(q_p\in\mathbb Q\). For each p choose
\(s_p\ge\max(0,-v_p(q_p))\) and put \(M=\prod_{p\in S}p^{s_p}\). Then \(Mq_p\in\mathbb Z_{(p)}\). It has a well-defined residue modulo \(p^{s_p}\): write it with denominator prime to p and invert that denominator modulo \(p^{s_p}\). When \(s_p=0\), this is a congruence modulo 1.

Choose an integer b satisfying

\[
b\equiv Mq_p\pmod{p^{s_p}}\qquad(p\in S).
\]

Such b exists by the integer Chinese remainder theorem. This theorem follows from Bézout's identity: for the pairwise coprime moduli \(m_p=p^{s_p}>1\), choose integers \(u_p\) with \(u_p(M/m_p)\equiv1\pmod{m_p}\); then the sum of the prescribed residues times \(u_p(M/m_p)\) has every prescribed residue.

Put \(a=b/M\in\mathbb Z[S^{-1}]\). At prime p, the numerator \(b-Mq_p\) belongs to \(p^{s_p}\mathbb Z_{(p)}\), while \(M/p^{s_p}\) is a unit in \(\mathbb Z_{(p)}\). Hence \(a-q_p\in\mathbb Z_{(p)}\) for every p. This proves surjectivity. \(\square\)

**Lemma 4.2 — PROVED; confidence 0.98.** Let D be a finite-dimensional rational vector space. Let L be a finitely generated R-submodule spanning D over \(\mathbb Q\), where \(R=\mathbb Z[S^{-1}]\). For every \(p\in S\), let \(C_p\subset D\) be a finitely generated \(\mathbb Z_{(p)}\)-submodule spanning D. Then

\[
L\longrightarrow\bigoplus_{p\in S}D/C_p
\tag{4.2}
\]

is surjective.

**Proof.** Choose a rational basis of D and let M be its integral span. Since every specified submodule spans D, write each basis vector as a rational combination of finitely many of its generators. Clearing the finitely many denominators, for all the finitely many submodules at once, gives an integer \(d>0\) with

\[
d(M\otimes R)\subseteq L,\qquad
d(M\otimes\mathbb Z_{(p)})\subseteq C_p\quad(p\in S).
\]

For representatives \(v_p\in D\), apply Lemma 4.1 in every chosen basis coordinate to \(v_p/d\). Obtain \(u\in M\otimes R\) satisfying \(u-v_p/d\in M\otimes\mathbb Z_{(p)}\). Then \(a=du\) is in L and \(a-v_p\in C_p\) for every p. \(\square\)

# 5. The corrected fracture square, proved on homotopy groups

**Lemma 5.1 — PROVED; confidence 0.98.** For every abelian group A there is an exact sequence

\[
0\longrightarrow A
\longrightarrow A\otimes R\ \oplus\!\prod_{p\in S}A\otimes\mathbb Z_{(p)}
\xrightarrow{d}\prod_{p\in S}A\otimes\mathbb Q
\longrightarrow0,
\tag{5.1}
\]

where \(d(a_0,(a_p))=(a_0-a_p)_p\).

**Proof.** First take A equal to \(\mathbb Z\). The kernel consists of a common rational number belonging to R and to every \(\mathbb Z_{(p)}\), \(p\in S\). A reduced denominator in R uses only primes of S; membership in every indicated local ring excludes all those primes. The common number is therefore integral. Surjectivity follows from Lemma 4.1: choose \(a_0\in R\) with \(a_0-q_p\in\mathbb Z_{(p)}\), and set \(a_p=a_0-q_p\).

Tensor this short exact sequence with A. Its rightmost term is a finite direct sum of copies of \(\mathbb Q\), hence is flat over \(\mathbb Z\). For clarity, localization is exact directly from the fraction criterion: an element a/s maps to zero in a localized quotient exactly when some allowed denominator t sends a into the original kernel, and then a/s is the image of the kernel element ta/(ts). An injection remains an injection because a fraction is zero exactly when an allowed denominator kills its numerator. This proves flatness of \(\mathbb Q\) and of every localization ring used here. The Tor term at the left is therefore zero, so tensoring preserves injectivity as well as exactness at the other terms. Finite products of abelian groups are finite direct sums, and tensoring therefore produces exactly (5.1). \(\square\)

**Proposition 5.2 — PROVED; confidence 0.98.** For a simple space W and finite nonempty S, the canonical diagram gives an equivalence

\[
W\simeq P:=\operatorname{holim}\left(
W_R\longrightarrow\prod_{p\in S}W_{\mathbb Q}
\longleftarrow\prod_{p\in S}W_{(p)}\right).
\tag{5.2}
\]

The left arrow is diagonal rationalization. No finiteness of \(\pi_1W\) is required for this proposition.

**Proof.** Choose localization maps \(\ell_R:W\to W_R\), \(\ell_p:W\to W_{(p)}\), rationalization maps to a common rational model G, and pointed comparison homotopies between the two resulting maps \(W\to G\). They exist by the universal property in May–Ponto, Theorem 6.1.2. They determine a comparison \(\chi:W\to P\).

Write \(B=W_R\times\prod_pW_{(p)}\), \(C=\prod_pG\). A path-space model for P consists of a point of B and, for each p, a path from its away-piece rational image to its p-piece rational image. Projection to B is the pullback of the endpoint path fibration of C; its fiber over the basepoint is \(\Omega C\). The homotopy exact sequence is the one of this fibration, with the comparison maps on homotopy groups given by the difference of the endpoint maps. This description, including the degree-one and component terms, is recorded in May–Ponto, Corollary 2.2.3.

For every \(i\ge1\), the comparison on \(\pi_iB\to\pi_iC\) is the map d in (5.1), with \(A=\pi_iW\). For \(i=1\) these are abelian groups because W is simple; there is no nonabelian interpretation of subtraction to resolve. Lemma 5.1 says these maps are all onto.

The components of P are the orbits of \(\pi_1C\) under the endpoint images of \(\pi_1B\). In the present abelian situation this is their quotient by the image of d. Surjectivity makes that quotient zero, so P is connected. In every positive degree, surjectivity of the preceding comparison map in the exact sequence makes

\[
\pi_iP\cong\ker\bigl(\pi_iB\to\pi_iC\bigr)\cong\pi_iW.
\]

The map induced by \(\chi\) is the diagonal map in (5.1), so these are the isomorphisms induced by \(\chi\), not just abstract isomorphisms. On CW models, Whitehead's theorem, Hatcher Theorem 4.5, makes \(\chi\) a homotopy equivalence. This proves (5.2). \(\square\)

The version with a single common rational target and a product of several prime-local pieces is not the square just proved. The product \(\prod_{p\in S}W_{\mathbb Q}\), and the diagonal left map into it, are essential.

# 6. Relative units and the precise deviation groups

**Lemma 6.1 — PROVED; confidence 0.98.** Let Y be connected, put \(B=Y\times Y\), \(A=Y\vee Y\), and let M be any abelian coefficient group. For every \(n\ge1\),

\[
H^n(B,A;M)\longrightarrow H^n(B;M)
\tag{6.1}
\]

is injective and has image the kernel of restriction to A.

**Proof.** For \(k>0\), identify \(H^k(A;M)\) with \(H^k(Y;M)\oplus H^k(Y;M)\). If \((u,v)\) is such a pair, \(\operatorname{pr}_1^*u+\operatorname{pr}_2^*v\) restricts to \((u,v)\), because the unwanted projection on each wedge summand is constant and therefore induces zero in positive-degree cohomology. Hence restriction is onto in positive degrees. In degree zero it is an isomorphism because B and A are connected.

In the long exact sequence of the pair, the map preceding (6.1) is the connecting map out of \(H^{n-1}(A;M)\). The just-proved surjectivity makes that connecting map zero. Exactness gives injectivity of (6.1) and identifies its image as claimed. \(\square\)

**Lemma 6.2 — PROVED; confidence 0.98.** Let M be a countable abelian group. Fix a map \(a:A\to K(M,n)\) and a strict extension \(f_0:B\to K(M,n)\). Relative homotopy classes of strict extensions of a form a torsor under

\[
H^n(B,A;M)=\widetilde H^n(Y\wedge Y;M).
\tag{6.2}
\]

For a finite product of Eilenberg–Mac Lane targets the torsor is the direct sum of these groups. If two strict extensions have the same absolute cohomology classes in every target coordinate, they are homotopic relative to A.

**Proof.** Use an abelian Eilenberg–Mac Lane model. For a strict extension f, the pointwise difference \(f-f_0\) is zero on A and therefore factors through \(B/A\). Conversely, adding any pointed map \(B/A\to K(M,n)\) to \(f_0\) gives an extension of a. These constructions are inverse on maps and on homotopies relative to A. Hatcher, Theorem 4.57, identifies pointed homotopy classes out of \(B/A\) with its reduced cohomology, which is the relative group in (6.2).

For a finite product, apply these inverse constructions in each coordinate. Equality of absolute cohomology classes says the relative difference maps to zero in (6.1). Lemma 6.1 makes its relative class zero. A pointed nullhomotopy on the quotient, added to \(f_0\), is a homotopy relative to A between the two extensions. \(\square\)

Let \(G=\prod_{i=1}^N K(V_i,i)\) as in (3.2), and let \(\iota_i\in H^i(G;V_i)\) be the class represented by the ith projection, with the coefficient basis already fixed. Define

\[
D_i=\widetilde H^i(G\wedge G;V_i).
\tag{6.3}
\]

By Lemmas 6.1 and 6.2, the rational unital multiplications form a torsor under \(\bigoplus_{i=1}^N D_i\), with coordinatewise addition as origin. For a multiplication \(\nu\), its ith deviation is the unique relative class represented absolutely by

\[
\nu^*\iota_i-\operatorname{pr}_1^*\iota_i-\operatorname{pr}_2^*\iota_i.
\tag{6.4}
\]

Every tuple of such relative classes is realized: represent the ith class by a map from \(G\wedge G\) to \(K(V_i,i)\), compose with the quotient, and add it to the two ith projections. The product of these coordinate maps is the required multiplication. On the wedge the correction maps are zero, so the unit is strict in these models. There are no associativity equations to impose in this problem.

# 7. Why the degree-n cross-term uses only lower layers

**Lemma 7.1 — PROVED; confidence 0.98.** For a connected CW complex Y, any abelian group M, and \(n\ge1\), the Postnikov map induces an isomorphism

\[
\widetilde H^n(P_{n-1}Y\wedge P_{n-1}Y;M)
\xrightarrow{\cong}
\widetilde H^n(Y\wedge Y;M).
\tag{7.1}
\]

**Proof.** Choose a one-zero-cell model for Y. Realize its map to \(P_{n-1}Y\) by adjoining cells of dimensions at least \(n+1\). Explicitly, first adjoin \((n+1)\)-cells along representatives of every element of \(\pi_nY\); then adjoin \((n+2)\)-cells to kill the next homotopy group of the resulting space, and continue. At the k-step, attaching \((k+1)\)-cells kills the specified \(\pi_k\) and leaves all lower homotopy groups unchanged, as the relative cellular approximation theorem gives zero relative homotopy groups below degree \(k+1\). For k=1 the attached two-cells kill the represented normal subgroup of \(\pi_1\), and attaching cells along all loops kills it entirely. In the union, every unwanted homotopy class is killed at its step; cellular approximation of a sphere map sees the relevant finite-dimensional skeleton. This is the Postnikov cell construction of Hatcher, Example 4.16. Denote the resulting CW model by Q, so \(Y\subset Q\simeq P_{n-1}Y\) and every relative cell has dimension at least \(n+1\).

The non-basepoint cells of a smash of two one-zero-cell CW complexes are products of positive-dimensional cells, with dimensions added. Every cell of \(Q\wedge Q\) not in \(Y\wedge Y\) contains one of the newly attached cells and a positive-dimensional cell in the other factor. Its dimension is at least \((n+1)+1=n+2\). Thus the relative cellular cochain groups of \((Q\wedge Q,Y\wedge Y)\) are zero through degree \(n+1\), for coefficients M. Their relative cohomology is zero in those degrees. The long exact sequence of this pair proves (7.1). \(\square\)

**Lemma 7.2 — PROVED; confidence 0.98.** For a rational unital multiplication on G, the degree-n deviation is a sum of cross-terms involving only the two copies of \(P_{n-1}G\). In particular \(D_1=0\).

**Proof.** Each rational cohomology group of G is finite-dimensional: this follows from its finite-dimensional rational homotopy groups and May–Ponto, Theorem 6.1.4. Hatcher's field Künneth theorem gives

\[
D_n\cong
\bigoplus_{\substack{a+b=n\\a,b>0}}
H^a(G;\mathbb Q)\otimes H^b(G;\mathbb Q)\otimes V_n.
\tag{7.2}
\]

To obtain the kernel of restriction, remove the two pure summands with a=0 or b=0; those are exactly the two wedge restrictions. Each remaining a,b is less than n. A factor \(K(V_i,i)\) has no positive cohomology below i, since it has a CW model with no positive cells below i. The product Künneth description therefore shows that cohomology of G in degrees less than n is pulled back from its factors of degrees less than n. Every cross-term in (7.2) is consequently pulled back from \(P_{n-1}G\times P_{n-1}G\), and vanishes when either of these two lower-layer inputs is the basepoint. For n=1 the indexing set in (7.2) is empty, so \(D_1=0\). \(\square\)

This proves the lower-layer assertion over arbitrary coefficients in (7.1), and proves the exact rational triangularity used in the gluing induction in (7.2). Infinite \(\pi_1\) contributes degree-one classes; it does not create a degree-one cross-term.

# 8. Power maps kill the bounded torsion obstructions

Fix a prime p and put \(R_p=\mathbb Z_{(p)}\). Let

\[
E=K(R_p^r,n),\qquad r<\infty,\quad n\ge1,
\]

and let \(s:E\to E\) be induced by multiplication by p on \(R_p^r\). Iterates \(s^b\) below mean composition, so \((s^b)_*\) on \(\pi_nE\) is multiplication by \(p^b\).

By May–Ponto, Theorem 6.1.4, \(H_i(E;R_p)\) is finitely generated over \(R_p\). Lemma 2.1 implies finite generation of cohomology with finitely generated \(R_p\)-module coefficients. In particular \(H^j(E;\mathbb F_p)\) is finite-dimensional in each degree.

**Lemma 8.1 — PROVED; confidence 0.98.** If \(2^b>d\), then

\[
(s^b)^*:H^j(E;\mathbb F_p)\longrightarrow H^j(E;\mathbb F_p)
\]

is zero for \(1\le j\le d\).

**Proof.** Let \(I=H^{>0}(E;\mathbb F_p)\) be the positive-degree ideal. Use addition \(\nu:E\times E\to E\) on an abelian Eilenberg–Mac Lane model. The field Künneth theorem applies because each cohomology group is finite-dimensional. For homogeneous x of positive degree, the unit identities imply

\[
\nu^*x=x\otimes1+1\otimes x+\sum_\ell a_\ell\otimes b_\ell,
\qquad |a_\ell|,|b_\ell|>0.
\]

Let \([k]\) denote the k-fold sum map. Pulling back along \(([k],\mathrm{id})\Delta\) gives

\[
[k+1]^*x=[k]^*x+x+
\sum_\ell([k]^*a_\ell)\smile b_\ell.
\]

Every term in the sum belongs to \(I^2\). Starting at k=1, induction gives \([k]^*x\equiv kx\pmod{I^2}\). The map \([p]\) induces multiplication by p on the unique nonzero homotopy group of E, and is the map s. Thus \(s^*(I)\subseteq I^2\).

Since pullback is a ring homomorphism, \(s^*(I^a)\subseteq I^{2a}\) for each positive a. After b iterations, \((s^b)^*(I)\subseteq I^{2^b}\). A product of \(2^b\) positive-degree classes has degree at least \(2^b\), so this ideal has no part in degrees \(1,\ldots,d\). \(\square\)

**Lemma 8.2 — PROVED; confidence 0.98.** Fix b as in Lemma 8.1. For every \(a\ge1\), the map \(s^{ba}\) induces zero on \(H^j(E;\mathbb Z/p^a)\), \(1\le j\le d\). The conclusion also holds for coefficients in a finite abelian p-group of exponent dividing \(p^a\).

**Proof.** Put \(u=s^b\). The case a=1 is Lemma 8.1. Suppose the conclusion holds for a-1. In the coefficient sequence

\[
0\longrightarrow\mathbb Z/p
\xrightarrow{1\mapsto p^{a-1}}\mathbb Z/p^a
\longrightarrow\mathbb Z/p^{a-1}\longrightarrow0,
\]

let z belong to \(H^j(E;\mathbb Z/p^a)\). The image of \((u^{a-1})^*z\) in coefficients \(\mathbb Z/p^{a-1}\) is zero by naturality and the induction hypothesis. The long exact coefficient sequence supplies \(y\in H^j(E;\mathbb Z/p)\) mapping to \((u^{a-1})^*z\). Pulling back once more gives \((u^a)^*z\) equal to the image of \(u^*y=0\). This proves the induction.

A finite abelian p-group is a finite direct sum of cyclic groups \(\mathbb Z/p^c\), \(c\le a\). Cohomology with this finite direct sum is the direct sum of their cohomology, since the cochain Hom functor commutes with finite direct sums of coefficient modules. Each cyclic summand is killed by \(u^c\), and further pullback leaves zero unchanged. Thus \(u^a\) kills all summands. \(\square\)

**Lemma 8.3 — PROVED; confidence 0.98.** Let M be a finitely generated \(R_p\)-module and let \(\alpha\in H^j(E;M)\), \(j\ge1\), be torsion. Some iterate \(s^t\) kills \(\alpha\). A single t can be chosen for any finite list of such classes.

**Proof.** Decompose \(M=R_p^a\oplus T\), where T is a finite abelian p-group. Consider a free-coefficient coordinate \(\alpha_0\in H^j(E;R_p)\). For j=1 the Ext term in (2.2) is \(\operatorname{Ext}^1_{R_p}(R_p,R_p)=0\), since E is connected. The remaining Hom module is torsion-free: if \(p^c f=0\), then \(p^c f(x)=0\) in the torsion-free group \(R_p\) for every x, so f=0. Thus \(\alpha_0=0\) in degree one.

For \(j\ge2\), choose c with \(p^c\alpha_0=0\). The coefficient sequence

\[
0\longrightarrow R_p\xrightarrow{p^c}R_p
\longrightarrow R_p/p^cR_p\longrightarrow0
\]

has connecting map \(\beta:H^{j-1}(E;\mathbb Z/p^c)\to H^j(E;R_p)\). Exactness supplies a class z with \(\beta z=\alpha_0\). Lemma 8.2 kills z after finitely many iterates of s. Naturality then gives \((s^t)^*\alpha_0=\beta((s^t)^*z)=0\).

There are finitely many free-coefficient coordinates, so take the maximum of their required exponents. If T has exponent \(p^a\), Lemma 8.2 kills its coefficient component in degree j after another finite bound; taking the maximum of that bound and the preceding bounds kills the entire class. For a finite list of classes take the maximum of the finitely many bounds obtained. Further pullback of a zero class remains zero. \(\square\)

The proof supplies a finite procedure for a bound: choose b with \(2^b\) greater than all relevant degrees, determine a p-power annihilator for each free-coefficient torsion coordinate, and use b times that exponent; include the exponent of each finite coefficient summand. No bound independent of the given finite tower is asserted or needed.

# 9. Actual correction maps into the full local space

**Lemma 9.1 — PROVED; confidence 0.98.** Let Y be a simple p-local N-type, with each \(A_j(Y)\) finitely generated over \(R_p\), and suppose every classifying invariant has zero rational coefficient image. For \(2\le n\le N\), choose a free-summand inclusion

\[
j_n:R_p^{r_n}\hookrightarrow\pi_nY.
\]

There are an integer \(K_{p,n}\ge0\) and a pointed map

\[
h_{p,n}:K(R_p^{r_n},n)\longrightarrow Y
\tag{9.1}
\]

whose projection into \(P_{n-1}Y\) is constant in a tower model and whose induced homomorphism on \(\pi_n\) is \(p^{K_{p,n}}j_n\).

**Proof.** If \(r_n=0\), use the constant map from a point. Otherwise put \(E=K(R_p^{r_n},n)\), with the power map s of Section 8. Choose the principal Postnikov tower \(Y_j=P_jY\), with

\[
\kappa_j:Y_{j-1}\to K(\pi_jY,j+1).
\]

Use the pointed homotopy-fiber model

\[
Y_j=\{(y,\gamma):\gamma(0)=\kappa_j(y),\ \gamma(1)=0\}.
\tag{9.2}
\]

Start with the constant map \(g_{n-1}:E\to Y_{n-1}\). The actual fiber of \(Y_n\to Y_{n-1}\) over the basepoint is \(\Omega K(\pi_nY,n+1)\). Choose a pointed equivalence from \(K(\pi_nY,n)\) to that loop space inducing the identity on \(\pi_nY\). Such an equivalence is obtained by the loop-suspension adjoint of a map representing the suspension of the fundamental class; representability gives the map, its induced homomorphism in degree n is the identity, and Whitehead's theorem gives the equivalence because the other homotopy groups on both sides vanish. Compose \(K(j_n,n)\) with this equivalence and the actual fiber inclusion to define \(g_n\). It induces \(j_n\) on \(\pi_n\) and has constant projection into \(Y_{n-1}\).

Suppose \(g_{j-1}:E\to Y_{j-1}\) has been constructed for \(j>n\). Its lifting obstruction is

\[
\alpha_j=g_{j-1}^*[\kappa_j]
\in H^{j+1}(E;\pi_jY).
\]

Its rational coefficient image is zero because that of \([\kappa_j]\) is zero. Lemma 2.1 makes \(\alpha_j\) a p-power torsion class. Lemma 8.3 supplies \(t_j\ge0\) with \((s^{t_j})^*\alpha_j=0\). The composite \(\kappa_jg_{j-1}s^{t_j}\) therefore represents zero in cohomology. Eilenberg–Mac Lane representability, Hatcher Theorem 4.57, gives a pointed nullhomotopy \(H_j\) from this composite to zero. Define

\[
g_j(x)=\bigl(g_{j-1}(s^{t_j}x),\ H_j(x,-)\bigr)
\]

in (9.2). This is a pointed lift. Replace every already constructed lower-stage map by its composite with the same \(s^{t_j}\). Compatibility of the maps through the lower tower is then maintained. The projection into \(Y_{n-1}\) remains constant because precomposing a constant map preserves it.

For \(j>n\), projection \(Y_j\to Y_{j-1}\) is an isomorphism on \(\pi_n\). The source map \(s^{t_j}\) multiplies \(\pi_nE\) by \(p^{t_j}\). Induction therefore shows that the final \(g_N\) induces

\[
p^{K_{p,n}}j_n,
\qquad K_{p,n}=\sum_{j=n+1}^N t_j.
\]

The sum is finite because the tower has finite height. Composing with the chosen equivalence \(Y_N\simeq Y\) gives (9.1). \(\square\)

The p-localizations of W satisfy the hypotheses of this lemma. Their simplicity follows from Lemma 2.2. Their homotopy groups are \(A_j\otimes R_p\). Localizing the principal tower identifies its rational classifying maps with the rational maps already assumed null.

Choose \(j_n\) so its free basis rationalizes to the fixed basis of \(V_n\). The nth rational coordinate of \(h_{p,n}\) is then \(p^{K_{p,n}}\) times the fundamental class of \(K(R_p^{r_n},n)\). To justify this last statement, the source has zero reduced homology below n and its nth homology is its nth homotopy group, by Hatcher, Theorem 4.32. The cohomology calculation (2.2) in degree n consequently identifies maps to \(K(V_n,n)\) with the induced homomorphism on that group. Equivalently the Eilenberg–Mac Lane source and target are n-types with the specified homomorphism. The lower rational coordinates vanish because the map has constant projection into \(P_{n-1}Y\).

# 10. One-coordinate modification of a complete multiplication

**Lemma 10.1 — PROVED; confidence 0.98.** Let \(Y=W_{(p)}\), and fix a unital multiplication \(\mu_p^0\) on Y. It can be chosen to have strict unit. For a unital multiplication f on Y and a pointed map

\[
c:Y\wedge Y\to K(R_p^{r_n},n),
\]

define

\[
\delta=h_{p,n}\,c\,q,
\qquad
f'=\mu_p^0(f,\delta),
\tag{10.1}
\]

where \(q:Y\times Y\to Y\wedge Y\) is the quotient. Then f' is unital. Its rational coordinates below n equal those of f, and its nth rational deviation equals that of f plus \(p^{K_{p,n}}c_{\mathbb Q}\). Higher coordinates are allowed to change.

**Proof.** The homotopy from \(\mu_p^0|_{Y\vee Y}\) to the fold extends over \(Y\times Y\) by the homotopy extension property, Hatcher Proposition 0.16. Its final map is homotopic to \(\mu_p^0\) and has strict unit. Make this replacement once. Apply the same operation to f when needed. Since all maps after q are pointed, \(\delta\) is exactly the basepoint on the wedge. Therefore

\[
f'(x,*)=\mu_p^0(f(x,*),*)=x,
\qquad
f'(*,y)=\mu_p^0(f(*,y),*)=y.
\]

Thus f' also has strict unit.

Use the fixed rational model G. The rationalization of \(\mu_p^0\) exists because rational localization preserves products and G is rational. In coordinate j it has the form

\[
(\mu_{p,\mathbb Q}^0)^*\iota_j
=\operatorname{pr}_1^*\iota_j+\operatorname{pr}_2^*\iota_j+d_j.
\]

Lemma 7.2 expresses every term of \(d_j\) as a product of positive-degree classes from both inputs, each of degree less than j. If \(j\le n\), every positive-degree class from the second input occurring here pulls back to zero under \(\delta\), since \(\delta\) has null projection into \(P_{n-1}Y\). Therefore \((f,\delta)^*d_j=0\).

For \(j<n\), \(\delta^*\iota_j=0\); hence \((f')^*\iota_j=f^*\iota_j\). For \(j=n\), Lemma 9.1 gives \(\delta^*\iota_n=p^{K_{p,n}}c_{\mathbb Q}\), so

\[
(f')^*\iota_n=f^*\iota_n+p^{K_{p,n}}c_{\mathbb Q}.
\]

Subtracting the unchanged two projection classes gives the same formula for deviations. All statements concern maps into the full Y, not tentative maps into a lower Postnikov stage. Thus the construction imposes no further higher-stage lifting condition. \(\square\)

# 11. The exact lattices that occur in Chinese remainder approximation

**Lemma 11.1 — PROVED; confidence 0.98.** The following are full lattices in the finite-dimensional rational vector space \(D_n\) of (6.3):

\[
\begin{aligned}
L_{R,n}&=\operatorname{im}\left(
\widetilde H^n(G_R\wedge G_R;F_n\otimes R)
\longrightarrow D_n\right),\\
L_{p,n}&=\operatorname{im}\left(
\widetilde H^n(W_{(p)}\wedge W_{(p)};R_p^{r_n})
\longrightarrow D_n\right).
\end{aligned}
\tag{11.1}
\]

The first is a finitely generated R-module and the second a finitely generated \(R_p\)-module. In each case “full” means that its rational span is all of \(D_n\). The coefficient bases and rationalization identifications in these maps are those fixed above. More explicitly, each displayed arrow first changes coefficients to the rational vector space and then applies the inverse of the cohomology pullback induced by the rationalization of the smash; that pullback is proved to be an isomorphism below.

**Proof.** For Y equal to \(G_R\) or \(W_{(p)}\), use its corresponding localization ring T. The homotopy groups of Y, and of \(Y\times Y\), are finitely generated T-modules. May–Ponto, Theorem 6.1.4, makes their homology groups finitely generated over T. The positive homology of \(Y\vee Y\) is the direct sum of the positive homology of its two summands. The long exact homology sequence of the wedge-to-product cofibration, and the Noetherian property of T, now give finite generation of the homology of \(Y\wedge Y\) in every degree.

Lemma 2.1 makes its indicated cohomology groups finitely generated and identifies their tensor product with \(\mathbb Q\) with rational-coefficient cohomology. The rationalization \(Y\to G\) is a rational homology isomorphism. Its product map is a rational homology isomorphism because localization preserves finite products. Its wedge map is a rational homology isomorphism by the direct-sum description. The long exact homology sequences of the two cofibrations therefore imply that \(Y\wedge Y\to G\wedge G\) is a rational homology isomorphism. With rational coefficients (2.2) converts this into a cohomology isomorphism. Thus tensoring either image in (11.1) with \(\mathbb Q\) gives all of \(D_n\).

Each image is torsion-free because it is a submodule of a rational vector space; finite generation over the relevant principal ideal domain makes it a finite free module. Finite-dimensionality of \(D_n\) follows at the same time. \(\square\)

Put

\[
C_{p,n}=p^{K_{p,n}}L_{p,n}.
\tag{11.2}
\]

These are again full \(R_p\)-lattices. Lemma 10.1 says that every element of \(C_{p,n}\) is an allowable change to the nth rational deviation of any full local multiplication, without changing any lower rational deviation. The precise approximation map used at degree n is

\[
L_{R,n}\longrightarrow\bigoplus_{p\in S}D_n/C_{p,n}.
\tag{11.3}
\]

It is onto by Lemma 4.2. Thus the arithmetic assertion is about the actual lattices furnished by the topology, rather than an unproved identification of all local correction groups with the same integral lattice.

# 12. The complete degree-by-degree compatibility construction

**Proposition 12.1 — PROVED; confidence 0.98.** One can choose unital multiplications on \(G_R\) and on every \(W_{(p)}\), \(p\in S\), whose induced rational multiplications on G have identical coordinate classes.

**Proof.** For every p choose a local multiplication using the stipulated local step, and rectify it to a strict-unit multiplication \(\mu_p^0\) as in Lemma 10.1. Use these fixed multiplications as the outer operations in all later corrections. Initially put \(\mu_p^{(1)}=\mu_p^0\).

The degree-one rational deviations vanish for every multiplication by Lemma 7.2. Thus the local multiplications already agree in degree one, with deviation \(a_1=0\).

Suppose that for some \(2\le n\le N\), full strict-unit multiplications \(\mu_p^{(n-1)}\) have been chosen whose deviations in degrees less than n agree with fixed classes \(a_i\in L_{R,i}\). Let \(d_{p,n}\in D_n\) be the current nth deviation of \(\mu_p^{(n-1)}\). By (11.3), choose

\[
a_n\in L_{R,n}
\quad\text{with}\quad
a_n-d_{p,n}\in C_{p,n}\quad(p\in S).
\tag{12.1}
\]

For each p, choose a cohomology class

\[
\gamma_{p,n}\in
\widetilde H^n(W_{(p)}\wedge W_{(p)};R_p^{r_n})
\]

whose rational image multiplied by \(p^{K_{p,n}}\) is \(a_n-d_{p,n}\). Such a preimage exists by the definition (11.2). Represent \(\gamma_{p,n}\) by a pointed map c using Hatcher, Theorem 4.57. Use this c in (10.1), with \(f=\mu_p^{(n-1)}\), and define the resulting full multiplication to be \(\mu_p^{(n)}\).

Lemma 10.1 proves three facts needed for this induction: the unit remains strict, all rational coordinates below n stay unchanged, and the nth deviation becomes exactly \(a_n\). The construction is performed separately for every p in the finite set S. If \(D_n=0\), set \(a_n=0\), use zero correction classes, and leave the local multiplications unchanged.

After the finitely many stages n=2 through N, write \(\mu_p=\mu_p^{(N)}\). Their rational deviations are the common tuple \((a_1,\ldots,a_N)\).

For each n choose a representative

\[
\gamma_{R,n}\in\widetilde H^n(G_R\wedge G_R;F_n\otimes R)
\]

whose rational image is \(a_n\); this is possible because \(a_n\in L_{R,n}\). Represent it by \(c_{R,n}:G_R\wedge G_R\to K(F_n\otimes R,n)\). Define the nth coordinate of \(\mu_R:G_R\times G_R\to G_R\) by

\[
(\mu_R)_n(x,y)=x_n+y_n+c_{R,n}(x\wedge y),
\tag{12.2}
\]

using addition in that Eilenberg–Mac Lane factor. The finite product of these coordinate maps is an actual multiplication. The correction is zero on the wedge, so it has strict unit. Its rational deviations are exactly \(a_n\). By the coordinate classification in Section 6, its rationalization and the rationalization of every \(\mu_p\) have the same homotopy class as maps \(G\times G\to G\). \(\square\)

This induction does not assert that every lower-stage H-structure extends over every higher stage. Every local modification is made using a map (9.1) into the full local space. Higher rational coordinates can change, but no higher integral obstruction is created: the modified full map already exists. The lower-coordinate calculation of Section 7 ensures that the later corrections do not undo the earlier matches.

# 13. Gluing the maps and their units

**Proposition 13.1 — PROVED; confidence 0.98.** The multiplications of Proposition 12.1 give an H-structure on W.

**Proof.** Put \(X=W\times W\), \(A=W\vee W\), and let \(\nabla:A\to W\) be the fold. Choose localization maps

\[
\ell_R:W\to G_R,\qquad \ell_p:W\to W_{(p)},
\]

rationalization maps \(\rho_R:G_R\to G\), \(\rho_p:W_{(p)}\to G\), and set \(g=\rho_R\ell_R\). Choose pointed homotopies

\[
\eta_p:g\simeq\rho_p\ell_p.
\tag{13.1}
\]

They are supplied by the localization universal property. We will use their versions with an initial constant half-interval as the comparison paths defining \(\chi:W\to P\) in Proposition 5.2.

Define

\[
f_R=\mu_R(\ell_R\times\ell_R):X\to G_R,
\qquad
f_p=\mu_p(\ell_p\times\ell_p):X\to W_{(p)}.
\]

Strict units give \(f_R|_A=\ell_R\nabla\) and \(f_p|_A=\ell_p\nabla\). Put \(u=\rho_Rf_R\), \(v_p=\rho_pf_p\). The agreement of rational multiplication coordinates in Proposition 12.1 implies that u and \(v_p\) have the same absolute cohomology classes in every coordinate of G. To see the identification explicitly, \(u\) is the pullback of the rationalization of \(\mu_R\) along \(g\times g\); \(v_p\) is the pullback of the rationalization of \(\mu_p\) along \((\rho_p\ell_p)\times(\rho_p\ell_p)\). The homotopy (13.1) identifies these two domain maps, and the rational multiplication classes themselves agree.

The wedge restrictions of u and \(v_p\) are not necessarily equal as maps: they are \(g\nabla\) and \(\rho_p\ell_p\nabla\). We now arrange the required relative homotopy explicitly.

The reverse of \(\eta_p\nabla\) is a homotopy on A from \(v_p|_A\) to \(g\nabla\). By the homotopy extension property, extend it to a pointed homotopy

\[
B_p:X\times I\to G,
\qquad B_p(-,0)=v_p,
\]

with \(B_p|_{A\times I}(a,t)=\eta_p(\nabla a,1-t)\). Let \(\bar v_p=B_p(-,1)\). Then \(\bar v_p|_A=g\nabla=u|_A\). Its absolute cohomology classes equal those of \(v_p\), hence those of u. Lemma 6.2 supplies a pointed homotopy \(C_p:u\simeq\bar v_p\) that is stationary on A.

Concatenate \(C_p\) with the reverse of \(B_p\). This gives a homotopy \(H_p:u\simeq v_p\). On A its first half is the constant map \(g\nabla\), and its second half is \(\eta_p\nabla\). Those are exactly the comparison paths chosen above for \(\chi\nabla\).

In the path-pullback model of (5.2), define

\[
F:X\longrightarrow P,
\qquad
F(x)=\bigl(f_R(x),(f_p(x))_{p\in S},(H_p(x,-))_{p\in S}\bigr).
\tag{13.2}
\]

Each path has the prescribed endpoints, so this is a map into the homotopy pullback. The calculation of its restriction gives

\[
F|_A=\chi\nabla
\]

in this path model, and hence in the CW homotopy category. Proposition 5.2 makes \(\chi\) an equivalence. Choose its pointed inverse in that category and define

\[
\mu=\chi^{-1}F:W\times W\longrightarrow W.
\]

Then \(\mu|_A\simeq\nabla\). This is an H-structure with the required homotopy unit. \(\square\)

**Conclusion of Theorem LC — PROVED; confidence 0.98.** Apply the given local step to the given Taylor operation. The hypotheses of Theorem 1.1 hold; Sections 2–13 construct the multiplication and verify its unit. Therefore W is an H-space. No associativity, homotopy commutativity, or finiteness of its abelian fundamental group was imposed.

# 14. The hypotheses and the compatibility issue

**Proposition 14.1 — PROVED; confidence 0.98.** Finite Postnikov height and finite generation enter the proof at the following distinct places. Infinite finitely generated abelian fundamental groups cause no additional obstruction.

**Proof.** Finite height makes the list of classifying invariants finite, so their orders and the exponents of the homotopy-group torsion have a single finite least common multiple. It makes the number of lifting steps in Lemma 9.1 finite, so the accumulated exponent \(K_{p,n}\) is finite. It makes the matching procedure of Section 12 finite, so it ends with a multiplication on the entire space. There is no passage to an inverse limit of tentative multiplications in that procedure.

Finite generation gives the homology finiteness needed in Lemma 2.1. The resulting coefficient base-change isomorphism turns rational vanishing of an integral classifying invariant into finite-order torsion. It also gives the finite ranks \(r_n\), finite-dimensional correction spaces \(D_n\), and finitely generated full lattices of Lemma 11.1. The finite-dimensional mod-p cohomology used in the power-map argument follows from finite generation of the homotopy of its Eilenberg–Mac Lane source.

The group exact sequence in Lemma 5.1 does not require finite generation. The fracture argument needs simplicity and a finite set S, but does not need finite generation or finite Postnikov height. The relative unit argument does not require either finiteness condition.

If \(\pi_1W=\mathbb Z^r\oplus T\) with T finite, its localizations are exactly \(R^r\oplus(T\otimes R)\), and its rationalization is \(\mathbb Q^r\). Lemma 2.2 proves, including the denominator issue, that these localized fundamental groups continue to act trivially. The degree-one deviation space is zero by Lemma 7.2. Corrections therefore begin at degree two, and their maps have constant projection to \(P_1W_{(p)}\). This accounts for every point at which an infinite fundamental group could have entered the construction. \(\square\)

**Corollary 14.2 — PROVED using May–Ponto (2012), Theorem 9.1.1; confidence 0.98.** For a simple space with finitely generated homotopy groups and finite Postnikov height, the following are equivalent: W admits an H-structure; every \(W_{(p)}\) admits an H-structure.

**Proof.** Localization of a multiplication gives a multiplication on the localization because localization preserves finite products; the unit homotopy localizes as well. This proves the forward direction. For the converse, rationalize one of the local multiplications. It makes \(W_{\mathbb Q}\) an H-space. Its rational homotopy groups are finite-dimensional. May–Ponto, Theorem 9.1.1, identifies a rational H-space of finite type with a product of rational Eilenberg–Mac Lane spaces. Its rational classifying invariants are therefore zero. Theorem 1.1 applies. This corollary is not needed to invoke the given Taylor local step, which already supplies the rational splitting. \(\square\)

**Example 14.3 — PROVED; confidence 0.98.** Rational splitting does not imply uniqueness, even up to change of coordinates, of rational H-structures.

**Proof.** Take \(G=K(\mathbb Q,1)\times K(\mathbb Q,2)\). Let x and y be the fundamental classes of degrees one and two. May–Ponto, Proposition 6.7.2, together with Künneth, gives

\[
H^*(G;\mathbb Q)=\Lambda(x)\otimes\mathbb Q[y].
\]

For \(c\in\mathbb Q\), cohomology representability supplies a multiplication with coordinate classes

\[
\nu_c^*x=x_1+x_2,\qquad
\nu_c^*y=y_1+y_2+c\,x_1x_2.
\]

The correction restricts to zero on the wedge, so the map has a homotopy unit, and Section 6 makes the unit strict if desired. For the interchange \(\tau:G\times G\to G\times G\), graded commutativity gives
\(\tau^*(x_1x_2)=x_2x_1=-x_1x_2\).
Künneth makes \(x_1x_2\) nonzero. If \(c\ne0\), the y-coordinate classes of \(\nu_c\tau\) and \(\nu_c\) differ by \(2c\,x_1x_2\ne0\); these maps are not homotopic. The multiplication \(\nu_0\) is the commutative addition multiplication. Homotopy commutativity is preserved by transport along a homotopy equivalence: conjugate a commutativity homotopy by that equivalence and its inverse. Therefore no change of coordinates identifies \(\nu_c\), \(c\ne0\), with \(\nu_0\). This verifies why rational compatibility must be constructed rather than assumed. \(\square\)

# 15. What can fail without finite Postnikov height

**Counterexample to the auxiliary implication — PROVED by Pan (2001), Proposition 3.5 and Theorems 1.5–1.6; confidence 0.99.** There is a simply connected finite-type space Z such that every \(Z_{(p)}\) is an H-space and every finite Postnikov section of Z is an H-space, but Z is not an H-space.

Pan's example is

\[
Z=\operatorname{hofib}\bigl(\psi:K(\mathbb Z,2)\longrightarrow\Omega S^6\bigr),
\]

where \(\psi\) is an essential special phantom map. Proposition 3.5 supplies existence; Theorem 1.5 proves nonexistence of an H-structure and equality of Mislin genus with \(K(\mathbb Z,2)\times\Omega^2S^6\); Theorem 1.6 proves that every finite Postnikov section is an H-space. These are the precise external results used for this example. Pan uses a strict unit; the homotopy extension argument in Lemma 10.1 turns any homotopy-unit multiplication in the present problem into one with strict unit, so his nonexistence conclusion applies to the present definition.

**Verification of the remaining hypotheses — PROVED; confidence 0.98.** The fiber sequence gives

\[
\pi_1Z=0,\qquad \pi_2Z=\mathbb Z,\qquad
\pi_nZ\cong\pi_{n+2}S^6\quad(n\ge3).
\]

Indeed, the only nonzero homotopy group of \(K(\mathbb Z,2)\) is in degree two; the groups of \(S^6\) in positive degrees below six vanish. Substitution into the fiber long exact sequence gives the displayed formulas in every degree. The homotopy groups of \(S^6\) are finitely generated by May–Ponto, Theorem 4.5.2, applied to this finite simply connected CW complex. Thus Z is simple and has finitely generated homotopy groups. Equality of Mislin genus means equality of the homotopy types at every prime; the comparison space is an H-space using addition on its first factor and loop concatenation on its second. Hence every \(Z_{(p)}\) is an H-space. Its rationalization is an H-space and a rational Eilenberg–Mac Lane product by Theorem 9.1.1 of May–Ponto. If Z had finite Postnikov height, one of the sections in Pan's Theorem 1.6 would be equivalent to Z, contradicting Theorem 1.5. Its height is therefore infinite.

**Scope — PROVED; confidence 1.00.** This example disproves the auxiliary local-to-global implication after dropping finite height. Neither Pan's cited results nor this proof provide a Taylor operation on Z. It is therefore not presented as a counterexample to the statement with the Taylor hypothesis retained. The argument here establishes no conclusion about that stronger statement without finite height.

# 16. An explicit counterexample to the auxiliary implication without finite type

**Proposition 16.1 — PROVED; confidence 0.98.** There is a simple two-type U with

\[
\pi_1U=\mathbb Q^2,\qquad \pi_2U=\mathbb Z,
\]

whose prime localizations and rationalization are Eilenberg–Mac Lane products, although U is not an H-space. The construction and its verification follow.

## 16.1. A nonsplit extension whose coefficient localizations split

Put

\[
B=\prod_{p\text{ prime}}\mathbb Z_{(p)},\qquad
C=B/\Delta\mathbb Z.
\]

The product is over localization rings, not p-adic integer rings; \(\Delta z\) is the constant integral tuple.

**Lemma 16.2 — PROVED; confidence 0.99.** C is uniquely divisible.

**Proof.** If \(n[b]=0\) for a positive integer n, then \(nb=\Delta z\) for an integer z. Every coordinate of b equals \(z/n\). A rational number lying in every \(\mathbb Z_{(p)}\) is integral, because any prime in its reduced denominator would exclude membership in the corresponding local ring. Thus b is an integral constant tuple and \([b]=0\).

For surjectivity of multiplication by n, take \(b=(b_p)\in B\). For each prime dividing n impose

\[
z\equiv-b_p\pmod{p^{v_p(n)}}.
\]

These congruences make sense in the local rings and have integer representatives. The finite integer Chinese remainder theorem proved in Lemma 4.1 supplies z. Then \(d_p=(b_p+z)/n\) belongs to \(\mathbb Z_{(p)}\): the congruence ensures this when p divides n, and otherwise n is a unit. Hence \(d=(d_p)\in B\) and \(n[d]=[b]\). Multiplication by every positive n is therefore bijective. Unique division defines the structure of a rational vector space on C. \(\square\)

Let \(b^*\) have coordinate 1 at p=2 and coordinate 0 at all other primes. Its class c in C is nonzero, because this tuple is not constant. Define \(j:\mathbb Q\to C\) by \(j(q)=qc\), and set

\[
E=\{(b,q)\in B\times\mathbb Q:[b]=j(q)\}.
\]

Projection to q gives the exact sequence

\[
0\longrightarrow\mathbb Z\xrightarrow{i}E\xrightarrow{\pi}\mathbb Q
\longrightarrow0,
\qquad i(z)=(\Delta z,0).
\tag{16.1}
\]

Its kernel is the displayed copy of \(\mathbb Z\); its surjectivity follows from surjectivity of \(B\to C\).

**Lemma 16.3 — PROVED; confidence 0.99.** The extension (16.1) is nonsplit, but its pushout along \(\mathbb Z\to\mathbb Z_{(p)}\) splits for every p, and its rational pushout splits.

**Proof.** Every homomorphism \(h:\mathbb Q\to\mathbb Z_{(p)}\) is zero. For any q, divisibility of \(\mathbb Q\) gives \(h(q)\in p^a\mathbb Z_{(p)}\) for every a. The intersection of these subgroups is zero, since a nonzero rational number has a finite p-adic valuation. Coordinate projection therefore shows \(\operatorname{Hom}(\mathbb Q,B)=0\). A section of (16.1) would have the form \(q\mapsto(h(q),q)\) with \([h(q)]=j(q)\). At q=1 this contradicts \(h=0\) and \(c\ne0\).

For a prime p, let \(\rho_p:E\to\mathbb Z_{(p)}\) send \((b,q)\) to \(b_p\). Its restriction to the kernel is the coefficient inclusion. The pushout middle group is

\[
E_p=(E\oplus\mathbb Z_{(p)})/\{(i(z),-z):z\in\mathbb Z\}.
\]

The map \(r_p([e,a])=\rho_p(e)+a\) is well-defined and retracts the coefficient-group inclusion. The projection \(E_p\to\mathbb Q\) restricts to an isomorphism on \(\ker r_p\). Surjectivity follows by taking any lift and subtracting the kernel element given by its retraction. Injectivity follows because a coefficient-group element with zero retraction is zero. This is a section, so the pushout splits. For the rational pushout, use \(E\xrightarrow{\rho_2}\mathbb Z_{(2)}\hookrightarrow\mathbb Q\) and define \(r([e,a])=\rho_2(e)+a\). This is well-defined on the pushout because it vanishes on each relation \((i(z),-z)\), and its restriction to the coefficient copy of \(\mathbb Q\) is the identity. For any element of the quotient \(\mathbb Q\), take a lift and subtract its value under r as a coefficient-group element. This produces a lift in \(\ker r\). An element in the kernel of the quotient map and in \(\ker r\) is a coefficient-group element with zero value under r, so is zero. Hence \(\ker r\) maps isomorphically to the quotient, giving a rational section. \(\square\)

Write \(\xi\in\operatorname{Ext}^1_{\mathbb Z}(\mathbb Q,\mathbb Z)\) for this extension class. Here is an explicit check of the extension-class interpretation and its naturality. Let \(F=\bigoplus_{n\ge1}\mathbb Ze_n\), with \(e_n\mapsto1/n!\). Its kernel K is free on \(u_n=e_n-(n+1)e_{n+1}\). Any finite sum supported through \(e_m\) reduces modulo the u's to a multiple of \(e_m\); if its rational image is zero, that multiple is zero. This proves generation of the kernel. A finite relation among the u's has a largest nonzero index r, and its coefficient on \(e_{r+1}\) is \(-(r+1)\) times that nonzero coefficient, a contradiction. This proves independence.

Choose lifts to an extension of the images of all the \(e_n\). The resulting map F into its middle group restricts to a map \(K\to M\), where M is its kernel. Its class in

\[
\operatorname{coker}\bigl(\operatorname{Hom}(F,M)\to\operatorname{Hom}(K,M)\bigr)
=\operatorname{Ext}^1(\mathbb Q,M)
\]

vanishes precisely when the lift can be adjusted by an M-valued map on F so as to vanish on K; that is precisely when a section from \(\mathbb Q\) exists. Applying a coefficient map to the kernel applies that map to this representative, which is the naturality under pushout. Lemma 16.3 therefore proves

\[
\xi\ne0,\qquad
\xi_{(p)}=0\text{ in }\operatorname{Ext}^1(\mathbb Q,\mathbb Z_{(p)}),
\qquad
\xi_{\mathbb Q}=0\text{ in }\operatorname{Ext}^1(\mathbb Q,\mathbb Q).
\tag{16.2}
\]

## 16.2. The classifying map

**Lemma 16.4 — PROVED; confidence 0.98.** With constant coefficients M,

\[
H^3(K(\mathbb Q,1);\mathbb Z)=0,
\qquad
H^3(K(\mathbb Q^2,1);M)\cong\operatorname{Ext}^1(\mathbb Q,M),
\tag{16.3}
\]

and the second isomorphism is natural in M.

**Proof.** For r=1 and r=2, form the mapping telescope

\[
T^r\xrightarrow{[2]}T^r\xrightarrow{[3]}T^r\xrightarrow{[4]}\cdots,
\]

where \([m]\) multiplies all circle coordinates by m. A compact map, or a compactly parametrized homotopy, into the telescope has bounded height. It lies in a finite initial subtelescope, which retracts onto its final torus. Thus homotopy groups are the direct limits of the homotopy groups of the tori: the fundamental group is \(\mathbb Q^r\) and every higher homotopy group is zero. These are models of \(K(\mathbb Q^r,1)\).

A finite singular chain has bounded height as well. Applying this to cycles and to chains witnessing boundaries shows that homology is the direct limit of the torus homologies. The circle has integral homology \(\mathbb Z\) in degrees zero and one. The two-torus has integral homology \(\mathbb Z,\mathbb Z^2,\mathbb Z\) in degrees zero, one and two: its CW chain complex has one zero-cell, two one-cells and one two-cell with zero differentials. Multiplication by m acts as multiplication by m in degree one and by its covering degree \(m^2\) in degree two. The products of the successive integers have unbounded valuation at every prime, as do their squares. The relevant colimits on \(\mathbb Z\) are therefore \(\mathbb Q\). Consequently

\[
\begin{array}{c|ccc}
&H_1&H_2&H_i\ (i>2)\\\hline
K(\mathbb Q,1)&\mathbb Q&0&0\\
K(\mathbb Q^2,1)&\mathbb Q^2&\mathbb Q&0.
\end{array}
\]

The cochain proof of the universal coefficient sequence (2.2) required no finite generation for the exact sequence itself; finite generation was used only for its additional finiteness and base-change conclusions. Apply that exact sequence here with R equal to \(\mathbb Z\). The Hom term in degree three vanishes because \(H_3=0\), so the natural Ext injection is an isomorphism. It is zero in the first row and gives (16.3) in the second. \(\square\)

Let \(X=K(\mathbb Q^2,1)\), and let \(k\in H^3(X;\mathbb Z)\) correspond to \(\xi\). Represent k by a pointed map

\[
k:X\longrightarrow K(\mathbb Z,3).
\]

Define U to be a CW model of its homotopy fiber, with projection \(q:U\to X\). In a path model its points are \((x,\gamma)\) with \(\gamma(0)=k(x)\), \(\gamma(1)=0\). The defining fiber sequence is

\[
K(\mathbb Z,2)\longrightarrow U\xrightarrow q X\xrightarrow k K(\mathbb Z,3).
\tag{16.4}
\]

**Lemma 16.5 — PROVED; confidence 0.98.** U is a simple two-type with the homotopy groups in Proposition 16.1. For every prime p,

\[
U_{(p)}\simeq K(\mathbb Q^2,1)\times K(\mathbb Z_{(p)},2),
\qquad
U_{\mathbb Q}\simeq K(\mathbb Q^2,1)\times K(\mathbb Q,2).
\tag{16.5}
\]

**Proof.** The long exact sequence of (16.4) makes U connected and gives \(\pi_1U=\mathbb Q^2\), \(\pi_2U=\mathbb Z\), and all other positive homotopy groups zero. The principal-fibration criterion of May–Ponto, Lemma 3.4.2, gives the trivial fundamental-group action on \(\pi_2U\). Its fundamental group is abelian, so U is simple.

All spaces in the homotopy-fiber diagram are nilpotent and the fiber is connected. May–Ponto, Proposition 6.2.5, identifies its localization with the homotopy fiber of the localized map. The base X is already p-local and rational, because its only homotopy group is a rational vector space. Localization of the target changes its sole homotopy group to \(\mathbb Z_{(p)}\), or to \(\mathbb Q\). Thus the localized classifying maps represent the coefficient images of k. The naturality in (16.3) and (16.2) makes every such image zero. The explicit path concatenation equivalence for a null classifying map given in Section 3 therefore proves (16.5). Coordinate addition supplies an H-structure on each product. \(\square\)

## 16.3. Nonexistence of an integral multiplication

**Lemma 16.6 — PROVED; confidence 0.99.** U is not an H-space.

**Proof.** Put \(Y=K(\mathbb Q,1)\). Let \(a_1,a_2:Y\to X\) induce the two coordinate inclusions on fundamental groups. Lemma 16.4 makes \(ka_i\) nullhomotopic. Choose pointed nullhomotopies; the path model (16.4) gives lifts \(\ell_i:Y\to U\) with \(q\ell_i=a_i\).

Suppose \(\mu:U\times U\to U\) had a homotopy unit. Its homomorphism on fundamental groups restricts to the identity on each factor. Since \(\pi_1U=\mathbb Q^2\) is abelian, the homomorphism is addition: \((a,b)=(a,0)+(0,b)\) maps to a+b.

It follows that

\[
q\mu(\ell_1\times\ell_2):Y\times Y\longrightarrow X
\]

induces the identity identification of \(\mathbb Q^2\) with \(\pi_1X\). Maps to \(K(A,1)\), for abelian A, are classified by their fundamental-group homomorphisms: representability gives \([Z,K(A,1)]=H^1(Z;A)\), and (2.2) gives \(H^1(Z;A)=\operatorname{Hom}(H_1Z,A)\) because \(H_0Z=\mathbb Z\) has zero Ext. In the present case all fundamental groups are already abelian.

Define \(b:X\to Y\times Y\) by the two coordinate homomorphisms, using this classification in each target factor. The displayed composite after b induces the identity on \(\pi_1X\), so the same classification makes it homotopic to \(\mathrm{id}_X\). Hence

\[
s=\mu(\ell_1\times\ell_2)b:X\longrightarrow U
\]

is a homotopy section of q. But kq has the nullhomotopy supplied by the defining paths in the homotopy fiber. Therefore \(k\simeq kqs\simeq *\), contradicting \(k\ne0\). This proves the lemma and Proposition 16.1. \(\square\)

**Scope — PROVED; confidence 1.00.** This example has finite Postnikov height two; finite generation fails at \(\pi_1U=\mathbb Q^2\). It disproves the auxiliary local-to-global assertion without finite type. No Taylor operation on U has been verified here, so it is not asserted to disprove the Taylor theorem with finite type omitted. The proof of Theorem LC and these two examples settle the stated finite-type finite-height theorem and the limitations of this local-to-global route, without claiming a result about Taylor spaces beyond those hypotheses.

# 17. Precise references

**Status — PROVED by the cited results; confidence 0.99 in the identifications and numbering.** Only the following external results are used. The principal gluing argument, its arithmetic approximation, its torsion-killing correction maps, and its relative unit handling were proved above.

1. **J. P. May and K. Ponto (2012), _More Concise Algebraic Topology: Localization, Completion, and Model Categories_, University of Chicago Press.** Corollary 2.2.3 (homotopy-pullback exact sequence); Lemma 3.4.2 (principal Eilenberg–Mac Lane fibrations and trivial action); Theorem 4.5.2 (nilpotent finite-type criteria); Theorems 6.1.2 and 6.1.4 (nilpotent localization and localized finite-type criteria); Propositions 6.2.3 and 6.2.5 (products and connected homotopy pullbacks under localization); Proposition 6.7.2 (rational Eilenberg–Mac Lane cohomology); Theorem 9.1.1 (rational H-space splitting). Theorem 9.4.5 describes compatible H-space mixing and is relevant context, not a substitute for the compatibility proof above. [Author PDF](https://www.math.uchicago.edu/~may/BOOKS/KateBookFinal.pdf).

2. **Allen Hatcher (2002), _Algebraic Topology_, Cambridge University Press; cited Cornell online edition.** Proposition 0.16 (homotopy extension for CW pairs); Theorem 3.15 (cohomological Künneth under the finite-free hypothesis); Theorem 4.5 (Whitehead); Theorem 4.8 (cellular approximation); Theorem 4.32 (Hurewicz); Proposition 4.13 (CW approximation); Example 4.16 (Postnikov sections by cell attachment); Theorem 4.57 (cohomology representability). The online Künneth numbering is 3.15, rather than 3.16 in some other copies. [Author PDF](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

3. **Jianzhong Pan (2001 preprint), “Having the H-space structure is not a generic property,” arXiv:math/0106257.** Proposition 3.5 (existence of the essential special phantom used); Theorem 1.5 (non-H-space in the same Mislin genus as an H-space); Theorem 1.6 (all finite Postnikov sections of this example are H-spaces). [Primary preprint](https://arxiv.org/abs/math/0106257).

4. **J. Peter May (1967), _Simplicial Objects in Algebraic Topology_.** Theorem 14.1 (CW realization); Corollary 14.6 (realization of a countable simplicial abelian group is a topological abelian group); Theorems 16.1 and 16.6 (comparison of simplicial and topological homotopy); Theorem 23.9 (the explicit cocycle model of an Eilenberg–Mac Lane complex). [Primary book scan](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/May-simp-ocr.pdf).

The Mislin-genus example shows why local H-structures cannot be mixed without controlling global compatibility. This is the compatibility issue in Zabrodsky mixing. Theorem 9.4.5 of May–Ponto is a precise formulation of compatible mixing in its stated finite-homology setting; its compatibility hypotheses are not inferred from a bare rational equivalence here. Sections 8–13 provide the compatibility argument appropriate to the finite Postnikov setting.

# 18. Adversarial self-audit

**Audit — the proof's mathematical claims are PROVED above; confidence 0.98.** The step most likely to conceal a failure is Lemma 9.1, specifically the claim that multiplying the source by a sufficiently high power of p removes all higher obstructions while retaining a nonzero, controllable nth rational coordinate. A lower-stage correction alone would not suffice: it could create an obstruction at the next stage.

The proof addresses this by constructing the map into the entire finite local tower before using it to alter any multiplication. Each actual lifting obstruction is a cohomology class on the fixed source \(K(\mathbb Z_{(p)}^{r_n},n)\); coefficient base change makes that class p-power torsion. Lemmas 8.1–8.3 kill it by a finite iterate of the source power map. The explicit path-fiber lift then exists. Only finitely many stages occur, so the product of all required p-powers is finite and nonzero rationally. This is why the attainable corrections contain a full lattice, rather than merely an unproved collection of rational directions.

If that torsion-killing statement failed, the correction lattice in Section 11 could have smaller rational span, the Chinese remainder map used in Section 12 would no longer solve the compatibility problem, and the proof would stop there. The mod-p ideal calculation, the coefficient exact sequences, and the explicit finite lifting induction are included precisely to make that possible failure independently checkable.
