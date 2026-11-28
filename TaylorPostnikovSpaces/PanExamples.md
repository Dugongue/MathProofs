# No normalized Taylor operation on Pan's special-phantom H-space counterexamples

**PROVED — for every \(m\geq1\), every normalized operation on Pan's space \(Z=\operatorname{hofib}(\psi:K(\mathbb Z,2m)\to\Omega S^{4m+2})\) induces a coordinate projection on \(\pi_{2m}Z\cong\mathbb Z\). Hence \(Z\) admits no normalized Taylor operation. Confidence: 0.98.**

This proof imports three precisely numbered results from Pan (2001), and proves the remaining mapping-space, cofiber, and operation arguments below. It excludes Pan's entire displayed family as counterexamples to normalized Taylor \(\Rightarrow\) H. It does not establish that implication for arbitrary spaces of infinite Postnikov height.

## 1. Definitions and exact imported results

All maps and homotopies are pointed. Let \(m\geq1\), and put
\[
d=2m,\qquad X=K(\mathbb Z,d),\qquad Y=\Omega S^{2d+2}.
\]
The space \(X\) has its additive Eilenberg–Mac Lane multiplication \(\mu_X\); the space \(Y\) has loop concatenation. Let
\[
\psi:X\longrightarrow Y
\]
be an essential special phantom map, let \(Z=\operatorname{hofib}(\psi)\), and let \(q:Z\to X\) be the fiber projection.

Here “essential” means not pointed nullhomotopic. A phantom map is a map whose restriction to every finite skeleton is nullhomotopic. The adjective “special” means that its composites into every prime localization of the target are nullhomotopic; this is Pan's definition in Section 2, following Theorem 2.8. We use the adjective only to invoke Proposition 3.5.

**PROVED by cited results; confidence 0.99.** The three inputs from Jianzhong Pan (2001), *Having the H-space structure is not a generic property*, arXiv:math/0106257v1, are:

1. **Theorem 2.8:** For the finite-type finite Postnikov space \(X^2=K(\mathbb Z^2,d)\) and \(Y=\Omega S^{2d+2}\), precomposition by rationalization induces a bijection
   \[
   r^*:[(X^2)_{\mathbb Q},Y]\longrightarrow[X^2,Y].
   \tag{1.1}
   \]
   This is the specialization with \(i=1\), \(j=0\), finite complex \(K=S^{2d+2}\), and source a space with finitely many nonzero homotopy groups.
2. **Theorem 3.3:** No essential map \(X\to Y\) is an H-map for these multiplications.
3. **Proposition 3.5:** Essential special phantom maps of this form exist, and, for each such map,
   \[
   (q\wedge q)^*:[X\wedge X,Y]\longrightarrow[Z\wedge Z,Y]
   \tag{1.2}
   \]
   is injective.

Pan's paper works with simply connected finite-type CW complexes. These hypotheses hold for the Eilenberg–Mac Lane sources used in (1.1). Finite type of \(K(\mathbb Z^2,d)\), in the homotopy and CW senses needed here, also follows from May–Ponto (2012), Theorem 4.5.2.

**Definition.** An operation \(t:Z^r\to Z\), with \(r\geq1\), is normalized when \(t\Delta_r\simeq\operatorname{id}_Z\). It is a normalized Taylor operation if, for each input \(i\), two words \(\alpha,\beta\in\{x,y\}^r\) differing at that input give homotopic maps \(td_\alpha\simeq td_\beta:Z^2\to Z\), where each \(d_\alpha\) selects the indicated projection in every coordinate.

**PROVED clarification, confidence 1.00.** The normalization is part of the hypothesis. Omitting it would allow the constant map to satisfy the displayed variable-identification identities on every space.

## 2. Quotient pullback is injective for loop-space targets

The following lemma supplies the exact injectivity needed twice later. Its proof includes the suspension retraction and the cofiber-kernel calculation.

**Lemma 2.1 — PROVED; confidence 0.99.** Let \(S,T\) be pointed CW complexes, and let \(L=\Omega M\) be a loop space. Write
\[
B=S\times T,\qquad A=S\vee T,\qquad C=B/A=S\wedge T,
\]
and let \(\Lambda:B\to C\) be the quotient. Then
\[
\Lambda^*:[C,L]\longrightarrow[B,L]
\tag{2.1}
\]
is injective.

**Proof.** Products are given the compactly generated CW product topology, and the wedge inclusion \(i:A\to B\) is a cofibration. Equivalently, one can use cellular models for this pair; the assertion is invariant under pointed homotopy equivalence.

For a pointed space \(P\), use the reduced suspension model
\[
\Sigma P=(P\times[0,1])/
(P\times\{0,1\}\cup\{*\}\times[0,1]).
\]
Let \(R:\Sigma B\to\Sigma A=\Sigma S\vee\Sigma T\) be
\[
R([(s,t),u])=
\begin{cases}
[s,2u]\text{ in }\Sigma S,&0\leq u\leq1/2,\\
[t,2u-1]\text{ in }\Sigma T,&1/2\leq u\leq1.
\end{cases}
\tag{2.2}
\]
The two formulas agree at the midpoint because both suspension endpoints are the basepoint. They also respect every collapsed subspace, so the formula is continuous and pointed.

On the summand \(\Sigma S\), the composite \(R\Sigma i\) is represented by the suspension-coordinate map \(u\mapsto\min(2u,1)\). It is homotopic to the identity by the functions
\[
u\longmapsto\min\left(\frac{u}{1-v/2},1\right),\qquad0\leq v\leq1.
\]
On the summand \(\Sigma T\), the composite is represented by \(u\mapsto\max(2u-1,0)\), homotopic to the identity by
\[
u\longmapsto\max\left(\frac{u-v/2}{1-v/2},0\right).
\]
Both homotopies preserve the basepoint, so they combine on the wedge. Thus
\[
R\Sigma i\simeq\operatorname{id}_{\Sigma A}.
\tag{2.3}
\]

Consider the reduced mapping cone \(C_i=B\cup_i CA\). Collapsing its contractible cone subcomplex \(CA\) identifies it with \(B/A\), and the resulting map
\[
e:C_i\longrightarrow C
\]
is a pointed homotopy equivalence by Hatcher (2002), Proposition 0.17. It restricts on \(B\) to \(\Lambda\). Let \(\delta:C_i\to\Sigma A\) collapse \(B\). The composite \(\Sigma i\,\delta\) is nullhomotopic by the following explicit homotopy. At parameter \(v\), send \(b\in B\) to \([b,v]\in\Sigma B\), and send the cone point represented by \((a,u)\), with \(u=0\) attached to \(i(a)\), to
\[
[i(a),v+(1-v)u]\in\Sigma B.
\]
The formulas agree when \(u=0\); at \(u=1\) and on the basepoint they give the basepoint. At \(v=0\) they represent \(\Sigma i\,\delta\), and at \(v=1\) they are constant. Combining this nullhomotopy with (2.3) proves
\[
\delta\simeq R\Sigma i\,\delta\simeq *.
\tag{2.4}
\]

Suppose \(f:C_i\to L\) restricts to a nullhomotopic map on \(B\). Choose a pointed nullhomotopy of \(f|_B\). The homotopy extension property for the CW pair \((C_i,B)\), Hatcher (2002), Proposition 0.16, extends it to a homotopy of \(f\). Its terminal map is zero on \(B\) and therefore factors through \(C_i/B=\Sigma A\). Consequently \([f]=[h\delta]\) for some \(h:\Sigma A\to L\), and (2.4) implies \([f]=0\). Transporting this assertion across \(e\) proves that the kernel of (2.1) is trivial.

Finally, for every pointed domain \(P\), \([P,\Omega M]\) is a group: multiplication is pointwise loop concatenation, inversion is loop reversal, and the identity is the constant-loop map. Reparametrization gives associativity on homotopy classes, and cancellation of a loop followed by its reverse gives the inverse identities. Precomposition preserves this group structure. Thus (2.1) is a group homomorphism with trivial kernel and is injective. \(\square\)

## 3. Nonzero scalar maps preserve essential smash classes

Let \([a]:X\to X\) denote the Eilenberg–Mac Lane map inducing multiplication by the integer \(a\) on \(\pi_dX=\mathbb Z\). It can be constructed as the map represented by \(a\iota\), where \(\iota\in H^d(X;\mathbb Z)\) represents the identity.

**Lemma 3.1 — PROVED; confidence 0.99.** If \(a,b\) are nonzero integers, then
\[
([a]\wedge[b])^*:[X\wedge X,Y]\longrightarrow[X\wedge X,Y]
\tag{3.1}
\]
is injective.

**Proof.** Put \(A_{a,b}=[a]\times[b]:X^2\to X^2\). Its rationalization induces \(\operatorname{diag}(a,b)\) on the sole nonzero homotopy group \(\mathbb Q^2\), in degree \(d\). Hence \((A_{a,b})_{\mathbb Q}\) is a pointed homotopy equivalence. Here localization of homotopy groups is May–Ponto (2012), Theorem 6.1.2, and the conclusion from isomorphisms of homotopy groups is Hatcher (2002), Theorem 4.5, applied to CW models.

The naturality square for rationalization gives
\[
r^*(A_{a,b})_{\mathbb Q}^*=A_{a,b}^*r^*
\]
on homotopy classes of maps into \(Y\). The map \(r^*\) is bijective by the imported specialization (1.1) of Pan's Theorem 2.8, and \((A_{a,b})_{\mathbb Q}^*\) is bijective because its underlying map is an equivalence. Thus \(A_{a,b}^*:[X^2,Y]\to[X^2,Y]\) is injective.

The quotient \(\Lambda_X:X^2\to X\wedge X\) satisfies
\[
([a]\wedge[b])\Lambda_X=\Lambda_XA_{a,b}.
\]
If two classes become equal after precomposition by \([a]\wedge[b]\), their images under \(\Lambda_X^*\) become equal after precomposition by \(A_{a,b}\). The just-proved injectivity makes those images equal, and Lemma 2.1 then makes the original classes equal. This proves (3.1). \(\square\)

No formula identifying \(\psi[a]\) with \(a^2\psi\), and no claimed natural identification of phantom groups with a real vector space, is used in this proof.

## 4. The H-deviation, with its group law and order fixed

In the group \([X^2,Y]\), put
\[
F=\psi\mu_X,\qquad
G=(\psi\operatorname{pr}_1)\cdot(\psi\operatorname{pr}_2),\qquad
\mathcal D=[F]\,[G]^{-1}.
\tag{4.1}
\]
The dot denotes pointwise loop concatenation, in the displayed order. Thus the inverse in (4.1) is the inverse of the entire product \(G\). Equivalently, \(\mathcal D[G]=[F]\). No commutativity of these mapping groups is assumed.

The two wedge restrictions of \(F\) and \(G\) are homotopic by the respective units. Therefore \(\mathcal D\) restricts to zero on \(X\vee X\). Represent \(\mathcal D\) by a map and use the homotopy extension property to make this representative constant on the wedge; it then factors through \(X\wedge X\). Lemma 2.1 makes the resulting class unique. Denote it by
\[
D\in[X\wedge X,Y],\qquad\Lambda_X^*D=\mathcal D.
\tag{4.2}
\]
This is the H-deviation class with the convention \(D\cdot G=F\), matching Pan's division convention in Definitions 2.3 and Proposition 2.1.

**Lemma 4.1 — PROVED by construction and Pan's Theorem 3.3; confidence 0.99.** The class \(D\) is nonzero.

**Proof.** If \(D=0\), then (4.2) gives \([F]=[G]\). This is precisely the H-map identity for \(\psi\). Pan's Theorem 3.3 says an essential \(\psi:X\to Y\) cannot satisfy that identity. \(\square\)

## 5. A two-input obstruction

First compute the lowest homotopy group used below.

**Lemma 5.1 — PROVED; confidence 0.99.** The space \(Z\) is \((d-1)\)-connected, \(\pi_dZ\cong\mathbb Z\), and \(q_*\) identifies this group with \(\pi_dX\). For every finite \(r\), maps \(Z^r\to X\) are classified by their homomorphisms \(\pi_d(Z^r)=\mathbb Z^r\to\mathbb Z\).

**Proof.** The homotopy fiber of \(q\) is \(\Omega Y=\Omega^2S^{2d+2}\). Its homotopy groups in degrees \(i<2d\) are
\[
\pi_i(\Omega^2S^{2d+2})=\pi_{i+2}(S^{2d+2})=0,
\]
because \(i+2<2d+2\). The homotopy-fiber exact sequence, May–Ponto (2012), Corollary 2.2.3, consequently identifies \(\pi_iZ\) with \(\pi_iX\) for \(i\leq d\). This proves the connectivity and group assertions.

The product \(Z^r\) has the same connectivity and has \(\pi_d(Z^r)=\mathbb Z^r\). The Hurewicz theorem, Hatcher (2002), Theorem 4.32, gives \(H_i(Z^r;\mathbb Z)=0\) for \(0<i<d\) and \(H_d(Z^r;\mathbb Z)\cong\pi_d(Z^r)\). In particular \(H_{d-1}=0\). The natural cohomology universal coefficient theorem, Hatcher (2002), Theorem 3.2, therefore gives
\[
H^d(Z^r;\mathbb Z)\cong\operatorname{Hom}(\pi_d(Z^r),\mathbb Z).
\]
Representability by \(X=K(\mathbb Z,d)\), May–Ponto (2012), Equation (3.4.1), identifies this with \([Z^r,X]\). All identifications are natural, proving the classification claimed. \(\square\)

**Lemma 5.2 — PROVED; confidence 0.98.** If \(f:Z^2\to Z\) induces
\[
f_*:\mathbb Z^2\longrightarrow\mathbb Z,\qquad
(u,v)\longmapsto au+bv
\]
on \(\pi_d\), then \(ab=0\).

**Proof.** Define the coordinate restrictions \(f_1(z)=f(z,*)\) and \(f_2(z)=f(*,z)\). Lemma 5.1 gives pointed homotopies
\[
qf_1\simeq[a]q,\qquad qf_2\simeq[b]q,
\tag{5.1}
\]
and
\[
qf\simeq\mu_X\bigl([a]q\operatorname{pr}_1,[b]q\operatorname{pr}_2\bigr).
\tag{5.2}
\]
The composite \(\psi q\) is nullhomotopic by the path defining the homotopy fiber. Composing (5.1) and (5.2) with \(\psi\) yields
\[
\psi[a]q\simeq *,\qquad \psi[b]q\simeq *,\qquad
\psi\mu_X\bigl([a]q\operatorname{pr}_1,[b]q\operatorname{pr}_2\bigr)\simeq *.
\tag{5.3}
\]
The first two nullhomotopies come from the actual restrictions \(f_1,f_2\). In particular, the argument assumes no existence of arbitrary power self-maps on \(Z\).

Pull back (4.2) along \(([a]q)\times([b]q):Z^2\to X^2\). Every factor in (4.1) becomes the identity of \([Z^2,Y]\) by (5.3). Consequently
\[
\Lambda_Z^*(q\wedge q)^*([a]\wedge[b])^*D=0
\quad\text{in }[Z^2,Y].
\]
Lemma 2.1 makes \(\Lambda_Z^*\) injective, and Pan's Proposition 3.5 makes \((q\wedge q)^*\) injective. It follows that
\[
([a]\wedge[b])^*D=0.
\tag{5.4}
\]
If \(a\ne0\) and \(b\ne0\), Lemma 3.1 makes the remaining pullback injective, and (5.4) would imply \(D=0\), contradicting Lemma 4.1. Thus at least one of \(a,b\) is zero. \(\square\)

## 6. Every normalized operation is a projection on the bottom homotopy group

**Theorem 6.1 — PROVED; confidence 0.98.** For every \(r\geq1\), every normalized map \(t:Z^r\to Z\) induces a coordinate projection on \(\pi_d(Z^r)=\mathbb Z^r\). Therefore \(Z\) has no normalized Taylor operation.

**Proof.** Since \(\pi_dZ=\mathbb Z\), there are integers \(a_1,\ldots,a_r\) such that
\[
t_*(u_1,\ldots,u_r)=\sum_{i=1}^r a_i u_i.
\]
Normalization implies
\[
\sum_{i=1}^r a_i=1.
\tag{6.1}
\]
For distinct \(i,j\), insert two variables in these positions and basepoints in all others. The resulting map \(t_{ij}:Z^2\to Z\) induces the coefficients \(a_i,a_j\). Lemma 5.2 gives \(a_ia_j=0\).

Thus at most one coefficient is nonzero. Equation (6.1) says that exactly one is nonzero and that its value is one. This proves the projection assertion, including the unary case.

Suppose \(t\) also satisfied the Taylor identities. Let \(i\) be the selected coordinate. The identity required at that coordinate gives words \(\alpha,\beta\) with \(\alpha_i\ne\beta_i\) and \(td_\alpha\simeq td_\beta\). On \(\pi_d(Z^2)=\mathbb Z^2\), these maps induce its two different coordinate projections, because \(t_*\) selects precisely coordinate \(i\). The projections differ on \((1,0)\), whereas homotopic maps induce equal homomorphisms. This is a contradiction. \(\square\)

## 7. Consequences and limits

**PROVED consequence; confidence 0.98.** Pan's essential special-phantom fibers, for every \(m\geq1\), fail the normalized Taylor hypothesis. They therefore cannot be used as counterexamples to normalized Taylor \(\Rightarrow\) H, although they remain counterexamples to the auxiliary assertion that local H-structures alone force a global H-structure when finite Postnikov height is omitted.

**PROVED statement of scope; confidence 1.00.** No conclusion about arbitrary infinite-height spaces follows from excluding this family. The argument uses the specific injectivity in Pan's Proposition 3.5 and the rational-source mapping theorem in his Theorem 2.8. Neither statement has been asserted for arbitrary spaces.

## 8. Precise references

- Jianzhong Pan (2001), *Having the H-space structure is not a generic property*, arXiv:math/0106257v1, submitted 29 June 2001. Theorem 2.8, Theorem 3.3, and Proposition 3.5 are the imported phantom-map results. Definitions 2.3 and Proposition 2.1 identify the H-deviation convention. <https://arxiv.org/pdf/math/0106257>.
- Allen Hatcher (2002), *Algebraic Topology*: Proposition 0.16, homotopy extension for CW pairs; Proposition 0.17, collapsing a contractible cofibration; Theorem 3.2, natural cohomology UCT; Theorem 4.5, Whitehead's theorem; Theorem 4.32, Hurewicz's theorem. Author PDFs: <https://pi.math.cornell.edu/~hatcher/AT/ATch0.pdf>, <https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf>, <https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf>.
- J. P. May and K. Ponto (2012), *More Concise Algebraic Topology: Localization, Completion, and Model Categories*: Corollary 2.2.3, homotopy-pullback exact sequence; Equation (3.4.1), cohomology representability; Theorem 4.5.2, equivalent finite-type conditions for nilpotent spaces; Theorem 6.1.2, localization of nilpotent homotopy groups and its universal property. Author PDF: <https://www.math.uchicago.edu/~may/BOOKS/KateBookFinal.pdf>.

## 9. Adversarial self-audit

**PROVED assessment; confidence 0.98.** The most delicate imported application is (1.1): Pan's Theorem 2.8 must be applied to the product \(K(\mathbb Z,2m)^2\), not to its smash. The product is a finite-type space with one nonzero homotopy group, so it lies exactly within the theorem's stated source class. The smash need not lie in that source class. Lemma 3.1 deliberately passes to the product through the independently proved injection \(\Lambda_X^*\); it never applies Pan's theorem directly to the smash. If the rationalization pullback in (1.1) were unavailable, essentiality of the deviation after arbitrary nonzero integer powers would no longer follow from this argument.
