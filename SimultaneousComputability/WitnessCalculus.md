# Witness transport and arithmetic descent

A witness diagram records which witnesses appear after extension, which become identified, and how automorphisms act. This note classifies a class of such diagrams, realizes their witnesses in smooth arithmetic families, and identifies when an existence reduction supplies witness transport.

## 1. A finite Galois probe category

Fix a finite Galois extension $L/K$ of number fields with group $G$. Use all intermediate fields as probes and all $K$-embeddings as arrows. The anchor is $L$, and $G_E=\operatorname{Gal}(L/E)$. A witness diagram $W$ is a covariant functor from these probes to sets, often given uniformly over an input $e$. In the effective setting the sets have uniformly c.e. domains of natural-number codes with decidable equality, and transport is computable on these domains.

If $S$ is a $G$-set, put $C(S)(E)=S^{G_E}$. For an embedding $\sigma:E\to F$ choose $g\in G$ extending $\sigma$. Transport sends $s$ to $gs$. This does not depend on the extension because two choices differ on the right by an element of $G_E$, and the target is fixed by $G_F$ since $g^{-1}G_Fg\subseteq G_E$. Composition follows by multiplying extensions. For a c.e. $G$-set with computable action, enumerate $S^{G_E}$ by enumerating $S$ and testing the finitely many action values of $G_E$.

**Theorem 1 (anchor adjunctions).** Evaluation $W\mapsto W(L)$ has the fully faithful right adjoint $C$. Its unit $\eta_E:W(E)\to W(L)^{G_E}$ is induced by inclusion into $L$. Evaluation also has a fully faithful left adjoint placing a given $G$-set at $L$ and the empty set at every proper field.

A natural map $W\to C(S)$ gives an equivariant map $W(L)\to S$. Conversely compose each $\eta_E$ with this equivariant map and restrict its values to $S^{G_E}$. Naturality follows by extending each embedding to $G$. The two constructions are inverse by naturality along inclusions into $L$. The left adjoint works because no proper probe receives an embedding from $L$. These are explicit Kan extension formulas.

Call a diagram **complete for descent** when every $\eta_E$ is a bijection. Failure of injectivity records witnesses that become identified at $L$. Failure of surjectivity records fixed witnesses at $L$ that do not descend. The inverse of a bijective $\eta_E$ in an effective diagram is computable on its image by enumeration and comparison of codes. Hence the adjunctions and reflection apply to effective diagrams as well.

Field points of an affine system over $K$ and integral points of a model over $\mathcal O_K$ are complete for descent. Fixed tuples over $L$ have each coordinate in $E$. In the integral case $\mathcal O_L\cap E=\mathcal O_E$. The same argument applies to the actual points of a nonreduced affine scheme.

## 2. Effective lifting of simultaneous profile reductions

**Theorem 2.** Let $W,V$ be uniform c.e. diagrams complete for descent on the full probe category. For a total computable input map $f$, the following conditions are equivalent.

1. For all $e,E$, nonemptiness of $W_e(E)$ implies nonemptiness of $V_{f(e)}(E)$.
2. There are uniformly computable natural maps $W_e\to V_{f(e)}$.

Thus an $f$ preserving all existence bits on each mapped input is already a simultaneous reduction with computable witness maps.

For the nontrivial implication, compute the finite orbit of a source anchor witness. Take its smallest code $a$ as representative and compute $H=\operatorname{Stab}_G(a)$. The test at $L^H$ guarantees a target anchor witness fixed by $H$. Enumerate the target and choose the first such witness $b$ deterministically. Send $ga$ to $gb$. This is independent of $g$ because $H$ fixes $b$. It is computable, equivariant, and transports down to each probe by Theorem 1 and effective inversion of the target descent bijections.

Every conjugacy type of subgroup is required if all finite $G$-sets are allowed and only existence is tested. If a type $H$ is missing, take $S=G/H$ and let $T$ be the union of $G/J$ over the tested $J$ with $S^J\ne\varnothing$. These $J$ are conjugate to proper subgroups of $H$, so $T^H=\varnothing$. The tests give existence implication, but there is no equivariant $S\to T$. Conversely one representative of each conjugacy class supplies every test used in the proof.

There is also a failure with equal existence bits and even when checking inclusions only. Retain two distinct quadratic fields $E,F$ over $K$ and their compositum $L$. Compare the point diagram of a single rational point with that of $\operatorname{Spec}(E)\amalg\operatorname{Spec}(F)$. Both have witnesses at all three fields. The two lower images coincide at the anchor in the first diagram and are disjoint in the second. No natural map can send the first to the second. Theorem 3 gives smooth hypersurface versions. Adding the probe $K$ distinguishes the profiles.

## 3. Exactly realized finite diagrams

**Theorem 3.** A finite witness diagram is naturally isomorphic to the integral point diagram of an affine hypersurface model over $\mathcal O_K$ whose generic fiber is smooth and geometrically integral, with integral local points everywhere, if and only if it is complete for descent. Given a full finite table, the construction is effective for fixed $K,L$. The ambient dimension is fixed and the degree is at most a constant depending on $K,L$ times $1+|W(L)|$.

Necessity is coordinate descent. For sufficiency, each orbit $G/H$ of $W(L)$ is the root set of the minimal polynomial of an integral primitive generator of $L^H/K$. Translate each chosen generator by an integer to avoid previous minimal polynomials. A nonzero integer translation cannot preserve a finite root set in characteristic zero. The product of the monic minimal polynomials has degree $|W(L)|$, and its root diagram is the desired one. For the empty table one may use an Eisenstein polynomial of prime degree above $[L:K]$. Apply integral arithmetic trace realization with $D=[L:K]$ to this single equation. This preserves all integral tuples naturally and gives the local witnesses and the format bounds. An effective full table supplies its stopping point, which can be unavailable for a merely c.e. finite domain. [Integral arithmetic trace realization](https://github.com/Dugongue/MathProofs/blob/7724fc270f13b7c3f174b60b16b8901c0f84433f/FourResearchPrograms/ArithmeticTraces.md)

There is an exact point-count version. For prescribed counts $m(H)$ on subgroups, invariant under conjugation, set
$$
 t(H)=\sum_{H\le J\le G}\mu(H,J)m(J).
$$
Here $\mu$ is the subgroup lattice Möbius function. The counts are realized if and only if each $t(H)$ is a nonnegative multiple of $[N_G(H):H]$. Indeed $t(H)$ counts elements of exact stabilizer $H$, and an orbit $G/H$ contributes exactly $[N_G(H):H]$ of them. The quotients give the orbit multiplicities, so here the point counts determine the finite diagram up to natural isomorphism. This uses the classical table of marks. [Galois sets](https://stacks.math.columbia.edu/tag/03QR) · [Table of marks](https://docs.gap-system.org/doc/ref/chap70.html)

**Inclusion-only tables.** First require injectivity into the anchor, so each field has a specified subset of a common finite set. When all intermediate fields occur, a table extends to a realizable diagram with all embeddings if and only if each witness has a least field of appearance, counts at conjugate least fields agree, and the number with least field $L^H$ is divisible by $[N_G(H):H]$. Necessity follows from fixed points and orbit counts. Conversely form the indicated $G$-set and match its elements to the labels by least fields. This matches every inclusion. For instance a unique witness first appearing at a quadratic field cannot be realized with no second conjugate witness at that field.

For a partial field list containing $L$, record the histogram of witness membership patterns on that list. Each $G/H$ gives such a histogram by testing $G_E\le gHg^{-1}$ at each coset. The table is realizable exactly when its histogram is a nonnegative integral combination of these finitely many histograms. Necessity decomposes the anchor into orbits. Sufficiency matches anchor labels by membership pattern. The test is finite because every orbit consumes at least one anchor witness.

### Countable diagrams up to effective bijection

**Theorem 3A.** Two uniform c.e. witness systems complete for descent admit computable natural bijections, input by input, exactly when their anchor actions have the same number of orbits of each conjugacy type on each input, including countably infinite multiplicities. The attainable multiplicity functions $m_H(e)\in\mathbb N\cup\{\aleph_0\}$ are exactly the families that admit a uniformly computable nondecreasing integer approximation, with unbounded approximation interpreted as $\aleph_0$.

For each conjugacy class fix one representative $H$. When an anchor witness is enumerated, compute its entire finite orbit and its stabilizers. Identify its type and, when first seeing that orbit, record the smallest element among those with stabilizer exactly $H$. This enumerates the orbits of each type once in a deterministic order. If the multiplicities agree, map the $j$-th source orbit of each type to the $j$-th target orbit of that type. Send the chosen source point to the chosen target point and extend equivariantly. Both points have stabilizer $H$, so this is an equivariant bijection on the paired orbit. On any input witness, the search for its orbit and for the corresponding target orbit terminates under equality of multiplicities. The inverse is computed in the same way. Theorem 1 transfers these bijections to every probe, including their inverses. The converse follows because any natural bijection is equivariant at the anchor. A computable change of input index can be handled by reindexing the target family first.

The running counts of distinct enumerated orbits of each type give the required monotone approximations. Conversely, start with such approximations and enumerate a copy of $G/H$ indexed by each $j$ as soon as the approximating count exceeds $j$. The disjoint union, coded by type, copy and coset, has a computable action and realizes the specified multiplicities. This proves the characterization even if the finite counts have no computable stopping stage.

In contrast to the finite case, cardinalities of the fixed sets alone may lose every finite orbit count. For nontrivial $G$, start with countably many one-point orbits and then add one free orbit. Both diagrams have cardinality $\aleph_0$ at every probe, but no natural bijection exists because only the second has a free orbit.

## 4. Uniform arithmetic retracts of c.e. witness diagrams

**Theorem 4.** Fix $L/K$ as above. For any uniform c.e. family $S_e$ of $G$-sets with computable action there is one computable family $H_e$ of affine hypersurface models with smooth geometrically integral generic fibers, bounded dimension and degree, and integral local points everywhere, and uniformly computable natural maps
$$
 C(S_e)\longrightarrow \bigl(E\mapsto H_e(\mathcal O_E)\bigr)
 \longrightarrow C(S_e)
$$
whose composite is the identity. These two systems have exactly the same existence profiles. The format bounds for fixed $K,L$ can be uniform in an index for $S$.

For each actual $H\le G$, the relation
$$
 R_H(e,a)\quad\Longleftrightarrow\quad a\in S_e,\quad a=\min(Ga),\quad
 \operatorname{Stab}_G(a)=H
$$
is c.e. Pick fixed integral primitive elements $\alpha_H$ of $L^H/K$ with monic minimal polynomials $f_H$. We need integer-coefficient equations $Q_H(e,a,v)=0$ over the probe rings whose solutions force $a$ to be an ordinary nonnegative integer and $R_H(e,a)$, and which admit an ordinary integer auxiliary tuple at every true label.

Here is why the predecessor's integer-definability argument supplies this extra existence of integer auxiliaries. Choose a number field $M$ containing $L$ and use a Diophantine definition of $\mathbb Z$ in $\mathcal O_M$. Expand the defining equations in an integral $\mathbb Z$-basis of $\mathcal O_M$, using its integer multiplication table. A solution over $\mathcal O_E$ then gives a witness in $\mathcal O_M\otimes_{\mathbb Z}\mathcal O_E$. The multiplication map to $\mathcal O_M$ shows that any successful tested scalar is an ordinary integer. Conversely, whenever the tested scalar is an integer, a witness in $\mathcal O_M$ has ordinary integer coordinates in the fixed basis. Apply this expanded test to the numeric variables of an MRDP representation of $R_H$. Encode nonnegativity wherever needed by four squares of designated ordinary integers. This yields $Q_H$, and the natural-number witnesses of MRDP and their tests supply the required ordinary integer auxiliary tuple. [Koymans–Pagano, Theorem 1.2](https://arxiv.org/html/2412.01768v3#S1.SS2) · [Universal Diophantine equation](https://doi.org/10.2307/2273588)

Use one affine system whose branches are
$$
 Q_H(e,a,v)=0,\qquad f_H(b)=0.
$$
Encode a finite branch choice by a variable ranging over distinct integer roots, and multiply each branch equation by all other label factors. On a probe domain that product is nonzero on its own branch. One universal MRDP polynomial treats the enumerator index and the branch as numeric parameters, so the degrees and dimension stay bounded. Apply integral arithmetic trace realization with $D=[L:K]$.

From a tuple on branch $H$, find $g\in G$ with $b=g\alpha_H$ by finite search and send the tuple to $ga$. The choice is immaterial because both $\alpha_H$ and $a$ have stabilizer $H$. This gives a $G_E$-fixed witness whenever the tuple is over $E$, and the map is natural. For the section, from $s\in S_e^{G_E}$ compute its canonical representative $a$, $H$, and $g$ with $ga=s$. The root $b=g\alpha_H$ lies in $\mathcal O_E$, because $G_E\subseteq gHg^{-1}$. Search over ordinary integer tuples for the first solution of $Q_H(e,a,v)=0$ in a fixed effective enumeration. It exists and the choice depends only on $(e,H,a)$. Use this tuple, the branch label and $b$, then the closed immersion into $H_e$. Transport changes only $b$, so this section is natural. Its composite with the projection is the identity. This is a statement about witness diagrams and computable natural maps, with no uniqueness requirement on the auxiliary tuple and no assertion that the section is algebraic.

For example, with $G=C_2$, a c.e. collection of free two-point orbits can vary undecidably with the input. The smooth models admit a natural projection with a section onto exactly those free orbits, so none of these witnesses gives a rational point.

## 5. Simultaneous relations on the visible witnesses

**Corollary 5.** Given finitely many uniform c.e. $G$-set families and finitely many uniformly c.e. $G$-invariant relations of fixed finite arities among them, every sort and relation has a smooth integral realization as in Theorem 4. On the quotient diagrams the coordinate projections of a relation are its original coordinate projections. Moreover, the relations have existential polynomial definitions on the shared orbit labels of their arguments over all the probe rings.

The relation itself is a c.e. $G$-set inside a finite product. This and Theorem 4 give the first assertion. For common labels, fix the subgroup labels $H_i$ of the arguments and choose a representative $(g_iH_i)_i$ for each diagonal $G$-orbit in the finite product $\prod_i G/H_i$. Its stabilizer is $J=\bigcap_i g_iH_i g_i^{-1}$. The tuple $(g_i\alpha_{H_i})_i$ generates $L^J$: its stabilizer is $J$. Take an integral primitive element $\alpha_J$ and express each root of the representative tuple as a polynomial in it, clearing denominators in the equations. Existence of a root of the minimal polynomial of $\alpha_J$, with these equations, enforces membership in that diagonal orbit. Conversely a tuple in that orbit over $E$ comes from an integral root in $E$, since the tuple generates the corresponding conjugate of $L^J$. On this chart the remaining test of the relation is the c.e. predicate of the ordinary integer codes $a_i$ given by evaluating it on $(g_i a_i)_i$. Invariance makes it the same predicate for every common translate. The integer test and finite branch construction from Theorem 4 combine the charts. This uses exactly the same visible labels $(H_i,a_i,b_i)$ for each sort in every relation. It applies in particular to the graph of a uniformly computable natural map of complete diagrams. It produces a polynomially defined correspondence on visible labels, with the earlier degree cutoff, rather than an algebraic morphism of the whole hypersurfaces.

## 6. Exact transfer to sections of graph covers

**Theorem 6.** For fixed $G$, the complete finite diagrams are exactly the section diagrams of finite graph covers with monodromy factoring through $G$, over one fixed bouquet of circles and its fixed coset probe covers. For c.e. diagrams one can use c.e. target graph covers with computable labelled edge transitions.

Fix generators $\Gamma$ for $G$ and a bouquet $B$ with a loop for each generator. A $G$-set $S$ gives the cover with vertices $S$ and edges labelled $\gamma$ from $s$ to $\gamma s$. Take the probe cover $B_H$ with vertices $G/H$. A section after pullback to $B_H$ is equivalent to a cover map $B_H\to B_S$ over $B$. Its vertex map is $G$-equivariant since it respects generator edges. It is determined by the value at $H$, which may be any $s\in S^H$. The embedding $L^H\to L^J$ coming from $g$ corresponds to the cover map $B_J\to B_H$ sending $J$ to $gH$. Precomposition sends $s$ to $gs$, exactly the field transport. Conversely a cover whose action factors through $G$ comes from such a set. In the effective infinite case a section is coded by its base vertex since $B_H$ is finite. Theorem 3 gives exact transfer to smooth arithmetic for finite diagrams, and Theorem 4 gives transfer by natural arithmetic retract for c.e. diagrams. [Hatcher, Algebraic Topology, §1.3](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) · [Stallings, Topology of finite graphs](https://doi.org/10.1007/BF02095993)

## 7. Questions raised by the witness results

1. **Exactness for c.e. witnesses.** Does every uniform c.e. $G$-set family admit a bounded-format smooth integral point realization by computable natural bijections without requiring a computably complete table at each input? Theorem 4 gives a retract. One sufficient condition for exactness is a uniform single-witness definition of numeric c.e. relations over all of the specified rings: the same integer-coefficient system would have to force the visible coordinates to be ordinary nonnegative integers and give exactly one complete auxiliary tuple for each true label over every probe. Under this condition the root-label projection in Theorem 4 is bijective, and uniqueness makes its inverse natural. The 2026 single-fold representation preprint concerns natural-number auxiliary solutions, and the arithmetic integer tests used here may have extra witnesses over other rings. [Single-fold Diophantine representation preprint](https://github.com/openai/math/tree/main/preprints/Single-fold-Diophantine-representations-September-24-2026)

2. **Probe complexity for restricted orbits.** Theorem 2 gives the exact worst-case requirement if all finite $G$-sets are allowed. Which tests suffice when the allowed stabilizers come from a specific arithmetic or geometric family? A separate question is which restricted membership histograms admit simpler membership criteria than finite monoid feasibility.

3. **Commuting algebraic realizations.** When can a computable natural map of witness diagrams be realized by a morphism between geometrically integral smooth realizations? Can finite chains of maps be represented with all their compositions holding at the level of ambient morphisms? Corollary 5 gives such graphs on visible labels and a computable natural section, under an explicit cutoff.

4. **Infinite anchors.** Find exact recognition conditions for diagrams with infinite profinite Galois groups and uniformly computable finite orbits. Individual finite-orbit transport can be managed at finite anchors. A uniform locally soluble arithmetic compiler through an unbounded tower would have to manage changing orbit types without one common bound on extension degrees.

## Status

These are written proofs with provisional publication priority. The adjunctions, subgroup marks and covering correspondence are established tools. The new conclusions concern exact smooth integral realization of witness tables, the effective lifting and omitted-probe tests for simultaneous computation, and the uniform c.e. witness retract and relational lift.
