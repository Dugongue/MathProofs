# Constructive witnesses and exact solution geometry under Q

## One-line verdict

**PROVED — confidence 0.97.** For every fixed finite-signature template in the fully arithmetic equality–congruence setting satisfying \(Q\), one can construct a satisfying assignment in polynomial time, compute the exact rational affine hull of all numerical solutions, and decide every rational affine equality consequence and linear-objective trichotomy, with explicit polynomial-size witnesses.

## Executive summary

1. The new result strengthens the preceding decision theorem to an explicit search theorem.
2. A satisfiable instance yields one finite assignment and one full-dimensional residue coset on which every atom is generically true.
3. The finite table recording these generic choices is preserved by the same fixed cyclic operation.
4. Its preservation proof uses one carefully chosen input point; the operation arity need not exceed the instance dimension.
5. A fixed finite-domain CSP solver and singleton-pin self-reduction select compatible labels and residues.
6. Substituting \((T,T^2,\ldots,T^d)\) in the free integer parameters gives a satisfying point for some \(0\le T\le hd\).
7. The output has polynomial binary length, even though its numerical magnitude can be large.
8. The resulting cell supplies \(d+1\) actual solutions forming an affine basis, all with the same finite assignment.
9. The numerical solution set has real convex hull exactly equal to its real affine hull, without taking closure.
10. A rational affine objective is either constant or unbounded in both directions; explicit feasible arithmetic rays certify the latter case.
11. The complete prerequisite proof and previous archives are included; no unprovided structural lemma is being substituted for a proof.
12. The C++ artifact implements the integer-avoidance subroutine, not the whole finite Taylor solver or the entire CSP algorithm.

Every mathematical assertion in these twelve lines is **PROVED, confidence 0.97**, by the numbered results in the chapters below and their reproduced prerequisites. “Confidence” records the authors' assessment of the written argument; it is not a formal-verification certificate.

## 0. Precise scope, definitions, and main theorem

### Definition W0.1 — PROVED, confidence 1.00; notation and input convention

Fix a finite relational signature and a structure \(\mathcal M\) in that signature. Its carriers consist of finitely many integer sorts, each identified externally with \(\mathbb Z\), and finitely many nonempty finite sorts. Every integer sort has the graph of addition and the singleton relation \(\{1\}\). Finite sorts include the label sort and any torsion sorts. The labels have singleton relations for their elements. For every basic relation \(R\) and every choice \(\eta\) of its finite arguments, a fixed Boolean formula \(\psi_{R,\eta}\) presents its integer fibre. Its atomic predicates are integer affine equalities and congruences. Negations and arbitrary finite Boolean connectives are allowed. An affine equality is \(a_0+\sum_i a_i x_i=0\), with integer coefficients. An affine congruence is \(a_0+\sum_i a_i x_i\equiv b\pmod q\), with a positive integer modulus \(q\). A disequality is the negation of an equality.

All fibre presentations, coefficients, finite domains, and arities are fixed with \(\mathcal M\). The variable input is a primitive-positive sentence: an existentially quantified conjunction of basic-relation atoms and well-typed equalities. A complete witness assigns a value to every variable of that sentence. The bit size of an integer is its signed binary length. Computational bounds refer to the length of this variable sentence, with the template fixed.

No integer order or half-space predicate is present. Integer sorts are not identified merely because their externally written fibre formulas mention both sorts. The distinction between an external coordinate formula and a pp-definable relation in \(\mathcal M\) is retained throughout the proof.

The original core assumption is compatible with this setting. The new extraction and geometry arguments do not use any further consequence of being a core.

### Definition W0.2 — PROVED, confidence 1.00; finite images and cyclic operations

A relation is pp-definable if an existential conjunction of basic relations and equalities defines it. For \(N\ge1\), reduce every integer coordinate modulo \(N\), and leave every finite coordinate unchanged. If \(S\) is pp-definable, write \(q_N(S)\) for its exact image under this map. The finite many-sorted structure \(D_N^{\rm pp}\) has all the relations \(q_N(S)\).

A sorted operation family consists of one operation of a common arity on each sort. It preserves a relation when coordinatewise application to any list of tuples from that relation produces another tuple of the relation. An operation is idempotent if \(f(a,\ldots,a)=a\). A \(p\)-ary operation is cyclic if

\[
f(a_0,a_1,\ldots,a_{p-1})=f(a_1,\ldots,a_{p-1},a_0).
\]

An idempotent operation is a Taylor operation if, for each of its argument positions, it satisfies an identity between two evaluations on variables \(x,y\) in which that position contains \(x\) on one side and \(y\) on the other. Other positions in those two evaluations may contain either variable. A finite structure is Taylor when it has such a polymorphism. The hypothesis \(Q\) is that every \(D_N^{\rm pp}\) is Taylor.

An idempotent operation of arity at least three is weak near-unanimity when all evaluations with one \(y\) among copies of \(x\) are equal. A cyclic idempotent operation satisfies these identities: rotating its inputs carries each placement of the single \(y\) to every other placement.

Singletons for every element of every finite sort may be adjoined for this proof. To justify the preservation of \(Q\), take a pp definition in the pinned expansion and replace its pinned finite parameters by additional free variables. Its image is a relation of the original \(D_N^{\rm pp}\); fixing those new arguments is preserved by an idempotent polymorphism. Therefore the expanded pp images retain that polymorphism. The expanded problem includes the original input language, so an algorithm for the expansion also solves the original instances.

### Definition W0.3 — PROVED, confidence 1.00; blocks, affine spaces, and generic cells

Integer sorts belong to the same block when their literal coordinate-identity relation is pp-definable in the finite-pinned expansion. This is an equivalence relation: identity provides reflexivity, interchanging free variables provides symmetry, and existential composition provides transitivity. Its equivalence classes are the blocks used below.

For a nonempty set \(S\subseteq\mathbb Q^n\), \(\operatorname{aff}_{\mathbb Q}S\) is the set of finite affine combinations \(\sum_i c_i s_i\) with rational coefficients summing to one. For \(S\subseteq\mathbb R^n\), its real convex hull \(\operatorname{conv}_{\mathbb R}S\) uses nonnegative real coefficients summing to one. A rational affine space is a set \(u+V\), with \(u\in\mathbb Q^n\) and \(V\) a rational linear subspace. Its real extension is \(u+\operatorname{span}_{\mathbb R}V\).

Fix an integer \(m\ge2\) divisible by every modulus in every basic fibre presentation. The integer cosets used in the construction are

\[
U_\rho=u+B(\rho+m\mathbb Z^d),
\qquad
u\in\mathbb Z^n,
\quad B\in\mathbb Z^{n\times d}.
\]

In the CSP application the columns of \(B\) are linearly independent and \(B\) is block diagonal. The rational affine hull is \(L=u+B\mathbb Q^d\). A fibre is generically true on \(U_\rho\) if it contains all of \(U_\rho\) except possibly the points in finitely many proper rational affine hyperplanes of \(L\). A form whose zero set in \(L\) is empty is already nonzero everywhere and imposes no exceptional points. A selected generic solution cell has the form

\[
C=\{u+B(\rho+mz):z\in\mathbb Z^d,\ h_j(u+B(\rho+mz))\ne0\ (1\le j\le h)\},
\tag{W0.1}
\]

where every \(h_j\) is an integer affine form nonidentically zero on \(L\). Every point of this cell will satisfy the original instance with one fixed finite assignment \(\eta^*\).

### Theorem W0.4 — PROVED, confidence 0.97; constructive and geometric theorem

For a fixed template of Definition W0.1 satisfying \(Q\), there is a deterministic polynomial-time algorithm with the following outputs on each pp instance \(I\).

* If \(I\) is unsatisfiable, it reports that fact.
* If \(I\) is satisfiable, it returns a complete satisfying assignment and polynomial-bit data \(u,B,\rho,\eta^*,h_1,\ldots,h_h\) for a nonempty cell (W0.1). Every point of that cell, paired with \(\eta^*\), satisfies \(I\).
* If \(S_I\subseteq\mathbb Z^n\) is the projection of all satisfying assignments onto all original integer variables, then

\[
\operatorname{aff}_{\mathbb Q}S_I=u+B\mathbb Q^d,
\qquad
\operatorname{conv}_{\mathbb R}S_I=u+B\mathbb R^d.
\tag{W0.2}
\]

* It outputs \(d+1\) actual complete satisfying assignments, all having the finite part \(\eta^*\), whose integer parts form an affine basis of the space in (W0.2).
* Given in addition an integer- or rational-coefficient affine equality in the original integer variables, it decides whether every solution satisfies it. When the equality is not entailed, it outputs a complete counterexample assignment of polynomial bit length.
* Given in addition a rational affine objective on the original integer variables, it reports precisely one of: infeasible; constant on all solutions, with that constant; or unbounded above and below, with two explicit feasible arithmetic rays and a common finite assignment witnessing those two directions.

The polynomial for a fixed template may depend on its finite-domain solver. The bit size of an extra equality or objective is included in the bound when such a query is supplied. A feasible arithmetic ray is a sequence \(b+nv\) for integers \(n\ge0\); it is not an assertion that the continuous segment between two integer solutions consists of integer solutions.

**Proof map.** Chapter I constructs the generic finite tables, proves preservation by a fixed cyclic operation, obtains a common finite assignment by singleton-pin self-reduction, and states the complete extraction algorithm. Chapter II proves the integer-avoidance construction, all size bounds, the rectangular normal-form reduction, and a general small-witness theorem. Chapter III proves (W0.2), the explicit affine basis, equality-consequence testing, and the objective trichotomy. The full prerequisite decision and structural proofs are reproduced in Appendix P of `N_Complete.md`, and also supplied as separately named source files. Each cited prerequisite is mapped precisely below. This proof map is not a replacement for the chapters or Appendix P. \(\square\)

## 1. Dependency ledger: what is old and what is new

### Lemma W0.5 — PROVED, confidence 1.00; retaining every original coordinate

Well-typed equality preprocessing does not limit the main theorem to a subset of the original variables. Integer equalities may be retained as rows of the initial arithmetic system, in which case the tuple \(x\) already contains every original integer variable. If they are used to identify variables, as in the preceding decision chapter, all output assignments, affine spaces, and affine queries can instead be transferred back to the full tuple in polynomial time.

**Proof.** In the first implementation, a well-typed equality between integer variables is the original row \(x_i-x_j=0\). It is supported within one original sort, hence within one block. The initial product-space invariant and the persistent original-row bounds hold for this row. Every subsequent proof in the decision chapter applies to the system with that row included; none requires that the two variables have already been identified.

For the second implementation, let \(\widetilde x\) list one representative of each identified integer-variable class. Define the integer matrix \(E\) with one row for each original variable and one column for each class, putting a single \(1\) in the column of that variable's class and zero elsewhere. The full original tuple is \(x=E\widetilde x\). Each class has a representative, so \(E\) has independent columns: if \(Ev=0\), its representative row gives every coordinate of \(v\) equal to zero. An original assignment satisfies all identified equalities exactly when it has this form. Replacing occurrences by their representatives preserves every other atom, so solutions correspond exactly under this map, with the identical finite-variable identification handled by copying class values.

If the reduced output is \(\widetilde u+\widetilde B\mathbb Q^d\), take \(u=E\widetilde u\) and \(B=E\widetilde B\). Independence of the columns of \(\widetilde B\) and injectivity of \(E\) imply independence of the columns of \(B\). Apply \(E\) to every returned integer witness and every arithmetic-ray description. Affine and convex combinations commute with the linear map \(E\), as is verified by distributing a finite sum: \(E\sum_i c_i v_i=\sum_i c_iEv_i\). Thus the proved hull identities transfer exactly. Every original fibre form can be used on the expanded tuple; after substituting \(E\widetilde x\), it has the same truth value as in the reduced tuple. In particular the returned generic cell expands to a cell in the full tuple with the corresponding original forms. A query \(c+a^{\mathsf T}x\) pulls back to \(c+a^{\mathsf T}E\widetilde x\), so implication and objective answers transfer as well.

The matrix entries are zero or one and each row merely copies one coordinate. Its construction, every expansion, and every query substitution therefore have polynomial size and time. Finite variable copies require no arithmetic or geometric interpretation. \(\square\)

### Proposition W1.1 — PROVED, confidence 0.97; precise prerequisite statements

The preceding complete proof, reproduced in Appendix P, establishes these facts for the setting of Definition W0.1.

1. **Block-generic operations from \(Q\).** For every sufficiently large prime \(p\nmid m\), there are common cyclic idempotent operations \(c_p\) on all finite sorts. For any \(p\) tuples of a basic relation, applying \(c_p\) to the finite arguments and taking independent affine combinations in the integer blocks preserves the relation outside finitely many proper affine hyperplanes in coefficient space. The coefficients in each block satisfy \(\sum_i\gamma_i=1\) and \(\gamma_i\equiv p^{-1}\pmod m\). The same means and finite operations preserve every pp image modulo \(m\).
2. **An exact polynomial refinement algorithm.** Given an instance, the algorithm either rejects correctly or returns a nonempty product affine integer space \(L_{\mathbb Z}=u+B\mathbb Z^d\) containing the integer part of every actual solution. The matrix \(B\) is block diagonal and has independent columns. Its output and every intermediate arithmetic representation have polynomial bit length.
3. **Stability.** At the returned space, the exact residue relaxation \(F_L\) is satisfiable. For each atom \(a\), the set of actual numerical tuples satisfying \(a\) with a finite assignment supported by \(F_L\) has rational affine hull all of \(L\).
4. **One generic cell exists.** The stable condition implies that one common finite assignment and one parameter residue class make every atom generically true. This is an existence statement; the new Chapter I supplies polynomial-time extraction.

**Full proof locations, with exact internal identifiers.** Item 1 is `N_next_structure.md`, Theorem 1 and Corollary 7.1, and `N_amplification.md`, Theorem II.8. Items 2–3 are `N_general_algorithm.md`, Definitions 3.1, 5.1, and 5.2, Lemmas 3.2 and 5.3–6.2, Proposition 6.3, Algorithm 8.1, and Theorem 8.2. Item 4 is that chapter's Lemmas 7.1–7.2. Their proofs are reproduced in full in Appendix P. The new Chapter I also rederives item 4, to make the interface between the prior refinement and the new extraction explicit.

The new proof does not replace the exact residue relaxation by the generic relaxation during refinement. Exact residue support is what justifies the affine reductions. The generic relaxation is used after stability, or as an early acceptance test only when it actually has a solution.

### Proposition W1.2 — PROVED, confidence 0.99; exact external results

Three external mathematical inputs occur in the cumulative proof:

* Libor Barto and Marcin Kozik (2012), *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*, **Theorem 4.1**, supplies cyclic terms of every prime arity greater than the size of a finite idempotent Taylor algebra. The sorted reduction and every application to this setting are proved in Appendix P.
* Ravindran Kannan and Achim Bachem (1979), *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, **Theorem 2 and Lemma 3**, supplies the polynomial square Hermite computation with a polynomial-bit unimodular multiplier. The rectangular integer-solution parametrization is written out in Chapter II and Appendix P; it is not hidden in a reference to an unspecified normal-form fact.
* Andrei A. Bulatov (2017), *A Dichotomy Theorem for Nonuniform CSPs*, **Theorem 4, implication (2) to (1)**, supplies the fixed finite-language tractability algorithm under a weak near-unanimity operation. Chapter I and Appendix P prove why all the changing finite tables belong to one fixed bounded-arity language satisfying that hypothesis.

The exact bibliography, primary links, and theorem-use map are in `REFERENCES.md`. These citations support only the statements just specified. The elementary polynomial-avoidance and geometric arguments are proved here and are not attributed to a fictitious reference.

## 2. Scope of the new conclusion relative to the original conjecture

**PROVED — confidence 0.97.** This report proves a constructive consequence of \(Q\) in the stated fixed finite-signature setting. It does not assert that the original shared-coefficient \(GC\) becomes equivalent to \(Q\). The previous report's explicit two-integer-sort counterexample and its uniform proof for every modulus are retained, in full, in Appendix P and the unchanged previous archive. The witness theorem uses the proved independent-block structure, which is exactly the structure on which the preceding decision theorem depends.

**PROVED — confidence 0.99.** The convex-hull assertions concern integer-coordinate projections. They assign no convex meaning to label elements or torsion elements. They remain true for the numerical solutions at the one returned finite assignment: that subset contains the same cell and is contained in the same affine space.

**PROVED — confidence 0.99.** Finite signature and a fixed template are material assumptions in the complexity statements. An arbitrary infinite signature supplied without an effective encoding is outside their scope. The algorithm is also not a linear-programming algorithm for ordered Presburger arithmetic: half-space predicates are absent from its hypotheses.

---

# Chapter I — Polynomial-time witness construction

**Verdict — PROVED, confidence 0.98.** Under the hypotheses of the preceding finite-signature block-generic classification, a satisfying assignment can be constructed in deterministic polynomial time whenever the input pp-instance is satisfiable. Every returned integer has polynomial binary length. At any current affine space, the algorithm accepts as soon as its finite generic-acceptance constraints are satisfiable. It can also decide and construct extensions of prescribed integer and finite partial assignments.

This chapter proves the new search theorem in full. The structural classification and the exact supported-hull refinement theorem are the earlier theorems reproduced in the cumulative archive. They are identified precisely in Section 1, so no additional structural assertion is being assumed silently.

## 1. Setting and previously proved inputs

### Definition 1.1 — the fixed template and input

**PROVED, confidence 1.00; definition.** Fix a finite-signature many-sorted structure \(\mathcal M\). Its integer sorts are copies of \(\mathbb Z\) carrying the graph of addition and the singleton \(1\). Its remaining sorts are finite and nonempty. For each basic relation and each assignment of its finite arguments, its integer fibre is supplied as a fixed Boolean formula in integer-affine equations and congruences. Negations of these predicates are allowed. Every numerical coefficient, congruence modulus, relation arity, and finite carrier is fixed with the template.

An input is a finite primitive-positive sentence, meaning an existentially quantified conjunction of atomic formulas over that template. After renaming existential variables, write \(x\) for all integer variables and \(\eta\) for all finite variables. Addition, integer equality, and integer pins are included among the arithmetic equations. Write \(a\) for an occurrence of any remaining basic relation, and write its constraint as \(R_a(x,\eta_a)\); its displayed integer arguments are selected coordinates of \(x\), with repetitions permitted. The tuple \(\eta_a\) selects its finite arguments from the global tuple \(\eta\), again with repetitions permitted.

For \(N\geq1\), let \(q_N\) reduce every integer coordinate modulo \(N\) and leave finite coordinates unchanged. The finite many-sorted structure \(D_N^{\mathrm{pp}}\) has the resulting finite carriers and, as its relations, \(q_N(S)\) for every pp-definable relation \(S\) of \(\mathcal M\). A many-sorted operation is one operation of a common arity on each carrier. It preserves a relation when its coordinatewise application to tuples of that relation produces another tuple of that relation. It is idempotent when \(f(v,\ldots,v)=v\) on every carrier. It is Taylor when it is idempotent and, for each argument position \(j\), it satisfies an identity \(f(u_0,\ldots,u_{k-1})=f(v_0,\ldots,v_{k-1})\) in the variables \(X,Y\), with \(u_i,v_i\in\{X,Y\}\) and \(u_j\ne v_j\), using the same identity on every carrier. Property \(Q\) means that \(D_N^{\mathrm{pp}}\) has such a Taylor polymorphism for every \(N\geq1\). A cyclic operation of arity \(k\) satisfies \(f(v_0,\ldots,v_{k-1})=f(v_1,\ldots,v_{k-1},v_0)\) on every carrier.

Finite singleton pins are included in the working language. An idempotent operation preserves them. The preceding classification proves that adjoining these pins preserves \(Q\).

Fix
\[
m=\operatorname{lcm}\bigl(2,\text{ all congruence moduli in the fixed fibre formulas}\bigr).
\]
In particular, every basic congruence has modulus dividing \(m\).

### Definition 1.2 — blocks and generic certificates

**PROVED, confidence 1.00; definition.** Let \(\Pi_*\) be the partition of integer sorts according to pp-definability of their literal numerical coordinate identity. Coordinates whose sorts belong to the same block will share coefficient vectors. Different blocks may use different coefficient vectors.

For an integer \(p\geq2\) relatively prime to \(m\), define the rational affine coefficient space
\[
W_p=
\prod_{b\in\Pi_*}
\left\{\gamma^b\in\mathbb Q^p:
\sum_{i=0}^{p-1}\gamma_i^b=1\right\}
\]
and its allowed integer subset
\[
\Gamma_p=
\left\{\gamma\in W_p:
\gamma_i^b\in\mathbb Z,\
\gamma_i^b\equiv p^{-1}\pmod m
\text{ for every }b,i\right\}.
\]
The residue mean on \(A=\mathbb Z/m\mathbb Z\) is
\[
f_p(r^0,\ldots,r^{p-1})=
p^{-1}\sum_{i=0}^{p-1}r^i.
\]

A generic certificate of arity \(p\) is a cyclic idempotent operation \(c_p\) on each finite sort such that the following holds. For every basic relation and every list of \(p\) actual tuples of that relation, combine integer coordinates using \(\gamma^b\) in their respective blocks and finite coordinates using \(c_p\). For every allowed \(\gamma\) outside a finite union of proper rational affine hyperplanes of \(W_p\), the output remains in the relation. The exceptional hyperplanes may depend on the chosen input tuples.

### Theorem 1.3 — exact imported dependencies

**PROVED, confidence 0.98; the complete proofs are in the accompanying earlier chapters.** This chapter uses precisely the following previously proved statements.

1. Under \(Q\), a generic certificate exists for every sufficiently large prime \(p\), and one fixed certificate \((p_0,c_{p_0})\) is available. This is Theorem 1 of *N_next_structure.md* together with Theorem II.8 of *N_amplification.md*. The finite search and its all-prime amplification are fully proved in those chapters.
2. The exact decision/refinement procedure of *N_general_algorithm.md*, Sections 3–7, maintains an affine product space \(L\) across \(\Pi_*\). Its integer points have an injective blockwise parametrization
   \[
   L_{\mathbb Z}=L\cap\mathbb Z^n
   =\{u+Bt:t\in\mathbb Z^d\},
   \tag{1.1}
   \]
   where \(u\) and \(B\) are integer, \(B\) has linearly independent columns, and all entries have polynomial binary length. These statements are Lemma 3.2 and the persistent-system analysis in that chapter. For a product space, the matrix \(B\) may and will be chosen block diagonal.
3. At such a current space, define the exact local residue relation
   \[
   P_a(r,\eta_a)
   \iff
   \exists t\in\mathbb Z^d\
   [t\equiv r\pmod m\ \wedge\ R_a(u+Bt,\eta_a)]
   \tag{1.2}
   \]
   and the exact finite relaxation
   \[
   F_L(r,\eta)=\bigwedge_aP_a(r,\eta_a).
   \tag{1.3}
   \]
   Its satisfiability is decidable in polynomial time by Lemmas 4.3–4.4 and Proposition 4.5 of that chapter.
4. Define the supported set for atom \(a\) by
   \[
   S_a=
   \left\{t\in\mathbb Z^d:
   \exists\eta\
   [F_L(q_m(t),\eta)\wedge R_a(u+Bt,\eta_a)]
   \right\},
   \qquad X_a=u+BS_a.
   \tag{1.4}
   \]
   If \(F_L\) is satisfiable, every \(S_a\) is nonempty. The affine hull of every \(X_a\) is computable in polynomial time. If one of those hulls is proper in \(L\), the refinement procedure adds original input equality rows so that the new space is that hull, remains a product across the blocks, and retains every actual solution of the instance. Every such refinement lowers the dimension. It adds only rows from a fixed finite list of original input equations, and therefore retains polynomial coefficient lengths. These are Lemmas 5.3–5.4, Lemmas 6.1–6.2, and Proposition 6.3 of that chapter.

The present proof does not call a solver on arbitrary new infinite-domain relations. Its new finite tables are explicit, bounded-arity tables. It also does not need to find pp definitions of the block identities. Those definitions justify the earlier structural theorem, while the algorithm uses the already computed finite partition.

The imported arithmetic parametrization theorem uses Kannan and Bachem (1979), Theorem 2 and Lemma 3, with the full rectangular-system reduction written in Lemma 2.2 of *N_general_algorithm.md*. Its proof and all structural dependencies are included in the same archive.

## 2. Elementary avoidance

### Lemma 2.1 — nonzero polynomials have nonzero integer values

**PROVED, confidence 1.00.** If a polynomial \(P\in\mathbb Q[z_1,\ldots,z_d]\) is nonzero, some \(z\in\mathbb Z^d\) satisfies \(P(z)\ne0\). A full affine integer lattice in a rational affine space is therefore not covered by finitely many zero sets of affine rational functions which are nonzero on that space.

**Proof.** For \(d=0\), a nonzero polynomial is a nonzero constant, so the unique empty tuple works. Suppose the assertion has been proved for \(d-1\) variables. Write
\[
P(z_1,\ldots,z_d)=
\sum_{j=0}^k P_j(z_1,\ldots,z_{d-1})z_d^j.
\]
Choose an index \(j\) for which \(P_j\) is nonzero. By the induction hypothesis there is an integer tuple \(w\) of length \(d-1\) with \(P_j(w)\ne0\). The specialized polynomial \(P(w,z_d)\) is a nonzero univariate polynomial.

A nonzero polynomial of degree at most \(k\) has at most \(k\) distinct roots over \(\mathbb Q\). To see this, polynomial division by \(z-a\) has remainder \(P(a)\); a root therefore supplies the factor \(z-a\). Removing one such factor reduces the degree by one, and induction on degree proves the root count. There are infinitely many integers, so some integer \(z_d\) is not a root. This completes the induction on \(d\).

Now parametrize a full affine integer lattice as \(v+C\mathbb Z^e\), where the rational affine hull of this set is the given affine space. Every affine function nonzero on that affine space has a nonzero pullback polynomial under \(z\mapsto v+Cz\). A product of nonzero rational polynomials is nonzero. Here is a proof of this fact that also covers any number of variables. With no variables it is the fact that the product of nonzero rationals is nonzero. With \(e\geq1\) variables, view two nonzero polynomials as polynomials in the last variable, with coefficients in the polynomial ring in the first \(e-1\) variables. Their highest-degree coefficients have nonzero product by induction on \(e\), so their product has nonzero highest-degree coefficient. Induction on the number of factors gives the finite-product statement. Apply the first part of the lemma to that product. At the resulting lattice point, all the functions are nonzero. The empty product is \(1\), so an empty family of forbidden zero sets causes no exception. \(\square\)

### Lemma 2.2 — residue cosets and allowed coefficient lattices are full

**PROVED, confidence 1.00.** For \(r\in A^d\), choose any integer lift \(\rho\). The set
\[
U_r=\{u+B(\rho+mz):z\in\mathbb Z^d\}
\tag{2.1}
\]
has rational affine hull \(L\), is nonempty, and does not depend on the lift. Also \(\Gamma_p\) has rational affine hull \(W_p\).

**Proof.** Two lifts differ by \(m\) times an integer vector, which only reindexes \(z\), so the set is independent of the lift. Taking \(z=0\) proves nonemptiness. Its direction vectors include \(mBe_j\) for every column \(Be_j\) of \(B\). Those columns span the direction of \(L\) by (1.1). Multiplication by the nonzero rational scalar \(m\) does not change their rational span. Consequently the rational affine hull is \(L\).

For the coefficient statement, choose an integer \(a\equiv p^{-1}\pmod m\). In one block the vector
\[
\gamma^0=(1-(p-1)a,a,\ldots,a)
\]
has coordinate sum \(1\). Its first coordinate also has residue \(a\), because \(pa\equiv1\pmod m\). Hence it is allowed. Adding any integer linear combination of
\[
m(e_i-e_0),\qquad 1\leq i<p,
\]
preserves every residue and the coordinate sum. These direction vectors span the rational subspace whose coordinate sum is zero. Thus the affine hull of the allowed set in one block is the entire coefficient hyperplane. The product over the blocks has affine hull \(W_p\). If the template has no integer coordinates in the instance, the product over the relevant zero-dimensional spaces is a point, and the same assertion holds. \(\square\)

### Lemma 2.3 — removing finitely many proper hyperplanes preserves the affine hull

**PROVED, confidence 1.00.** Let \(U\) be a full affine integer lattice with rational affine hull \(L\). If finitely many affine rational functions are nonzero on \(L\), the points of \(U\) at which they are all nonzero have affine hull \(L\).

**Proof.** Lemma 2.1 proves that this set is nonempty. Suppose its affine hull \(H\) were proper in \(L\). Choose a rational point \(v\in H\). A rational basis for the direction space of \(H\) extends to a rational basis for the direction space of \(L\), with at least one additional basis vector. Define a rational linear functional which is zero on the former basis and takes value \(1\) on one additional vector; assign any rational values, for example zero, on the remaining additional basis vectors. Translating this functional by \(v\) gives an affine rational function which vanishes on \(H\) but is nonzero on \(L\). Extend it to the ambient rational coordinate space by extending a basis if needed. Appending this function to the finite list and applying Lemma 2.1 produces a point in the alleged set outside \(H\), a contradiction. \(\square\)

## 3. The finite generic-acceptance relation

### Definition 3.1 — generic acceptance

**PROVED, confidence 1.00; definition.** For an atom \(a\), a global parameter residue \(r\in A^d\), and a tuple \(\eta_a\) of its finite arguments, define
\[
G_a(r,\eta_a)
\tag{3.1}
\]
to mean that all points of \(U_r\) outside a finite union of proper rational affine hyperplanes of \(L\) satisfy \(R_a(x,\eta_a)\). Empty zero sets may be omitted from the union. In dimension zero there are no nonempty proper hyperplanes, so \(G_a\) then means that the unique point of \(L\) satisfies the fibre.

### Lemma 3.2 — exact Boolean evaluation of generic acceptance

**PROVED, confidence 1.00.** To evaluate \(G_a(r,\eta_a)\), make the following replacements in the supplied fibre formula of \(R_a(\cdot,\eta_a)\).

1. Replace an exact equation \(\ell(x)=0\) by the truth value of
   \[
   \ell(u+Bt)\text{ is the zero affine function of }t.
   \]
2. Replace a congruence by its truth value at any \(x=u+B\rho\), where \(\rho\) lifts \(r\).
3. Evaluate the resulting Boolean formula, including all its negations.

The resulting truth value is exactly \(G_a(r,\eta_a)\). If it is false, every satisfying point of \(R_a(\cdot,\eta_a)\) in \(U_r\) lies in a finite union of proper rational affine hyperplanes of \(L\).

**Proof.** An exact equation either vanishes identically on \(L\), or its restricted affine function is nonzero. In the latter case its zero set in \(L\) is either empty or a proper rational affine hyperplane. Remove all those nonempty zero sets for the finitely many exact equations in the supplied formula. At any remaining point of \(U_r\), every equation has precisely the truth value in replacement 1.

For a congruence with modulus \(e\mid m\), replacing \(\rho\) by \(\rho+mz\) changes every integer argument by an integer multiple of \(m\), and therefore changes its integer-affine left side by a multiple of \(e\). Its truth is constant on \(U_r\) and is given by replacement 2. Affine constants cause no change in this reasoning. Since all atomic predicate values are now fixed, the Boolean formula is constant on the remaining set, with the value obtained by replacement 3.

If that value is true, the definition of \(G_a\) holds. If it is false, every satisfying point is inside the removed hyperplanes, proving the last assertion. It remains to exclude the possibility that a false value nevertheless satisfies Definition 3.1 via a different hyperplane list. Such a possibility would cover \(U_r\) by the union of the two finite lists: on the complement of the first list the formula is false, and on the complement of the second list it would be true. Lemmas 2.1 and 2.2 give a point outside their union, which is impossible. This proves exact equivalence. \(\square\)

The exact equations include those appearing underneath arbitrary negations or within arbitrary Boolean subformulas. The proof fixes the truth of every atomic predicate, so it handles these syntactic positions without any additional case assumption.

## 4. One fixed cyclic operation preserves every generic table

### Theorem 4.1 — preservation with no dimension restriction

**PROVED, confidence 0.99.** Fix the single generic certificate \((p_0,c_{p_0})\) from Theorem 1.3, and abbreviate it as \((p,c)\). For every current product space \(L\) and every atom \(a\), the relation \(G_a\) is preserved by the coordinatewise residue mean \(f_p\) on its \(d\) parameter residues and by \(c\) on its finite arguments. The arity \(p\) is fixed with the template and need not exceed \(\dim L\).

**Proof.** Suppose
\[
G_a(r^i,\eta_a^i),\qquad 0\leq i<p.
\]
Set
\[
r^*=p^{-1}\sum_{i=0}^{p-1}r^i\in A^d,\qquad
\eta_a^*=c(\eta_a^0,\ldots,\eta_a^{p-1}).
\tag{4.1}
\]
The operation on finite arguments is coordinatewise according to their sorts.

List all exact affine forms in the output fibre formula \(R_a(\cdot,\eta_a^*)\) whose restrictions to \(L\) are nonzero. Their nonempty zero sets are finitely many proper hyperplanes of \(L\).

Because \(G_a(r^0,\eta_a^0)\) holds, there is a finite exceptional hyperplane list outside which every point of \(U_{r^0}\) satisfies the first input fibre. Apply Lemmas 2.1 and 2.2 to avoid both that input exception list and every output form just listed. This gives
\[
x^0=u+Bt^0\in U_{r^0},\qquad
R_a(x^0,\eta_a^0),
\tag{4.2}
\]
with every listed output form nonzero at \(x^0\). For each index \(i\) with \(1\leq i<p\), use generic acceptance and finite avoidance to choose
\[
x^i=u+Bt^i\in U_{r^i},\qquad
R_a(x^i,\eta_a^i).
\tag{4.3}
\]
These are full assignments of the global integer tuple; the basic relation uses their selected local coordinates.

For coefficient vectors \(\gamma\in W_p\), combine these full assignments blockwise:
\[
z_j(\gamma)=
\sum_{i=0}^{p-1}\gamma_i^{b(j)}x_j^i.
\tag{4.4}
\]
Here \(b(j)\) is the block of coordinate \(j\). Since \(L\) is a product and every coefficient vector sums to \(1\), \(z(\gamma)\in L\). More explicitly, because \(B\) is block diagonal, there is a parameter vector \(t^*(\gamma)\) whose block coordinates are the same affine combinations of the corresponding coordinates of the \(t^i\), and \(z(\gamma)=u+Bt^*(\gamma)\). For allowed integer coefficients, \(t^*(\gamma)\) is integer. Every coefficient has residue \(p^{-1}\) modulo \(m\), so
\[
t^*(\gamma)\equiv p^{-1}\sum_i t^i
\equiv r^*\pmod m.
\]
Therefore every allowed output belongs to \(U_{r^*}\).

For each listed output form \(\ell\), the pullback
\[
\gamma\longmapsto\ell(z(\gamma))
\tag{4.5}
\]
is an affine rational function on \(W_p\). It is nonzero. Indeed, at the rational point where every block coefficient vector is \(e_0=(1,0,\ldots,0)\), the output is \(x^0\), and \(\ell(x^0)\ne0\) by (4.2). This rational evaluation is used only to prove that the affine function is not identically zero. The point \(e_0\) need not satisfy the prescribed coefficient congruences.

The generic certificate applied to the actual relation tuples in (4.2)–(4.3) excludes finitely many proper coefficient hyperplanes and guarantees relation membership outside them. The pullbacks (4.5) exclude finitely many further proper coefficient hyperplanes, ignoring any empty zero sets. By Lemmas 2.1 and 2.2 there is an allowed coefficient tuple outside the union of these exceptions. Its output \(z\) satisfies
\[
R_a(z,\eta_a^*),
\]
belongs to \(U_{r^*}\), and makes every output form nonzero unless that form vanishes identically on \(L\).

Consequently the atomic truth values at this output are exactly the generic truth values from Lemma 3.2: identically zero equations hold, every other exact equation fails, and every congruence has the value prescribed by \(r^*\). The Boolean fibre formula is true at the output, so its generic evaluation is true. Lemma 3.2 gives \(G_a(r^*,\eta_a^*)\), as required.

No step required the \(p\) selected points to span \(L\). The first chosen point detects every relevant nonzero output form, which is sufficient to prove every coefficient pullback nonzero. \(\square\)

## 5. Bounded finite compression and an effective finite solver

### Definition 5.1 — local residues and their actual image

**PROVED, confidence 1.00; definition.** Let \(k_a\) be the number of integer argument positions of atom \(a\), counting repeated positions separately. Select those rows of \(u\) and \(B\), with repetitions, to obtain \(u_a\) and \(B_a\). Define
\[
\Theta_a:A^d\longrightarrow A^{k_a},
\qquad
\Theta_a(r)=u_a+B_ar.
\tag{5.1}
\]
The entries of \(u_a\) and \(B_a\) in this expression are reduced modulo \(m\).

For \(v\in A^{k_a}\), define \(V_a(v,\eta_a)\) by evaluating the fibre formula as follows: replace exact equations by their truth as identities on the full current space \(L\), and evaluate congruences directly at the local integer residues \(v\). Define the finite table
\[
T_a=
\{(v,\eta_a):
v\in\operatorname{im}\Theta_a
\text{ and }V_a(v,\eta_a)\text{ is true}\}.
\tag{5.2}
\]

### Lemma 5.2 — exact bounded compression

**PROVED, confidence 1.00.** The arity of \(T_a\) is bounded by the fixed template. It can be explicitly computed in time polynomial in the input length. For every global residue \(r\) and finite tuple \(\eta_a\),
\[
G_a(r,\eta_a)
\iff
T_a(\Theta_a(r),\eta_a).
\tag{5.3}
\]
The tables \(T_a\) are all preserved by the same residue mean \(f_p\) and finite operations \(c\) from Theorem 4.1.

**Proof.** The first equivalence follows directly from Lemma 3.2: every congruence depends only on the local argument residues, and every exact equation has already been replaced by a value depending only on \(L\) and the finite argument tuple. The actual-image condition is automatically satisfied for \(\Theta_a(r)\).

Let \(v_1,\ldots,v_d\) be the columns of \(B_a\) modulo \(m\), regarded as vectors in \(A^{k_a}\). Compute
\[
H_0=\{0\},\qquad
H_j=\{h+\alpha v_j:
h\in H_{j-1},\ \alpha\in A\}
\quad(1\leq j\leq d).
\tag{5.4}
\]
An induction proves that \(H_j\) is exactly the set of linear combinations of the first \(j\) columns. At \(j=0\) the only empty combination is zero. If the assertion holds at \(j-1\), adjoining an arbitrary coefficient \(\alpha\) of column \(v_j\) gives every combination of the first \(j\) columns and gives no other vector. Therefore
\[
\operatorname{im}\Theta_a=u_a+H_d.
\tag{5.5}
\]
There are at most \(m^{k_a}\) states in any \(H_j\). The number \(k_a\), the modulus \(m\), and all finite carrier sizes are fixed, so each stage of (5.4) has bounded cost and there are \(d\) stages. Enumerating the actual image and all finite argument tuples has bounded total size. For each tuple, testing exact equation identities reduces to checking whether all coefficients and the constant term of its substitution in \(u+Bt\) vanish. Those coefficients have polynomial length and are obtained by polynomially many integer operations. Congruence evaluation and the remaining Boolean evaluation then have polynomial time. This proves computability and the arity bound.

For preservation, take \(p\) tuples
\[
(v^i,\eta_a^i)\in T_a.
\]
By the actual-image condition choose \(r^i\) with \(\Theta_a(r^i)=v^i\). Equation (5.3) gives \(G_a(r^i,\eta_a^i)\). Theorem 4.1 gives generic acceptance at
\[
r^*=f_p(r^0,\ldots,r^{p-1}),\qquad
\eta_a^*=c(\eta_a^0,\ldots,\eta_a^{p-1}).
\]
The affine map \(\Theta_a\) commutes with this mean:
\[
\begin{aligned}
\Theta_a(r^*)
&=u_a+B_a\left(p^{-1}\sum_i r^i\right)\\
&=p^{-1}\sum_i(u_a+B_ar^i)
=f_p(v^0,\ldots,v^{p-1}).
\end{aligned}
\tag{5.6}
\]
The second equality uses \(p^{-1}p=1\) in \(A\). Applying (5.3) to the output proves that the mean and \(c\) preserve \(T_a\).

The actual-image restriction in (5.2) is part of the proof. Without it, an arbitrary accepted local residue tuple might have no global preimage \(r^i\), and the preservation argument would not apply. \(\square\)

### Proposition 5.3 — a polynomial finite decision and search procedure

**PROVED, confidence 0.99, using Bulatov (2017), Theorem 4, condition (2) implying condition (1).** For every current \(L\), the finite instance
\[
F_L^{\mathrm{gen}}(r,\eta)
=
\bigwedge_aG_a(r,\eta_a)
\tag{5.7}
\]
can be decided in polynomial time. If it is satisfiable, a satisfying assignment \((r,\eta)\) can be constructed in polynomial time.

**Proof.** Introduce a local residue tuple \(v_a\) for each atom, impose the table constraint \(T_a(v_a,\eta_a)\), and impose the affine congruences
\[
v_a=u_a+B_ar\pmod m.
\tag{5.8}
\]
By Lemma 5.2, existentially quantifying the new local residue variables gives exactly (5.7). Each row of (5.8) is represented by a chain of finite additions and singleton pins. All coefficients can be reduced to \(0,\ldots,m-1\). A coefficient \(\alpha r_j\) is represented by at most \(m-1\) repeated additions; \(m\) is fixed. Summing the resulting terms uses at most a constant multiple of \(d+1\) auxiliary additions per row. Constants are pinned residue values. Thus the entire expansion has polynomial size.

The finite addition relation on \(A\), every affine equation on \(A\), and every singleton on \(A\) are preserved by the mean \(f_p\). For addition, from \(x_i+y_i=z_i\) for every input row \(i\), multiplying by \(p^{-1}\) and summing gives \(f_p(x)+f_p(y)=f_p(z)\). For a constant pin, \(f_p(a,\ldots,a)=p^{-1}pa=a\). The finite singleton pins are preserved by idempotence of \(c\). Lemma 5.2 proves preservation of every \(T_a\).

These many-sorted relations all belong to one fixed finite language. To make that statement explicit, let \(K\) be a template-dependent upper bound on the arities of the tables, addition, and pins. There are finitely many sort patterns of length at most \(K\), and for each pattern finitely many subsets of the corresponding finite Cartesian product. Retain all such relations preserved by the fixed operation family \((f_p,c)\), and include the finite addition and pins. This defines a finite language independent of the instance. Every table arising above is among those retained relations.

For completeness, convert the many-sorted finite problem into a single-sorted one. Let \(D\) be the direct product of all its finite carriers, including \(A\). For a sorted relation \(T\) whose \(j\)-th position has carrier \(D_j\), define a relation \(\widehat T\) on the same number of \(D\)-valued positions by requiring that the projections to \(D_j\) form a tuple of \(T\). The other coordinates are unrestricted. Give every original sorted variable one \(D\)-valued variable and replace every atom by its cylindrical relation \(\widehat T\). A sorted solution extends to a \(D\)-valued solution by choosing arbitrary values in unused coordinates, since every carrier is nonempty. A \(D\)-valued solution projects to a sorted solution. The two instances are therefore equisatisfiable. The product of \(f_p\) and all the \(c\) operations preserves every \(\widehat T\), because the relevant coordinate of the product output is the corresponding sorted operation applied to the relevant input coordinates.

An idempotent cyclic operation of arity \(p\) is a weak near-unanimity operation: the \(p\) tuples with one occurrence of \(y\) and \(p-1\) occurrences of \(x\) are cyclic rotations of one another, so all their outputs agree; idempotence gives the value \(x\) on the all-\(x\) tuple. Thus the resulting fixed single-sorted finite language has a weak near-unanimity polymorphism. Bulatov (2017), Theorem 4, implication (2) to (1), gives a polynomial-time decision algorithm for its CSP. The transformation and its inverse projection have polynomial size, so they give the claimed finite decision procedure.

To construct a satisfying assignment, first use that procedure to check satisfiability. If it is unsatisfiable, report that fact. Otherwise order the principal variables \(r,\eta\) in any fixed order. For each unassigned variable, enumerate its finite carrier in a fixed order and test the current finite instance with that variable pinned to each candidate value. At least one candidate maintains satisfiability, because the current instance has a solution. Retain the first successful pin and continue. Every carrier size is constant, and every singleton is in the same preserved language. The number of calls is at most a fixed constant times the number of principal variables. Every call concerns an instance of polynomial size. At the end, all principal variables have values extending to a solution of the finite expanded instance. Equivalence with (5.7) proves that these values satisfy \(F_L^{\mathrm{gen}}\). Auxiliary variables need not be returned. This is deterministic polynomial-time search. \(\square\)

### Proposition 5.4 — optional compression by congruence rows

**PROVED, confidence 1.00.** Local integer residues in Definition 5.1 may instead be replaced by the values of a bounded list of congruence rows in the parameter residues. This alternative gives the same relation \(G_a\) and has the same preservation and polynomial-time properties.

**Proof.** For each possible finite tuple of the atom, substitute \(u+Bt\) in every congruence of its fibre formula. A modulus \(e\mid m\) congruence
\[
\lambda(t)+b\equiv0\pmod e
\]
is equivalent to
\[
(m/e)\lambda(t)+(m/e)b\equiv0\pmod m.
\]
Collect the homogeneous linear rows \((m/e)\lambda\) for all finite tuples and all congruence occurrences in a matrix \(C_a\). Their number is bounded because the template and finite carriers are fixed. Exact equations contribute no rows: after generic evaluation their truth is independent of \(r\). The Boolean evaluation in Lemma 3.2 depends on \(r\) only through \(C_ar\), the known affine constants, and the finite tuple.

Define the row table as the image of \(G_a\) under
\[
(r,\eta_a)\longmapsto(C_ar,\eta_a).
\]
Because membership in \(G_a\) is constant on fibres of this map, pulling the table back recovers exactly \(G_a\). Its actual image is computed by the column-generation procedure (5.4), with the bounded number of rows replacing \(k_a\). The mean commutes with the linear map \(C_a\), so the proof of preservation in Lemma 5.2 applies directly after deleting the constant term \(u_a\). Every subsequent finite encoding uses linear row equations of the same type as (5.8). Consequently both constructions describe and solve the identical global finite generic-acceptance relation. \(\square\)

## 6. A stable decision state has a simultaneous generic solution

### Definition 6.1 — stability

**PROVED, confidence 1.00; definition.** A current state is stable if \(F_L\) from (1.3) is satisfiable and
\[
\operatorname{aff}_{\mathbb Q}X_a=L
\]
for every atom \(a\), with \(X_a\) defined in (1.4).

### Theorem 6.2 — generic acceptance at a stable state

**PROVED, confidence 0.99.** At every stable state, \(F_L^{\mathrm{gen}}\) is satisfiable.

**Proof.** If there are no atoms \(a\), the conjunction defining \(F_L^{\mathrm{gen}}\) is empty. Choose any residue vector and choose any values for the unconstrained finite variables; every finite carrier is nonempty. This gives a solution.

Suppose at least one atom occurs. For each \(a\), stability gives a finite list of at most \(\dim L+1\) points of \(X_a\) which affinely spans \(L\). To justify this bound, begin with one point of the nonempty set \(X_a\). If its current affine span is proper in \(L\), the equality \(\operatorname{aff}X_a=L\) supplies a point of \(X_a\) outside that span. Appending the point strictly increases the dimension of the span. After at most \(\dim L\) appendings the span is \(L\).

For every chosen point \(u+Bt\in X_a\), Definition (1.4) supplies a finite assignment \(\eta\) with \(F_L(q_m(t),\eta)\) true and with the atom \(R_a(u+Bt,\eta_a)\) true. Collect all these finite solutions of \(F_L\) in one list, reserving a separate row for each chosen spanning point of each atom. The list is nonempty.

Choose a sufficiently large prime \(q\) for which the generic certificate exists, with \(q\) greater than the number of reserved rows. Such a prime exists: there are infinitely many primes, since if a finite list contained all of them then a prime divisor of one plus their product would not belong to the list. Every sufficiently large prime meets the threshold in Theorem 1.3 and avoids the finitely many prime divisors of \(m\). Pad the list to \(q\) rows by repetitions of any one finite solution of \(F_L\). Write the rows as \((r^i,\eta^i)\), \(0\leq i<q\).

For each atom \(a\) and each row \(i\), the exact relation \(P_a(r^i,\eta_a^i)\) supplies an actual point
\[
x_a^i=u+Bt_a^i\in U_{r^i}
\]
satisfying \(R_a(x_a^i,\eta_a^i)\). On a row reserved for a chosen spanning point of \(X_a\), choose precisely that point. Consequently, for every atom \(a\), the list \(x_a^0,\ldots,x_a^{q-1}\) affinely spans \(L\).

Define the common residue and common finite assignment
\[
r^*=q^{-1}\sum_{i=0}^{q-1}r^i,\qquad
\eta^*=c_q(\eta^0,\ldots,\eta^{q-1}).
\tag{6.1}
\]
Fix one atom \(a\). The rational affine map from \(W_q\) to \(L\) which sends its block coefficient vectors to the blockwise combination of \(x_a^0,\ldots,x_a^{q-1}\) is surjective. Indeed, their projected lists affinely span the projection of \(L\) onto each block, because projecting an affine spanning expression projects its affine combination and its coefficients. In a given block, arbitrary coefficient vectors whose sum is \(1\) therefore produce every point of that block's affine factor. Coefficients in distinct blocks are independent, and \(L\) is the product of those factors. Choosing a producing coefficient vector in each block produces every point of \(L\).

Every allowed integer coefficient tuple gives a point of \(U_{r^*}\), by the block-diagonal parametrization and the residue calculation already used in Theorem 4.1. Suppose for contradiction that \(G_a(r^*,\eta_a^*)\) were false. Lemma 3.2 then places every point of this output fibre within \(U_{r^*}\) in finitely many proper affine hyperplanes of \(L\). The pullback of the affine equation of each such hyperplane is nonzero on \(W_q\), because the coefficient map is surjective onto \(L\). Thus the pullbacks have proper or empty zero sets. Generic preservation for this fixed list of actual relation tuples excludes finitely many further proper hyperplanes of \(W_q\). Lemmas 2.1 and 2.2 give an allowed coefficient tuple outside both exception families. Its output belongs to the relation by generic preservation, belongs to \(U_{r^*}\), and lies outside every hyperplane which was asserted to contain that output fibre. This is a contradiction.

Therefore \(G_a(r^*,\eta_a^*)\) holds. The same residue vector \(r^*\) and the same full finite assignment \(\eta^*\) were used for every atom, so they satisfy \(F_L^{\mathrm{gen}}\).

The prime \(q\) in this proof may grow with the instance. It is used only to establish the existence of a generic finite solution. The actual finite solver of Proposition 5.3 uses the single fixed certificate of arity \(p_0\); it does not construct \(c_q\) or enumerate a table of arity \(q\). \(\square\)

## 7. Explicit integer witness construction

### Theorem 7.1 — a generic finite solution yields a polynomial-size integer witness

**PROVED, confidence 0.99.** Given the current data \(u,B\) and a solution \((r,\eta)\) of \(F_L^{\mathrm{gen}}\), one can construct a satisfying assignment of the original pp-instance in deterministic polynomial time. Every returned integer has polynomial binary length.

**Proof.** Choose the canonical lift
\[
\rho\in\{0,\ldots,m-1\}^d
\]
of \(r\). For each atom \(a\), use its chosen finite tuple \(\eta_a\) and list every exact affine form in the supplied fibre formula whose restriction to \(L\) is nonzero. Repetitions may remain. Let the total number of forms be \(H\). Because every basic fibre formula is fixed, \(H\) is bounded by a template-dependent constant times the number of atom occurrences.

Substitute
\[
x=u+B(\rho+mz)
\tag{7.1}
\]
into all listed forms. This gives affine polynomials
\[
h_\nu(z)=b_\nu+\sum_{j=1}^d a_{\nu j}z_j,
\qquad 1\leq \nu\leq H.
\tag{7.2}
\]
Every \(h_\nu\) is nonzero: if it were zero as a polynomial, the original form would vanish on all of \(U_r\), whose affine hull is \(L\) by Lemma 2.2, and hence would vanish identically on \(L\), contrary to its selection.

If \(d=0\), every polynomial (7.2) is a nonzero constant, and there are no parameter choices to make. Output \(x=u\). If \(H=0\), there are no forms to avoid; choose \(z=0\). These cases already give the required generic truth pattern.

For \(d\geq1\) and \(H\geq1\), test in increasing order the integers
\[
s\in\{0,1,\ldots,Hd\}
\]
at the parameter vector
\[
z(s)=(s,s^2,\ldots,s^d).
\tag{7.3}
\]
For each \(\nu\),
\[
h_\nu(z(s))=
b_\nu+\sum_{j=1}^d a_{\nu j}s^j
\tag{7.4}
\]
is a nonzero polynomial in \(s\). Its coefficients occur at distinct degrees \(0,1,\ldots,d\), and at least one coefficient is nonzero by (7.2). The powers in (7.3) start at \(1\); this prevents any coordinate term from being merged with the constant coefficient. Every polynomial has at most \(d\) roots. The union of the root sets of all \(H\) polynomials has at most \(Hd\) elements. Among the \(Hd+1\) tested integers there is therefore an \(s\) at which every polynomial is nonzero. Choose the first such \(s\) and define \(x\) by (7.1).

This \(x\) lies in \(U_r\), so every congruence has the value used in the generic evaluation. Every equation which vanishes identically on \(L\) holds at \(x\). Every other exact equation fails, because its defining affine form was listed and is nonzero at the chosen point. Thus every atomic predicate in every selected fibre has exactly its generic truth value from Lemma 3.2. Since \(G_a(r,\eta_a)\) is true for each atom, each whole Boolean fibre formula evaluates to true at \(x\). The retained arithmetic equations hold because \(x\in L_{\mathbb Z}\). Together with the finite assignment \(\eta\), this is a satisfying assignment of the original instance.

It remains to prove polynomial running time and output length. Let \(L_0\geq1\) bound the binary lengths of the entries of \(u\) and \(B\). By Theorem 1.3, \(L_0\) is polynomial in the input length. Every coefficient in (7.2) is obtained by substituting a bounded-arity, fixed-coefficient form into \(u+B(\rho+mz)\). Its binary length is therefore polynomial in the input length. There are polynomially many such coefficients and \(H=O(\text{input length})\).

There are \(Hd+1\) trials, which is polynomial because \(d\leq n\), the number of integer input variables. At each trial the integers \(s^j\) have binary length at most
\[
1+j\log_2(Hd+1)\leq 1+d\log_2(Hd+1).
\]
They can be computed by \(d\) successive multiplications, and every polynomial (7.4) can be evaluated by repeated multiplication and addition. Integer addition and the school multiplication algorithm take polynomial time in the operand bit lengths, so the entire search has polynomial bit complexity.

For a concrete output bound, set \(S=\max(1,Hd)\). The selected coordinates satisfy \(|z_j|\leq S^d\). Since \(0\leq\rho_j\leq m-1\), the output coordinates obey
\[
|x_i|
\leq
2^{L_0}
+d\,2^{L_0}\bigl(m-1+mS^d\bigr).
\tag{7.5}
\]
It follows that their signed binary lengths are at most
\[
L_0+
O\!\left(
\log(d+1)+\log m+d\log(Hd+1)
\right).
\tag{7.6}
\]
When \(d=0\) or \(H=0\), the separately specified choices give an equal or smaller polynomial bound. The modulus \(m\) is fixed, so (7.6) is polynomial in the input length. This proves both the complexity and the witness-size claims. \(\square\)

## 8. The complete search algorithm, with early acceptance

### Theorem 8.1 — polynomial search with acceptance at the first successful generic test

**PROVED, confidence 0.98.** Under \(Q\), in the finite-signature setting of Definition 1.1, the following algorithm either returns a satisfying assignment or correctly reports that the pp-instance is unsatisfiable. Its running time and its output bit length are polynomial in the input length.

1. Initialize the stored equation system with the explicit arithmetic equations and pins. Compute its integer solution set. If it is empty, report unsatisfiable.
2. Compute the blockwise parametrization \(L_{\mathbb Z}=u+B\mathbb Z^d\).
3. Construct the generic finite instance \(F_L^{\mathrm{gen}}\) by the bounded tables of Section 5.
4. If it is satisfiable, use Proposition 5.3 to obtain \((r,\eta)\), use Theorem 7.1 to construct the integer tuple, and return the resulting full assignment.
5. If \(F_L^{\mathrm{gen}}\) is unsatisfiable, run the exact finite-relaxation procedure for \(F_L\). If \(F_L\) is unsatisfiable, report unsatisfiable.
6. Otherwise compute the supported affine hulls \(\operatorname{aff}X_a\). Choose one that is proper in \(L\), refine by the original-cell equation procedure, and return to step 2.

**Proof.** The initial arithmetic equations are necessary for every actual solution. An empty initial integer solution set therefore proves unsatisfiability. At every refinement, Theorem 1.3 preserves all actual solutions, and the current \(L\) stays a product with a polynomial-size integer parametrization.

Any acceptance in step 4 is correct by Theorem 7.1, which constructs an actual satisfying assignment from generic finite acceptance at any current \(L\). Stability is not required for this direction.

If step 5 rejects because \(F_L\) is unsatisfiable, there can be no actual solution retained in \(L\). Indeed, an actual solution \(x=u+Bt\) with finite assignment \(\eta\) would satisfy every \(P_a(q_m(t),\eta_a)\) by using \(t\) itself as the existential witness in (1.2), and hence would satisfy \(F_L\). Therefore such rejection is correct.

Suppose step 6 is reached. The finite relaxation \(F_L\) is satisfiable. If every supported affine hull were \(L\), the state would be stable. Theorem 6.2 would then imply that \(F_L^{\mathrm{gen}}\) is satisfiable, contrary to the unsuccessful test in step 4. Hence at least one proper supported affine hull exists. The refinement requested in step 6 is therefore always available when needed. Theorem 1.3 supplies that refinement and its invariant preservation. If its integer solution set is empty, the retained-solution invariant proves unsatisfiability; otherwise the next iteration proceeds.

Every refinement strictly lowers the nonnegative integer \(\dim L\), initially at most \(n\). There are at most \(n\) refinements. At a zero-dimensional nonempty state, no nonempty supported set has a proper affine hull. Thus, if the algorithm has not rejected, Theorem 6.2 ensures that it accepts; the loop cannot become stuck.

Every iteration uses polynomial-time parametrization, finite table construction, finite CSP calls, and, when necessary, the imported polynomial-time exact relaxation and hull computation. The stored equations remain drawn from the original finite list, so their coefficients and all derived parametrizations have polynomial bit length throughout. There are at most \(n+1\) iterations and polynomially many solver calls within each. Theorem 7.1 bounds the final witness length and its construction time.

This proves total correctness and polynomial complexity. Because step 4 precedes further hull refinement, the algorithm stops at the first current affine space at which generic finite acceptance is satisfiable. \(\square\)

### Corollary 8.2 — search does not require a strict polymorphism

**PROVED, confidence 1.00.** The search construction does not assert or require that the final integer assignment is obtained by one fixed polymorphism of \(\mathcal M\).

**Proof.** The finite solver produces a residue and finite assignment using a fixed finite cyclic polymorphism only on the bounded auxiliary finite tables. The integer construction then chooses \(s\) after inspecting all exact affine forms of the particular input instance, and forms the instance-dependent point (7.1). Different instances or finite assignments may choose different \(s\), \(u\), \(B\), and \(\rho\). Generic certificates are used to establish preservation of the auxiliary tables and existence at stable states; they do not supply a fixed strict operation on the original infinite structure. Therefore no strict polymorphism assertion enters any step of the algorithm or its proof. \(\square\)

## 9. Extension of prescribed partial assignments

### Lemma 9.1 — binary integer constants have short pp pin constructions

**PROVED, confidence 1.00.** In an integer sort with addition and the singleton \(1\), the equation \(x=a\), for an integer \(a\) supplied in binary, has a pp implementation using \(O(1+\log(|a|+1))\) atoms and auxiliary variables.

**Proof.** Let \(o\) be a variable pinned to \(1\). A zero variable \(z\) is defined by the addition atom \(z+o=o\), whose unique integer solution is \(z=0\).

For \(a=0\), identify \(x\) with \(z\), or add the equality \(x=z\). For a positive integer \(a\), read its binary expansion from the leading \(1\). Initialize a current variable \(v\) to \(o\). For every subsequent bit, introduce a variable \(w\) and require \(v+v=w\). If the bit is zero, replace the current variable by \(w\). If the bit is one, introduce a variable \(v'\), require \(w+o=v'\), and replace the current variable by \(v'\). After processing each bit, induction on the number of processed bits shows that the current value is the integer represented by that binary prefix: appending a zero doubles the preceding prefix, and appending a one doubles it and adds one. At the end, identify \(x\) with the final current variable. Every bit uses at most two addition atoms and at most two new variables.

For negative \(a\), first construct a variable \(v\) equal to the positive integer \(|a|\) by that procedure, and impose \(x+v=z\). This forces \(x=-|a|=a\). Every introduced variable is existential. The construction has one pinned variable \(o\), one zero equation, at most two atoms per binary digit, and at most one final additive-inverse equation. Its size has the asserted bound. \(\square\)

### Corollary 9.2 — polynomial-time completion under finite and integer pins

**PROVED, confidence 0.99.** Given a pp-instance together with any prescribed values of some integer variables in binary and of some finite variables, one can decide in polynomial time whether the partial assignment extends to a full solution. If it does, a full extension of polynomial bit length can be returned. The polynomial is measured in the instance length plus the binary lengths of the prescribed integers.

**Proof.** Add each finite pin as a singleton constraint. These pins belong to the working expansion and are preserved by the idempotent finite operations. Implement every integer pin by Lemma 9.1. The expanded pp-instance has length polynomial, in fact linear up to a template-dependent factor, in the original length plus all supplied binary lengths.

Every extension of the partial assignment satisfies these additional constraints, by assigning their explicitly constructed intermediate sums their forced integer values. Conversely, every solution of the expanded instance has every pinned original variable equal to its prescribed value, because the constructions in Lemma 9.1 have exactly those outputs and the finite pins are singletons. Thus the expanded instance is satisfiable exactly when the requested extension exists.

Apply Theorem 8.1 to that expanded instance. If it is unsatisfiable, report that no extension exists. If it is satisfiable, restrict the returned assignment to the original variables. It is a full solution extending the prescribed values. The polynomial runtime and witness-length bounds are polynomial in the expanded length, hence in the stated input size. Conflicting pins are covered: their expanded constraints are jointly satisfiable only if the prescribed values agree, and the same solver detects a conflict. \(\square\)

### Corollary 9.3 — a polynomial bound for a finite sequence of pin updates

**PROVED, confidence 1.00.** For a finite sequence of additional finite or binary integer pins, the extension question after every update can be answered, with witnesses when they exist, in total polynomial time in the total size of the original instance and the entire update sequence.

**Proof.** After each update, apply Corollary 9.2 to the original instance with all pins supplied so far. If \(T\) is the number of updates and \(L\) is the total encoding length, then every prefix has length at most \(L\), and \(T\leq L\) under any encoding which records at least one symbol per update. If one call takes at most \(P(L)\) time for a fixed polynomial \(P\), all calls together take at most \(L P(L)\), again a polynomial. Each returned witness has the polynomial length bound from Corollary 9.2. This is a bound for rerunning the algorithm on prefixes; no stronger amortized data-structure guarantee is asserted. \(\square\)

## 10. Exact computational specification

### Proposition 10.1 — reproducibility and what was, and was not, enumerated

**PROVED, confidence 1.00.** The search theorem does not depend on a bounded empirical enumeration. The following finite constructions specify the algorithm completely.

1. The template supplies fixed fibre formulas and the fixed modulus \(m\). The earlier finite certificate procedure supplies the block partition, one prime \(p_0\), and the operations \(c_{p_0}\).
2. Each current integer equality system is solved by the polynomial normal-form procedure stated in Theorem 1.3. It yields the exact \(u,B\), not an approximation.
3. For every atom, enumerate the local residue image by (5.4), starting at the singleton zero vector, processing parameter columns in their given order, and iterating scalars in the order \(0,\ldots,m-1\). Remove duplicates by exact equality of finite residue vectors.
4. For every attained local residue tuple and every finite argument tuple, evaluate the explicit generic Boolean formula of Lemma 3.2. These evaluations give the complete finite table \(T_a\).
5. Solve the finite instance with those tables and the affine residue equations. Construct principal variable values by the first-successful-value self-reduction in Proposition 5.3.
6. List exact forms in atom order and formula occurrence order. Test \(s=0,1,\ldots,Hd\) in that order, with exact integer evaluation of (7.4), and return the first successful point.
7. If the generic finite instance is unsatisfiable, apply the completely specified exact supported-hull refinement procedure in the earlier chapter and repeat.

**Proof.** Steps 1–2 are the specified imported preprocessing and arithmetic procedures. Lemma 5.2 proves the exactness, bounded table size, and termination of steps 3–4. Proposition 5.3 proves correctness and polynomial cost of step 5, including its choice order. Theorem 7.1 proves the finite guaranteed range and exact correctness of step 6. Theorem 8.1 proves that step 7 can be repeated at most \(n\) times, is available whenever needed, and preserves all actual solutions. Thus the listed computations are a finite exact algorithm, with no numerical tolerances or unverified search cutoff.

No enumeration of small moduli or small instance dimensions is used to establish the theorem. The only finite state enumeration in this new construction is the explicitly bounded local-residue image and table enumeration. The proof of correctness covers all input dimensions and all instances. \(\square\)

## 11. Precise references and dependency boundaries

**PROVED, confidence 1.00; reference record.**

- Andrei A. Bulatov, 2017. *A Dichotomy Theorem for Nonuniform CSPs*. Proceedings of the 58th IEEE Symposium on Foundations of Computer Science, pages 319–330. **Theorem 4, implication (2) to (1)**: the finite weak-near-unanimity condition implies polynomial-time solvability. DOI: 10.1109/FOCS.2017.37. Author PDF: https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf. This is the only external theorem applied directly in the new finite solver proof.
- Ravi Kannan and Achim Bachem, 1979. *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*. SIAM Journal on Computing 8(4), pages 499–507. **Theorem 2 and Lemma 3**. DOI: 10.1137/0208040. Used through the fully written rectangular reduction in Lemma 2.2 of the preceding general-algorithm chapter.
- Libor Barto and Marcin Kozik, 2012. *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*. Logical Methods in Computer Science 8(1), article 7. **Theorem 4.1**. Authoritative article PDF: https://lmcs.episciences.org/673/pdf. Used in the preceding finite-certificate amplification theorem; no extra cyclic-arity assertion is invoked in this new chapter beyond Theorem 1.3.

The local theorem references in Section 1 identify proofs included in the cumulative package. This chapter strengthens their decision result to a constructive search result. It does not claim a new proof of the original shared-coefficient Conjecture N, and it does not replace the previously identified distinction between shared and independent integer blocks.

## 12. Adversarial self-audit

### Audit 12.1 — the most delicate new step

**PROVED, confidence 0.99.** The most delicate new step is preservation of \(G_a\) by one fixed arity \(p_0\) while the affine dimension of an instance is unbounded.

The incorrect shortcut would be to choose \(p_0\) actual points whose affine hull is the entire current space. That is impossible in general when \(\dim L\geq p_0\). Theorem 4.1 uses a different argument: after computing the output finite tuple, it chooses just the first actual input point to avoid every exact output form which is nonzero on \(L\). Such a point exists because the first input slice is generic and full. Rational projection to this point proves each output-form pullback nonzero. The full allowed coefficient lattice can then avoid their finitely many zero sets simultaneously.

This proof explicitly uses that \(G_a\) means generic truth on a full residue lattice, not merely nonemptiness of the fibre. If that hypothesis were weakened to nonemptiness, the specially selected first input point could fail to exist, and the proof would break at (4.2). The present definition and Lemma 3.2 give precisely the required stronger hypothesis.

### Audit 12.2 — the actual-image restriction

**PROVED, confidence 1.00.** The tables in Section 5 must discard local residue tuples outside \(\operatorname{im}\Theta_a\).

The finite operation preservation proof lifts each table input to a global parameter residue. The column-generation construction computes exactly the attainable set, so every retained tuple has such a lift. Without that condition, a locally acceptable Boolean type could have no globally attainable parameter residue. Its inclusion would have no preservation proof. The explicit actual-image condition in (5.2) closes this gap.

### Audit 12.3 — existence versus computation at large prime arity

**PROVED, confidence 0.99.** The stable-state existence proof uses a possibly large prime \(q\), while the computational finite solver uses only the fixed prime \(p_0\).

Constructing the full table of \(c_q\) would not have a polynomial bound in the instance size merely from the existence theorem. The algorithm never does that. Theorem 6.2 proves that the bounded-arity finite generic instance has a solution; Proposition 5.3 finds that solution using preservation by \(c_{p_0}\). The distinct roles of the two primes are stated in both proofs. If the prior all-prime generic theorem were false, stable-state existence could fail; the fixed-arity closure theorem and the direct witness construction would still remain valid under their stated hypotheses, but completeness of the full refinement algorithm would no longer follow.

### Audit 12.4 — coefficient and witness sizes

**PROVED, confidence 0.99.** Polynomial arithmetic size depends on the earlier original-equation refinement invariant.

An arbitrary sequence of chosen equations with uncontrolled coefficients could cause uncontrolled growth in a parametrization. The imported refinement theorem stores only original positive equality rows, so its polynomial HNF bounds apply uniformly over all iterations. After that, the moment-curve construction adds at most \(O(d\log(Hd+1))\) bits per parameter coordinate and the explicit bound (7.6) controls the output. If that inherited invariant failed, the new moment-curve construction would remain polynomial in the supplied \(u,B\), but the overall polynomial bound in the original instance length would need a separate proof.

### Audit 12.5 — confidence and scope

**PROVED, confidence 0.98.** The new theorem is a complete constructive consequence of the preceding block-generic classification and refinement theorem. The key fixed-arity closure argument, finite compression, self-reduction, and moment-curve witness construction have also been checked independently in the companion audit chapter. There are no conjectural steps in this extension. Its scope is the finite-signature, equality/congruence fibre setting in Definition 1.1, together with the actual arithmetic and block hypotheses stated there. It does not assert the same algorithm for order inequalities, infinite signatures presented without an effective finite bound, or integer sorts lacking the arithmetic assumed by the imported theorem.

---

# Chapter II — Exact integer avoidance and size bounds

**PROVED — confidence 0.99.** A finite list of proper affine zero conditions on an explicitly parametrized integer affine coset can be avoided deterministically in polynomial time, with an explicit polynomial bound on the binary length of the returned point. The construction is elementary: substitute a moment curve into the free integer parameters and inspect a bounded interval of integer values.

This note supplies the constructive step required after the finite part of the labelled additive-integer CSP algorithm has selected a common finite assignment and residue class. It also proves polynomial-size integer witnesses for satisfiable finite Boolean combinations of affine equations and congruences, without assuming \(Q\). That latter statement is a witness-size result, not a polynomial-time method for choosing a satisfiable Boolean branch.

## 1. Exact input model and definitions

**Definition 1 — PROVED, confidence 1.00; notation.** Let \(n,d,h\) be nonnegative integers. Let

\[
u\in\mathbb Z^n,\qquad
B\in\mathbb Z^{n\times d},\qquad
m\in\mathbb Z_{>0},\qquad
\rho\in\mathbb Z^d.
\]

Consider the nonempty affine integer coset

\[
U=u+B(\rho+m\mathbb Z^d)
  =\{u+B\rho+mBz:z\in\mathbb Z^d\}.
\tag{1.1}
\]

The matrix \(B\) need not have independent columns for the avoidance theorem. It will have independent columns in the CSP application. Its entries, the entries of \(u,\rho\), and \(m\) are given in binary.

For \(1\le j\le h\), let

\[
\ell_j(x)=b_j+\sum_{k=1}^n a_{jk}x_k
\tag{1.2}
\]

be an affine form with integer coefficients given in binary. A rational-coefficient form may first be multiplied by the product of the positive denominators of its coefficients. This multiplication does not change its zero set. The product has binary length at most the sum of the denominator lengths, so clearing denominators preserves polynomial encoding length.

An affine form is **proper on \(U\)** when it is nonzero at some point of \(U\), or equivalently when it does not vanish identically there. Its zero set on \(U\) may be empty; that case causes no difficulty.

The required task is to find \(x\in U\) with

\[
\ell_j(x)\ne0\quad\text{for every }1\le j\le h,
\tag{1.3}
\]

or to certify that some listed form vanishes identically on \(U\), in which case (1.3) is impossible.

## 2. Pullback to free integer parameters

### Lemma 2 — PROVED, confidence 1.00

Put \(x_0=u+B\rho\). The pullback of \(\ell_j\) through (1.1) is

\[
L_j(z)=c_j+\sum_{i=1}^d v_{ji}z_i,
\qquad
c_j=\ell_j(x_0),
\qquad
v_{ji}=m\sum_{k=1}^n a_{jk}B_{ki}.
\tag{2.1}
\]

The form \(\ell_j\) vanishes identically on \(U\) if and only if

\[
c_j=0\quad\text{and}\quad v_{j1}=\cdots=v_{jd}=0.
\tag{2.2}
\]

**Proof.** Substitute \(x=x_0+mBz\) into (1.2) and distribute the finite sums. This gives (2.1). If all the displayed coefficients are zero, the pullback is zero for every integer \(z\), so the form vanishes on \(U\). Conversely, if it vanishes on \(U\), evaluate the pullback first at \(z=0\), which gives \(c_j=0\), and then at each integer unit vector \(z=e_i\), which gives \(c_j+v_{ji}=0\), hence \(v_{ji}=0\). This proves both directions. \(\square\)

In dimension \(d=0\), the coefficient list is empty and the condition says simply \(\ell_j(u)=0\). The coset then consists of the single point \(u\).

## 3. The explicit moment-curve construction

### Lemma 3 — PROVED, confidence 1.00

A nonzero univariate polynomial over \(\mathbb Q\) of degree at most \(d\) has at most \(d\) distinct roots.

**Proof.** A nonzero polynomial of degree zero has no roots. If \(a\) is a root of a positive-degree polynomial \(P\), polynomial division gives \(P(T)=(T-a)Q(T)\), because the remainder is the constant \(P(a)=0\). Every root of \(P\) different from \(a\) is a root of \(Q\), whose degree is one less. Induction on degree proves the stated bound. \(\square\)

### Theorem 4 — PROVED, confidence 1.00

Assume every \(\ell_j\) is proper on \(U\). There is an integer

\[
T\in\{0,1,\ldots,hd\}
\tag{3.1}
\]

such that

\[
x=u+B\rho+mB(T,T^2,\ldots,T^d)^{\mathsf T}
\tag{3.2}
\]

satisfies every required disequality (1.3). The first such \(T\) in increasing order is found by a deterministic polynomial-time algorithm.

**Proof.** By Lemma 2, every affine pullback \(L_j\) is nonzero. Substitute

\[
z_i=T^i\qquad(1\le i\le d)
\]

to obtain

\[
P_j(T)=c_j+\sum_{i=1}^d v_{ji}T^i.
\tag{3.3}
\]

The powers \(1,T,T^2,\ldots,T^d\) have distinct degrees. Therefore the polynomial (3.3) is identically zero exactly when all its coefficients are zero. Lemma 2 excludes that possibility. Each \(P_j\) has degree at most \(d\), so Lemma 3 gives at most \(d\) roots. The union of the root sets of the \(h\) polynomials contains at most \(hd\) integers. The interval (3.1) contains \(hd+1\) integers, so one of them makes every \(P_j\) nonzero.

For this \(T\), formula (3.2) is of the form (1.1), and (2.1) gives

\[
\ell_j(x)=P_j(T)\ne0.
\]

To find the first such \(T\), compute the coefficients in (2.1), then evaluate (3.3) for \(T=0,1,\ldots,hd\), stopping when all values are nonzero. Horner evaluation uses at most \(d\) integer multiplications and additions for one polynomial at one candidate. The coefficient computation has polynomially many arithmetic operations, and there are only \((hd+1)h\) polynomial evaluations. Section 4 proves polynomial bit bounds for every integer involved, establishing polynomial running time in binary encoding.

If \(h=0\), there are no conditions: \(T=0\) and \(x=u+B\rho\) work. If \(d=0\), each proper pullback is a nonzero constant and the same sole candidate \(T=0\) returns \(u\). Thus (3.1) and (3.2), interpreted with empty vectors when appropriate, cover those cases as well. \(\square\)

### Algorithm 5 — PROVED, confidence 1.00

The complete avoidance procedure is:

```text
Input: u, B, positive m, rho, and affine forms ell_1,...,ell_h.

1. Compute x0 = u + B rho.
2. For each j compute c_j = ell_j(x0)
   and the row v_j = m a_j B.
3. If some c_j and all entries of v_j are zero,
   return NO_POINT, with that index j as certificate.
4. For T = 0,1,...,h*d, in this order:
       Evaluate each P_j(T) = c_j + sum_i v_ji T^i by Horner's rule.
       If every value is nonzero:
           Compute z = (T,T^2,...,T^d).
           Return x0 + m B z.
```

**Proof of correctness.** Step 3 is justified by Lemma 2: its displayed zero coefficient row proves that the indexed form vanishes at every point of \(U\), so no point meets all disequalities. If step 3 does not occur, Theorem 4 ensures that step 4 returns a point before its loop ends. Substitution verifies both membership in \(U\) and all disequalities. No other output is possible. \(\square\)

The algorithm never expands the product \(\prod_jP_j\). It evaluates each short coefficient list directly.

## 4. Explicit output and intermediate bit bounds

### Proposition 6 — PROVED, confidence 1.00

Suppose \(0\le\rho_i<m\) for each \(i\), and write

\[
U_0=\max_k|u_k|,
\qquad
B_0=\max_{k,i}|B_{ki}|,
\qquad
M=\max(1,hd).
\]

Empty maxima are interpreted as zero. The output of Algorithm 5 satisfies

\[
\|x\|_\infty
\le U_0+dB_0\bigl(m-1+mM^d\bigr)
\le U_0+2dmB_0M^d.
\tag{4.1}
\]

The second inequality is also valid when \(d=0\), since both added terms are then zero.

If \(|u_k|<2^b\) and \(|B_{ki}|<2^b\) for an integer \(b\ge1\), the signed binary length

\[
\operatorname{len}_{\pm}(a)=1+\left\lceil\log_2(1+|a|)\right\rceil
\]

of each output coordinate is at most

\[
b+2+\left\lceil\log_2(1+2dm)\right\rceil
+d\left\lceil\log_2M\right\rceil.
\tag{4.2}
\]

**Proof.** Algorithm 5 chooses \(0\le T\le hd\). For \(1\le i\le d\), therefore \(|T^i|\le M^d\). Each coordinate of \(B\rho\) has absolute value at most \(dB_0(m-1)\), and each coordinate of \(mB(T,\ldots,T^d)^{\mathsf T}\) has absolute value at most \(mdB_0M^d\). This gives the first inequality in (4.1). Since \(m-1\le m\) and \(M^d\ge1\), the second follows.

With the stated bit bounds, the right side of (4.1) is less than

\[
2^b\bigl(1+2dmM^d\bigr)
\le 2^b(1+2dm)M^d.
\]

Adding one to this positive bound increases its base-two logarithmic bound by at most one. Adding the sign bit and rounding each logarithmic term upward yields (4.2). In dimension zero the output is \(u\), and the same formula is a valid upper bound. \(\square\)

If \(\rho\) is not given in canonical form, it may be reduced coordinatewise modulo \(m\): the coset (1.1) is unchanged, since changing \(\rho\) by \(m\) times an integer vector is absorbed into \(z\). Therefore the canonical-residue hypothesis entails no restriction.

### Proposition 7 — PROVED, confidence 0.99

Algorithm 5 has polynomial bit complexity in the complete binary input encoding. This assertion includes the values tested at candidates that are rejected.

**Proof.** Let \(L\ge1\) bound the binary lengths of all input integers. The number of integers in the input bounds the explicitly supplied dimensions \(n,d,h\), apart from empty arrays, whose declared dimensions are treated directly by the boundary cases already proved.

Computing \(x_0=u+B\rho\) uses \(O(nd)\) integer products and additions. Its coordinate magnitudes are bounded by \(2^L+d2^{2L}\). Computing all \(c_j\) and \(v_{ji}\) then uses \(O(hnd+hn)\) products and additions. Formula (2.1) bounds their binary lengths by

\[
3L+O\bigl(\log(n+1)+\log(d+1)\bigr).
\tag{4.3}
\]

This bound also follows by multiplying the displayed magnitude bounds: a coefficient \(v_{ji}\) is a sum of \(n\) products followed by multiplication by \(m\), and \(c_j\) is the sum of an input constant and \(n\) products involving \(x_0\).

Let \(C\) be the maximum absolute value of the computed coefficients \(c_j,v_{ji}\). At every candidate \(T\) in the loop, \(|T|\le M\). A polynomial value and every partial Horner value have magnitude at most

\[
(d+1)\max(1,C)M^d.
\tag{4.4}
\]

Indeed, a partial Horner value is a sum of at most \(d+1\) coefficient terms, each with absolute value at most \(CM^d\). Its binary length is consequently bounded by the coefficient bound (4.3), plus \(O(\log(d+1)+d\log M)\). Intermediate products before the next addition have the same form with at most one additional factor \(M\), so they have polynomial binary length too.

There are at most \((hd+1)hd\) Horner multiplication-and-addition pairs. Computing the powers in the returned vector needs at most \(d\) further multiplications, and constructing the output needs \(O(nd)\) products and additions. Addition and multiplication of integers with polynomial binary length are polynomial-time operations by their direct digit algorithms. Thus both the operation count and every operand length are polynomial in the input length, proving the claim. \(\square\)

The numerical value \(T^d\) may be large. Its binary length is only \(O(d\log(hd+1))\), which is the quantity relevant to polynomial-time output.

## 5. Constructing a generic Boolean-fibre point

### Proposition 8 — PROVED, confidence 0.99

Suppose one finite assignment \(\eta^*\) and one residue vector \(\rho\) have been chosen so that every input atom's fibre is generically true on

\[
U=u+B(\rho+m\mathbb Z^d),
\]

where all fibre congruence moduli divide \(m\). Then a single actual integer assignment satisfying every atom can be computed in polynomial time, with the bound (4.2), using only the supplied fibre formulas and \(u,B,m,\rho\).

Here “generically true” means true outside finitely many proper rational affine zero sets in the rational affine hull of \(U\).

**Proof.** Fix every finite argument to its value in \(\eta^*\). List all affine forms that occur in exact equation predicates in all these fibre formulas. For each form compute its pullback coefficients by Lemma 2. Discard forms whose pullback is identically zero; on all of \(U\), their equation predicates are true. Keep every other form in the avoidance list.

Apply Algorithm 5 to the kept forms. Each is proper by its coefficient test, so the algorithm returns a point \(x\in U\) where every kept form is nonzero. Exact equations in every fibre therefore have their generic truth values: an identically zero form gives true, and each other form gives false.

Each congruence predicate also has its generic truth value at \(x\), because every integer coordinate of \(x\) has the residue of \(u+B\rho\) modulo \(m\), and its modulus divides \(m\). Boolean connectives preserve evaluation when all their atomic predicates have the prescribed values. Thus every fibre formula evaluates to its generic truth value, which was assumed true. The same point \(x\), together with \(\eta^*\), satisfies all atoms simultaneously.

For completeness, the assumption stated in terms of exceptional affine zero sets yields exactly this Boolean generic truth value. Outside the zero sets of the retained displayed forms, all exact-equation predicates have the fixed values just described, while all congruence predicates have fixed values throughout \(U\). The Boolean formula consequently has one common truth value on that complement. If this value were false, combine the retained form list with the finitely many proper affine forms whose zero sets are the exceptions in the assumed generic-truth statement, clearing denominators first. Every added form is proper on \(U\): if it vanished at all \(u+B\rho+mBz\), evaluation at \(z=0\) and the unit vectors would show that it vanished on the rational affine hull as well, contrary to properness there. Algorithm 5 finds a point avoiding this combined finite list. At that point the Boolean evaluation would be false while the assumed generic-truth statement makes it true, a contradiction. Therefore the common Boolean value used above is true.

The total number \(h\) of listed forms is linear in the number of atoms for a fixed template. Their coefficient sizes and the matrix data are polynomially bounded in the CSP algorithm. Propositions 6–7 therefore give the claimed output and time bounds. Repeated variables are substituted as the same coordinate, so the argument does not assume distinct arguments. If no forms remain, any point of \(U\), in particular \(u+B\rho\), realizes the same generic truth values. \(\square\)

This construction allows affine forms involving different original integer sorts. It is an external arithmetic computation on coordinates; no mixed-sort pp-definability assertion is needed for evaluating a supplied fibre formula.

## 6. Integer normal-form input and a complete rectangular reduction

The cited external algorithmic statement is **Ravindran Kannan and Achim Bachem (1979), Theorem 2 and Lemma 3**, in *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, SIAM Journal on Computing **8**(4), 499–507, DOI [10.1137/0208040](https://doi.org/10.1137/0208040). It computes the column Hermite form of a nonsingular square integer matrix together with a unimodular multiplier in polynomial time, with polynomial bit lengths.

The following reduction records exactly the form required for witness construction.

### Lemma 9 — PROVED, confidence 0.99

For an integer system \(Ax=b\), one can decide integer feasibility and, when feasible, compute

\[
\{x\in\mathbb Z^n:Ax=b\}=u+B\mathbb Z^d
\tag{6.1}
\]

in polynomial time, with polynomial bit lengths for \(u\) and \(B\).

**Proof.** Use rational elimination to test consistency and choose \(r=\operatorname{rank}_{\mathbb Q}A\) independent rows \(A'\), with the corresponding \(b'\). Rational consistency ensures that every omitted row equation is the same rational linear combination of the selected equations as its right-hand side. Thus the selected system is equivalent over both \(\mathbb Q\) and \(\mathbb Z\).

If \(r=0\), consistency means every right-hand side is zero. Take \(u=0\) and \(B=I_n\). If there are no variables, feasibility is exactly this test on the right-hand sides, and the returned point is the unique empty tuple.

For \(r>0\), permute columns so that \(A'P=[C\ D]\) with \(C\) nonsingular of size \(r\). Form

\[
E=\begin{pmatrix}C&D\\0&I_{n-r}\end{pmatrix}.
\]

It is nonsingular because its determinant is \(\det C\). Apply the cited square Hermite algorithm to obtain unimodular \(K\) with \(EK\) lower triangular. Its first \(r\) rows have the form \([H_0\ 0]\), with \(H_0\) nonsingular. Put \(U=PK\). Then

\[
A'U=[H_0\ 0].
\]

Under the integral bijection \(x=Uz\), the system fixes the first \(r\) entries to the rational vector \(v=H_0^{-1}b'\). If any entry is nonintegral, there is no integer solution. If all entries are integral, the remaining \(n-r\) entries are arbitrary integers. Set \(u=U(v,0)\) and let \(B\) be the last \(n-r\) columns of \(U\). This proves (6.1).

The Hermite theorem bounds the multiplier computation. Rational elimination and the fixed-coordinate solve have polynomial bit complexity: the reduced fractions arising from elimination are ratios of subdeterminants; for a matrix of dimension at most \(n\) and entry magnitude at most \(H\), each such determinant is at most \(n!H^n\) in magnitude, by its permutation expansion. Their binary lengths are polynomial in \(n\) and \(\log H\). Reducing fractions after each of the polynomially many elimination operations maintains polynomial operand lengths. The final matrix products use polynomially many arithmetic operations on those bounded integers. \(\square\)

## 7. Polynomial-size witnesses without the hypothesis Q

### Theorem 10 — PROVED, confidence 0.99

For every fixed finite-signature template with finite sorts and integer fibres given by finite Boolean combinations of affine equations and congruences, every satisfiable pp instance has an actual satisfying assignment whose integer coordinates have polynomial binary length in the instance size. This statement does not require \(Q\).

Given a satisfying choice of finite-variable values and one satisfying DNF cell for each atom, such an assignment is constructible in polynomial time.

**Proof.** Fix DNF presentations of every finite fibre. Replace negated congruences by disjunctions of their other residue values when preparing these fixed presentations; this is a finite template-dependent computation. On a satisfiable instance, choose its finite-variable values and one cell satisfied by its actual tuple in every atom. These choices select a conjunction of affine equations, positive congruences, and affine disequalities. The number of selected predicates is linear in the instance size, and their coefficients and moduli have template-bounded lengths.

Replace each congruence

\[
\ell(x)\equiv a\pmod q
\]

by an equation \(\ell(x)-a=qy\) with a fresh integer variable \(y\). The resulting equality system has polynomial size. It has an integer solution, since the chosen branch was satisfied. Use Lemma 9 to compute its full integer solution coset \(u+B\mathbb Z^d\). Every selected disequality is nonidentically zero on that coset; otherwise the chosen branch would have no satisfying point.

Apply Algorithm 5 with \(m=1\) and \(\rho=0\). It returns an integer solution satisfying every selected disequality. The construction preserves all equations, including those encoding the congruences. Discard the auxiliary congruence variables. The remaining integer coordinates, together with the selected finite values, satisfy every chosen fibre cell and therefore every original atom.

Lemma 9 gives polynomial bit lengths for \(u,B\). The parameter dimension and disequality count are polynomial in the instance size. Formula (4.2) then gives a polynomial binary-length bound for every output coordinate, and the total assignment length is polynomial because the number of variables is polynomial.

If a satisfying finite/cell choice is supplied, every step just described is deterministic and polynomial-time. Selecting that choice is not asserted to be polynomial-time for arbitrary templates. \(\square\)

### Corollary 11 — PROVED, confidence 0.99

These CSPs have NP certificates consisting of the actual finite and integer variable values, not merely of a branch whose feasibility is checked by another algorithm.

**Proof.** Theorem 10 gives an actual polynomial-length satisfying assignment whenever the instance is satisfiable. Given its finite values and binary integer coordinates, compute every fixed affine form, evaluate every fixed congruence and Boolean connective, and test all atoms. The number of atoms is polynomial, their arities and coefficient lists are fixed, and arithmetic on the certificate's polynomially many bits is polynomial-time. A passing assignment is an actual solution; a satisfiable instance has one by Theorem 10. \(\square\)

## 8. Adversarial checks

### Check 12 — PROVED, confidence 1.00: the curve starts with T, not 1

The curve is \((T,T^2,\ldots,T^d)\). Replacing it by \((1,T,\ldots,T^{d-1})\) would invalidate the theorem: the nonzero affine form \(z_1-1\) would then vanish on every curve point. With the stated powers, the affine constant is the coefficient of degree zero and every parameter coefficient has its own positive degree. Therefore no nonzero affine pullback becomes the zero polynomial.

### Check 13 — PROVED, confidence 1.00: the coset is preserved exactly

The returned point differs from \(u+B\rho\) by \(mBz\) with \(z\in\mathbb Z^d\). It is therefore in the exact coset (1.1), not merely in its rational affine hull. If \(B\) is an integer kernel basis from Lemma 9, all integer equations are preserved exactly.

### Check 14 — PROVED, confidence 1.00: constant forms and zero dimension

A constant nonzero pullback contributes no forbidden candidate. A zero pullback is detected before the search and certifies impossibility. With zero free parameters, the coset contains one point and these same coefficient tests decide every disequality. No genericity assertion is used to manufacture a point in a zero-dimensional space.

### Check 15 — PROVED, confidence 0.99: large values versus large encodings

The coordinates of the moment curve may grow exponentially in the parameter dimension, but their binary lengths satisfy (4.2). All computations are exact integer operations on polynomially many bits. No real-number approximation or unit-cost assumption for unbounded integers enters the running-time proof.

### Check 16 — PROVED, confidence 0.99: scope of the broad witness theorem

Theorem 10 proves polynomial-size witnesses and polynomial construction after a successful branch is specified. It does not decide which Boolean branch is satisfiable. The separate \(Q\)-based finite generic-table argument supplies that missing deterministic branch-selection information in the tractable setting. Positive inequalities or order conditions are outside this note's arithmetic language; the moment-curve search was proved for equations, congruences, and disequalities only.

## 9. Reproducibility

**PROVED — confidence 1.00.** Algorithm 5 specifies the full enumeration space, exact coefficient computations, loop order, acceptance test, and returned point. Its guarantee is uniform in all dimensions, coefficient magnitudes, moduli, and finite lists of proper forms. No bounded-range experiment is used to justify the theorem. The finite interval \(0\le T\le hd\) is proved sufficient, rather than selected empirically.

---

# Chapter III — Exact affine and convex solution geometry

**PROVED — confidence 0.99.** Once the generic-cell witness construction has produced one residue class whose generic points all satisfy the instance, the same certificate determines the exact rational affine hull, the exact real convex hull, and the behavior of every rational affine objective on the integer coordinates. The constructions below return actual satisfying assignments. All finite-sort variables can keep one common value tuple throughout.

The geometric statements in this chapter are conditional only on the explicitly stated containments in Definition 1. The preceding CSP algorithm is responsible for producing these containments. No assertion that every arbitrary Boolean affine CSP has such a certificate is made here.

## 1. Input, solution projections, and hull conventions

### Definition 1 — PROVED, confidence 1.00; notation and hypotheses

Let \(n,d,h\) be nonnegative integers, with \(d\le n\). The input data consist of:

- an integer vector \(u\in\mathbb Z^n\);
- an integer matrix \(B\in\mathbb Z^{n\times d}\) with linearly independent columns;
- an integer \(m\ge1\) and a vector \(\rho\in\mathbb Z^d\);
- integer affine forms
  \[
  h_j(x)=b_j+a_j^{\mathsf T}x,
  \qquad b_j\in\mathbb Z,\quad a_j\in\mathbb Z^n,
  \quad 1\le j\le h;
  \]
- a set \(S\subseteq\mathbb Z^n\), interpreted as the integer-coordinate projection of all satisfying assignments of one CSP instance;
- one fixed tuple \(\eta^*\) of values of every variable of every finite sort.

Define

\[
\begin{aligned}
U&=u+B(\rho+m\mathbb Z^d),\\
L_{\mathbb Q}&=u+B\mathbb Q^d,\\
L_{\mathbb R}&=u+B\mathbb R^d,\\
C&=\{x\in U:h_j(x)\ne0\text{ for every }1\le j\le h\}.
\end{aligned}
\tag{1.1}
\]

The hypotheses to be used are precisely:

\[
\text{no }h_j\text{ vanishes identically on }U,
\qquad C\subseteq S\subseteq L_{\mathbb Q},
\tag{1.2}
\]

and every \(x\in C\), combined with the same finite tuple \(\eta^*\), is an actual satisfying assignment. Membership \(S\subseteq\mathbb Z^n\) was already required, so the second containment also says \(S\subseteq L_{\mathbb Q}\cap\mathbb Z^n\).

If initially supplied forms have rational coefficients, multiply each form by the product of the positive denominators of its coefficients. This replaces it by an integer affine form with exactly the same zero set. The binary length of the product is at most the sum of the binary lengths of those denominators. Thus the normalization has polynomial bit complexity and preserves (1.1) and (1.2). All quantities below, including the common threshold, use these normalized integer forms.

The rational affine hull \(\operatorname{aff}_{\mathbb Q}(A)\) of a nonempty set \(A\subseteq\mathbb Q^n\) is the set of finite sums \(\sum_{i=1}^r q_i a_i\), where \(a_i\in A\), \(q_i\in\mathbb Q\), and \(\sum_iq_i=1\). The real affine hull \(\operatorname{aff}_{\mathbb R}(A)\) allows real coefficients in place of rational coefficients. The rational convex hull \(\operatorname{conv}_{\mathbb Q}(A)\) requires, in addition, \(q_i\ge0\). The real convex hull \(\operatorname{conv}_{\mathbb R}(A)\) requires real nonnegative coefficients with sum one. These hull definitions use finite combinations; no topological closure is included.

When \(d=0\), the matrix \(B\) has no columns, the vector \(\rho\) is empty, and \(U=L_{\mathbb Q}=L_{\mathbb R}=\{u\}\). When \(h=0\), the conditions defining \(C\) are empty and \(C=U\).

## 2. A common threshold for every lattice direction

### Lemma 2 — PROVED, confidence 1.00

One can compute \(x_0\in C\) deterministically in polynomial time in the binary encoding of \(u,B,m,\rho\), and the forms \(h_j\). Its coordinates have polynomial binary length.

**Proof.** The pullback of a form is

\[
h_j(u+B\rho+mBz)=c_j+\sum_{i=1}^d v_{ji}z_i,
\]

where

\[
c_j=h_j(u+B\rho),\qquad
v_{ji}=m a_j^{\mathsf T}B_i.
\]

Here \(B_i\) denotes column \(i\) of \(B\). Hypothesis (1.2) says that the coefficient list \((c_j,v_{j1},\ldots,v_{jd})\) is not zero. Substituting \(z_i=t^i\) therefore yields a nonzero polynomial of degree at most \(d\), since the constant and the powers \(t,t^2,\ldots,t^d\) have distinct degrees. A nonzero polynomial of degree at most \(d\) has at most \(d\) distinct roots: dividing by \(t-a\) at a root \(a\) reduces the degree by one, and induction on the degree proves the assertion. Hence at most \(hd\) integers are roots of at least one of the \(h\) polynomials. Test \(t=0,1,\ldots,hd\) and choose the first value for which all are nonzero. Then

\[
x_0=u+B\rho+mB(t,t^2,\ldots,t^d)^{\mathsf T}
\tag{2.1}
\]

belongs to \(C\).

The test uses at most \((hd+1)hd\) multiplication-addition pairs by Horner evaluation. With \(M=\max(1,hd)\), all powers have at most \(d\lceil\log_2M\rceil+1\) bits. All other intermediate values are sums and products of polynomially many input integers and these powers, so their bit lengths are polynomial. Formula (2.1) then has polynomial binary length. Detailed numerical bounds and all arithmetic estimates appear as Propositions 6 and 7 of `Witness_bounds.md`.

If \(h=0\), choose \(t=0\) and return \(u+B\rho\). If \(d=0\), each proper form is a nonzero constant on the sole point \(u\); the same choice returns \(u\). Thus the construction includes both boundary cases. \(\square\)

### Lemma 3 — PROVED, confidence 1.00

Let \(x_0\in C\). Define

\[
\alpha_j=h_j(x_0),\qquad
A=\max\bigl(\{0\}\cup\{|\alpha_j|:1\le j\le h\}\bigr),
\qquad T=A+1.
\tag{2.2}
\]

For every vector \(v\in mB\mathbb Z^d\) and every integer \(t\) with \(|t|\ge T\), one has

\[
x_0+tv\in C.
\tag{2.3}
\]

The same threshold \(T\) works for every direction \(v\) in this lattice.

**Proof.** Because \(x_0\in U\), there is an integer vector \(z_0\) with

\[
x_0=u+B\rho+mBz_0.
\]

Write \(v=mBw\) for an integer vector \(w\). Then

\[
x_0+tv=u+B\rho+mB(z_0+tw)\in U
\]

for every integer \(t\).

For each \(j\), set \(\beta_j=a_j^{\mathsf T}v\). It is an integer. Direct expansion gives

\[
h_j(x_0+tv)=\alpha_j+t\beta_j.
\tag{2.4}
\]

The coefficient \(\beta_j\) is the value of the linear part of \(h_j\) at \(v\); it is not in general \(h_j(v)\), because the latter also includes the affine constant \(b_j\).

If \(\beta_j=0\), (2.4) equals \(\alpha_j\), which is nonzero because \(x_0\in C\). If \(\beta_j\ne0\), its integrality gives \(|\beta_j|\ge1\). Thus

\[
|t\beta_j|\ge|t|\ge T=A+1>|\alpha_j|.
\]

Numbers of distinct absolute value cannot sum to zero, so (2.4) is nonzero. This verifies every defining disequality of \(C\), proving (2.3).

When \(h=0\), one has \(A=0,T=1\), and the residue-coset computation proves the claim without a disequality test. When \(v=0\), the point remains \(x_0\); the \(\beta_j=0\) case applies to every form. These observations also cover \(d=0\). \(\square\)

The points in (2.3), with a fixed direction and integer parameter, form a discrete arithmetic sequence. The assertion does not say that every real point on the corresponding Euclidean ray is an integer solution.

## 3. An explicit affine basis of actual solutions

### Theorem 4 — PROVED, confidence 1.00

The exact affine hulls are

\[
\operatorname{aff}_{\mathbb Q}(C)
=\operatorname{aff}_{\mathbb Q}(S)=L_{\mathbb Q},
\tag{3.1}
\]

and

\[
\operatorname{aff}_{\mathbb R}(C)
=\operatorname{aff}_{\mathbb R}(S)=L_{\mathbb R}.
\tag{3.2}
\]

An explicit affine basis consists of the \(d+1\) points

\[
x_0,\qquad x_i=x_0+TmB_i\quad(1\le i\le d),
\tag{3.3}
\]

where \(x_0,T\) are constructed in Lemmas 2 and 3. Each point in (3.3), combined with the same finite tuple \(\eta^*\), is an actual satisfying assignment.

**Proof.** Lemma 3, with \(v=mB_i\) and \(t=T\), gives \(x_i\in C\) for every \(i\). The point \(x_0\) belongs to \(C\) by construction. Hypothesis (1.2) therefore supplies the asserted full satisfying assignments with common finite tuple \(\eta^*\).

The difference vectors are

\[
x_i-x_0=TmB_i.
\]

They are linearly independent over \(\mathbb Q\) and over \(\mathbb R\), since \(T,m\) are nonzero and the columns of \(B\) are independent. Their span over either field is exactly the column span of \(B\) over that field.

To verify the affine-hull assertion directly, fix \(K=\mathbb Q\) or \(K=\mathbb R\). Every affine combination of the points in (3.3) is \(x_0+Bq\) for some \(q\in K^d\), and lies in \(L_K\). Conversely, if \(y\in L_K\), then \(y-x_0=Bq\) for some \(q\in K^d\), because both \(y\) and \(x_0\) lie in \(L_K\). The identity

\[
y=\left(1-\sum_{i=1}^d\frac{q_i}{Tm}\right)x_0
   +\sum_{i=1}^d\frac{q_i}{Tm}x_i
\]

expresses \(y\) as an affine combination of (3.3). Thus those points have affine hull \(L_K\).

Now use \(\{x_0,x_1,\ldots,x_d\}\subseteq C\subseteq S\subseteq L_K\). Every affine combination of points in \(S\) remains in \(L_K\): if \(s_i=u+Bq_i\) and \(\sum_i\lambda_i=1\), then \(\sum_i\lambda_i s_i=u+B\sum_i\lambda_iq_i\). The inner set already has hull \(L_K\), so both intervening hulls equal \(L_K\). This proves (3.1) and (3.2).

If \(d=0\), the list (3.3) consists of \(x_0=u\) alone. The containments give \(C=S=\{u\}\), and their rational and real affine hulls are the same singleton. \(\square\)

## 4. Exact convex hull, without taking a closure

### Theorem 5 — PROVED, confidence 1.00

One has

\[
\operatorname{conv}_{\mathbb R}(C)
=\operatorname{conv}_{\mathbb R}(S)=L_{\mathbb R},
\tag{4.1}
\]

and

\[
\operatorname{conv}_{\mathbb Q}(C)
=\operatorname{conv}_{\mathbb Q}(S)=L_{\mathbb Q}.
\tag{4.2}
\]

Each point in the right-hand side of either equality is a convex combination of at most \(d+1\) points of \(C\). For (4.2) all coefficients may be rational. In all these combinations, every point of \(C\) extends to a satisfying assignment using the same \(\eta^*\).

**Proof.** First suppose \(d\ge1\), and put \(v_i=mB_i\). Fix \(K=\mathbb Q\) or \(K=\mathbb R\), and take any \(y\in L_K\). There are coefficients \(c_i\in K\) with

\[
y=x_0+\sum_{i=1}^d c_iv_i,
\tag{4.3}
\]

because multiplying a basis by the nonzero integer \(m\) does not change its span. Let

\[
s=T+\left\lceil\sum_{i=1}^d|c_i|\right\rceil.
\tag{4.4}
\]

Then \(s\) is a positive integer, \(s\ge T\), and \(s\ge\sum_i|c_i|\). For each index with \(c_i\ne0\), define

\[
\varepsilon_i=
\begin{cases}
1,&c_i>0,\\
-1,&c_i<0,
\end{cases}
\qquad
w_i=x_0+\varepsilon_i s v_i,
\qquad
\lambda_i=\frac{|c_i|}{s}.
\]

Lemma 3 gives \(w_i\in C\). Define

\[
\lambda_0=1-\sum_{i:c_i\ne0}\lambda_i.
\]

All weights are nonnegative and their sum is one. Expanding the weighted sum gives

\[
\begin{aligned}
\lambda_0x_0+\sum_{i:c_i\ne0}\lambda_iw_i
&=\left(\lambda_0+\sum_{i:c_i\ne0}\lambda_i\right)x_0
  +\sum_{i:c_i\ne0}|c_i|\varepsilon_iv_i\\
&=x_0+\sum_{i=1}^d c_iv_i\\
&=y.
\end{aligned}
\tag{4.5}
\]

The combination uses \(x_0\) and at most one point for each of the \(d\) directions. When \(K=\mathbb Q\), all \(c_i\) and all weights are rational. When \(K=\mathbb R\), all weights are real. This proves \(L_K\subseteq\operatorname{conv}_K(C)\).

For the reverse inclusion, take a finite convex combination \(\sum_i\lambda_i s_i\) of points \(s_i=u+Bq_i\in S\), with coefficients from \(K\). Since \(\sum_i\lambda_i=1\), the combination equals \(u+B\sum_i\lambda_iq_i\in L_K\). Thus

\[
L_K\subseteq\operatorname{conv}_K(C)
\subseteq\operatorname{conv}_K(S)\subseteq L_K,
\]

which proves both equalities. Formula (4.5) is an exact finite combination, so no closure operation is required.

If \(d=0\), the containments imply \(C=S=L_{\mathbb Q}=L_{\mathbb R}=\{u\}\). A single point is the convex combination of itself with weight one, proving both assertions and the bound \(d+1=1\).

Every point used lies in \(C\), so the final assertion about \(\eta^*\) follows from the explicit hypothesis in Definition 1. \(\square\)

The conclusion concerns the integer-coordinate projection. It does not embed the finite sorts into a vector space, assign numerical costs to their elements, or assert a convex-hull identity in such an enlarged space.

## 5. Every rational affine objective: constant or unbounded both ways

### Theorem 6 — PROVED, confidence 1.00

Let

\[
f(x)=c+a^{\mathsf T}x,
\qquad c\in\mathbb Q,\quad a\in\mathbb Q^n.
\tag{5.1}
\]

Exactly one of the following alternatives occurs.

1. If \(a^{\mathsf T}B=0\), then \(f\) is constant on every point of \(S\). Its minimum and maximum both exist and equal \(f(x_0)\).
2. If \(a^{\mathsf T}B\ne0\), then \(f\) is unbounded above and unbounded below on \(S\). There are explicit integer vectors \(p_+,p_-,v\), with \(a^{\mathsf T}v>0\), such that for every integer \(n\ge0\),
   \[
   p_++nv\in C,
   \qquad p_--nv\in C.
   \tag{5.2}
   \]
   In particular \(\sup_{x\in S}f(x)=+\infty\) and \(\inf_{x\in S}f(x)=-\infty\).

Every point in both sequences can use the same finite assignment \(\eta^*\). The alternatives and a finite description of the sequences can be computed in polynomial time from the supplied certificate and the binary coefficients of \(f\).

**Proof.** If \(a^{\mathsf T}B=0\), then for every \(x=u+Bq\in L_{\mathbb Q}\),

\[
f(x)=c+a^{\mathsf T}u+a^{\mathsf T}Bq=c+a^{\mathsf T}u.
\]

Since \(S\subseteq L_{\mathbb Q}\) and \(x_0\in S\), the first alternative follows.

If \(a^{\mathsf T}B\ne0\), choose the smallest index \(i\) for which \(a^{\mathsf T}B_i\ne0\). Let \(\sigma=1\) when this number is positive and \(\sigma=-1\) when it is negative, and define

\[
v=\sigma mB_i,
\qquad \delta=a^{\mathsf T}v=m|a^{\mathsf T}B_i|>0,
\qquad p_+=x_0+Tv,
\qquad p_-=x_0-Tv.
\tag{5.3}
\]

For every integer \(n\ge0\), the two points in (5.2) are \(x_0+(T+n)v\) and \(x_0-(T+n)v\). Lemma 3 places both in \(C\). Their objective values are respectively

\[
f(x_0)+(T+n)\delta,
\qquad f(x_0)-(T+n)\delta.
\tag{5.4}
\]

Because \(\delta>0\), the first expression exceeds every prescribed real bound for all sufficiently large integers \(n\), and the second is less than every prescribed real lower bound for all sufficiently large integers \(n\). For example, if \(K\) is a real upper bound, choose an integer \(n> (K-f(x_0))/\delta-T\); such an integer exists by the defining Archimedean property of the real numbers. This proves unboundedness above. Applying the same argument to \((f(x_0)-K)/\delta-T\) proves unboundedness below.

The two alternatives exhaust whether the rational row vector \(a^{\mathsf T}B\) is zero. The second excludes constancy, so the criterion for constancy is also necessary. Exact rational dot products determine the alternative and the sign \(\sigma\), and formulas (5.3) compute the sequence descriptions. Their polynomial bit bounds are proved in Proposition 8 below. Membership in \(C\) supplies the common finite tuple \(\eta^*\).

When \(d=0\), the row vector \(a^{\mathsf T}B\) is empty and therefore zero, so the first alternative applies. The case \(h=0\) is covered by \(T=1\) in Lemma 3. \(\square\)

### Theorem 6A — PROVED, confidence 1.00: all rational affine equality consequences

For a supplied rational affine form \(g(x)=c+a^{\mathsf T}x\), the equality \(g(x)=0\) holds for every \(x\in S\) if and only if

\[
c+a^{\mathsf T}u=0\qquad\text{and}\qquad a^{\mathsf T}B=0.
\tag{5.5}
\]

The test is polynomial-time in the certificate and query encodings. When (5.5) fails, one of the already constructed \(d+1\) assignments in (3.3) is a complete satisfying assignment violating the equality. It can be found in polynomial time. These statements concern externally specified affine queries, including queries mixing independent original integer sorts; no assertion that the query relation is pp-definable is needed.

**Proof.** If (5.5) holds and \(x=u+Bq\in S\), then

\[
g(x)=c+a^{\mathsf T}u+a^{\mathsf T}Bq=0,
\]

so the equality is entailed. Conversely, suppose \(g\) vanishes on every point of \(S\). It vanishes in particular at \(x_0\) and every \(x_i=x_0+TmB_i\) from (3.3). Subtracting the two values gives

\[
0=g(x_i)-g(x_0)=Tm\,a^{\mathsf T}B_i.
\]

Since \(T,m\) are positive, every \(a^{\mathsf T}B_i\) is zero. Thus \(a^{\mathsf T}B=0\). Because \(x_0\in u+B\mathbb Q^d\), it follows that \(g(u)=g(x_0)=0\). This proves (5.5).

For explicit counterexample extraction, first evaluate \(g(x_0)\). If it is nonzero, return the full assignment with integer part \(x_0\) and finite part \(\eta^*\). If it is zero but (5.5) fails, then \(a^{\mathsf T}B\) must be nonzero: a zero row would make \(g\) constant on the entire affine space, with constant value \(g(x_0)=0\), which would imply (5.5). Choose the first index \(i\) with \(a^{\mathsf T}B_i\ne0\) and return the full assignment whose integer part is \(x_i\). It is satisfying by Theorem 4 and violates the equality because \(g(x_i)=Tm\,a^{\mathsf T}B_i\ne0\).

Exact rational dot products and zero tests use polynomially many operations on polynomial-bit numbers; the denominator bound is the one proved in Proposition 8. The output assignment is one of the polynomial-bit assignments already constructed there. If \(d=0\), the criterion reduces to \(g(u)=0\), and \(u\) itself is a counterexample whenever that value is nonzero. \(\square\)

For an infeasible original instance, every equality is vacuously entailed: there is no satisfying assignment violating it. The full algorithm first runs its feasibility stage and reports this case separately. No counterexample assignment is requested or returned in that case.

### Corollary 7 — PROVED, confidence 1.00

In the nonconstant case, given a rational threshold \(K\), one can produce actual satisfying assignments with objective value strictly greater than \(K\) and strictly less than \(K\), in polynomial time in the certificate, objective, and threshold encodings.

**Proof.** For the upper assignment use

\[
n_+=\max\left(0,\left\lfloor\frac{K-f(x_0)}{\delta}-T\right\rfloor+1\right).
\]

This nonnegative integer satisfies \(n_+>(K-f(x_0))/\delta-T\): when the expression on the right is negative the maximum selects either zero or a larger integer, while when it is nonnegative the floor plus one exceeds it. Thus \(x_0+(T+n_+)v\in C\) has objective value strictly greater than \(K\).

For the lower assignment use

\[
n_-=\max\left(0,\left\lfloor\frac{f(x_0)-K}{\delta}-T\right\rfloor+1\right).
\]

The same floor inequality gives \(f(x_0)-(T+n_-)\delta<K\), and Lemma 3 makes the corresponding point feasible. Arithmetic on rational numerators and denominators, integer floor division, and the final integer vector products have polynomial bit complexity. Each \(n_\pm\) has polynomial binary length because its defining rational expression does. Both full assignments use \(\eta^*\). \(\square\)

## 6. Output sizes and a constructive rational convex decomposition

### Proposition 8 — PROVED, confidence 0.99

The following objects are computable with polynomial binary encoding length and polynomial running time:

- \(x_0,A,T\) from Lemmas 2 and 3;
- the \(d+1\) full satisfying assignments in Theorem 4;
- the constant objective value, or the two start points and direction in Theorem 6;
- given any rational \(y\in L_{\mathbb Q}\), an exact rational convex combination of at most \(d+1\) full satisfying assignments whose integer-coordinate combination is \(y\).

In the last assertion, the bound is polynomial in the original certificate encoding and the binary encoding of \(y\). At a binary-encoded index \(n\ge0\), either point of (5.2) is computable with binary length polynomial in the certificate encoding and \(\log_2(n+1)\). No bound independent of \(n\) is asserted for the infinitely many points of a nonconstant sequence.

**Proof.** Lemma 2 gives polynomial bit length for \(x_0\). To make the subsequent estimates explicit, suppose

\[
|b_j|, |(a_j)_k|\le H,
\qquad |(x_0)_k|\le X,
\]

for integers \(H,X\ge1\). Evaluation gives

\[
|\alpha_j|\le H+nHX=H(1+nX).
\]

Consequently

\[
T\le1+H(1+nX).
\tag{6.1}
\]

If \(|B_{ki}|\le D\), then \(|(mB_i)_k|\le mD\) and

\[
|(x_0\pm TmB_i)_k|\le X+TmD.
\tag{6.2}
\]

Taking binary logarithms of (6.1) and (6.2) proves polynomial bit bounds from those for \(H,X,D,m,n\). Evaluating \(h\) forms, taking a maximum, and forming \(d\) integer vector products use polynomially many arithmetic operations. The fixed finite tuple is copied once per output assignment, so outputting all \(d+1\) assignments also has polynomial total length.

For a sequence point, the coordinate bound is

\[
|(x_0\pm(T+n)v)_k|\le X+(T+n)|v_k|.
\]

Its logarithm is bounded by the sum of the logarithms of the displayed input magnitudes plus an absolute constant. Thus it is polynomial in the original encoding and \(\log_2(n+1)\). The direction and starts in (5.3) have polynomial bit length. Rational dot products used in the objective test also have polynomial bit length: a common denominator can be chosen as the product of the denominators of the coefficients of \(a\) and \(c\), whose binary length is at most their total input length. Clearing that denominator reduces every sign test and every objective evaluation to polynomially many integer operations on polynomially many bits.

For rational convex decomposition, first solve

\[
mBc=y-x_0
\tag{6.3}
\]

over \(\mathbb Q\). Its solution is unique because the columns of \(B\) are independent, and it exists by the assumption \(y\in L_{\mathbb Q}\). Rational elimination finds \(d\) independent rows and solves the resulting nonsingular square system. To see the relevant size bound directly, clear the denominators of \(y-x_0\) by their product, whose binary length is at most the sum of their binary lengths. The resulting square coefficient system is integral. By the determinant expansion, a \(d\)-by-\(d\) determinant with entry magnitudes at most \(H_1\) has magnitude at most \(d!H_1^d\). Cramer's determinant ratios for (6.3), including the cleared common denominator, therefore have polynomial numerator and denominator lengths. Rational elimination with fractions reduced after each operation has the same bound: at each pivot, an unreduced Schur-complement entry is a ratio of minors, as follows by multiplying out the determinant of the block formed by the pivot rows and columns and the one additional row and column. Thus one can select the independent rows and obtain these coefficients in polynomial time using polynomially many arithmetic operations on polynomially many bits. This is the rational-elimination bound also written out in the arithmetic chapter and in Lemma 9 of `Witness_bounds.md`.

Compute the rational sum \(\sum_i|c_i|\), its integer ceiling, and \(s\) from (4.4). The sum can use the product of the denominators as a common denominator, so it has polynomial bit length. Its ceiling and \(s\) have polynomial bit length as well. Form \(w_i=x_0+\operatorname{sgn}(c_i)smB_i\) for every nonzero \(c_i\), and weights \(|c_i|/s\) and \(1-\sum_i|c_i|/s\). These are integer vectors and rational numbers with polynomial bit length. Their feasibility and exact weighted-sum identity were proved in Theorem 5. Attach the same \(\eta^*\) to each vector to obtain the required full satisfying assignments.

If \(d=0\), the only rational target \(y\in L_{\mathbb Q}\) is \(x_0=u\). Return its full satisfying assignment with weight one, and perform no linear-system solve. \(\square\)

For a target with arbitrary real coordinates, Theorem 5 proves existence of a finite real convex combination. Proposition 8 asserts an exact finite-input algorithm only when the target coordinates are rational and supplied in binary.

## 7. Complete algorithm at a certified generic solution cell

### Algorithm 9 — PROVED, confidence 0.99

The following procedure uses exactly the data and verified hypotheses of Definition 1.

```text
INPUT:
  u, B, m, rho, integer affine forms h_1,...,h_h, finite tuple eta_star;
  certified containments C ⊆ S ⊆ u + B Q^d;
  optional rational objective f(x) = c + a^T x;
  optional rational equality query g(x) = b + q^T x = 0;
  optional rational target y in u + B Q^d.

1. Compute x0 by the first successful moment-curve parameter
   t in {0,...,h*d}; use t=0 when h=0 or d=0.
2. Evaluate alpha_j = h_j(x0).
   Set T = 1 + max({0} ∪ {|alpha_j| : 1 <= j <= h}).
3. Record x0 with finite tuple eta_star as a satisfying assignment.
4. Record the affine-space description u + B Q^d.
5. For i=1,...,d, record x0 + T*m*B_i with finite tuple eta_star.
   Together with x0 these assignments form an affine basis.
6. If an objective was supplied:
     Compute the rational row a^T B.
     If it is zero, report CONSTANT with value f(x0).
     Otherwise choose the first nonzero coordinate i, set
       v = sign(a^T B_i) * m * B_i,
       p_plus = x0 + T*v, p_minus = x0 - T*v,
     and record the two arithmetic sequences
       p_plus + n*v and p_minus - n*v, n >= 0 integer,
     each with finite tuple eta_star.
7. If an equality query g was supplied:
     Test g(u)=0 and q^T B=0.
     If both hold, report ENTAILED.
     Otherwise record the first point among x0,x1,...,xd
       at which g is nonzero, with the same finite tuple eta_star.
8. If a rational target y was supplied:
     If d=0, record x0 with weight 1.
     If d>0:
       Solve m*B*c = y-x0 over Q.
       Put s = T + ceil(sum_i |c_i|).
       For each nonzero c_i record
         x0 + sign(c_i)*s*m*B_i with weight |c_i|/s.
       Record x0 with weight 1 - sum_i |c_i|/s.
       Attach finite tuple eta_star to all points.
9. Return all recorded data and optional-query answers.
```

**Proof of correctness and complexity.** Lemma 2 proves step 1. Lemma 3 proves the common threshold in step 2. Hypothesis (1.2) proves the actual satisfying-assignment claim in step 3. Theorem 4 proves steps 4 and 5, including equality of the reported affine hull with the hull of all solutions. Theorem 6 proves every outcome of step 6. Theorem 6A proves both outcomes and the guaranteed counterexample search in step 7. Theorem 5 proves the convex combination returned at step 8. Proposition 8 proves polynomial bit complexity and output sizes. Every loop, branch, arithmetic expression, and enumeration interval used by the procedure is specified above. \(\square\)

## 8. Application to the labelled additive-integer CSP algorithm

### Corollary 10 — PROVED, confidence 0.99, conditional on the preceding witness-construction theorem

Suppose the preceding \(Q\)-based witness-construction algorithm, on a satisfiable instance, computes an integer affine space \(u+B\mathbb Z^d\) containing the integer part of every solution, a common residue vector \(\rho\) modulo \(m\), and a finite tuple \(\eta^*\) for which all original atoms are generically true on \(u+B(\rho+m\mathbb Z^d)\). List the affine forms in the chosen fibre formulas that do not vanish identically on this affine space. Then all conclusions of Theorems 4, 5, 6, and 6A, and Algorithm 9, apply to the full integer-coordinate solution projection.

**Proof.** After fixing \(\eta^*\), each atom is a Boolean combination of exact affine equations and congruences. Every congruence truth value is constant on the chosen residue coset, since the fixed modulus \(m\) is divisible by its modulus. An affine form vanishing identically on the containing affine space vanishes at every point of the coset. Every other exact affine form is placed on the avoidance list. At a point avoiding all these forms, every exact-equation predicate has its generic truth value. Boolean evaluation therefore gives the generic truth value of each fibre, which by the assumed finite-table solution is true. Hence every point in the set \(C\) defined by this list and coset satisfies the original instance with finite tuple \(\eta^*\).

The old refinement invariant supplies the second containment \(S\subseteq u+B\mathbb Q^d\). The integer kernel basis produced by the arithmetic step has independent columns. Every retained affine form is proper on the residue coset: its rational affine hull equals \(u+B\mathbb Q^d\), because \(m\ne0\), so a form vanishing on the entire coset would vanish on the containing affine space. This last assertion can also be checked by the coefficient test: if the linear coefficients \(m a^{\mathsf T}B\) are zero, then \(a^{\mathsf T}B=0\), and a zero constant pullback would force the form to vanish on every \(u+Bq\). Thus all hypotheses of Definition 1 hold, and the cited theorems apply. \(\square\)

For an unsatisfiable instance there is no nonempty solution hull to produce and no objective optimization over solutions. The decision stage must report unsatisfiability first. The geometric procedure is called only after the witness stage has certified the nonempty generic cell.

## 9. Adversarial self-audit

### Audit 11 — PROVED, confidence 1.00: the essential hypothesis is a common solution cell

The step with the greatest potential for misuse is the passage from one feasible point to the whole cell \(C\subseteq S\). It is not valid for an arbitrary satisfying Boolean branch unless that entire branch has been verified. Here it is an explicit hypothesis, and Corollary 10 proves it from the preceding finite generic-table solution. If the finite-table argument failed to give one common residue and one common finite tuple whose generic fibres all hold, the present geometric theorems would remain valid as conditional statements, but their application to the full CSP would fail at that containment.

### Audit 12 — PROVED, confidence 1.00: integral slopes are required for the displayed threshold

The threshold \(T=1+\max_j|h_j(x_0)|\) uses that every nonzero slope \(a_j^{\mathsf T}v\) is an integer of absolute value at least one. This follows from normalized integer forms and integer lattice directions. Rational forms must be cleared first, as explicitly required in Definition 1. Without clearing, the displayed bound could fail for an arbitrarily small nonzero rational slope.

### Audit 13 — PROVED, confidence 1.00: affine and convex hulls are not the solution set

The equalities concern hulls of the integer solution projection, not equality of \(S\) with an affine space. A point on a forbidden hyperplane can lie in the convex hull while failing the original instance. The proof uses actual feasible endpoints and their convex combinations only to establish a hull identity. It never treats a nonintegral convex combination as a satisfying assignment.

### Audit 14 — PROVED, confidence 1.00: no bounded nonconstant integer objective is possible under these hypotheses

For each nonzero objective direction, the two arithmetic sequences in (5.2) have objective increments \(+\delta\) and \(-\delta\), where \(\delta>0\). These are actual solutions with fixed finite tuple. Thus even a proposed one-sided bound would contradict an explicit sequence. If an instance were found with a nonconstant objective bounded above or bounded below, it would disprove the generic-cell certificate for that instance, not merely a numerical estimate in this chapter.

### Audit 15 — PROVED, confidence 1.00: no finite-label optimization assertion is hidden here

The objective is an affine function of the integer coordinates only. Assigning arbitrary costs to labels and optimizing their sum is a different problem. All geometric constructions keep one finite tuple \(\eta^*\) fixed, so they do not search for a best finite tuple and provide no such optimization claim.

## 10. References and reproducibility

**PROVED — confidence 1.00.** Every geometric assertion in this chapter has a proof above. The moment-curve construction and its detailed bounds are Theorem 4 and Propositions 6–7 of `Witness_bounds.md`, which contains its full elementary proof. The arithmetic input conventions and rational elimination bounds are given there as Lemma 9, with the external normal-form reference precisely identified as Kannan and Bachem (1979), Theorem 2 and Lemma 3. The present chapter invokes no additional external geometric theorem.

Algorithm 9 specifies every finite computation used here. The two infinite sequences are represented by exact start vectors and an exact integer step vector; their validity for every integer index is proved by Lemma 3. The convex-hull assertion is justified by the exact formula (4.5) for each target point. No bounded numerical experiment or sampling claim substitutes for either uniform proof.

---

# Appendix A — Independent audit of witness extraction

**Verdict — PROVED, confidence 0.98.** The proposed search theorem is valid under the hypotheses and already-proved structural results of the preceding classification. The central new lemma is that the finite relation of *generic acceptance on a fixed affine residue coset* is preserved by the same fixed cyclic operation. It does not require the fixed arity to exceed the dimension of the current affine space.

## 1. Exact hypotheses and notation

Fix a finite-signature template with integer sorts carrying addition and the pin 1, together with nonempty finite sorts. Every fibre at fixed finite arguments has a finite Boolean presentation in affine integer equations and congruences. There is no order predicate. Let m be a fixed positive multiple of every basic congruence period, with m at least 2.

Let Pi be the partition of integer sorts used by a proved block-generic certificate. Fix a prime p at least 2, coprime to m, and one cyclic idempotent finite-sort operation family c of arity p. Its numerical residue components are the p-mean modulo m. The assumed certificate says that, for every fixed list of p actual tuples of a basic relation R, blockwise integer combinations

\[
z_B=\sum_{i=0}^{p-1}\gamma_i^B x_B^i,
\qquad
\sum_i\gamma_i^B=1,
\qquad
\gamma_i^B\equiv p^{-1}\pmod m
\]

with finite output c remain in R outside finitely many proper rational affine hyperplanes of the coefficient space. Different blocks have independent coefficient vectors.

The current integer solution set is parametrized as

\[
L_{\mathbb Z}=\{u+Bt:t\in\mathbb Z^d\},
\]

where u is integral, B has independent integral columns, B is block diagonal, and its rational image

\[
L=u+B\mathbb Q^d
\]

is the current rational affine space. Partition the parameter coordinates according to the same blocks. For a residue tuple r in (Z/m)^d, use its coordinate representatives in {0,...,m-1} and put

\[
U_r=\{u+B(r+ms):s\in\mathbb Z^d\}.
\]

The set U_r is nonempty and has affine hull L. This follows because the columns of mB span the direction space of L.

For one input atom a, let psi_a(x,eta_a) be its supplied fibre formula, after substituting its original integer argument coordinates from the global tuple x. Repeated arguments use the same coordinate. The finite tuple eta_a uses the atom's original finite variables, with repetitions retained.

All claims in this note are mathematical proofs. No bounded-modulus experiment or unreported table enumeration is used as evidence.

## 2. Elementary lattice avoidance

### Lemma 2.1 — PROVED, confidence 1.00

A nonzero polynomial over the rationals does not vanish on all integer tuples.

**Proof.** Induct on the number of variables. For zero variables, the polynomial is a nonzero constant. For a positive number d, write the polynomial as a polynomial in its last variable, with coefficient polynomials in the first d-1 variables. Choose a nonzero coefficient polynomial. By the induction hypothesis, the first d-1 variables can be chosen to make that coefficient nonzero. The specialized univariate polynomial is nonzero and has at most its degree many roots, because division by X-a removes every distinct root and lowers degree. An integer outside that finite root set completes the induction. \(\square\)

### Lemma 2.2 — PROVED, confidence 1.00

If U is a full affine integer lattice in a rational affine space L, finitely many proper rational affine hyperplanes of L cannot cover U. Removing them leaves a set with affine hull L.

**Proof.** Parametrize a full sublattice of U by an affine map from Z^e whose rational image is L. Each proper hyperplane pulls back to a nonzero affine polynomial. Their product is nonzero, so Lemma 2.1 gives a parameter point outside all of them. If the remaining set had a proper affine hull, place that hull inside one additional proper rational affine hyperplane and append its equation to the same avoidance list. The resulting point would belong to the remaining set while lying outside its affine hull, which is impossible. \(\square\)

This applies to U_r and to the permitted coefficient lattices: the latter have base vector (1-(p-1)a,a,...,a), where a represents p^{-1} modulo m, and spanning directions m(e_i-e_0).

## 3. The generic acceptance relation

### Definition 3.1

For an atom a, define the finite relation G_a on parameter residues and finite arguments by

\[
G_a(r,\eta_a)
\quad\Longleftrightarrow\quad
\{x\in U_r:\psi_a(x,\eta_a)\}
\text{ contains }U_r\text{ outside finitely many proper affine hyperplanes of }L.
\]

The word generic in this definition is entirely explicit. After eta_a is fixed, substitute x=u+Bt into every affine form. An exact equality is generically true precisely when its substituted affine function is identically zero on Q^d. Congruences are evaluated at t=r modulo m. Retain the Boolean connectives of the original fibre formula.

### Lemma 3.2 — PROVED, confidence 0.99

The displayed syntactic test is equivalent to Definition 3.1. If it is false, every satisfying point of the fibre on U_r lies in a finite union of proper affine hyperplanes of L.

**Proof.** Every congruence in the fibre has period dividing m. Therefore its truth value is fixed on U_r and is obtained by substituting t=r. For an exact equality ell(x)=0, either ell vanishes identically on L, in which case it is true everywhere on U_r, or its zero set is proper on L, in which case it is false outside that zero set. A nonzero constant restriction has empty zero set and contributes no obstruction.

Remove all proper zero hyperplanes of the finitely many non-identically-zero exact forms in the fibre. Every atomic predicate has a constant truth value on what remains, and this constant is precisely the stated syntactic replacement. Consequently the whole Boolean formula has that replacement truth value. If true, Definition 3.1 holds. If false, all satisfying points are in the removed union. Lemma 2.2 ensures that the complement is nonempty, and also ensures that a finite union of proper hyperplanes cannot contain a co-generic subset of U_r. Thus the two alternatives cannot both hold. \(\square\)

## 4. The new preservation lemma

### Theorem 4.1 — PROVED, confidence 0.99

The relation G_a is preserved by the fixed family consisting of the p-mean on parameter residues and c on finite arguments.

**Proof.** Take p tuples

\[
(r^0,\eta^0),\ldots,(r^{p-1},\eta^{p-1})\in G_a.
\]

Set

\[
r^*=p^{-1}\sum_i r^i\pmod m,
\qquad
\eta^*=c(\eta^0,\ldots,\eta^{p-1}).
\]

Let H_out be the finite family of exact affine forms in the output fibre psi_a(.,eta^*) whose restrictions to L are not identically zero. By generic acceptance of the first input, its satisfying points contain U_{r^0} outside finitely many proper hyperplanes. By Lemma 2.2, choose a point x^0 in that first satisfying fibre at which every form in H_out is nonzero. If a form is a nonzero constant on L, it is automatically nonzero. Choose one point x^i in each remaining satisfying fibre, for 1<=i<p; those fibres are nonempty by Lemma 2.2.

Apply the block-generic certificate to these p actual input tuples. It supplies finitely many proper coefficient hyperplanes outside which the combined output satisfies psi_a(.,eta^*).

For each ell in H_out, its value on the combined integer tuple is an affine function of the coefficient vectors. That function is not identically zero. Indeed, at the rational coefficient choice gamma^B=e_0 in every block, the combined tuple is x^0, and ell(x^0) is nonzero. This rational projection choice is used only to prove nonidentity; it is not asserted to satisfy the prescribed coefficient congruences.

Avoid all these output-form zero hyperplanes and all the certificate's exceptional hyperplanes simultaneously inside the permitted integer coefficient lattice. Lemma 2.2 gives such coefficients. Because L is a product across blocks and each block's coefficients sum to one, the combined point z lies in L. Writing x^i=u+Bt^i gives, blockwise,

\[
z_B=u_B+B_B\sum_i\gamma_i^B t_B^i.
\]

The parameter residue of this expression is p^{-1} sum_i r_B^i, so z lies in U_{r^*}. The finite output is eta^*. The output satisfies psi_a by the certificate. Every exact form not identically zero on L is nonzero at z by the chosen avoidance; every identically-zero form is zero at z. Congruences at z have exactly the values prescribed by r^*.

Thus z realizes the generic truth pattern described in Lemma 3.2 for the output fibre, and the fibre formula is true at z. The generic truth value is therefore true, proving G_a(r^*,eta^*). \(\square\)

### Audit observation 4.2 — PROVED, confidence 0.99

The proof does not require p to exceed dim L. One selected input point avoids every proper output-form zero set. That alone makes all relevant coefficient pullbacks nonzero, because the coefficient map contains that selected point in its rational image. A full affine span of L by the p input points is unnecessary here.

This is why the same fixed finite cyclic operation can preserve all generic-acceptance tables even when the current affine dimension grows with the instance size.

## 5. Bounded-arity compression

### Lemma 5.1 — PROVED, confidence 0.99

There is a fixed bound K depending only on the template such that, for every current parametrization and atom a, one can compute a matrix C_a with at most K rows and a finite relation T_a^gen of bounded arity satisfying

\[
G_a(r,\eta_a)
\quad\Longleftrightarrow\quad
T_a^{\rm gen}(C_ar,\eta_a).
\]

Every such table is preserved by the same fixed residue-mean/finite-operation family. Its computation is polynomial in the bit size of the current parametrization.

**Proof.** For every possible finite argument tuple, apply Lemma 3.2. The exact equality literals become fixed Boolean constants depending on L and that tuple. The remaining dependence on r is only through the finitely many original congruence forms, after substituting x=u+Bt. The number of forms over all finite argument tuples is bounded in terms of the fixed relation. Stack their linear coefficient rows, reducing them modulo m, into C_a. Their affine constants are retained in the finite Boolean table. If desired, split each row into its separate parameter-block contributions; the number of blocks is fixed and the row count remains bounded. Each original row value is recovered as the sum of its contributions.

Membership in G_a depends only on C_ar and eta_a. Define

\[
T_a^{\rm gen}
=\{(C_ar,\eta_a):(r,\eta_a)\in G_a\}.
\]

If G_a(r,eta_a) holds, the corresponding table tuple is present. If the table contains (C_ar,eta_a), it has a preimage r' with C_ar'=C_ar and G_a(r',eta_a). The dependence only on row values then gives G_a(r,eta_a). This proves the equivalence.

The actual-image restriction can be computed directly. The image of C_a on (Z/m)^d is the subgroup generated by its columns. Starting from {0}, process each column v and replace the current subgroup S by {s+jv:s in S,0<=j<m}. At all times there are at most m^K possible vectors, a template-dependent constant. Thus the image is computed in O(d) stages, each of constant finite size. For each attained row tuple and finite argument tuple, evaluate the substituted Boolean formula from Lemma 3.2. The number of evaluations is constant, and all coefficient substitutions and equality-identity tests have polynomial bit complexity.

For preservation, take p tuples of T_a^gen and choose actual preimages in G_a. Apply Theorem 4.1 to the preimages. Since all numerical components are the same p-mean,

\[
C_a\left(p^{-1}\sum_i r^i\right)
=p^{-1}\sum_i C_ar^i\pmod m.
\]

The image of the preserved G_a tuple is exactly the desired table output. Hence T_a^gen is preserved. This argument needs no pp definition of G_a and no pp definition of a row that happens to mix blocks. \(\square\)

### Audit observation 5.2 — PROVED, confidence 0.99

The generic relation is easier to compress than the exact residue relation P_a used by the decision algorithm. Its exact equality predicates have been replaced by truth constants; no primitive-coordinate saturation is required for those equalities. Only the fixed number of original congruence forms need to be retained. The actual-image restriction is still required: arbitrary table values outside the image of C_a need not preserve the common operation.

## 6. A finite generic solution exists at a stable space

The preceding decision theorem uses the exact finite relaxation

\[
F_L(r,\eta)=\bigwedge_a P_a(r,\eta_a),
\]

where

\[
P_a(r,\eta_a)\iff
\exists t\,[t\equiv r\pmod m\land R_a(u+Bt,\eta_a)].
\]

It also uses the pp support set

\[
S_a=\{t:\exists\eta\,[F_L(q_m(t),\eta)\land R_a(u+Bt,\eta_a)]\}.
\]

A stable stage has F_L satisfiable and aff_Q S_a=Q^d for every non-arithmetic atom. The proof below uses the already-proved existence of generic cyclic certificates at every sufficiently large prime arity. That arity may depend on the instance in this existence proof; the polynomial algorithm will use only the fixed p-ary table invariance from Theorem 4.1.

### Lemma 6.1 — PROVED, confidence 0.98

At a stable stage, the finite instance

\[
\bigwedge_a G_a(r,\eta_a)
\]

is satisfiable.

**Proof.** If there are no non-arithmetic atoms, any parameter residue and any assignment to unconstrained finite variables satisfies the empty conjunction.

Assume there is at least one atom. For each a, choose at most d+1 points of S_a whose affine hull is Q^d. Such a list is obtained by starting with one point and repeatedly selecting a point outside the current affine span; each selection increases its dimension, and aff S_a=Q^d guarantees a point whenever needed. Choose a witnessing finite solution of F_L for every selected point.

Place all these finite solutions in one list, retaining one distinct row for each selected witness. Choose a sufficiently large prime q exceeding the number of rows and exceeding the generic-certificate threshold. Fill the remaining rows by repetitions of any solution of F_L. For every row i and every atom a, exact membership in P_a supplies a point t_a^i with the row's residue r^i and with R_a(u+Bt_a^i,eta_a^i). On the rows selected for atom a, retain its originally selected point. Hence the list t_a^i spans Q^d for every a.

Set

\[
r^*=q^{-1}\sum_i r^i\pmod m,
\qquad
\eta^*=c_q(\eta^0,\ldots,\eta^{q-1}).
\]

For one atom a, independent blockwise rational affine combinations of the points u+Bt_a^i map the coefficient space onto L. The spanning list spans L after applying the injective affine map, its projection spans each block of L, and the block coefficients are independent. Every permitted integer combination lies in U_{r^*}.

Suppose G_a(r^*,eta_a^*) were false. Lemma 3.2 would place every satisfying point in that fibre and coset inside finitely many proper affine hyperplanes of L. The coefficient map is onto L, so all those pullbacks are proper. Generic preservation excludes only finitely many further proper coefficient hyperplanes. Lattice avoidance produces permitted coefficients outside both families. Their output satisfies the atom but lies outside the asserted covering hyperplanes, a contradiction.

Thus G_a(r^*,eta_a^*) holds for every a. The residue r^* and full finite assignment eta^* are shared by all atoms, so they solve the claimed finite instance. \(\square\)

## 7. Finding a finite assignment in polynomial time

### Proposition 7.1 — PROVED, confidence 0.99

At a stable stage, a simultaneous satisfying assignment to all parameter residues and finite variables for the generic-acceptance instance can be found in polynomial time.

**Proof.** By Lemma 5.1 the constraints compress to bounded-arity tables preserved by the same fixed cyclic operation, together with modular linear equations connecting row-value variables to parameter residues. All tables belong to one fixed finite language: the carriers and arity bound are fixed, so only finitely many tables exist, and retain those preserved by the fixed operation. Modular linear equations are encoded by chains of addition over Z/m and pins, which are preserved by the residue mean. The cyclic operation is idempotent and weak near-unanimity. Bulatov (2017), Theorem 4, condition (2) implying condition (1), gives the polynomial finite decision oracle, with the sorted-to-product reduction already proved in the preceding classification.

To find values, maintain a satisfiable finite instance. Choose an unassigned variable and try its fixed finite carrier values in a fixed order, asking the oracle whether the instance conjoined with that singleton pin is satisfiable. At least one value succeeds because the current instance has a solution. Retain the first successful pin and continue. The common operation is idempotent, so all singleton pins belong to the same preserved finite language. The number of variables is polynomial in the original instance size and every carrier size is constant. Therefore the number and size of oracle calls are polynomial. When all needed variables are pinned, their values form a satisfying assignment. Lemma 6.1 guarantees initial satisfiability. \(\square\)

## 8. Explicit integer witness and its bit bound

### Proposition 8.1 — PROVED, confidence 0.99

Given a solution (r,eta) of the generic-acceptance instance, one can construct a full integer solution of the original CSP in deterministic polynomial time, with polynomial bit length.

**Proof.** For each atom at its chosen finite tuple, list every exact affine form ell in its supplied Boolean presentation whose restriction to L is not identically zero. Let h be the total number of listed forms. Repetitions may remain in the list. The number h is at most a fixed constant times the number of atom occurrences.

Substitute

\[
x=u+B(r+ms).
\]

Each listed form becomes a nonzero affine function of s in Q^d. Nonidentity follows because s maps rationally onto L. If d=0, each such function is a nonzero constant and the unique point u already has the generic truth pattern. Return u with eta.

For d>0, use

\[
s(T)=(T,T^2,\ldots,T^d).
\]

An affine function c+sum_{j=1}^d a_j s_j becomes the polynomial c+sum_{j=1}^d a_j T^j. It is nonzero because the powers 1,T,...,T^d have distinct exponents and the affine coefficient list is not identically zero. Its degree is at most d. Thus at most hd integers are forbidden by the entire list. Test T=0,1,...,hd and choose the first making all listed forms nonzero. There are hd+1 candidates, so one succeeds. If h=0, the single candidate T=0 succeeds.

At the resulting x, every exact equality has its generic truth value: an identically-zero form is zero everywhere on L, and every other listed form has been made nonzero. Congruences have the values prescribed by r because the parameter tuple is r modulo m. Every atom's generic-acceptance predicate is true, so its Boolean formula is true at x. The explicit arithmetic equations also hold because x belongs to L_Z. The pair (x,eta) therefore satisfies the entire original instance.

For the bit bound, suppose the entries of u and B have absolute value below 2^b, and take M=max(1,hd). Then 0<=T<=hd implies |T^j|<=M^d, and the canonical residue coordinates satisfy 0<=r_j<m. Hence

\[
|x_i|\le 2^b\bigl(1+d\,m(1+M^d)\bigr).
\]

Its binary length is bounded by

\[
b+O\bigl(\log(d+1)+\log m+d\log(M+1)\bigr).
\]

The previous decision algorithm recomputes u and B from original input equation rows, so b is polynomially bounded in the original input length. Also d and h are at most polynomial in that length, and m is fixed. Thus all outputs and all candidate arithmetic have polynomial bit length. There are polynomially many candidates and forms; repeated multiplication evaluates the powers in polynomial time. This proves the stated construction and complexity. \(\square\)

## 9. Final adversarial conclusions

**PROVED, confidence 0.99.** The fixed-arity versus growing-dimension concern is resolved by Theorem 4.1's single selected input point. No claim that p fixed points span a growing affine space is used in preservation of the generic tables.

**PROVED, confidence 0.99.** The generic tables need not be pp-definable in the original template. Their preservation is established directly from the generic certificate. The finite solver requires preservation, not pp-definability of those tables.

**PROVED, confidence 0.99.** Exact residue images remain necessary in the preceding decision phase and stable-stage existence proof. The simpler generic tables are introduced only after that phase has established stability. Replacing the earlier exact relaxation by generic tables before refinements would not be justified by this proof.

**PROVED, confidence 0.99.** The moment curve uses positive exponents 1,...,d. Starting with exponent zero could make a nonzero affine form vanish identically on the curve; for example, s_1-1 would vanish if s_1(T)=1.

**PROVED, confidence 0.99.** Zero-dimensional spaces, empty form lists, pure finite atoms, constant nonzero affine forms, repeated variables, and singleton pins are all included in the constructions above.

**PROVED, confidence 0.98.** Combining the preceding decision procedure with Sections 5–8 gives a deterministic polynomial-time algorithm which either correctly reports unsatisfiability or returns a complete satisfying assignment. The integer entries have polynomial binary length. The external computational theorem used in the new finite extraction is exactly Bulatov (2017), Theorem 4, condition (2) to condition (1); the arithmetic normal-form bound is the one already fully reduced in the preceding report.

**Most delicate step.** Theorem 4.1 depends on the output fibre having only affine zero forms and congruences of period dividing m. This lets one carefully chosen input point certify nonzero pullbacks for every possible generic output obstruction. If half-space predicates or congruences outside the chosen period were introduced, that argument would no longer establish the same generic truth test.

---

# Appendix B — Independent geometric audit

**PROVED — confidence 0.99.** The geometric consequences below follow from a single feasible generic cell. They do not use Q directly; Q is relevant upstream, where the cell and the ambient affine space are constructed. The hypotheses must therefore be stated explicitly.

## 1. Hypotheses and notation

Let `n,d,h` be nonnegative integers. Let `m` be a positive integer, let `u` be in `Z^n`, let `B` be an integer `n` by `d` matrix with linearly independent columns over `Q`, and let `rho` be in `Z^d`. Let `f_1,...,f_h` be affine forms with integer coefficients. Assume that

\[
C=\{u+B(\rho+mz):z\in\mathbb Z^d,\ f_j(u+B(\rho+mz))\ne0\text{ for all }j\}
\]

is nonempty. Let `S` be the projection of a solution set onto its integer coordinates, and assume

\[
C\subseteq S\subseteq L_{\mathbb Q}:=u+B\mathbb Q^d.
\]

All points of `S` are integer vectors. Put `L_R=u+B R^d` and `L_Z=u+B Z^d`. These three sets are different objects: an affine rational space, its real scalar extension, and one affine integer lattice. An assertion about the rational affine hull refers to `L_Q`, not to `L_Z`. The parent construction has the stronger containment `S subseteq L_Z`, so the displayed hypothesis is satisfied there.

An affine hull over a field is the set of all finite affine combinations with coefficients in that field; an affine combination has coefficients whose sum is one. A real convex hull is the set of all finite real affine combinations with nonnegative coefficients. Neither definition takes a topological closure.

## 2. Integer tail lemma

### Claim 2.1 — PROVED; confidence 1.00

Choose `x0` in `C`, write the columns of `B` as `B_1,...,B_d`, and put

\[
T=1+\max_{1\le j\le h}|f_j(x_0)|,
\qquad v_k=mB_k.
\]

When `h=0`, take the maximum over the empty list to be zero, so `T=1`. For every column `k`, every integer `s>=T`, and each sign `epsilon` in `{1,-1}`, the point `x0+epsilon*s*v_k` belongs to `C`.

**Proof.** Because `x0` belongs to the coset, there is an integer vector `z0` with `x0=u+B(rho+m*z0)`. The proposed point is

\[
x_0+\epsilon s v_k=u+B(\rho+m(z_0+\epsilon s e_k)),
\]

where `e_k` is the integer unit vector in coordinate `k`; hence it belongs to the same coset. Write `a_j` for the linear coefficient row of `f_j`. Its value at this point is

\[
f_j(x_0)+\epsilon s\,a_jv_k.
\]

If the integer `a_jv_k` is zero, this equals the nonzero number `f_j(x0)`. If that integer is nonzero, its absolute value is at least one. Consequently,

\[
|\epsilon s\,a_jv_k|\ge s\ge T>|f_j(x_0)|.
\]

Two real numbers of different absolute values cannot sum to zero, since a sum of zero would imply that one is the negative of the other and thus has the same absolute value. The displayed form value is therefore nonzero for both signs. This reasoning applies separately to every forbidden form, and proves that the point belongs to `C`. When the list of forms is empty, only the coset-membership argument is needed. ∎

## 3. Feasible affine basis and rational affine hull

### Claim 3.1 — PROVED; confidence 1.00

The `d+1` feasible points

\[
x_0,\quad x_0+Tv_1,\quad\ldots,\quad x_0+Tv_d
\]

are affinely independent, and

\[
\operatorname{aff}_{\mathbb Q}(S)=L_{\mathbb Q}.
\]

**Proof.** All displayed points are feasible by Claim 2.1. Their differences from `x0` are `Tm B_k`. Since `T` and `m` are nonzero and the columns of `B` are independent, these `d` differences are linearly independent over `Q`. This is precisely affine independence of the displayed points. Their rational affine hull is `x0+B Q^d`. Because `x0-u=B(rho+m*z0)` has a rational parameter vector, this hull is `u+B Q^d=L_Q`.

Every rational affine combination of points `u+B*t_i` in `L_Q`, with rational coefficients `alpha_i` summing to one, equals `u+B*sum(alpha_i*t_i)` and therefore belongs to `L_Q`. The hypothesis `S subseteq L_Q` consequently implies that its rational affine hull is contained in `L_Q`, while the displayed feasible affine basis shows it contains `L_Q`. The equality follows. For `d=0`, the single point `x0=u` is the claimed affine basis. ∎

## 4. Exact real convex hull

### Claim 4.1 — PROVED; confidence 1.00

The actual real convex hull, without a closure operation, satisfies

\[
\operatorname{conv}_{\mathbb R}(S)=L_{\mathbb R}.
\]

**Proof.** Every real affine space is closed under finite convex combinations: if points have the form `u+B*t_i`, then a convex combination with coefficients `alpha_i` has the form `u+B*sum(alpha_i*t_i)` because `sum(alpha_i)=1`. Therefore the containment `S subseteq L_R` gives `conv_R(S) subseteq L_R`.

For the reverse containment, choose any `y` in `L_R`. Since `m` is nonzero and `x0-u` is in the image of `B`, there exist real numbers `c_1,...,c_d` with

\[
y=x_0+\sum_{k=1}^d c_kv_k.
\]

If all `c_k` are zero, then `y=x0` is already in `C`. Otherwise choose an integer `S0` at least `T` and at least `sum_k |c_k|`. Such an integer exists, for example the maximum of `T` and the ceiling of that finite sum. For each nonzero `c_k`, let `epsilon_k` be `1` when `c_k>0` and `-1` when `c_k<0`, and put

\[
y_k=x_0+\epsilon_k S_0v_k,\qquad
\alpha_k=|c_k|/S_0.
\]

The number `S0` is positive because `T>=1`. Claim 2.1 gives `y_k in C`. Every `alpha_k` is positive and their sum is at most one. Put `alpha_0=1-sum_{c_k!=0} alpha_k`, which is nonnegative. Direct expansion gives

\[
\alpha_0x_0+\sum_{c_k\ne0}\alpha_ky_k
=x_0+\sum_{c_k\ne0}(|c_k|/S_0)\epsilon_k S_0v_k
=x_0+\sum_k c_kv_k=y.
\]

This is a finite convex combination of at most `d+1` points of `C`. Therefore `y` lies in `conv_R(C)`, which is contained in `conv_R(S)`. Every point of `L_R` has now been included, proving equality without a closure operation. When `d=0`, the same equality is the equality of three singleton sets. ∎

## 5. Rational affine objectives

### Claim 5.1 — PROVED; confidence 1.00

Let `g(x)=b+a*x` have rational coefficients. It is constant on `S` if and only if `a*B=0`. If `a*B` is nonzero, two explicit feasible arithmetic tails witness that `g` is unbounded both above and below on `S`.

**Proof.** If `a*B=0`, then `g(u+B*t)=b+a*u` for every real parameter `t`, so `g` is constant on `L_R` and on `S`. If `a*B` is nonzero, choose a column `B_k` with `a*B_k!=0`. Put `v=m*B_k` if `a*(m*B_k)>0`, and put `v=-m*B_k` otherwise. Since `m>0`, these choices are exhaustive and ensure `a*v>0`.

For each nonnegative integer `r`, Claim 2.1 gives both feasible points

\[
x^+_r=x_0+(T+r)v,
\qquad x^-_r=x_0-(T+r)v.
\]

Their objective values are

\[
g(x^+_r)=g(x_0)+(T+r)a v,
\qquad g(x^-_r)=g(x_0)-(T+r)a v.
\]

The fixed rational number `a*v` is positive. For any real upper bound `H`, choosing an integer `r` larger than `(H-g(x0))/(a*v)-T` makes the first displayed value larger than `H`. For any real lower bound `K`, choosing an integer `r` larger than `(g(x0)-K)/(a*v)-T` makes the second value smaller than `K`. Hence neither a finite upper bound nor a finite lower bound exists. In particular the objective is not constant. When `d=0`, `a*B=0` is automatic and only the constant case occurs. ∎

## 6. Bit lengths and scope

### Claim 6.1 — PROVED; confidence 0.99

If `x0`, `B`, `m`, and the listed forms have polynomial bit length and there are polynomially many coordinates and forms, the displayed affine basis and arithmetic-tail descriptions have polynomial bit length and are constructible in polynomial time.

**Proof.** Each form value `f_j(x0)` is computed by one constant term and a sum of `n` products. If every input entry has at most `b` bits in absolute value, the product terms have at most `2b` bits and the sum has at most `2b+ceil(log2(n+1))+2` bits, with a harmless additional sign bit. Taking absolute values, comparing a polynomial number of such integers, selecting their maximum, and adding one leaves a polynomial bound on the number of bits in `T`. Each `v_k=m B_k` is a product of two polynomial-bit integers. Each point `x0+T*v_k` is a sum and product of polynomial-bit integers. Listing `d+1` such points takes polynomial space and arithmetic work. Rational dot products `a*B_k` and sign comparisons can be performed by clearing the finitely many denominators: the product of polynomially many denominators of polynomial bit length itself has polynomial bit length. The two tails are represented by their integer start points `x0+T*v` and `x0-T*v` and integer directions `v` and `-v`; this is a finite description with polynomial bit length. ∎

The scope is the numeric projection. If the generic cell was certified using one fixed assignment to all finite sorts, every point of `C` and every displayed basis point or tail retains that same finite assignment. Nothing here forms a convex combination of labels or finite torsion values. The existence of a convex combination for every real `y` is a geometric statement; it is not a claim that an arbitrary real input has a finite exact digital representation. For rational `y`, the coefficients can be computed by rational linear algebra, and the displayed convex combination is finite and exact.

## 7. Adversarial audit

**PROVED — confidence 1.00:** integrality is essential to the simple threshold. It gives `|a_jv_k|>=1` whenever the slope is nonzero. For rational slopes with unbounded denominators, the proposed `T=1+max|f_j(x0)|` would not suffice without rescaling forms. Here all avoidance forms and directions are explicitly integral, so this condition is satisfied.

**PROVED — confidence 1.00:** affine independence of the columns of `B` is essential only to the assertion that the listed points are an affine basis of cardinality `d+1`. The tail and convex-hull arguments continue to work with dependent columns, but the listed points would no longer be an affine basis. The parent algorithm constructs `B` with independent columns, so the stronger claim applies.

**PROVED — confidence 1.00:** the cell containment `C subseteq S` is essential. Knowing only that `C` meets every relation separately is insufficient if the finite assignments differ between relations. The constructive theorem must first provide one simultaneous finite assignment and one global coset whose entire generic cell satisfies every input atom. These geometric deductions begin only after that stronger conclusion is established.

All statements above have full proofs in this note and require no external mathematical citation.

---

# Appendix C — Cross-chapter audit

**Verdict — PROVED, confidence 0.98.** The main promises in Theorem W0.4 follow from the combined arguments in *Witness_algorithm.md*, *Witness_bounds.md*, and *Witness_geometry.md*, using exactly the preceding structural and refinement results identified in the dependency ledger. Early acceptance does not weaken either containment needed for the affine and convex hull theorems. The added affine-equality theorem is correct. The original-variable bookkeeping has been resolved by Lemma W0.5.

This is a mathematical dependency and interface audit. It does not claim that the proof has been checked by a formal proof assistant. Its conclusions concern the exact finite-signature, fixed-template, equality-and-congruence scope stated in the chapters.

## 1. Main-theorem promise map

**PROVED, confidence 0.99.** Every mathematical output promised in Theorem W0.4 has a specified construction and proof.

| Promise | Complete proof source | Critical hypothesis checked |
|---|---|---|
| Correct rejection or a full satisfying assignment | Algorithm chapter, Theorem 8.1 | The exact refinement preserves every actual solution; stable exact support forces generic finite acceptance. |
| Polynomial-bit generic cell with one common finite assignment | Algorithm chapter, Lemma 3.2 and Theorem 7.1; geometry chapter, Corollary 10 | Every exact form nonidentically zero on the current space is excluded, while all congruences are fixed on the selected residue coset. |
| Exact rational affine hull of all numerical solutions | Geometry chapter, Theorem 4 | A full affine basis lies in the generic cell, and every solution lies in the current affine space. |
| Exact real convex hull, without closure | Geometry chapter, Theorem 5 | Its explicit finite convex-combination identity represents each real point of the containing affine space. |
| A basis of actual complete solutions with one finite tuple | Geometry chapter, Lemma 3 and Theorem 4 | The common integral threshold avoids every listed form along each basis direction. |
| Rational affine equality entailment and a counterexample when false | Geometry chapter, Theorem 6A | Vanishing at the constructed affine basis is equivalent to vanishing identically on the returned affine space. |
| Infeasible, constant, or unbounded both ways for an affine objective | Algorithm feasibility theorem; geometry chapter, Theorem 6 | A nonzero objective direction supplies two explicit feasible discrete arithmetic rays. |
| Polynomial running time and output sizes | Bounds chapter, Propositions 6–7 and Lemma 9; algorithm chapter, Proposition 5.3 and Theorems 7.1–8.1; geometry chapter, Proposition 8 | All finite carriers and table arities are fixed; arithmetic is exact and measured in binary length. |
| Outputs and queries in all original variables | Front chapter, Lemma W0.5 | Equality identification is either avoided or reversed by an injective coordinate-copy map. |

**Proof of the map.** The cited results contain both the displayed constructions and their correctness arguments. The remaining sections of this audit verify the interfaces that are not immediate from a theorem title: the two containments at early acceptance, the fixed finite assignment throughout geometry, the exact query formulas, and the distinction between newly proved results and imported prerequisites. The claims in the table are thereby reduced to the complete written proofs at the stated locations. \(\square\)

## 2. Early acceptance preserves the full solution geometry

### Proposition A1 — PROVED, confidence 1.00

Let \(S\subseteq\mathbb Z^n\) be the set of integer parts of all full solutions of the original instance. At any iteration where the generic finite instance is satisfiable, the algorithm supplies a cell
\[
C=
\{u+B(\rho+mz):z\in\mathbb Z^d,\ 
h_j(u+B(\rho+mz))\ne0\text{ for every }j\}
\]
and one complete finite tuple \(\eta^*\) satisfying
\[
C\subseteq S\subseteq L_{\mathbb Q},
\qquad L_{\mathbb Q}=u+B\mathbb Q^d.
\]
Every \(x\in C\) is a full satisfying assignment when paired with \(\eta^*\). These assertions do not require that the current state already be stable.

**Proof.** Initially every actual solution satisfies the explicit arithmetic rows, so its integer part lies in the initial arithmetic space. The imported original-cell refinement theorem says that every subsequent refinement retains every actual solution. Induction over the refinements therefore gives \(S\subseteq L_{\mathbb Q}\) at every iteration, including an iteration where early acceptance occurs.

Now take a satisfying assignment \((r,\eta^*)\) of the generic finite instance. Lift \(r\) to the canonical integer vector \(\rho\). Collect every exact affine form in every atom's chosen finite fibre which is not identically zero on the current \(L_{\mathbb Q}\). For every point of \(C\), an identically zero exact equation is true and every listed exact equation is false. Every congruence has a fixed truth value on the residue coset, because its modulus divides \(m\). Thus every atomic predicate has exactly the value used in the generic Boolean evaluation. That evaluation is true for every atom by the selected generic finite assignment. All retained arithmetic rows hold because \(C\subseteq L_{\mathbb Z}\). Hence every point of \(C\), with the same \(\eta^*\), satisfies every original atom.

No step in either containment used supported-hull stability. The first used the invariant maintained before acceptance; the second used the actual successful generic finite assignment. \(\square\)

### Corollary A2 — PROVED, confidence 1.00

Early acceptance already determines the exact affine hull, even if some refinement computations have not been run at that iteration.

**Proof.** The matrix \(B\) has independent columns. Every listed form is nonzero on the full residue lattice. The avoidance theorem supplies \(x_0\in C\). The geometry chapter constructs
\[
T=1+\max\bigl(\{0\}\cup\{|h_j(x_0)|\}_j\bigr)
\]
and proves that all \(d+1\) points
\[
x_0,\quad x_0+TmB_i\quad(1\le i\le d)
\]
belong to \(C\). Their differences span the direction space of \(L_{\mathbb Q}\). Thus
\[
L_{\mathbb Q}
=\operatorname{aff}_{\mathbb Q}C
\subseteq\operatorname{aff}_{\mathbb Q}S
\subseteq L_{\mathbb Q}.
\]
All inclusions are equalities. The real convex-hull proof applies to the same containments, using its explicit signed basis-direction endpoints. Consequently no additional refinement is needed to validate the geometric outputs. \(\square\)

## 3. Equality consequences and objective queries

### Proposition A3 — PROVED, confidence 1.00

The added Theorem 6A correctly decides every rational affine equality on the original integer variables, including equalities mixing independent integer blocks.

**Proof.** Write the queried form as \(g(x)=c+a^{\mathsf T}x\). If
\[
g(u)=0,\qquad a^{\mathsf T}B=0,
\]
then \(g(u+Bq)=0\) for every rational \(q\), so every actual solution satisfies the equation by Proposition A1.

If all actual solutions satisfy the equation, apply it to the actual solutions
\[
x_0,\ x_i=x_0+TmB_i.
\]
Subtracting \(g(x_0)=0\) from \(g(x_i)=0\) gives
\[
Tm\,a^{\mathsf T}B_i=0
\]
for every column. Since \(T,m>0\), all those dot products vanish. The form is constant on \(u+B\mathbb Q^d\), and its value at \(u\) equals its value at \(x_0\), which is zero. This proves both directions.

If the test fails, evaluating \(g\) on the constructed basis must detect a nonzero value. Otherwise the preceding subtraction argument would make the test pass. Each detected point is already an actual complete solution with the common finite assignment. Rational query arithmetic has polynomial bit length after clearing denominators as described in the geometry chapter. Evaluating an externally supplied query does not add it to the CSP signature and needs no pp definition. \(\square\)

**PROVED, confidence 1.00.** The objective trichotomy is also fully supported. In the feasible case, \(a^{\mathsf T}B=0\) makes the objective constant on all solutions. A nonzero coordinate of that row gives an integer direction \(v=\pm mB_i\) with positive objective increment. The points \(x_0\pm(T+n)v\), \(n\ge0\), all lie in the same cell by the geometry chapter's integral-slope estimate. Their values tend in opposite unbounded directions. This is an exact assertion about integer solutions, not an assertion that continuous Euclidean rays consist of integer assignments.

**PROVED, confidence 1.00.** Infeasibility is handled before either geometric query procedure. Equality entailment is then vacuous and no counterexample is returned. The objective algorithm reports infeasibility rather than claiming that a minimum, maximum, or direction exists on an empty set.

## 4. Scope and conventions across the chapters

### Proposition A4 — PROVED, confidence 1.00

The differing levels of generality in the chapters are compatible.

**Proof.** The front and algorithm chapters assume a fixed finite-signature template with actual integer addition and the pin \(1\), finite nonempty carriers, and Boolean equality/congruence fibres. The block-generic and refinement inputs are invoked only in that setting.

The bounds chapter allows an arbitrary explicitly supplied integer affine coset, arbitrary binary coefficients, and even dependent columns of \(B\). Its avoidance result needs only that the listed forms be nonzero on that coset. That result therefore applies to the more specialized independent-column cosets supplied by the CSP algorithm. Its separate small-witness theorem makes no tractability claim for choosing a successful Boolean branch, so it does not conflict with the need for \(Q\) in deterministic branch selection.

The geometry chapter requires independent columns and the explicit containments \(C\subseteq S\subseteq L_{\mathbb Q}\). Proposition A1 verifies those hypotheses in the CSP application. Its use of an arbitrary positive modulus includes the fixed modulus \(m\ge2\) of the CSP chapter.

Finite pins use one convention throughout: all finite singletons are adjoined, idempotence preserves them, and a pp relation in that expansion is a pinned fibre of a pp relation with additional finite free variables. Thus the same \(Q\) operation preserves its image. The block partition is taken after this finite-pin expansion. The finite self-reduction uses precisely those allowed pins.

Binary integer partial assignments in the algorithm chapter are implemented using addition and the pin \(1\) with polynomial-size addition chains. This matches the actual arithmetic assumed in the front chapter. Querying an external affine form is separate from adjoining a new CSP relation, so the equality and objective algorithms do not require any extra mixed-sort pp arithmetic.

All geometric statements concern numerical projections. Keeping the finite assignment fixed is explicitly justified by \(C\subseteq S_{\eta^*}\), where \(S_{\eta^*}\) is the solution projection at that finite assignment. Since \(S_{\eta^*}\subseteq S\subseteq L_{\mathbb Q}\), the same hull identities hold for that restricted projection. No cost optimization or convex interpretation of finite labels is asserted. \(\square\)

### Proposition A5 — PROVED, confidence 1.00

Lemma W0.5 resolves the original-coordinate convention completely.

**Proof.** If equality rows are retained, the full variable tuple is present throughout, and the initial rows \(x_i-x_j=0\) lie within one integer sort. They preserve the product invariant and the original-row bit bounds.

If variables are identified, let \(E\) copy one representative coordinate into all original coordinates of its equality class. Each class has an original representative, so \(Ev=0\) implies \(v=0\) by reading those representative rows. Therefore \(E\) is injective. Replacing reduced data \(\widetilde u,\widetilde B\) by
\[
u=E\widetilde u,\qquad B=E\widetilde B
\]
preserves column independence. Solutions correspond by coordinate copying. Affine combinations, convex combinations, and the residue-cell parametrization commute with \(E\) by distributing the defining finite sums. A query \(c+a^{\mathsf T}x\) pulls back to \(c+a^{\mathsf T}E\widetilde x\). Thus all witnesses, hulls, equality answers, and objective rays transfer to all original variables. The matrix merely copies coordinates, so the transformation has polynomial cost. \(\square\)

## 5. Boundary-case audit

**PROVED, confidence 1.00.** The following cases are covered by the written proofs.

| Case | Verified behavior |
|---|---|
| No integer variables | The parameter dimension is zero; the finite solver decides the instance and supplies the finite assignment. Numerical hulls consist of the empty tuple when feasible. |
| No remaining relation atoms | The generic finite conjunction is empty; an arbitrary residue and arbitrary unconstrained finite values are valid. |
| No exceptional forms | The first curve parameter is zero; every point of the selected residue coset is usable. The geometry threshold is \(T=1\). |
| Zero-dimensional current space | The unique integer point must satisfy each generic fibre; the affine basis has one point and every objective is constant. |
| Constant nonzero form | It removes no point and no curve candidate. |
| Identically zero exact form | Its equation is generically true and it is omitted from the avoidance list. In the standalone avoidance problem, requiring its disequality is correctly rejected. |
| Repeated arguments | Substitution uses the same global coordinate or finite variable at every repeated occurrence; the local residue-image construction preserves those equalities. |
| Composite modulus | All calculations take place in the ring \(\mathbb Z/m\mathbb Z\); only \(p^{-1}\) is used, and \(\gcd(p,m)=1\) guarantees its existence. |
| Finite unary or nullary constraint | Its generic value is just its finite truth value; an empty integer-coordinate tuple causes no additional arithmetic requirement. |
| Rational or constant query | Exact rational dot products and the zero test apply, with the constant case covered by the empty or zero direction row. |
| Conflicting partial pins | The expanded pp-instance is unsatisfiable exactly when the constraints cannot be jointly extended. |
| Large witness magnitudes | Every operation is bounded in binary length; no unit-cost arithmetic assumption is used. |

The rational convex decomposition routine promises an exact algorithm for a rational target supplied in the reported affine space. The proof for arbitrary real targets is an existence proof with an explicit finite combination; no finite-input computation on arbitrary real encodings is claimed.

## 6. Exact dependency boundary

### Proposition A6 — PROVED, confidence 0.99

The new geometric arguments are unconditional consequences of their displayed cell certificate. The end-to-end \(Q\)-based algorithm additionally depends on the included preceding structural proof and on the three stated external algorithmic theorems.

**Proof.** Given explicit \(u,B,m,\rho\), proper affine forms, and verified containments \(C\subseteq S\subseteq L_{\mathbb Q}\), the avoidance, basis, convex decomposition, equality-query, and objective-ray proofs use only the formulas written in the new chapters. No conclusion about pp images is needed to prove those conditional statements.

To obtain the certificate from \(Q\), the algorithm uses these preceding results:

1. \(Q\) supplies a common block-generic family, including one fixed certificate and certificates at all sufficiently large prime arities.
2. Exact finite residue relaxations and supported hulls are computable in polynomial time.
3. Original-cell refinements retain every actual solution, remain products across the correct blocks, lower dimension, and preserve polynomial arithmetic size.

The new fixed-arity closure theorem then makes the generic tables tractable, and the new stable-state theorem proves that their simultaneous satisfiability eventually occurs. The exact references to the preceding proofs are recorded in Theorem 1.3 of the algorithm chapter and Proposition W1.1 of the front chapter. These results are reproduced prerequisites rather than new assumptions proved only by this audit.

Barto and Kozik (2012), Theorem 4.1, enters the earlier Taylor-to-cyclic and amplification argument. Kannan and Bachem (1979), Theorem 2 and Lemma 3, supplies the polynomial integer normal-form computation used by the fully written rectangular reduction. Bulatov (2017), Theorem 4, implication (2) to (1), supplies the fixed finite-language CSP algorithm. The sorted reduction and the fact that all changing tables lie in one fixed finite language are proved in the new algorithm chapter, rather than inferred from an unspecified changing-template tractability claim.

If the prior block-generic theorem failed, the proof that the generic tables share a finite Taylor operation could fail, as could the stable-state existence argument. If the prior refinement invariant failed, the containment of all solutions in the returned affine space could fail. If the prior polynomial bit bound failed, the new algorithms would remain polynomial in the supplied certificate encoding, but an end-to-end bound in the original instance length would no longer follow. These are the exact remaining dependency boundaries. They are explicitly exposed in the cumulative deliverable. \(\square\)

## 7. Interface corrections verified during this audit

**PROVED, confidence 1.00.** The original-variable issue is resolved by the added Lemma W0.5. The geometry chapter's complete algorithm now includes the equality-query input and its entailment/counterexample step, and Corollary 10 cites Theorem 6A. These additions align the executable mathematical procedure with every promise in Theorem W0.4.

Intermediate result production in the geometric procedure must mean recording outputs, followed by a single final return of the accumulated results. It must not terminate at the first produced point. The mathematical proofs already construct the entire collection; the final pseudocode was checked with this output convention.

**PROVED, confidence 0.98.** No additional mathematical gap was found in the audited new chapters after these interface clarifications. This conclusion is limited to the new constructive theorem and its composition with the explicitly included earlier results; it is not a new independent verification of every line of the previous structural classification.

---

# Appendix D — Final adversarial audit

## Verdict

**PROVED — confidence 0.97.** The new constructive theorem is supported by the complete chapters in this package and by the complete prerequisite argument reproduced in `N_Complete.md`, Appendix P. There is no claim that the C++ program implements the whole theorem, and there is no claim of machine formalization of the mathematical proof.

## 1. The most vulnerable new inference

**PROVED — confidence 0.99.** The key new inference is preservation of generic acceptance by one fixed cyclic operation while instance dimension grows. Its full proof is Chapter I, Theorem 4.1.

The output finite tuple is computed first. This determines the list of exact affine forms in the output fibre. Every form that is nonidentically zero on the current affine space is then avoided by the first actual input point. That selection is possible because the first input is generic on a full residue lattice. At the rational coefficient choice projecting every block to this first point, every listed output form is nonzero. Hence none of their coefficient pullbacks is the zero affine function. The allowed integer coefficient set has full rational affine hull, so it avoids those pullbacks and the certificate's preservation exceptions simultaneously.

This proves the needed preservation without asserting that a fixed number of inputs spans an arbitrarily large affine space. The distinction is decisive. If the first input fibre were merely nonempty, its satisfying points could all lie on an output obstruction, and the selection argument would fail. If order inequalities replaced affine zero tests, avoiding hyperplanes would no longer force the claimed generic Boolean truth pattern. Neither weakening is part of the theorem.

## 2. What is inherited and what would fail without it

**PROVED — confidence 0.97.** The implication from \(Q\) to the hypotheses of the new algorithm is inherited from the preceding complete structural and decision proof. This package includes that proof verbatim, both expanded and in the unchanged previous archive. Its exact internal dependencies are listed in Proposition W1.1 and Chapter I, Theorem 1.3.

Two inherited facts are essential. First, all sufficiently large prime arities have block-generic certificates. A potentially large arity is used only to prove that stability implies the existence of one common generic residue/finite assignment. The algorithm itself solves a fixed bounded-arity finite language using one fixed prime. Second, the refinement step stores only original input equality rows. This guarantees polynomial bit length in the original input, not merely in the current derived matrices.

If the inherited structural necessity theorem failed, the new preservation theorem would still hold for templates explicitly equipped with the stated generic certificate, and the arithmetic and geometric theorems would still hold for a supplied generic-cell certificate. The unconditional \(Q\)-based completeness conclusion would then lose its justification. If the original-row invariant failed, the final arithmetic construction would remain polynomial in its supplied lattice data, but the overall bit bound in the original pp-instance length would require a replacement argument. The archive includes the full proofs of both inherited facts so these dependencies can be checked rather than taken on trust.

## 3. Exact finite images and one fixed solver

**PROVED — confidence 0.99.** Every generic table contains only local residue tuples in the actual image of the affine map \(r\mapsto u_a+B_ar\pmod m\). The image is computed by the explicit column-generation recurrence in Chapter I, Lemma 5.2. Its cardinality is bounded by \(m^{k_a}\), a template constant.

The preservation proof selects actual global preimages of table inputs. Adding unattained tuples would invalidate that step. The exact image restriction is consequently retained both in the definition and in the executable mathematical specification.

The fixed modulus, finite carriers, and bounded table arities imply that all generated tables belong to one finite collection of relations preserved by one fixed cyclic operation family. The many-sorted-to-product reduction and singleton self-reduction are fully written. Thus the finite-domain theorem is applied to one fixed language, rather than to an uncontrolled sequence of new templates.

## 4. Early acceptance and the exact affine hull

**PROVED — confidence 0.99.** Early acceptance does not compromise the affine-hull conclusion. The refinement invariant gives \(S\subseteq L\) at every iteration, not just at a stable iteration. A successful generic finite assignment gives a whole cell \(C\subseteq S\) with rational affine hull \(L\). Therefore \(\operatorname{aff}_{\mathbb Q}S=L\) even when the algorithm accepts before performing all possible support computations. The full affine-basis construction proves this identity by explicit solutions.

Well-typed variable identifications are handled by Lemma W0.5. Keeping equality rows avoids any coordinate loss; using the injective row-copy map transfers outputs back to all original integer variables. Finite labels are restored by copying class values. No integer-coordinate projection is silently substituted for the tuple promised in the main theorem.

## 5. The integer construction and its boundary cases

**PROVED — confidence 1.00.** The powers in the integer curve are \(T,T^2,\ldots,T^d\), beginning at exponent one. This keeps the affine constant at degree zero distinct from every parameter coefficient. Beginning with exponent zero could make the nonzero form \(z_1-1\) vanish on the whole curve. The sixth deterministic test detects that mistake.

Every retained form pulls back to a nonzero polynomial of degree at most \(d\). With \(h\) forms, the complete interval \(0,\ldots,hd\) contains a successful candidate. The theorem does not rely on a heuristic search cutoff or a small-modulus experiment. The case \(d=0\) is the unique point; the case \(h=0\) uses the base point. Nonzero constant forms impose no restriction. An identically zero restriction is detected from its constant and every slope, even when the ambient form itself is nonzero.

The large numerical size of \(T^d\) does not cause a large binary encoding: its bit length is \(O(d\log(hd+1))\). The detailed bounds cover all failed candidates as well as the returned point.

## 6. Geometry: what is, and is not, concluded

**PROVED — confidence 1.00.** The three distinct objects are

\[
u+B\mathbb Z^d,
\qquad u+B\mathbb Q^d,
\qquad u+B\mathbb R^d.
\]

The first is an integer affine lattice, the second a rational affine space, and the third its real extension. The solution set need not equal any of them. The statements are that its rational affine hull equals the second and its real convex hull equals the third. Forbidden hyperplanes can contain points of the convex hull which are not solutions.

The threshold \(T=1+\max_j|h_j(x_0)|\), with zero included in the maximum, uses integer-normalized forms. For every integer lattice direction \(v\in mB\mathbb Z^d\), its nonzero slopes are integers of magnitude at least one. That is why both arithmetic tails \(x_0\pm(T+n)v\) avoid every listed zero form for all integers \(n\ge0\). They are discrete sequences of actual solutions with fixed finite values. No claim is made that a continuous ray consists of integer solutions.

The affine-objective theorem concerns numerical coordinates only. It does not solve arbitrary cost optimization over labels. The equality-query theorem concerns affine equalities; it does not claim that affine hull data alone decide every disequality, congruence, or arbitrary Boolean query. The optional rational convex-decomposition algorithm takes rational targets in binary; existence of real decompositions is proved separately without pretending to encode arbitrary real inputs finitely.

## 7. What was computed

**PROVED — confidence 1.00 for the recorded execution.** The arithmetic source was compiled as C++17 with GMP exact integers and no compiler warnings. Eleven deterministic cases passed. Their complete input files, independently specified expected outputs, actual outputs, standard-error outputs, build records, and a Python exact-substitution test driver are included in `witness_code/`.

The optional Boost backend was not compiled in this environment because its header was absent. This limitation is recorded in the build log. The tested GMP configuration implements the same source's mathematical arithmetic path. No execution claim is made for the unbuilt configuration.

These tests check the concrete arithmetic implementation. They neither prove \(Q\) for a template nor verify the whole CSP solver. The mathematical proofs, including the inherited uniform all-modulus arguments, provide the uniform claims. No finite test set is offered in their place.

## 8. What the archive contains

**PROVED — confidence 1.00 as a file-content record, subject to the included manifest check.** `N_Constructive.md` is the complete new report. `N_Complete.md` appends the entire preceding proof as Appendix P. Individual new and prior chapters are included for citation and inspection. `previous/N_Next.zip` is the unchanged previous archive; it already contains the earlier archive chain. The original problem and latest request are included. `MANIFEST.json` records the size and SHA-256 hash of every other archive member, and `verify_archive.py` checks them.

The main mathematical confidence is 0.97 because the cumulative theorem has substantial inherited structural dependencies and has not been mechanically formalized. Every new proof step has been written out; independent mathematical audits found no remaining gap in the new extraction and geometric extension. No step in this extension is labelled SKETCH or CONJECTURE.

---

# References

**PROVED — confidence 0.99; reference record.** The cumulative proof uses the following external results only for the exact statements described below. Every further structural, arithmetic, and geometric claim used here is proved in the included chapters or is explicitly identified as user-stipulated background in the unchanged prior report.

## 1. Finite cyclic terms

**Libor Barto and Marcin Kozik (2012).** *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*. Logical Methods in Computer Science **8**(1), article 07. **Theorem 4.1.** A finite idempotent Taylor algebra has a cyclic term of every prime arity greater than its cardinality.

Primary published PDF: <https://lmcs.episciences.org/673/pdf>.
DOI: <https://doi.org/10.2168/LMCS-8(1:7)2012>.

Application: the preceding structural and amplification chapters obtain the common cyclic operations on finite image sorts. The many-sorted product reduction and preservation under terms are proved there. The new witness chapter uses their proved all-prime generic-certificate conclusion and one fixed cyclic certificate; it makes no additional uncited cyclic-arity assertion.

## 2. Polynomial integer normal forms

**Ravindran Kannan and Achim Bachem (1979).** *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*. SIAM Journal on Computing **8**(4), 499–507. **Theorem 2 and Lemma 3.** Used for polynomial square nonsingular Hermite computation with a polynomial-bit unimodular multiplier.

Publisher/DOI: <https://doi.org/10.1137/0208040>.

The theorem numbering was checked in the original-paper text reproduced at <https://studyres.com/doc/14829602/paper---math-tamu> and <https://studylib.net/doc/7924410/paper>. These are mirrors of the original paper, not additional theorem attributions.

Application: `Witness_bounds.md`, Lemma 9, gives the complete reduction from a rectangular integer system to that square Hermite computation and derives the full integer solution parametrization. The prior arithmetic appendix and general-algorithm chapter give the same reduction and the exact residue-image formula. Rational elimination bit bounds are stated and justified in those proofs. No assertion about general rectangular forms is left to an unspecified reference.

## 3. Fixed finite-domain CSP tractability

**Andrei A. Bulatov (2017).** *A Dichotomy Theorem for Nonuniform CSPs*. Proceedings of the 58th Annual IEEE Symposium on Foundations of Computer Science, 319–330. **Theorem 4, implication (2) to (1).** Used for the polynomial-time tractability of a fixed finite constraint language with a weak near-unanimity polymorphism.

Primary author PDF: <https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf>.
DOI: <https://doi.org/10.1109/FOCS.2017.37>.

Application: `Witness_algorithm.md`, Proposition 5.3, proves that all the varying generic tables have bounded arity, are preserved by one common cyclic idempotent family, and therefore lie in one fixed finite language. It writes out the sorted-to-product reduction, the weak-near-unanimity identities, and the finite singleton-pin search reduction. The earlier general-algorithm chapter proves the corresponding statement for exact residue tables.

## 4. Optional older appendix reference

**Manuel Bodirsky, Barnaby Martin, Marcello Mamino, and Antoine Mottet (2018).** *The Complexity of Disjunctive Linear Diophantine Constraints*. 43rd International Symposium on Mathematical Foundations of Computer Science, LIPIcs **117**, article 33, 33:1–33:16. **Proposition 21** and **Theorem 22** are used in the optional older family chapter and archival audit, respectively for fixed finite Horn-template tractability and the binary-parameter quantifier-free Horn arithmetic algorithm. The new constructive theorem does not use this paper as an additional black box.

Primary published PDF: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.33/LIPIcs.MFCS.2018.33.pdf>.
DOI: <https://doi.org/10.4230/LIPIcs.MFCS.2018.33>.

## 5. Internal prerequisites reproduced in full

The following are internal theorem citations to earlier work in this same cumulative deliverable. They are not invented external publications.

| Needed statement | Complete proof location |
|---|---|
| Q implies block-generic operations | `prerequisites/chapters/N_next_structure.md`, Theorem 1 and Corollary 7.1 |
| Fixed certificate amplifies to all sufficiently large prime arities | `prerequisites/chapters/N_amplification.md`, Theorem II.8 |
| All-modulus sufficiency and finite criterion | That chapter, Theorems II.9–II.12 |
| Product lattice parametrization | `prerequisites/chapters/N_general_algorithm.md`, Lemma 3.2 |
| Exact finite residue relaxation and one fixed solver | That chapter, Lemmas 4.3–4.4 and Proposition 4.5 |
| Supported pp sets and computable hulls | That chapter, Lemmas 5.3–5.4 |
| Original-cell refinement and polynomial persistent data | That chapter, Lemmas 6.1–6.2 and Proposition 6.3 |
| Stable-state generic feasibility | That chapter, Lemmas 7.1–7.2; also reproved in `Witness_algorithm.md`, Theorem 6.2 |
| Prior decision theorem | That chapter, Algorithm 8.1 and Theorem 8.2 |
| Original shared-GC counterexample, including Q for every N | `prerequisites/chapters/N_next_counter.md` |

`N_Complete.md` reproduces the entire prior continuous report as Appendix P, so all these proofs are also available in one reading file.

## 6. No new external geometric theorem

**PROVED — confidence 1.00.** The integer root bound, constructive avoidance, common arithmetic-tail threshold, affine-basis construction, exact rational and real convex decompositions, affine-equality test, and objective trichotomy are proved in the new chapters. No generic appeal to a geometric theorem, compactness theorem, or unnamed “standard argument” is used to justify them. The implementation dependencies GMP and the optional Boost.Multiprecision backend are software choices, not citations offered in place of those proofs.



---

# Appendix P — Complete prerequisite proof, reproduced in full

**PROVED — confidence 0.97; reproduced prerequisite argument.** The text below is the entire preceding continuous report, unchanged. Its individual source chapters are in `prerequisites/chapters/`. The preceding archive is also retained byte for byte in `previous/N_Next.zip`. Internal part and theorem numbering in this appendix is the numbering of that earlier report.

# A complete replacement theorem for labelled additive integer CSPs

**Verdict — PROVED (confidence 0.94): for every finite-signature template in the stated equality–congruence setting, the condition \(Q\) has an explicit finite decision test and implies polynomial-time solvability. The correct generic criterion permits independent affine combinations on the maximal pp-identifiable blocks of integer sorts.**

This is a proof of a replacement classification, not a proof of the old shared-coefficient Conjecture N. The two-independent-sort counterexample from the previous turn continues to refute that conjecture under the literal mixed-coordinate reading. The new theorem supplies the missing general tractability argument for \(Q\).

## Executive summary

1. Integer sorts are grouped only when their literal coordinate identity is pp-definable after finite pins are added.
2. Under \(Q\), every pp-definable affine hull splits as a product across these groups.
3. This forces generic preservation with one independent coefficient vector per group.
4. One cyclic certificate at one explicitly bounded prime arity amplifies to every large prime arity.
5. It then preserves images of every pp relation at every modulus, proving the converse.
6. Enumerating partitions and finite operation tables therefore decides \(Q\).
7. A general CSP algorithm keeps an integer affine space and the exact residue images of each entire atom in that space.
8. Each such image compresses into a bounded-arity finite Taylor relation, so the finite stage is polynomial-time solvable.
9. Every strict refinement adds equations from an original input clause; there are only linearly many dimension drops and polynomially sized arithmetic data.
10. At a stable stage, generic combinations and simultaneous hyperplane avoidance prove satisfiability.
11. With the stipulated hardness implication \(\neg Q\Rightarrow\mathrm{NP\text{-}hard}\), this gives a decidable P/NP-complete classification for finite presentations.
12. The complete proofs, algorithms, counterexample verification, independent audit notes, and prior archive are included in the accompanying ZIP.

## Scope and status convention

The template has finitely many nonempty sorts and a finite relational signature. Every integer sort carries its actual addition graph and pin \(1\), or has fixed pp definitions of them. Each fibre at fixed finite arguments is supplied by a finite Boolean combination of affine equations and congruences. Disequalities are negated equations. There is no order predicate. Several integer sorts are allowed, and an externally written equation may mix their numerical coordinates even when that equation is not itself pp-definable.

These are the finite-presentation hypotheses needed for an effective classification. This report makes no claim about arbitrary infinite signatures or presentations by an unspecified oracle. The core hypothesis is retained from the question for the stipulated hardness implication; the new proof of \(Q\Rightarrow\mathrm P\) does not need it.

If addition and the pin are given by fixed pp definitions, name them first. This does not change the family of pp-definable relations, hence does not change \(Q\); expanding each newly named atom by its fixed definition gives a polynomial reduction back to the original signature. The subsequent chapters may therefore treat addition and the pin as actual basic relations.

Every numbered lemma, theorem, and corollary below is labelled **PROVED**. Confidence values report the degree of checking, not a substitute for proof. The proofs are mathematical arguments checked independently within this research session; they are not a claim of machine verification or prior publication. The independent notes record an earlier stage at which the algorithmic part had not yet been completed. Part III supplies that part and supersedes those earlier scope remarks.

## Definitions and statement of the classification

A primitive-positive formula is a finite conjunction of atomic formulas with some variables existentially quantified. Equalities are typed. A pp-definable relation is the relation of its free-variable assignments. A polymorphism of arity \(k\) is a family of functions, one \(k\)-ary function on each sort, preserving every relation by coordinatewise application.

An operation family is **idempotent** if \(t(x,\ldots,x)=x\) on every sort. It is **cyclic** if

\[
t(x_0,x_1,\ldots,x_{k-1})=t(x_1,\ldots,x_{k-1},x_0).
\]

It is a **Taylor family** if it is idempotent and, for each argument position \(i\), there are two words \(u^i,v^i\in\{x,y\}^k\), with \(u^i_i\ne v^i_i\), such that \(t(u^i)=t(v^i)\) on every sort. The same words must work simultaneously on all sorts. A cyclic idempotent operation of arity at least two is Taylor: rotate a word whose only \(x\) is in position \(i\) so that position \(i\) contains \(y\).

For \(N\ge1\), reduction \(q_N\) takes integer coordinates modulo \(N\) and leaves finite coordinates unchanged. The structure \(D_N^{\mathrm{pp}}\) has all the relations \(q_N(S)\), with \(S\) ranging over pp-definable relations of the original template. Thus \(Q\) means that every one of these finite-domain, possibly infinitely related structures has an idempotent Taylor polymorphism. The proof always works with the image of an entire pp diagram; it never replaces a simultaneous integer lift by unrelated atomwise lifts.

Adjoin all finite singleton pins, which preserves \(Q\) by Part I. Let \(\Pi_*\) be the partition of integer sorts under pp-definability of their literal numerical identity. Put

\[
m=\operatorname{lcm}(2,\text{all congruence moduli in all basic fibre presentations}),
\qquad
D=m^s\prod_j|E_j|,
\]

where \(s\) is the number of integer sorts and the \(E_j\) are all finite sorts. For \(s\ge1\), let \(p_0\) be the least prime greater than \(D\).

For a partition \(\Pi\), a **block-generic certificate at arity \(p\)** consists of one idempotent cyclic \(p\)-ary operation on every finite sort such that all basic relations are preserved generically by

\[
z_B=\sum_{i=0}^{p-1}\gamma_i^B x_B^i,
\qquad
\sum_i\gamma_i^B=1,
\qquad
\gamma_i^B\equiv p^{-1}\pmod m,
\]

using independent integer coefficient vectors for distinct blocks. “Generically” means outside a finite union of proper rational affine hyperplanes of the coefficient space, for each fixed input family. Part II gives an explicit arithmetic test for this condition, so the definition is effective and does not rely on an unspecified genericity oracle.

### Main theorem — PROVED, confidence 0.94

For the above finite-presentation setting, the following are equivalent:

1. \(Q\).
2. Some partition and some finite operation tables form a block-generic certificate at the single arity \(p_0\).
3. For the canonical partition \(\Pi_*\), there are block-generic cyclic certificates at every sufficiently large prime arity.

These equivalent conditions are decidable from the finite fibre presentations. Whenever they hold, \(\operatorname{CSP}(\mathcal M)\in\mathrm P\).

Under the question's stipulated implication \(\neg Q\Rightarrow\operatorname{CSP}(\mathcal M)\) NP-hard, the remaining templates are NP-complete. The NP upper bound is proved below. Consequently \(Q\) is an exact algebraic dividing condition for this dichotomy. Writing the literal equivalence “\(\operatorname{CSP}(\mathcal M)\in\mathrm P\iff Q\)” additionally presupposes \(\mathrm P\ne\mathrm{NP}\), as it does in every P/NP-complete dichotomy.

The proof is divided into three complete parts. Part I establishes the geometry forced by \(Q\) and the generic necessity statement. Part II proves amplification, the uniform converse for every modulus, and finite decidability. Part III proves the polynomial-time algorithm. The arithmetic appendix proves every additional algorithmic reduction used there, except for the explicitly cited normal-form and finite-CSP theorems.

### Relation to the original \(GC\) — PROVED, confidence 0.98

If all integer sorts belong to one pp-identification block, Part I gives a single common coefficient vector and hence the original \(GC\), using its generic-preservation characterization from the question. In particular, the result applies with one integer sort and arbitrary finite labels and torsion sorts. For independent sorts, \(GC\) can fail even though \(Q\) and polynomial-time solvability hold. The explicit two-sort example is proved again in the counterexample chapter.

The distinction concerns the allowed mixed-coordinate setting. No use is made here of the question's label-free “brief form” theorem; a version of that theorem using shared coefficients must have the corresponding restriction on how independent coordinate sorts can occur in zero forms.

---

# Part I. Structural necessity and pp-identifiable blocks

**Status: PROVED, confidence 0.97.** This chapter proves the necessity theorem used in the new finite criterion. Part II proves amplification of one finite cyclic certificate to all sufficiently large prime arities. Part III, `N_general_algorithm.md`, supplies the complete polynomial-time classification argument.

## 1. Conventions and exact statement

There are finitely many nonempty integer sorts, each identified externally with the additive group of integers and carrying the graph of addition and the constant $1$. There are finitely many nonempty finite sorts. The signature is finite. For every basic relation and every assignment of its finite arguments, a particular defining Boolean combination of integer-affine equations and congruences is fixed. A disequation is the negation of an equation. The external integer coordinates in this description may belong to different integer sorts. Such an external description does not, by itself, make a mixed-sort linear equation pp-definable.

A primitive-positive, or pp, formula is a formula obtained from atomic formulas using conjunction and existential quantification. Every relation defined by a pp formula is called pp-definable. Integer constants obtainable from $1$ and addition are allowed as an abbreviation for their pp definitions.

For $N\geq 1$, let $q_N$ reduce every integer coordinate modulo $N$ and leave every finite coordinate unchanged. The structure $D_N^{\mathrm{pp}}$ has all relations $q_N(S)$, where $S$ is pp-definable. A polymorphism is a family of operations, one for each sort and with a common arity, preserving every relation coordinatewise. An operation of arity $p$ is cyclic if

\[
f(x_0,x_1,\ldots,x_{p-1})=f(x_1,\ldots,x_{p-1},x_0).
\]

We assume $Q$: every $D_N^{\mathrm{pp}}$ has a Taylor polymorphism. The finite Taylor-to-cyclic theorem is used in the following precise form: on a finite idempotent algebra $A$, Taylor implies a cyclic term of every prime arity greater than $|A|$. The cited result is Barto and Kozik (2012), *Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem*, Theorem 4.1. Applied to the direct product of the finite sorts, it supplies common cyclic operations on all sorts. To see that an infinite relational signature is harmless here, choose one Taylor polymorphism, regard it as the sole basic operation of a finite algebra, apply the theorem, and observe that every term in this operation preserves every original relation.

We may add constants for every element of every finite sort. Indeed, a pp formula using finite parameters becomes a parameter-free pp formula after replacing those parameters by extra free variables. Its mod-$N$ image is the fibre of that pp image at the specified finite values. Idempotent polymorphisms preserve every such fibre. Consequently this expansion preserves $Q$. All pp-definability statements in this note refer to this expansion.

For two integer sorts $s,t$, define $s\sim t$ when the coordinate identity

\[
E_{st}=\{(a,b)\in Z_s\times Z_t:a=b\text{ as external integers}\}
\]

is pp-definable. This is an equivalence relation. Reflexivity is equality. Symmetry interchanges the two variables. If $E_{st}$ and $E_{tu}$ are pp-definable, then

\[
E_{su}(x,z)\iff\exists y\,[E_{st}(x,y)\wedge E_{tu}(y,z)]
\]

proves transitivity. Write $\Pi$ for its partition into blocks.

Fix an integer $m\geq 1$ divisible by every congruence modulus in every fixed basic-fibre description. Such an $m$ exists because the signature and the finite sorts are finite.

For $p\nmid m$, a block coefficient vector is an integer vector $\gamma^b=(\gamma^b_0,\ldots,\gamma^b_{p-1})$ satisfying

\[
\sum_i\gamma_i^b=1,
\qquad
\gamma_i^b\equiv p^{-1}\pmod m\quad(0\leq i<p).
\]

Coefficient vectors for distinct blocks are independent. Their rational affine parameter space is

\[
P_p=\prod_{b\in\Pi}\{\gamma^b\in\mathbb Q^p:\sum_i\gamma_i^b=1\}.
\]

Their permitted integer set is denoted $\Gamma_{p,m}\subseteq P_p$. A statement about these coefficients holds generically if it holds at every point of $\Gamma_{p,m}$ outside a finite union of proper rational affine hyperplanes of $P_p$. A hyperplane with empty intersection with $P_p$ imposes no restriction.

**Theorem 1 — PROVED, confidence 0.97.** Assume $Q$. For every sufficiently large prime $p\nmid m$, there is one common cyclic idempotent family $c_p$ on the finite sorts with the following property. For every basic relation $R$, and every $p$ tuples $(x^i,\eta^i)\in R$, form the finite output $\eta^*=c_p(\eta^0,\ldots,\eta^{p-1})$ coordinatewise. For an integer coordinate $j$ whose sort belongs to block $b$, set

\[
z_j=\sum_{i=0}^{p-1}\gamma_i^b x_j^i.
\]

Then $(z,\eta^*)\in R$ for generic coefficients $\gamma\in\Gamma_{p,m}$. The same coefficient choice can satisfy any specified finite collection of these tests simultaneously.

The proof occupies Sections 2–7. Section 8 gives an explicit decision procedure for testing any proposed finite operation family, partition, arity, supports, and residue coefficients.

## 2. Elementary arithmetic and finite avoidance

**Lemma 2.1 — PROVED, confidence 1.00.** Within one block of $\Pi$, every integer linear equation and every congruence is pp-definable.

**Proof.** The equation $z+1=1$ defines $z=0$. The equation $x+y=0$ defines the additive inverse of $x$. Repeated addition defines multiplication by every nonnegative integer; composition with additive inversion defines multiplication by negative integers. Repeated addition of $1$, together with inversion, defines every integer constant. Any integer linear equation can therefore be assembled using addition graphs and existential variables for intermediate values. If its variables lie in several sorts of one block, use the pp coordinate identities to copy all of them into one selected sort of that block, assemble the equation there, and existentially quantify the copies. Finally,

\[
\ell(x)\equiv r\pmod d
\quad\Longleftrightarrow\quad
\exists w\,[\ell(x)-r=d w]
\]

defines a congruence. Every variable in this last equation can be placed in the selected sort. This proves the claim. $\square$

**Lemma 2.2 — PROVED, confidence 1.00.** Let $P$ be a rational affine space and let $\Gamma\subseteq P$ contain a parametrized lattice

\[
a+\mathbb Z v_1+\cdots+\mathbb Z v_d
\]

whose rational affine hull is $P$. Given finitely many rational polynomial functions on $P$, none identically zero, some point of this lattice makes all of them nonzero.

**Proof.** Choose the $v_i$ to be a rational basis of the direction space of $P$; if the displayed vectors are redundant, select a spanning independent subfamily. Substitution $x=a+\sum_i t_i v_i$ turns each polynomial into a nonzero polynomial over $\mathbb Q$ in $d$ variables. Their product is nonzero: order monomials lexicographically after comparing total degree; the product of the leading monomials is the leading monomial of the product and has nonzero coefficient.

A nonzero rational polynomial $F(t_1,\ldots,t_d)$ cannot vanish on all of $\mathbb Z^d$. Here is a proof by induction on $d$. For $d=0$, $F$ is a nonzero constant. For $d>0$, write $F=\sum_{k=0}^K F_k(t_1,\ldots,t_{d-1})t_d^k$, where $F_K\ne0$. The induction hypothesis gives integers $t_1,\ldots,t_{d-1}$ at which $F_K\ne0$. The resulting univariate polynomial has at most $K$ roots: division by $t-a$ removes each distinct root and lowers the degree by one. Choose an integer $t_d$ outside this finite set of roots. At that integer point the product, and hence every factor, is nonzero. $\square$

Every coefficient set $\Gamma_{p,m}$ contains such a lattice with hull $P_p$. In one block, choose an integer $a\equiv p^{-1}\pmod m$; the vector

\[
(1-(p-1)a,a,\ldots,a)
\]

belongs to the permitted set. All its differences with the permitted set include $m(e_i-e_0)$, $1\leq i<p$, and these vectors span the direction space. Taking their product over blocks proves the assertion.

## 3. What $Q$ forces on pp integer relations

**Lemma 3.1 — PROVED, confidence 1.00.** A cyclic $p$-ary polymorphism of $D_N^{\mathrm{pp}}$, where $p\nmid N$, acts on every integer sort by

\[
(u_0,\ldots,u_{p-1})\longmapsto p^{-1}\sum_i u_i\pmod N.
\]

**Proof.** Preservation of the addition graph says that its integer component $f:(\mathbb Z/N)^p\to\mathbb Z/N$ is a group homomorphism. Thus

\[
f(u_0,\ldots,u_{p-1})=\sum_i a_i u_i,
\qquad a_i=f(e_i).
\]

Cyclicity gives $a_i=a_{i+1}$ for all indices modulo $p$. Preservation of the constant $1$ gives $\sum_i a_i=1$. Therefore all coefficients equal the unique inverse $p^{-1}\pmod N$. When $N=1$, both the domain and codomain of each integer component are singleton groups, and the same formula denotes their unique operation. $\square$

**Lemma 3.2 — PROVED, confidence 1.00.** Under $Q$, if $S$ is a pp-definable relation with only integer free coordinates, then $q_N(S)$ is empty or a coset of an additive subgroup of $(\mathbb Z/N)^d$.

**Proof.** Assume $q_N(S)\ne\varnothing$. Choose a prime $p\nmid N$, greater than $3(N-1)$, for which $D_N^{\mathrm{pp}}$ has a common cyclic $p$-ary polymorphism. The cited finite theorem supplies every sufficiently large prime, so this choice is possible. Choose $k_0,k_1,k_2\in\{0,\ldots,N-1\}$ congruent respectively to $p,p,-p\pmod N$. Their sum $t$ is at most $3(N-1)<p$, and $p-t$ is divisible by $N$. Add $p-t$ to $k_2$, leaving the other two counts unchanged. The resulting nonnegative counts sum to $p$ and have the same residues modulo $N$.

For $a,b,c\in q_N(S)$, apply the cyclic polymorphism to $k_0$ copies of $a$, $k_1$ copies of $b$, and $k_2$ copies of $c$. Lemma 3.1 gives $a+b-c\in q_N(S)$. Fix $a_0\in q_N(S)$ and put $B=q_N(S)-a_0$. Then $0\in B$, and $B$ is closed under $u+v-w$. In particular $u+v\in B$ and $-u\in B$ whenever $u,v\in B$. Hence $B$ is an additive subgroup and $q_N(S)=a_0+B$. For $N=1$, the conclusion follows because the ambient group is a singleton. $\square$

**Lemma 3.3 (finite hyperplane cover) — PROVED, confidence 1.00.** Under $Q$, suppose a pp-definable integer relation $S$ is contained in a union of a nonempty finite family of rational affine hyperplanes. Then one of those hyperplanes contains $S$.

**Proof.** Clear denominators in the hyperplane equations and write the cover as $S\subseteq\bigcup_{j=1}^h\{\ell_j=0\}$, with integer-affine forms $\ell_j$. If $S$ is empty, every hyperplane contains it. Assume $S\ne\varnothing$ and that no hyperplane contains it. For each $j$, choose $s_j\in S$ with $\ell_j(s_j)\ne0$. Choose a prime $q>h$ and $q>|\ell_j(s_j)|$ for every $j$.

By Lemma 3.2, $A=q_q(S)$ is an affine subspace over $\mathbb F_q$: an additive subgroup of $(\mathbb Z/q)^d$ is closed under multiplication by all elements of $\mathbb F_q$, because scalar multiplication is repeated addition. Each reduced equation $\ell_j=0$ cuts out a proper subset of $A$, since $q_q(s_j)$ violates it. Such an intersection is empty or has cardinality $|A|/q$. To verify the latter claim, translate $A$ to its direction vector space $V$. If the linear part of $\ell_j$ vanishes on $V$, the proper intersection is empty. Otherwise choose $v\in V$ on which that linear part is nonzero. Each coset of the one-dimensional subspace $\mathbb F_qv$ has $q$ points, and the equation has exactly one solution on that coset. The claimed cardinality follows.

Reducing the original cover modulo $q$ gives

\[
|A|\leq\sum_{j=1}^h|A\cap\{\ell_j=0\}|\leq h|A|/q<|A|,
\]

a contradiction. $\square$

## 4. Extracting the direction lattice of a pp slice

For a nonempty set $S\subseteq\mathbb Z^d$, write $\operatorname{aff}_{\mathbb Q}S$ for its rational affine hull, the intersection of all rational affine spaces containing it. Equivalently, for any $s_0\in S$, it is $s_0+\operatorname{span}_{\mathbb Q}\{s-s_0:s\in S\}$. Its direction space is the corresponding rational linear space.

**Lemma 4.1 — PROVED, confidence 0.99.** Assume $Q$. Let $S\subseteq\mathbb Z^d$ be nonempty and pp-definable. Suppose $S$ has an explicit Boolean description by affine equations and congruences, all congruence moduli divide $m$, and all its elements have one residue $r\pmod m$. Put

\[
A=\operatorname{aff}_{\mathbb Q}S,
\qquad V=A-A,
\qquad L=V\cap\mathbb Z^d.
\]

Then $S-S=mL$. In particular, the relation $L$, with each coordinate retaining its original sort, is pp-definable by

\[
L(w)\iff\exists u,v\,[S(u)\wedge S(v)\wedge\bigwedge_{j=1}^d(u_j-v_j=mw_j)].
\]

Moreover, $S$ contains every point of $A\cap(r+m\mathbb Z^d)$ outside finitely many proper rational affine hyperplanes of $A$.

**Proof.** The affine space $A$ has rational defining equations. For completeness, choose a rational basis of its direction space, extend it to a basis of $\mathbb Q^d$, and take the dual coordinate functionals corresponding to the added basis vectors. Their vanishing on $x-s_0$, for a fixed $s_0\in S$, defines $A$. Multiplying by common denominators gives integer-affine equations.

Conjoin these equations to the external Boolean description of $S$. This changes no points of $S$. This is an external-description step; it does not assert that the equations of $A$ are individually pp-definable. On the residue class $r+m\mathbb Z^d$, every congruence in the description has a fixed truth value because its modulus divides $m$. Replace it by that truth value. Distribute the resulting finite Boolean formula into disjunctive normal form, changing negated equations to disequations. Discard empty disjuncts. We obtain finitely many nonempty cells

\[
C_j=\bigl(E_j\cap(r+m\mathbb Z^d)\bigr)\setminus\bigcup_t\{h_{jt}=0\},
\]

where $E_j\subseteq A$ is a rational affine subspace and each $h_{jt}$ is an integer-affine form.

At least one $E_j$ equals $A$. If all were proper, each $E_j$ would lie in a rational affine hyperplane whose equation is not identically zero on $A$. To construct such a hyperplane, choose a rational point of $E_j$, extend a basis of the direction of $E_j$ to one of the direction of $A$, and take a dual functional nonzero on one added vector. Extend that functional to $\mathbb Q^d$, translate its zero equation through the chosen point, and clear denominators. These finitely many hyperplanes would cover $S$. Lemma 3.3 would put all of $S$ in one of them, so its affine hull $A$ would lie in that hyperplane, contradicting its construction.

Choose a nonempty full-hull cell $C$ with $E_j=A$, and choose $a\in C$. Then

\[
A\cap(r+m\mathbb Z^d)=a+mL.
\]

Indeed, a point $z$ belongs to the left side exactly when $z-a\in V\cap m\mathbb Z^d=m(V\cap\mathbb Z^d)=mL$. The lattice $a+mL$ has affine hull $A$: a rational basis of $V$, multiplied by suitable nonzero integer denominators, supplies integer vectors in $L$ spanning $V$. Every excluded form $h_t$ in this cell is nonzero as an affine function on $A$, because the cell contains $a$.

The inclusion $S-S\subseteq mL$ follows from the fixed residue and $S\subseteq A$. For the reverse inclusion, let $h\in mL$. Translation by $h$ maps $A$ bijectively to itself. Thus every function $z\mapsto h_t(z)$, and every function $z\mapsto h_t(z+h)$, is nonzero on $A$. Lemma 2.2 applied to a spanning lattice inside $a+mL$ gives $z\in a+mL$ at which all these functions are nonzero. Both $z$ and $z+h$ belong to the selected cell, hence to $S$. Their difference is $h$. Therefore $S-S=mL$.

The displayed pp formula now defines $L$: its witnesses exist exactly when $mw\in S-S=mL$, which is equivalent to $w\in L$. All equations $u_j-v_j=mw_j$ are within one original integer sort and are pp-definable by Lemma 2.1. Finally, the full-hull cell $C\subseteq S$ proves the last assertion. $\square$

**Lemma 4.2 (no fixed residue required for direction extraction) — PROVED, confidence 0.99.** In Lemma 4.1, omit the requirement that $S$ has a single residue modulo $m$, and retain the requirement that every congruence modulus in its Boolean description divides $m$. Then

\[
m(V\cap\mathbb Z^d)\subseteq S-S\subseteq V\cap\mathbb Z^d,
\]

and the same pp formula

\[
\exists u,v\,[S(u)\wedge S(v)\wedge(u-v=mw)]
\]

defines exactly $V\cap\mathbb Z^d$.

**Proof.** Add the external equations of $A=\operatorname{aff}_{\mathbb Q}S$ to its Boolean description. Split that description over the finitely many residue classes modulo $m$, and distribute the remaining equation and disequation conditions into cells. These are finitely many nonempty sets

\[
(E_j\cap(r_j+m\mathbb Z^d))\setminus\bigcup_t\{h_{jt}=0\},
\qquad E_j\subseteq A.
\]

If every $E_j$ were proper in $A$, their containing hyperplanes would contradict Lemma 3.3, exactly as in the proof of Lemma 4.1. Hence one cell has $E_j=A$. Choosing $a$ in that cell identifies its underlying lattice as $a+m(V\cap\mathbb Z^d)$. For any $h\in m(V\cap\mathbb Z^d)$, finite avoidance of the excluded forms at $z$ and at $z+h$ gives $z,z+h$ in that same cell. This proves the first inclusion. The second follows because every difference of two points of $A$ belongs to $V$ and is integral. Now if $w\in V\cap\mathbb Z^d$, then $mw\in S-S$, so the pp formula has witnesses. Conversely, if it has witnesses, then $mw\in V$; since $V$ is a rational linear space and $w$ is integral, $w\in V\cap\mathbb Z^d$. $\square$

The residue splitting in this proof is used to establish existence. It need not be performed by an algorithm, and its potentially exponential number of residue classes causes no computational step in the later affine-hull algorithm.

## 5. A pp direction lattice must split across maximal blocks

**Lemma 5.1 — PROVED, confidence 0.99.** Let $V\subseteq\mathbb Q^d$ be a rational linear space. Assign each coordinate its original integer sort and group coordinates according to the maximal pp-identity partition $\Pi$. If $V\cap\mathbb Z^d$ is pp-definable, then

\[
V=\prod_{b\in\Pi}V_b
\]

for rational subspaces $V_b$ in the coordinate spaces of the individual blocks.

**Proof.** Write the ambient vector space as $E=\bigoplus_bE_b$. Set $P_b=V\cap E_b$ and choose a rational complement $U_b$ with $E_b=P_b\oplus U_b$. Such a complement is obtained by extending a rational basis of $P_b$ to one of $E_b$. Put $P=\bigoplus_bP_b$ and $U=\bigoplus_bU_b$. Since $P\subseteq V$, decomposition in $E=P\oplus U$ gives

\[
V=P\oplus V',\qquad V'=V\cap U.
\]

No nonzero vector of $V'$ is supported in just one block: a vector of $V'\cap E_b$ would belong to both $P_b$ and $U_b$.

Suppose $V'\ne0$. Choose a nonzero vector of $V'$ whose block support $J$ has minimum cardinality. Multiplying by a positive integer denominator gives $a\in V'\cap\mathbb Z^d$ with that same support. Necessarily $|J|\geq2$. Consider

\[
W=V\cap\bigoplus_{b\in J}\mathbb Q a_b.
\]

The second space is contained in $U$, so $W\subseteq V'$. We claim $W=\mathbb Q a$. Inclusion $\mathbb Q a\subseteq W$ is immediate. If $w\in W$, write uniquely $w_b=t_ba_b$ for $b\in J$. If the rational numbers $t_b$ are not all equal, choose $b_0\in J$. Then $w-t_{b_0}a$ is a nonzero vector of $V'$ supported in a strict subset of $J$, contradicting minimality. Hence all $t_b$ are equal and $w\in\mathbb Qa$.

Let $L=V\cap\mathbb Z^d$. For each $b\in J$, choose one integer sort in that block and introduce an integer variable $t_b$ in it. Define the following relation on these variables by a pp formula:

\[
D((t_b)_{b\in J})\iff
\exists y\,[L(y)\wedge
\bigwedge_{b\in J}\bigwedge_{j\in b}(y_j=a_jt_b)
\wedge\bigwedge_{j\notin\cup_{b\in J}b}(y_j=0)].
\]

Each equation uses variables of one block, so Lemma 2.1 applies, including the required transport between sorts. A witness belongs to $W=\mathbb Qa$; since every $a_b\ne0$, this forces all $t_b$ to be the same integer. Conversely, if all $t_b=n\in\mathbb Z$, then $y=na\in L$ is a witness. Thus $D$ is exactly the relation saying that all its scalar arguments are the same external integer.

Choose two distinct blocks in $J$ and existentially quantify all other scalar variables. The resulting pp relation is the coordinate identity between the selected representative sorts of those two blocks. This contradicts maximality of the equivalence classes of $\Pi$. Therefore $V'=0$, and $V=P=\bigoplus_bP_b$, which is the asserted product. $\square$

An affine consequence will be used below. If $A\ne\varnothing$ and its direction $V$ splits as above, then for any $a\in A$,

\[
A=a+V=\prod_b(a_b+V_b).
\]

Thus the affine hull of every slice from Lemma 4.1 is a product across the maximal blocks.

## 6. A prime circulant cannot erase a nonzero integer vector

**Lemma 6.1 — PROVED, confidence 1.00.** Let $p$ be prime, let $\gamma_0,\ldots,\gamma_{p-1}\in\mathbb Z$ satisfy $\sum_i\gamma_i=1$, and let $a_0,\ldots,a_{p-1}\in\mathbb Z$. If

\[
\sum_i\gamma_i a_{i+j}=0\qquad(0\leq j<p),
\]

where indices are read modulo $p$, then every $a_i=0$.

**Proof.** Let $P$ be the cyclic permutation matrix with $(Pa)_j=a_{j+1}$. Put $G(t)=\sum_i\gamma_i t^i$. The equations are $G(P)a=0$. Since $G(1)=1$, polynomial division gives an integer polynomial $H$ with $G(t)=1+(t-1)H(t)$.

Reduce matrices modulo $p$. Since $P^p=I$, and every intermediate binomial coefficient $\binom pk$ is divisible by $p$,

\[
(P-I)^p=P^p-I=0.
\]

The matrices $P-I$ and $H(P)$ commute. Hence $K=(P-I)H(P)$ satisfies $K^p=0$, and

\[
(I+K)\sum_{r=0}^{p-1}(-K)^r=I.
\]

Thus $G(P)=I+K$ is invertible modulo $p$, and $a\equiv0\pmod p$. Write $a=pa^{(1)}$. The original integer equation gives $G(P)a^{(1)}=0$. Repeating the argument shows that every coordinate of $a$ is divisible by every power of $p$. The only integer with that property is $0$: a nonzero integer has absolute value less than $p^k$ for sufficiently large $k$, and cannot then be a nonzero multiple of $p^k$. $\square$

## 7. Proof of Theorem 1

Choose a sufficiently large prime $p\nmid m$ and a common cyclic idempotent $p$-ary polymorphism $f$ of $D_m^{\mathrm{pp}}$. Let $c_p$ be its restriction to the finite sorts. Fix one basic relation $R$ and input tuples $(x^i,\eta^i)\in R$, indexed by $\mathbb Z/p\mathbb Z$.

For block $b$, let $x_b^i$ collect all integer coordinates of that tuple belonging to sorts in $b$, and define

\[
H_b=\operatorname{aff}_{\mathbb Q}\{x_b^0,\ldots,x_b^{p-1}\},
\qquad H=\prod_bH_b.
\]

An empty coordinate block contributes the zero-dimensional one-point affine space. Each $H_b$ is pp-definable by equations within its block. Indeed, choose one input point, take a rational basis for the span of its differences from the other input points, extend to a basis of the ambient block coordinate space, use the corresponding dual equations, and clear denominators. Lemma 2.1 expresses the resulting integer-affine equations pp.

Let

\[
\eta^*=c_p(\eta^0,\ldots,\eta^{p-1}),
\qquad
r^*=p^{-1}\sum_iq_m(x^i).
\]

Consider the pp relation

\[
S=\{x\in H\cap\mathbb Z^d:R(x,\eta^*)\text{ and }x\equiv r^*\pmod m\}.
\]

All finite values $\eta^*$ are pinned. The equations for $H$ and the coordinatewise residue conditions are pp-definable. Its external Boolean description has congruence moduli dividing $m$.

We next prove $S\ne\varnothing$ and obtain enough points of it to determine its affine hull. Introduce, for each block $b$, integer variables $\gamma_i^b$ in one selected sort of that block, subject to $\sum_i\gamma_i^b=1$. For each $j\in\mathbb Z/p\mathbb Z$, introduce an integer tuple $Y_j$ and a finite tuple $\theta_j$. Impose

\[
Y_{j,b}=\sum_i\gamma_i^b x_b^{i+j},
\qquad R(Y_j,\theta_j).
\]

These equations are linear in the variables $\gamma_i^b$, because every $x_b^{i+j}$ is a fixed integer tuple. They can therefore be written pp using Lemma 2.1. Regard all displayed variables as free variables of one pp-definable relation $P$.

For each $h\in\mathbb Z/p\mathbb Z$, this relation has the tuple

\[
\gamma_i^b=\begin{cases}1&i=h,\\0&i\ne h,\end{cases}
\qquad Y_j=x^{h+j},\qquad\theta_j=\eta^{h+j}.
\]

Apply $f$ to the mod-$m$ images of these $p$ tuples. Since $q_m(P)$ is a relation of $D_m^{\mathrm{pp}}$, the output belongs to it and hence has an actual integer lift satisfying the entire displayed pp diagram. In that lift,

\[
\gamma_i^b\equiv p^{-1}\pmod m,
\qquad q_m(Y_j)=r^*,
\qquad\theta_j=\eta^*.
\]

The first two statements use Lemma 3.1. The last uses cyclicity of the finite operations: as $h$ runs through its ordered inputs, the list $(\eta^{h+j})_h$ is a cyclic rotation of $(\eta^h)_h$. The actual lift retains $\sum_i\gamma_i^b=1$, so $Y_{j,b}\in H_b$. Hence every $Y_j\in S$, and $S$ is nonempty.

Put $A=\operatorname{aff}_{\mathbb Q}S$ and $V=A-A$. Lemma 4.1 makes $V\cap\mathbb Z^d$ pp-definable. Lemma 5.1 therefore gives

\[
A=\prod_bA_b,
\qquad A_b\subseteq H_b.
\]

We claim $A_b=H_b$ for every block. Let $\ell$ be any integer-affine equation defining $A_b$. Since all $Y_{j,b}\in A_b$,

\[
0=\ell(Y_{j,b})=\sum_i\gamma_i^b\ell(x_b^{i+j})
\qquad(0\leq j<p).
\]

The second equality uses $\sum_i\gamma_i^b=1$ to account for the constant term of $\ell$. Lemma 6.1 implies $\ell(x_b^i)=0$ for every $i$. This holds for a full finite defining family of equations of $A_b$, so every $x_b^i\in A_b$. Their affine hull $H_b$ is contained in $A_b$. The reverse inclusion was already known. Therefore $A=H$.

The final assertion of Lemma 4.1 now gives proper rational affine hyperplanes $K_1,\ldots,K_t$ of $H$ such that

\[
\bigl(H\cap(r^*+m\mathbb Z^d)\bigr)\setminus\bigcup_{j=1}^tK_j\subseteq S.
\]

The rational affine map

\[
\Phi:P_p\longrightarrow H,
\qquad
\Phi(\gamma)_b=\sum_i\gamma_i^b x_b^i
\]

is surjective. In one block this is exactly the definition of the affine hull of the input points, and coefficient spaces for distinct blocks are independent. Hence the inverse image of every proper hyperplane $K_j$ is a proper hyperplane of $P_p$, or is empty. For $\gamma\in\Gamma_{p,m}$, the tuple $\Phi(\gamma)$ is integral and has residue $r^*$. Outside those finitely many inverse-image hyperplanes it belongs to $S$, giving the required output in $R$.

For any finite collection of tests, collect all their exceptional hyperplanes in the same coefficient space $P_p$. Lemma 2.2 gives a point of $\Gamma_{p,m}$ outside their union. Purely finite relations require no exceptional hyperplanes, since $c_p$ preserves them. Empty relations have no input tuples and impose no test. Zero-dimensional affine spaces are covered by the same proof: a proper affine hyperplane cannot contain their sole point, so their exceptional sets are empty. This handles all cases and proves Theorem 1. $\square$

**Corollary 7.1 (any existing prime cyclic polymorphism suffices) — PROVED, confidence 0.99.** Assume $Q$. Let $p$ be any prime coprime to $m$, and let $f$ be any common idempotent cyclic $p$-ary polymorphism of $D_m^{\mathrm{pp}}$. Its finite-sort components form a generic-preservation certificate, with full supports and coefficients congruent to $p^{-1}$ modulo $m$, on the maximal pp-identity partition.

**Proof.** The lower bound on $p$ in Theorem 1 was used only to obtain the existence of $f$ from the finite Taylor-to-cyclic theorem. Once $f$ is given, the construction in Section 7 applies to that very operation. Lemma 3.1 uses only coprimality of $p$ and $m$. The cyclic pp diagram uses only cyclicity. Lemma 6.1 uses only primality of $p$ and the integer coefficient sum $1$. The hyperplane-cover and direction-splitting arguments use $Q$ but impose no further restriction on this arity. Every conclusion in Section 7 therefore holds for the specified $f$ and $p$. $\square$

## 8. An explicit finite-operation generic-preservation test

This section allows arbitrary prescribed nonempty active supports. The full-support cyclic case in Theorem 1 is obtained by setting every support to $[n]$ and every residue coefficient to $n^{-1}\pmod m$, where $n$ is prime and coprime to $m$.

Fix a partition $\Pi$, an arity $n\geq1$, and for every block $b$:

- a nonempty support $I_b\subseteq\{1,\ldots,n\}$;
- residues $a_i^b\in\mathbb Z/m$ with $a_i^b=0$ for $i\notin I_b$ and $\sum_i a_i^b=1$.

Fix also an operation $f_A:A^n\to A$ on every finite sort $A$. Coefficients are required to satisfy

\[
\gamma_i^b=0\ (i\notin I_b),\qquad
\sum_i\gamma_i^b=1,\qquad
\gamma_i^b\equiv a_i^b\pmod m.
\]

These permitted integer coefficients form a nonempty affine lattice with the full rational affine hull obtained by omitting the congruence conditions. To construct a base point, choose an anchor $j_b\in I_b$, choose arbitrary integer lifts of all $a_i^b$ with $i\in I_b\setminus\{j_b\}$, set inactive entries to zero, and set the anchor to one minus the sum of the other entries. The residue-sum condition ensures the required anchor residue. The directions $m(e_i-e_{j_b})$ span the direction space.

**Lemma 8.1 (generic zero test) — PROVED, confidence 1.00.** Write an output integer-affine form as

\[
\ell(z)=c+\sum_b L_b(z_b),
\]

where every $L_b$ is homogeneous linear. For a fixed input array $x^1,\ldots,x^n$, the form $\ell(\sum_i\gamma_i^b x_b^i)_b$ is identically zero on the coefficient affine space if and only if

\[
L_b(x_b^i)=L_b(x_b^{j_b})
\quad\text{for every }b\text{ and }i\in I_b,
\]

and

\[
c+\sum_bL_b(x_b^{j_b})=0.
\]

**Proof.** Eliminate the anchor coefficient in each block by $\gamma_{j_b}^b=1-\sum_{i\in I_b\setminus\{j_b\}}\gamma_i^b$. The form becomes

\[
c+\sum_bL_b(x_b^{j_b})+
\sum_b\sum_{i\in I_b\setminus\{j_b\}}
\gamma_i^b\bigl(L_b(x_b^i)-L_b(x_b^{j_b})\bigr).
\]

The remaining coefficients are independent rational variables. An affine function of independent variables vanishes identically exactly when its constant term and every variable coefficient vanish. To verify necessity directly, evaluate first with all independent variables zero, and then with just one variable equal to $1$. Sufficiency follows by substitution. $\square$

Denote the displayed conjunction of input equations by $Z_\ell(X)$. It is a finite conjunction of integer linear equations in the input coordinates. No coefficient variable remains in it.

For a congruence $h(z)\equiv0\pmod d$, where $d\mid m$, write $h(z)=c+\sum_bH_b(z_b)$. Choose integer representatives $\alpha_i^b$ of the residue coefficients, with inactive representatives zero. Every permitted coefficient tuple gives the same congruence truth value, namely

\[
c+\sum_b\sum_i\alpha_i^bH_b(x_b^i)\equiv0\pmod d.
\]

Indeed, replacing $\alpha_i^b$ by $\gamma_i^b$ changes each summand by a multiple of $m$, hence by a multiple of $d$. The choice of representatives is immaterial for the same reason.

**Lemma 8.2 (exact generic truth) — PROVED, confidence 1.00.** Fix the finite input arguments $\eta^1,\ldots,\eta^n$ of a basic relation $R$, and let $\eta^*=f(\eta^1,\ldots,\eta^n)$. In the fixed defining Boolean formula $\varphi_{R,\eta^*}(z)$:

1. replace every equation $\ell(z)=0$ by $Z_\ell(X)$;
2. replace every disequation $\ell(z)\ne0$ by $\neg Z_\ell(X)$;
3. replace every congruence by the frozen congruence just displayed;
4. retain every Boolean connective.

Call the resulting Boolean-linear formula $G_{R,\eta^*}(X)$. For a fixed integer input array $X$, the output belongs to $R$ for generic permitted coefficients if and only if $G_{R,\eta^*}(X)$ is true.

**Proof.** Every output equation whose pullback is identically zero holds at every coefficient tuple. Each remaining output equation holds only on a proper rational affine hyperplane of the coefficient space. There are finitely many output forms. Outside the union of those proper hyperplanes, the truth value of every equation is exactly the truth value of its substituted predicate $Z_\ell(X)$, and disequations have the complementary truth values. Every congruence has its substituted value at every permitted coefficient tuple. Therefore the whole Boolean formula has the constant value $G_{R,\eta^*}(X)$ outside this finite exceptional union.

If that value is true, this proves generic preservation. If it is false, no finite collection of additional proper hyperplanes can make preservation generic: Lemma 2.2 supplies a permitted lattice point outside the union of the original and additional exceptional sets, and at that point the output still fails the relation. Thus the equivalence is exact, including coefficient spaces of dimension zero. $\square$

It follows that the proposed operation data generically preserve $R$ if and only if, for every tuple of finite input arguments, the following existential formula is unsatisfiable:

\[
\exists x^1\cdots x^n\left[
\bigwedge_{i=1}^n\varphi_{R,\eta^i}(x^i)
\ \wedge\ \neg G_{R,\eta^*}(X)
\right].
\]

This is a Boolean combination of integer linear equations, disequations, and congruences. All finite argument choices can be enumerated exactly because every finite sort is finite.

### 8.3 A self-contained satisfiability algorithm for the test formulas

**Lemma 8.3 — PROVED, confidence 1.00.** Satisfiability of the existential Boolean-linear formulas in the preceding display is decidable by a terminating, explicit arithmetic procedure.

**Proof.** Put the Boolean formula into disjunctive normal form. Negations of equations become disequations, and negations of disequations become equations. Replace a negated congruence modulo $d$ by the disjunction of its other $d-1$ possible residue classes. Distribute these finite disjunctions. It remains to decide finitely many conjunctions of linear equations, congruences, and disequations.

For each congruence $C_jx\equiv e_j\pmod{d_j}$, introduce an integer variable $y_j$ and the equation $C_jx-d_jy_j=e_j$. The equations and congruences become one integer matrix equation $Az=b$. We describe a finite diagonalization algorithm that either finds no integer solution or gives all integer solutions.

Keep track of invertible integer row and column operations. If the current matrix is zero, stop. Otherwise move a nonzero entry to the top-left position by row and column swaps, and multiply its row by $-1$ if necessary to make the pivot positive. Divide each other entry of the first column by the pivot using the division algorithm and subtract the corresponding multiple of the first row. A nonzero remainder has smaller absolute value than the pivot; move it to the pivot position and repeat. Once the first-column entries are multiples of the pivot, subtract the required multiples to make them zero. Perform the corresponding division and subtraction operations on the first row using columns. If a nonzero remainder occurs, exchange its column with the first column, obtaining a smaller positive pivot, and repeat the row and column reductions. Each return caused by a nonzero remainder strictly decreases the positive pivot. There can be only finitely many such returns. Between them, only finitely many entries are processed. Eventually the first row and column have no nonzero entries except the pivot. Apply the same procedure to the remaining lower-right submatrix. There are finitely many rows and columns, so this recursive procedure terminates.

The outcome is $UAV=D$, where $U,V$ are products of integer row or column elementary matrices with integer inverses, and $D$ is diagonal with nonzero entries $d_1,\ldots,d_r$ followed by zeros. The original equation is equivalent, under $z=Vw$, to $Dw=Ub$. It has an integer solution exactly when $d_i\mid(Ub)_i$ for $1\leq i\leq r$, and all entries of $Ub$ in zero rows are zero. These finitely many conditions are directly decidable. If they hold, the first $r$ coordinates of $w$ are fixed quotients; all remaining coordinates are arbitrary integers. Thus all solutions have the explicit form

\[
z=z_0+\sum_{j=1}^k t_jv_j,
\qquad t_j\in\mathbb Z,
\]

where the vectors $v_j$ are the appropriate columns of $V$.

Substitute this parametrization into every disequation. Each becomes an integer-affine form in $t_1,\ldots,t_k$ required to be nonzero. If one is identically zero, the conjunction is unsatisfiable. If none is identically zero, the conjunction is satisfiable by Lemma 2.2. This last existence check can also produce a finite-search witness without an unbounded search: substitute $t_j=T^j$. Each disequation becomes a nonzero univariate polynomial of degree at most $k$. If there are $h$ disequations, at most $hk$ integers are excluded; one of $T=0,1,\ldots,hk$ works. When $k=0$, all disequations are nonzero constants and the unique equation solution works.

Accept the original formula if at least one disjunct is satisfiable, and reject it otherwise. Every step terminates. $\square$

The procedure is a decision procedure, not a polynomial-time bound. Its use in a fixed finite certificate test is fully effective regardless of its cost.

## 9. Scope and audit

**PROVED, confidence 0.97.** The maximal pp-identity partition supplies independent blockwise generic cyclic closure under $Q$. Neither the proof nor the exact membership test requires deciding that maximal partition: a later finite criterion may enumerate all partitions of the finitely many integer sorts, since the maximal partition is one of them.

**PROVED, confidence 1.00.** The finite-operation test is a Boolean-linear satisfiability test. It contains no products of unknown input variables and unknown coefficient variables. The coefficient variables have been eliminated symbolically by Lemma 8.1.

**Adversarial audit.** The most delicate step is the extraction of a pp direction lattice from a fibre slice. A bare affine hull need not be pp-definable, and this chapter never assumes it is. Its equations are used only to organize an external Boolean description. For one residue slice the actual pp relation obtained is $V\cap\mathbb Z^d$, through the proved equality $S-S=m(V\cap\mathbb Z^d)$. Without a fixed residue, that exact difference equality need not hold; Lemma 4.2 proves the two inclusions that still make the same scaled-difference formula define the full direction lattice. The modulus must contain the congruence periods: without that hypothesis the required inclusion of $m(V\cap\mathbb Z^d)$ is not justified.

The second delicate step is the block-splitting lemma. It uses a minimal-support vector in a quotient complement of the within-block directions, not a minimal-support vector in the original space $V$. This subtraction of within-block directions is essential: the original space can contain many single-block vectors even when it has additional mixed constraints. The complement construction makes the pp-defined scalar equality exact, with no congruence or divisibility restriction.

The third delicate step is surjectivity of the coefficient map. It uses the product of the affine hulls for the maximal blocks, and genuinely independent coefficient vectors for distinct blocks. One common coefficient vector across all sorts need not map onto that product. Replacing the product by a common affine hull would invalidate the conclusion for the known independent-sort cancellation examples.

The algorithmic consequence for every finite-signature template satisfying $Q$ is proved in Part III. The original common-weight generic template is not equivalent to this blockwise closure when the integer sorts are independent, as the explicit counterexample chapter proves.

## 10. Recovering the blocks from a generic certificate

**Lemma 10.1 — PROVED, confidence 1.00.** Let $\Pi_0$ be any partition of the integer sorts. Suppose a full-support generic-preservation certificate exists at an arity $p\geq2$, with independent coefficient vectors on the blocks of $\Pi_0$. Then every pp-definable coordinate identity joins two sorts in the same block of $\Pi_0$. Thus $\Pi_0$ coarsens the maximal pp-identity partition.

**Proof.** First extend generic preservation from basic relations to any one pp formula

\[
S(x)\iff\exists y\,\bigwedge_{a=1}^k R_a(z_a).
\]

Take $p$ tuples in $S$ and select one witness tuple $y$ for each. For every atom $R_a$, the certificate supplies finitely many proper exceptional hyperplanes in the common coefficient space such that the combined assignment satisfies that atom outside those hyperplanes. The operation on a finite-sort variable is the prescribed finite operation, and the operation on every integer variable uses the coefficient vector for its block. The same combined value is therefore used at every occurrence of a variable. Outside the union of the $k$ finite exceptional families, all atoms hold simultaneously. Their combined existential variables witness the combined free tuple in $S$. Equality atoms are preserved when their two arguments have the same sort; constant atoms are preserved by idempotence and the condition that coefficients sum to one. These observations also cover pp formulas that explicitly contain equality and constants.

Now suppose $E_{st}=\{(n,n):n\in\mathbb Z\}$ is pp-definable, but $s,t$ belong to distinct blocks $b,b'$ of $\Pi_0$. Apply the preceding extension to the $p$ pairs $(1,1),(0,0),\ldots,(0,0)$. Their combined free coordinates are $\gamma_1^b$ and $\gamma_1^{b'}$. Their difference is a nonzero affine function on the full coefficient space: set the coefficient vector in block $b$ to its first basis vertex, the coefficient vector in block $b'$ to its second basis vertex, and the vectors in other blocks to arbitrary basis vertices. The difference at this rational parameter point equals $1$. Hence its zero set is a proper hyperplane. Generic pp preservation says that the difference vanishes outside finitely many proper exceptional hyperplanes. Lemma 2.2 gives a permitted integer coefficient point outside those exceptional hyperplanes and outside the difference-zero hyperplane. At that point both conclusions would have to hold, which is impossible. Thus $s,t$ lie in the same certificate block. $\square$

**Corollary 10.2 — PROVED, confidence 0.99.** Suppose a finite test is proved equivalent to the existence of one full-support certificate, and suppose its successful certificates amplify to the arities required in Theorem 1. Under $Q$, the maximal pp-identity partition is the unique finest successful partition.

**Proof.** Theorem 1 makes the maximal pp-identity partition successful. Lemma 10.1 shows that every successful partition coarsens it. Hence it is the unique finest one. Enumerating the finite set of all partitions and applying the finite test recovers it whenever $Q$ holds. $\square$

---

# Part II. A finite certificate for all finite pp images

**Verdict — PROVED, confidence 0.98.** Under the hypotheses of Part I, the condition \(Q\) is equivalent to one explicitly decidable generic-preservation test at one fixed prime arity, for one of finitely many partitions of the integer sorts. A successful certificate yields cyclic polymorphisms of \(D_N^{\mathrm{pp}}\) for every \(N\geq 1\). The finest successful partition is exactly the partition into pp-identifiable integer sorts.

References to “Part I” mean the accompanying document *Independent integer blocks: necessity and an exact finite-operation test*, saved as \(N_{\mathrm{next\_structure}}\). All external uses of the finite Taylor theorem are to Barto and Kozik (2012), Theorem 4.1.

## II.1. Definitions and the finite search space

There are \(r\) integer sorts \(Z_1,\ldots,Z_r\), each carrying its actual addition relation and the constant \(1\), and finitely many nonempty finite sorts \(E_1,\ldots,E_t\). The finite sorts include the original label and torsion sorts. The signature is finite. For each basic relation \(R\) and each fixed tuple \(\eta\) of its finite arguments, a finite Boolean formula

\[
\varphi_{R,\eta}(x)
\]

is supplied. Its atomic predicates are integer-affine equalities \(\ell(x)=0\) and congruences \(\ell(x)\equiv 0\pmod d\), with integer coefficients and positive modulus \(d\). Negation is allowed. Integer coordinates from different sorts may occur in these external fibre descriptions.

A primitive-positive, or pp, formula is a formula formed from atomic formulas by conjunction and existential quantification. For \(N\geq 1\), the map \(q_N\) reduces integer coordinates modulo \(N\) and leaves finite coordinates unchanged. The relation symbols of \(D_N^{\mathrm{pp}}\) include \(q_N(S)\) for every pp-definable relation \(S\).

A many-sorted operation is a family of operations, one on each sort, all of the same arity. Preservation means coordinatewise preservation of each relation. An \(n\)-ary operation \(f\) is idempotent if \(f(a,\ldots,a)=a\), and cyclic if

\[
f(a_0,a_1,\ldots,a_{n-1})
 =
f(a_1,\ldots,a_{n-1},a_0).
\]

The condition \(Q\) says that every \(D_N^{\mathrm{pp}}\) has an idempotent Taylor polymorphism. We use the notion of Taylor operation in the following explicit form: in addition to idempotence, for every argument position \(j\) there is an identity

\[
f(u_0,\ldots,u_{n-1})=f(v_0,\ldots,v_{n-1}),
\qquad u_i,v_i\in\{X,Y\},
\qquad u_j\neq v_j.
\]

Finite singleton pins can be adjoined without changing \(Q\). The proof is given in Part I, Section 1: a pp relation with finite parameters is a slice of a parameter-free pp relation, and idempotent polymorphisms preserve such slices.

Until Section II.8, assume \(r\geq 1\). Choose

\[
m
 =
\operatorname{lcm}
 \bigl(2,\text{ all moduli in all supplied basic fibre formulas}\bigr).
\]

Thus \(m\geq 2\). If no congruence occurs, this definition gives \(m=2\). The factor \(2\) is used below to ensure that a nonzero residue coefficient can detect the syntactic presence of a variable.

Let \(\Pi\) be any partition of \(\{Z_1,\ldots,Z_r\}\). A block \(B\in\Pi\) groups integer sorts which will use the same coefficient vector. Different blocks have independent coefficient vectors. For \(n\geq 2\) coprime to \(m\), define the rational affine coefficient space

\[
W_{\Pi,n}
 =
\prod_{B\in\Pi}
 \left\{
   \gamma^B\in\mathbb Q^n:
   \sum_{i=0}^{n-1}\gamma_i^B=1
 \right\}.
\]

Its permitted integer coefficient set is

\[
\Gamma_{\Pi,n,m}
 =
\left\{
 \gamma\in W_{\Pi,n}:
 \gamma_i^B\in\mathbb Z,\quad
 \gamma_i^B\equiv n^{-1}\pmod m
 \text{ for every }B,i
\right\}.
\]

This set is nonempty and has rational affine hull \(W_{\Pi,n}\). To verify both facts, let \(a\) represent \(n^{-1}\pmod m\). The vector

\[
(1-(n-1)a,a,\ldots,a)
\]

belongs to one block's permitted set. Adding any integer multiple of \(m(e_i-e_0)\), for \(1\leq i<n\), preserves all congruences and the coefficient sum. These direction vectors span the whole direction space. Taking their product over blocks proves the assertion.

Let \(c=(c_E)_{E\in\{E_1,\ldots,E_t\}}\) be a family of \(n\)-ary operations on the finite sorts. It is idempotent and cyclic when every \(c_E\) is.

**Definition II.1 — generic certificate.** The triple \((\Pi,n,c)\) is a generic certificate modulo \(m\) if \(c\) is idempotent and cyclic and the following property holds. For every basic relation \(R\) and every list of actual tuples

\[
(x^0,\eta^0),\ldots,(x^{n-1},\eta^{n-1})\in R,
\]

put

\[
\eta^*=c(\eta^0,\ldots,\eta^{n-1})
\]

coordinatewise. For an integer coordinate \(j\) whose sort belongs to \(B\), put

\[
z_j(\gamma)
 =
\sum_{i=0}^{n-1}\gamma_i^B x_j^i.
\]

There is a finite union \(K\) of proper rational affine hyperplanes of \(W_{\Pi,n}\), depending on this relation and this list of input tuples, such that

\[
\gamma\in\Gamma_{\Pi,n,m}\setminus K
\quad\Longrightarrow\quad
(z(\gamma),\eta^*)\in R.
\]

This is a statement about the existence of many admissible integer combinations. It does not assert that one fixed integer affine operation is a polymorphism of the original structure.

The elementary avoidance result used below is Part I, Lemma 2.2: on a rational affine space, a full affine integer lattice cannot be covered by the zero sets of finitely many nonzero rational polynomials. That lemma includes its proof by induction on the number of variables.

### Lemma II.2 — extension to pp relations

**PROVED, confidence 1.00.** A generic certificate preserves every pp-definable relation in the same generic sense. Finite singleton parameters are allowed.

**Proof.** Fix \(n\) tuples of a pp relation and fix a pp definition of that relation. For each tuple choose one complete satisfying assignment of all existential variables. This produces \(n\) satisfying assignments of the same finite conjunction of atoms.

For every basic-relation atom, the generic-certificate property gives finitely many proper exceptional hyperplanes. Regard them as hyperplanes in the global coefficient space. If a block does not occur in that atom, pull its exceptions back along the projection which forgets that block. A proper hyperplane remains proper, since the projection is surjective.

A typed equality atom is preserved because its equal coordinates use the same block coefficients. An integer pin is preserved because the coefficients sum to \(1\). A finite pin is preserved by idempotence of \(c\). Every atom therefore holds after combination outside a finite union of proper hyperplanes. At every such coefficient choice the combined complete assignment witnesses the pp relation. Its free coordinates are the prescribed combination. This proves the assertion. \(\square\)

## II.2. Passing between many sorts and one finite algebra

### Lemma II.3 — the sorted product construction

**PROVED, confidence 1.00.** Let \(A_1,\ldots,A_s\) be finite nonempty sets, and let \(f_i:A_i^k\to A_i\) be operations of the same arity. The product

\[
A=A_1\times\cdots\times A_s
\]

has an operation \(f\) acting coordinatewise by the \(f_i\). Every term \(\tau\) in \(f\) acts coordinatewise by the corresponding terms in the \(f_i\). An identity for these term operations holds on \(A\) if and only if it holds on every factor.

If the \(f_i\) form a many-sorted polymorphism, every term family in them remains a many-sorted polymorphism, even when the relation signature is infinite.

**Proof.** For a term consisting of one variable, the coordinatewise assertion is the definition of projection. Suppose it holds for \(\tau_1,\ldots,\tau_k\). In the term \(f(\tau_1,\ldots,\tau_k)\), coordinate \(i\) is obtained by applying \(f_i\) to coordinate \(i\) of the subterms. It is therefore the corresponding term on \(A_i\). Induction proves the assertion for every term.

If an identity holds on every factor, it holds coordinatewise on their product. Conversely, fix arbitrary base points in all factors except \(A_i\), which is possible because every factor is nonempty. Varying only the \(A_i\) coordinates of the input tuples shows that an identity on the product implies the identity on \(A_i\).

For preservation, take input tuples of any one relation and evaluate a term recursively. Each leaf is an input tuple in the relation. At an internal node, the polymorphism is applied to tuples already in the relation, so its output remains in that relation. Thus the root tuple lies in the relation. The argument applies to each relation separately and imposes no finiteness requirement on the collection of relations. \(\square\)

### Lemma II.4 — a cyclic operation is Taylor

**PROVED, confidence 1.00.** An idempotent cyclic operation of arity \(k\geq 2\) is a Taylor operation.

**Proof.** For each argument position \(j\), form the tuple with \(X\) in position \(j\) and \(Y\) in every other position. Cyclically rotating that tuple gives a second tuple having \(Y\) in position \(j\), because \(k\geq 2\). The two operation values are equal by cyclicity. These are the required Taylor identities, and idempotence is assumed. \(\square\)

## II.3. Independent coefficients on a term tree

Fix a generic certificate \((\Pi,p,c)\), with \(p\geq 2\) and \(\gcd(p,m)=1\). A term in one \(p\)-ary operation symbol is viewed as a finite rooted tree. Repeated syntactic occurrences of a subterm are distinct nodes of this tree.

At each internal node and in each block, use a fresh coefficient vector from \(\Gamma_{\Pi,p,m}\). Finite coordinates are combined by \(c\). Thus finite output values are determined by the formal term, whereas integer values depend on the chosen node coefficients.

Let \(a\in\mathbb Z\) represent \(p^{-1}\pmod m\). We parameterize the coefficients at a node and block by independent integers \(u_1,\ldots,u_{p-1}\):

\[
\gamma_i=a+m u_i\quad(1\leq i<p),
\qquad
\gamma_0=1-\sum_{i=1}^{p-1}\gamma_i.
\]

All coefficients then have residue \(a\pmod m\). Over \(\mathbb Q\), this parameterization is a bijection onto the affine space of coefficient vectors with sum \(1\).

### Lemma II.5 — valid node parameters are polynomially dense

**PROVED, confidence 1.00.** Fix a basic relation \(R\), a term \(\tau\), and actual tuples of \(R\) assigned to its variables. Given any nonzero rational polynomial \(P\) in all the node parameters, one can choose integer node parameters such that every internal node output belongs to \(R\) and \(P\neq 0\).

**Proof.** Order the internal nodes so that each node follows its internal children. A finite tree admits such an order: repeatedly choose an unlisted node all of whose children have already been listed or are leaves.

We prove the assertion for every initial segment of that order. For the empty segment there are no parameters and a nonzero polynomial is a nonzero constant.

Suppose the assertion holds for the first \(j-1\) nodes. Let \(P\) be a nonzero polynomial in the parameters of the first \(j\) nodes. View \(P\) as a polynomial in the parameters of node \(j\), with coefficients that are polynomials in the earlier parameters. At least one coefficient polynomial is nonzero. By the induction hypothesis choose the earlier integer parameters so that all earlier outputs are in \(R\) and that coefficient polynomial is nonzero. The specialized polynomial \(P\) is nonzero in the remaining parameters of node \(j\).

Every child of node \(j\) is now an actual tuple of \(R\). The certificate gives finitely many proper exceptional hyperplanes for combining those child tuples. Under the displayed parameterization, those hyperplanes have nonzero affine defining polynomials. Multiply their defining polynomials and the specialized \(P\). The product is nonzero. Part I, Lemma 2.2, supplies integer parameters at which it is nonzero. The current output then belongs to \(R\), and \(P\neq 0\). This completes the induction. \(\square\)

The preceding induction is needed because the exceptional hyperplanes at a node may depend on its actual child values. No uniform choice of exceptions over all possible child values is assumed.

### Lemma II.6 — the root map has the required affine hull

**PROVED, confidence 1.00.** Suppose every variable \(X_0,\ldots,X_{q-1}\) occurs syntactically in \(\tau\). Fix integer input tuples \(x^0,\ldots,x^{q-1}\). The rational affine hull of the root outputs, allowing all rational sum-\(1\) node coefficients independently in each block, is

\[
H
 =
\prod_{B\in\Pi}
 \operatorname{aff}_{\mathbb Q}
 \{x_B^0,\ldots,x_B^{q-1}\}.
\]

Consequently, the pullback of every affine functional which is not identically zero on \(H\) is a nonzero polynomial in the node parameters.

**Proof.** Each nested combination in one block is an affine combination of the source tuples in that block. Its coefficients still sum to \(1\), as is proved by multiplying the outer coefficient sum by the inner coefficient sums. Hence every root output belongs to \(H\).

Fix one desired source index \(i_B\) for each block \(B\). Choose an occurrence of \(X_{i_B}\) in the term. Along the path from that occurrence to the root, give coefficient \(1\) to the child on the path and coefficient \(0\) to every other child. Give arbitrary sum-\(1\) coefficients to nodes off the path. Do this independently in every block. The root output in block \(B\) is then exactly \(x_B^{i_B}\).

The root image therefore contains every grid point \((x_B^{i_B})_B\). These grid points have affine hull \(H\). Indeed, start at the point \((x_B^0)_B\), change one block \(B\) to index \(i\), and subtract the starting point. The resulting vectors are supported in one block and equal \(x_B^i-x_B^0\) there. Their span is exactly the direction space of \(H\).

Every root coordinate is polynomial in the node parameters, by recursive substitution into the affine combinations. If a nonzero affine functional on \(H\) pulled back to the zero polynomial, it would vanish on the entire root image and therefore on its affine hull \(H\), a contradiction. \(\square\)

The \(0\)-\(1\) node coefficients in this proof are used only at rational parameter points to determine the affine hull. They need not satisfy the prescribed integer residues. The permitted integer coefficient lattice has the full rational parameter space as its affine hull, so this use is legitimate.

### Lemma II.7 — the two possible generic truth values

**PROVED, confidence 1.00.** Fix a basic relation \(R\), a finite argument tuple \(\eta\), a residue tuple \(r_0\pmod m\), and a nonempty rational affine space \(H\) such that

\[
H\cap(r_0+m\mathbb Z^d)\neq\varnothing.
\]

Exactly one of the following holds:

1. \(R(\,\cdot\,,\eta)\) contains every point of \(H\cap(r_0+m\mathbb Z^d)\) outside finitely many proper affine hyperplanes of \(H\).
2. \(R(\,\cdot\,,\eta)\cap H\cap(r_0+m\mathbb Z^d)\) is contained in finitely many proper affine hyperplanes of \(H\).

**Proof.** Every congruence atom in the fibre formula has constant truth value on the residue class, because its modulus divides \(m\). An exact affine equality is either identically true on \(H\), identically false there, or true exactly on a proper affine hyperplane of \(H\). Remove the finitely many hyperplanes from the third case. All atomic truth values, and hence the Boolean formula's truth value, are now constant.

If that constant value is true, conclusion 1 holds. If it is false, conclusion 2 holds. The residue lattice is not covered by finitely many proper hyperplanes, by Part I, Lemma 2.2. Hence both conclusions cannot hold at once. \(\square\)

## II.4. Amplification from one arity to all large prime arities

### Theorem II.8 — single-certificate amplification

**PROVED, confidence 0.99.** If \(r\geq 1\), \(m\geq 2\), and \((\Pi,p,c)\) is a generic certificate modulo \(m\), then \((\Pi,q,c_q)\) is a generic certificate modulo \(m\) for some idempotent cyclic family \(c_q\) at every prime arity

\[
q>
K,
\qquad
K=m^r\prod_{j=1}^t |E_j|.
\]

**Proof.** Form the finite product

\[
A=(\mathbb Z/m)^r\times E_1\times\cdots\times E_t.
\]

Give it one \(p\)-ary basic operation \(t\). On each numeric factor its component is

\[
(x_0,\ldots,x_{p-1})
 \longmapsto p^{-1}\sum_i x_i\pmod m,
\]

and on each finite factor it is \(c_E\). The operation \(t\) is idempotent and cyclic. By Lemma II.4 it is Taylor. Barto and Kozik (2012), Theorem 4.1, gives a cyclic \(q\)-ary term \(\tau_q\) in this one operation for every prime \(q>|A|=K\).

Lemma II.3 makes its component terms cyclic on every factor. They are idempotent: a term in an idempotent operation evaluates to \(a\) when all its variables equal \(a\), by induction on the term tree.

Each numerical component of \(\tau_q\) is a linear form modulo \(m\). This follows by induction: a variable is linear, and a \(p\)-mean of linear forms is linear. Its coefficients sum to \(1\), because the basic coefficients have sum \(1\) and composition multiplies and sums them without changing that total. Cyclicity implies that all \(q\) coefficients are equal, by evaluating the operation on the coordinate unit vectors. Their common value is \(q^{-1}\pmod m\). This inverse exists because \(q>K\geq m\).

Every variable \(X_0,\ldots,X_{q-1}\) occurs in the term. If \(X_i\) were absent, its coefficient in every numerical component would be \(0\). Its coefficient is instead the unit \(q^{-1}\), which is nonzero because \(m\geq 2\). This is the point at which an actual nontrivial numeric residue factor is used.

Let \(c_q\) be the finite components of \(\tau_q\). Fix \(q\) actual tuples of a basic relation \(R\). Evaluate the term tree with independent permitted integer coefficients at every node and block. Its finite root output is the fixed tuple

\[
\eta^*=c_q(\eta^0,\ldots,\eta^{q-1}),
\]

and its numeric root residue is the fixed tuple

\[
r_0=q^{-1}\sum_{i=0}^{q-1}x^i\pmod m.
\]

The residue assertion holds because each internal node reduces to the original \(p\)-mean modulo \(m\), so reduction of the whole tree is precisely the numerical component of \(\tau_q\).

Put

\[
H
 =
\prod_{B\in\Pi}
 \operatorname{aff}_{\mathbb Q}
 \{x_B^0,\ldots,x_B^{q-1}\}.
\]

Any integer choice of permitted node coefficients gives a root tuple in \(H\) at residue \(r_0\), whether or not that tuple lies in \(R\). Thus the residue lattice in Lemma II.7 is nonempty.

Suppose conclusion 2 of that lemma held. Its finitely many covering hyperplanes pull back under the root polynomial map to nonzero polynomials by Lemma II.6. Their product is nonzero; if there are no covering hyperplanes, take the polynomial \(1\). Lemma II.5 supplies integer node parameters such that every internal output belongs to \(R\) and this product is nonzero. The root then belongs to \(R\) but lies outside its asserted covering hyperplanes. This is a contradiction.

Conclusion 1 therefore holds. The direct \(q\)-ary coefficient map

\[
\gamma\longmapsto
 \left(\sum_i\gamma_i^B x_B^i\right)_{B\in\Pi}
\]

maps \(W_{\Pi,q}\) onto \(H\), because each block independently realizes every affine combination of its source points. Pulling back the finitely many excluded hyperplanes gives proper affine hyperplanes of \(W_{\Pi,q}\). Every permitted direct coefficient vector has residue \(r_0\). Outside those pullbacks its output belongs to \(R\) with finite tuple \(\eta^*\).

This is exactly the generic-certificate condition for \((\Pi,q,c_q)\). The finite operation table \(c_q\) came from the single fixed term \(\tau_q\), so it is independent of \(R\) and of its input tuples. \(\square\)

## II.5. Lifting the certificate to every modulus

### Theorem II.9 — all-\(N\) sufficiency

**PROVED, confidence 0.99.** If \(r\geq 1\) and a generic certificate exists modulo \(m\), then \(Q\) holds.

**Proof.** Fix any \(N\geq 1\). By Theorem II.8 choose a prime \(q>K\) coprime to \(N\) and a generic certificate \((\Pi,q,c_q)\). Such a prime exists because only finitely many primes divide \(N\).

Define an operation family \(f_N\) by the \(q\)-mean on each \(\mathbb Z/N\) sort and \(c_q\) on each finite sort. It is idempotent and cyclic. We prove that it preserves every pp-image relation.

Let \(S\) be pp-definable and take \(q\) tuples of \(q_N(S)\). Choose actual lifts \(u^0,\ldots,u^{q-1}\in S\). By Lemma II.2 their combinations with finite output \(c_q\) belong to \(S\) outside finitely many proper coefficient hyperplanes.

Set

\[
L=\operatorname{lcm}(m,N).
\]

Restrict coefficients to

\[
\sum_i\gamma_i^B=1,
\qquad
\gamma_i^B\equiv q^{-1}\pmod L.
\]

The permitted set is nonempty and has the same rational affine hull \(W_{\Pi,q}\), by the construction in Section II.1 with \(L\) in place of \(m\). It is a subset of the allowed mod-\(m\) set. Part I, Lemma 2.2, gives a coefficient choice in it outside the finitely many exceptional hyperplanes. The resulting tuple belongs to \(S\).

Modulo \(N\), its integer coordinates are exactly the \(q\)-means of the chosen input residues; its finite coordinates are exactly the \(c_q\) outputs. It is therefore an actual lift of the componentwise \(f_N\)-output. This proves preservation of \(q_N(S)\).

The argument applies to every pp relation \(S\), so \(f_N\) is an idempotent cyclic polymorphism of \(D_N^{\mathrm{pp}}\). Lemma II.4 makes it Taylor. Since \(N\) was arbitrary, \(Q\) follows. The case \(N=1\) is included: the numerical residue sorts then have one element, and the same lifting argument applies. \(\square\)

## II.6. The exact finite decision criterion

Define

\[
K=m^r\prod_{j=1}^t|E_j|,
\]

and let \(p_0\) be the least prime strictly greater than \(K\). This is a fixed number determined by the template and the chosen fibre presentations. Because \(r\geq 1\), it satisfies \(p_0>m\).

The finite search enumerates:

1. every partition \(\Pi\) of the \(r\) integer sorts;
2. every operation table \(c_E:E^{p_0}\to E\) on each finite sort;
3. only those table families satisfying all idempotence and cyclicity equalities.

There are finitely many partitions and finitely many tables. Each algebraic equality is checked on a finite list of inputs.

### Theorem II.10 — fixed-prime equivalence

**PROVED, confidence 0.98.** For \(r\geq 1\),

\[
Q
\quad\Longleftrightarrow\quad
\text{some enumerated }(\Pi,p_0,c)
\text{ is a generic certificate modulo }m.
\]

**Proof.** Suppose first that \(Q\) holds. Choose an idempotent Taylor polymorphism of \(D_m^{\mathrm{pp}}\). Apply the product construction of Lemma II.3 to its components. This gives a finite idempotent Taylor algebra of cardinality \(K\). Barto and Kozik (2012), Theorem 4.1, gives a cyclic \(p_0\)-ary term. Its sortwise components remain polymorphisms of every relation of \(D_m^{\mathrm{pp}}\), by Lemma II.3, and remain idempotent.

Its integer components are the \(p_0\)-means by Part I, Lemma 3.1. Part I, Corollary 7.1, applies to this particular prime and this particular cyclic polymorphism: its finite components give a generic certificate for the partition \(\Pi_*\) into maximal pp-identifiable classes. The pair \((\Pi_*,c)\) occurs in the finite enumeration.

Conversely, any enumerated candidate which is a generic certificate implies \(Q\) by Theorem II.9. No pp-definability assumption on the blocks of this candidate is needed in this direction. \(\square\)

### Lemma II.11 — explicit generic truth formula

**PROVED, confidence 1.00.** The generic-certificate test for each fixed candidate is an effective finite list of universal Boolean-linear implications.

**Proof.** Fix a basic relation \(R\), finite input tuples \(\eta^0,\ldots,\eta^{p_0-1}\), and their candidate output

\[
\eta^*=c(\eta^0,\ldots,\eta^{p_0-1}).
\]

For each output affine form write

\[
\ell(z)=a_0+\sum_{B\in\Pi}L_B(z_B),
\]

where \(L_B\) is the homogeneous linear part using the coordinates in block \(B\).

Replace an output equality \(\ell(z)=0\) by

\[
\ell(x^0)=0
\quad\wedge\quad
\bigwedge_{B\in\Pi}
\bigwedge_{i=1}^{p_0-1}
\left(
L_B(x_B^i)=L_B(x_B^0)
\right).
\tag{II.1}
\]

To justify this replacement, substitute the affine combinations and eliminate \(\gamma_0^B\):

\[
\ell(z)
 =
\ell(x^0)
 +
\sum_{B\in\Pi}
\sum_{i=1}^{p_0-1}
\gamma_i^B
\bigl(L_B(x_B^i)-L_B(x_B^0)\bigr).
\]

The coefficient variables are independent over \(\mathbb Q\). This affine expression is identically zero exactly when (II.1) holds. If it is not identically zero, its equality to zero is confined to a proper affine hyperplane and is generically false.

Replace an output congruence \(\ell(z)\equiv 0\pmod d\) by

\[
\sum_{i=0}^{p_0-1}\ell(x^i)\equiv 0\pmod d.
\tag{II.2}
\]

Indeed, \(d\mid m\), and every permitted coefficient is \(p_0^{-1}\pmod d\). Therefore

\[
\ell(z)
 \equiv
 a_0+p_0^{-1}\sum_{B,i}L_B(x_B^i)
 \equiv
 p_0^{-1}\sum_i\ell(x^i)
 \pmod d.
\]

The element \(p_0^{-1}\) is a unit modulo \(d\), proving the equivalence.

Keep every Boolean connective, including negations, from the fibre formula. Denote the resulting formula by

\[
\mathsf{Gen}_{\Pi,p_0}(\varphi_{R,\eta^*}).
\]

Outside the union of the finitely many exceptional exact-equality hyperplanes, every atomic predicate has precisely the replacement truth value. Hence the Boolean formula's generic truth is exactly the truth of \(\mathsf{Gen}\).

The candidate is a certificate exactly when, for every basic \(R\) and every finite input list, the following implication holds over integer source tuples:

\[
\forall x^0\cdots\forall x^{p_0-1}
\left[
 \bigwedge_{i=0}^{p_0-1}\varphi_{R,\eta^i}(x^i)
 \ \Longrightarrow\
 \mathsf{Gen}_{\Pi,p_0}(\varphi_{R,\eta^*})
\right].
\tag{II.3}
\]

For one direction, truth of the right-hand generic formula gives the required exceptional hyperplanes. For the other, if that formula is false for some actual input list, all valid output tuples lie in the intrinsic exceptional hyperplanes. A generic-certificate assertion would put all permitted coefficients outside another finite collection of proper hyperplanes into that same exceptional set. The avoidance lemma forbids this.

There are finitely many implications (II.3). Negating one yields an existential Boolean combination of integer-affine equations and congruences. Part I, Lemma 8.3, gives a terminating explicit decision procedure for exactly these formulas. Applying it to every negation decides the candidate. \(\square\)

The decision procedure is fully specified: compute \(m\) and \(p_0\), enumerate the partitions and finite operation tables, check the finite identities, form all formulas (II.3), and decide their negations by Part I, Lemma 8.3. This finite search is a decidability result; its size is not asserted to be polynomial in the description of the template.

## II.7. The finest passing partition

Let \(\Pi_*\) be the equivalence classes of literal pp-definable coordinate identity, allowing finite singleton parameters:

\[
Z_i\sim Z_j
\quad\Longleftrightarrow\quad
\{(a,b)\in Z_i\times Z_j:a=b\}
\text{ is pp-definable}.
\]

Reflexivity is typed equality; symmetry exchanges the two free variables; transitivity existentially composes two identity graphs. These facts establish that \(\Pi_*\) is a partition.

### Theorem II.12 — the partition is effectively recovered

**PROVED, confidence 0.99.** If \(Q\) holds, every partition occurring in a passing generic certificate is coarser than \(\Pi_*\), while \(\Pi_*\) itself passes. Consequently \(\Pi_*\) is the unique passing partition with the largest number of blocks.

**Proof.** Theorem II.10 and Part I, Corollary 7.1, show that \(\Pi_*\) passes at the fixed arity \(p_0\).

Suppose \((\Pi,p_0,c)\) passes and a pp identity graph links two sorts in different blocks \(B,C\) of \(\Pi\). By Lemma II.2 the graph is generically preserved. Give it the input \((1,1)\) in position \(0\) and the input \((0,0)\) in every other position. Its outputs are

\[
\gamma_0^B,\qquad \gamma_0^C.
\]

The equation \(\gamma_0^B=\gamma_0^C\) defines a proper affine hyperplane of \(W_{\Pi,p_0}\): the two block coefficient vectors vary independently, and \(p_0\geq 2\) permits either zeroth coordinate to change while its block sum remains \(1\). Generic preservation would require the full permitted coefficient lattice outside finitely many proper hyperplanes to lie inside this additional proper hyperplane. Part I, Lemma 2.2, makes that impossible.

Thus each \(\Pi_*\) class lies in one block of \(\Pi\). Every passing partition is coarser than \(\Pi_*\). A strictly coarser partition has strictly fewer blocks. Since \(\Pi_*\) itself passes, it is the unique passing partition with the largest block count. The finite search computes it. \(\square\)

This argument avoids a negative pp-definability test. The search never has to prove that an identity relation lacks a pp definition.

## II.8. The case of no integer sorts

Assume now \(r=0\). There is no coefficient space to vary, no modular arithmetic to lift, and no constraint on an arity arising from invertibility modulo \(m\). Every \(D_N^{\mathrm{pp}}\) is the same finite pp expansion of the original finite template.

Put

\[
K=\prod_{j=1}^t|E_j|,
\]

and let \(p_0\) be the least prime greater than \(K\). A certificate is simply an idempotent cyclic \(p_0\)-ary family preserving every basic finite relation.

### Theorem II.13 — finite-only case

**PROVED, confidence 1.00.** When \(r=0\), \(Q\) holds if and only if one of the finitely many idempotent cyclic \(p_0\)-ary families preserves every basic relation.

**Proof.** If \(Q\) holds, take a Taylor polymorphism of the finite pp expansion and apply Lemma II.3 and Barto and Kozik (2012), Theorem 4.1. The resulting \(p_0\)-ary cyclic term family preserves every basic relation and is idempotent.

Conversely, suppose such a family exists. It preserves every pp relation: choose witnesses for each input tuple, combine every variable by its sort component, and every atomic relation remains true. Lemma II.4 makes the family Taylor. Since all \(D_N^{\mathrm{pp}}\) coincide, \(Q\) follows for all \(N\).

There are finitely many operation tables. Idempotence, cyclicity, and preservation of each finite basic relation are checked by enumerating their finite input lists. Thus the test terminates. The only partition of the empty collection of integer sorts is the empty partition, so there is no partition-recovery issue. \(\square\)

If there are no sorts at all, the empty product is a one-element set. Only nullary relations can occur, their pp satisfiability is determined directly by their truth values, and the preceding empty operation-family conventions remain consistent.

## II.9. Adversarial audit of the amplification argument

**PROVED, confidence 0.99.** The use of \(m\geq 2\) is necessary for the chosen proof of syntactic variable occurrence. With a one-element numeric residue sort, every coefficient is numerically zero, so a cyclic term could omit variables without contradiction. The stipulated modulus includes \(2\), which removes that issue whenever an integer sort exists.

**PROVED, confidence 0.99.** Independent node coefficients do not assert a strict infinite-domain term operation. They construct one complete witness assignment for a finite diagram. Their finite coordinates and numerical residues still evaluate the same fixed finite term. Lemma II.5 is the precise justification for choosing those coefficients while avoiding a prescribed polynomial obstruction.

**PROVED, confidence 0.99.** Full algebraic dominance of the root coefficient map is unnecessary. Each fibre obstruction is an affine equality, so Lemma II.6's full affine hull makes its pullback a nonzero polynomial. Polynomial avoidance is exactly the amount of density used.

**PROVED, confidence 0.99.** The all-\(N\) argument is uniform. The modulus \(\operatorname{lcm}(m,N)\) imposes the desired residue output while preserving a full affine coefficient lattice. Restricting to that lattice cannot turn a proper rational affine hyperplane into a cover.

**Most delicate step.** The generic exceptional hyperplanes for a node can depend on its children. Lemma II.5 addresses this by first choosing earlier parameters so that one nonzero coefficient of the target polynomial survives, and only then choosing the current parameters. Replacing that induction by an assertion that “generic choices compose” would omit a necessary argument.

## II.10. External reference used in this part

Libor Barto and Marcin Kozik, 2012. *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*. Logical Methods in Computer Science 8(1), article 07. **Theorem 4.1**: a finite idempotent Taylor algebra has a cyclic term of every prime arity greater than its cardinality.

Primary article PDF: https://lmcs.episciences.org/673/pdf

---

# Part III. The general polynomial-time algorithm

## Verdict and the exact scope

**PROVED — confidence 0.97.** In the finite-signature, fully arithmetic, label-fibred setting specified below, property \(Q\) implies that the CSP is decidable in polynomial time. The algorithm uses exact residue images of individual atoms relative to a changing affine integer solution space. It refines that space only by original positive equations from the input, which controls both the number of refinements and all coefficient sizes.

**PROVED — confidence 0.97.** Combined with the separately proved equivalence between \(Q\) and a finite block-generic certificate, this gives an effective tractability criterion. The shared-coefficient criterion \(GC\) is not substituted for the block-generic criterion in this proof.

## 1. Setting, dependencies, and notation

### Definition 1.1: the template and the input model

**PROVED — confidence 1.00; this is a definition.** Fix a structure \(\mathcal M\) with finitely many integer sorts \(Z_s\), each externally identified with \(\mathbb Z\) and carrying the graph of addition and the singleton \(1\). There are finitely many nonempty finite sorts; these include the label sorts and any torsion sorts. The signature is finite. For every basic relation \(R\) and every assignment \(\eta\) of its finite arguments, fix a Boolean formula for the integer fibre \(R(\cdot,\eta)\), using affine integer equations, congruences, and their negations. Cross-sort affine forms in these external descriptions are allowed. Such an external form is not automatically a pp-definable mixed-sort arithmetic relation.

The input of \(\operatorname{CSP}(\mathcal M)\) is a finite primitive-positive sentence over this fixed signature. Its length is the input-size parameter. Every number in a basic fibre description is fixed with the template. Addition is represented relationally, so an input atom has bounded arity and a fixed coefficient description.

Choose and fix \(m\geq2\) divisible by every congruence modulus in the basic fibre descriptions. The choice \(m\geq2\) is harmless even when no congruence is present.

### Definition 1.2: \(Q\), blocks, and generic combinations

**PROVED — confidence 1.00; this is a definition.** For \(N\geq1\), \(q_N\) reduces integer coordinates modulo \(N\) and leaves finite coordinates unchanged. The finite many-sorted structure \(D_N^{\rm pp}\) contains \(q_N(S)\) for every pp-definable relation \(S\) of \(\mathcal M\). Property \(Q\) says that every \(D_N^{\rm pp}\) has an idempotent Taylor polymorphism.

Adjoin singleton relations for all elements of every finite sort. This preserves \(Q\): replace finite parameters in a pp formula by additional free variables, and use idempotence to preserve the corresponding pinned fibre of its pp image. Solving the original CSP reduces to solving this expansion by keeping the input unchanged, so a polynomial algorithm for the expansion is sufficient. All pp definitions below are in this finite-pinned expansion.

Two integer sorts are in the same block if the literal coordinate identity between them is pp-definable. This is an equivalence relation, because identity is reflexive, exchanging variables gives symmetry, and existential composition gives transitivity. Let \(\Pi_*\) be the resulting partition. Every affine integer equation involving sorts within a single block is pp-definable: use the coordinate identities to move values to one representative sort, addition and \(1\) to build each fixed coefficient and constant, and existential variables for intermediate sums. Congruences within a block are pp-definable by \(\ell(x)\equiv r\pmod d\iff\exists z\,[\ell(x)-r=dz]\).

For a prime \(p\nmid m\), a permitted block coefficient vector \(\gamma^b\) has integer entries with

\[
\sum_{i=1}^{p}\gamma_i^b=1,
\qquad
\gamma_i^b\equiv p^{-1}\pmod m.
\tag{1.1}
\]

Different blocks have independent vectors. Generic validity means validity outside finitely many proper rational affine hyperplanes of the product of these coefficient spaces.

### Proposition 1.3: previously proved structural facts used here

**PROVED — confidence 0.98, with full proofs in the companion structural chapters.** The following statements are used as established lemmas, rather than as unproved assumptions.

1. **Finite image affine-coset property.** If \(S\) is pp-definable and has only integer free coordinates, every nonempty \(q_N(S)\) is an affine subgroup coset. This is Lemma 3.2 of `N_next_structure.md`.
2. **Hyperplane-cover property.** If such an \(S\) is covered by finitely many rational affine hyperplanes, one of them contains \(S\). This is Lemma 3.3 of that chapter.
3. **Direction extraction.** If \(S\) has one residue modulo a period \(d\) of its Boolean arithmetic description and rational affine hull \(H\), then \(S-S=d((H-H)\cap\mathbb Z^n)\); hence the direction lattice is pp-definable by a scaled-difference formula. This is Lemma 4.1 of that chapter.
4. **Block splitting.** A rational linear space whose integer lattice is pp-definable is a product across \(\Pi_*\). This is Lemma 5.1 of that chapter.
5. **Block-generic operations.** For every sufficiently large prime \(p\nmid m\), there is a common cyclic idempotent operation \(c_p\) on all finite sorts such that the \(p\)-mean on integer residues together with \(c_p\) preserves every pp image modulo \(m\), and generic combinations using (1.1) preserve every basic relation. This is Theorem 1 of `N_next_structure.md`, with its uniform all-prime amplification also proved in Theorem II.8 of `N_amplification.md`.

The present chapter supplies the additional algorithm, its finite compression, every refinement step, and the complete polynomial-time bound. The referenced companion proofs are part of the full deliverable.

### Lemma 1.4: affine hulls of the pp sets needed by the algorithm split

**PROVED — confidence 0.99.** Suppose \(S\subseteq\mathbb Z^d\) is nonempty, pp-definable with parameter coordinates typed by blocks, and has an external Boolean description whose congruence moduli divide \(m\). Then \(\operatorname{aff}_{\mathbb Q}S\) is a product of rational affine spaces across the blocks.

**Proof.** Put \(H=\operatorname{aff}_{\mathbb Q}S\). Partition \(S\) into the finitely many residue slices

\[
S_r=S\cap(r+m\mathbb Z^d),\qquad r\in(\mathbb Z/m)^d.
\]

Each slice is pp-definable, since its coordinate congruences are within single sorts. At least one nonempty slice has affine hull \(H\). If not, the hull of each nonempty slice is a proper rational affine subspace of \(H\), hence lies in a rational affine hyperplane whose equation is not identically zero on \(H\). To obtain such a hyperplane, extend a basis of that proper subspace's direction to a basis of the direction of \(H\), choose a rational linear functional zero on the first basis and nonzero on an added vector, and translate its zero set through a rational point of the smaller affine space. Extend the functional to the ambient coordinate space. These finitely many hyperplanes cover \(S\). Proposition 1.3(2) would put all of \(S\), and therefore \(H\), in one of them, contradicting the choice of its equation.

Choose a slice \(S_r\) with hull \(H\). Proposition 1.3(3) makes \((H-H)\cap\mathbb Z^d\) pp-definable. Proposition 1.3(4) splits its rational direction space across the blocks. For a point \(a\in H\), translation gives

\[
H=a+(H-H)=\prod_b\bigl(a_b+(H-H)_b\bigr).
\]

This is the required product. ∎

## 2. Arithmetic and generic lemmas

### Lemma 2.1: finite avoidance on an integer affine coset

**PROVED — confidence 1.00.** Let \(U=u+H\subseteq\mathbb Z^n\) be a nonempty coset of an additive subgroup. If affine rational functions \(g_1,\ldots,g_r\) are each nonzero somewhere on \(U\), they are simultaneously nonzero at some point of \(U\).

**Proof.** Pick \(v_j\in U\) with \(g_j(v_j)\ne0\). For an integer \(t\), set

\[
z(t)=u+\sum_{j=1}^{r}t^j(v_j-u)\in U.
\]

For each \(i\),

\[
g_i(z(t))=g_i(u)+\sum_{j=1}^{r}t^j\bigl(g_i(v_j)-g_i(u)\bigr).
\]

If its constant coefficient is zero, its coefficient of \(t^i\) is \(g_i(v_i)\ne0\). If its constant coefficient is nonzero, the polynomial is already nonzero. Thus every displayed polynomial is nonzero. A nonzero degree-\(r\) polynomial has at most \(r\) roots, as follows by repeatedly factoring \(t-a\) at each distinct root. The union of the forbidden integer root sets is finite. Choose any integer outside it. For \(r=0\), any point of \(U\) works. ∎

### Lemma 2.2: integer equality systems, parametrizations, and exact residue images

**PROVED — confidence 0.99, using the cited normal-form theorem.** Given an integer matrix equation \(At=b\), one can in polynomial time determine whether it has an integer solution. If it does, one can compute an integer particular solution \(t_0\) and an integer matrix \(V_0\) whose columns are a basis of its homogeneous integer solution group, so that

\[
\{t\in\mathbb Z^d:At=b\}=t_0+V_0\mathbb Z^{d-r},
\qquad r=\operatorname{rank}_{\mathbb Q}A.
\tag{2.1}
\]

One can also compute \(r\) integer row vectors \(w_1,\ldots,w_r\) and integers \(c_1,\ldots,c_r\) such that, for every modulus \(m\geq1\), its exact residue image is

\[
q_m(\{t:At=b\})=
\{\bar t\in(\mathbb Z/m)^d:w_i\bar t=c_i\pmod m\text{ for }1\leq i\leq r\}.
\tag{2.2}
\]

All output matrices have bit length bounded by a polynomial in the input matrix size and coefficient bit length.

**Proof.** The normal-form algorithm used here is Kannan and Bachem (1979), *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, Theorem 2 together with Lemma 3: the square nonsingular integer Hermite computation and its unimodular multiplier have polynomial running time and polynomial output bit length. The following reduction specifies exactly how that result is used for a rectangular matrix.

First check rational consistency and select \(r\) linearly independent rows \(A'\) with the corresponding entries \(b'\). If rational consistency fails, reject. If it holds, every remaining row equation is the same rational linear combination of the selected equations as its right-hand side, so the selected system is equivalent over both \(\mathbb Q\) and \(\mathbb Z\). If \(r=0\), consistency means that all right-hand sides are zero, and the solution set is all of \(\mathbb Z^d\); take \(t_0=0\), \(V_0=I_d\), and no rows in (2.2).

For \(r>0\), permute columns so that \(A'P=[C\ D]\), with \(C\) an invertible \(r\times r\) matrix. Form the nonsingular square integer matrix

\[
W=\begin{pmatrix}C&D\\0&I_{d-r}\end{pmatrix}.
\]

Apply the cited algorithm in the column, lower-triangular convention. Transposition converts an alternative row convention to this one. It supplies a unimodular integer matrix \(U\) for which

\[
WU=\begin{pmatrix}H_0&0\\H_1&H_2\end{pmatrix},
\]

where \(H_0\) is nonsingular. Put \(V=PU\). Then \(A'V=[H_0\ 0]\), and \(V\) is unimodular. Writing \(t=Vz\), the system is equivalent to

\[
z_1,\ldots,z_r=H_0^{-1}b'.
\]

If this fixed vector is not integral, no integer \(z\), hence no integer \(t\), exists. If it is integral, call it \(c\), take \(t_0=V(c,0)\), and take \(V_0\) to be the last \(d-r\) columns of \(V\). Every integer solution has a unique such free-coordinate vector because \(V^{-1}\) is integral. This proves (2.1).

Let \(w_i\) be row \(i\) of \(V^{-1}\), \(1\leq i\leq r\). An integer residue vector \(\bar t\) lifts to a solution if and only if its \(z=V^{-1}t\) residues have first \(r\) entries \(c_i\pmod m\). Necessity follows from the fixed exact \(z_i=c_i\). For sufficiency, choose \(z_i=c_i\) exactly for \(i\leq r\), and lift each remaining residue coordinate arbitrarily to an integer. The vector \(t=Vz\) is an exact solution with the required residue. This proves (2.2).

The auxiliary square matrix has polynomial size and coefficient length. The cited theorem bounds the Hermite computation and \(U\). Inverting a unimodular matrix and the nonsingular block \(H_0\), and selecting independent rows and columns, can be done by exact rational elimination in polynomial bit complexity. For a direct size bound on the rational intermediate values, every reduced fraction obtained while solving an independent subsystem is a ratio of subdeterminants by Cramer's formula; a determinant of an \(s\times s\) integer matrix with entries of absolute value at most \(B\) has absolute value at most \(s!B^s\), by its permutation expansion. Its bit length is at most \(\log_2(s!)+s\log_2\max(1,B)+1\), polynomial in matrix dimension and input bit length. Fraction reduction after each arithmetic operation maintains these bounds. Integer matrix multiplication has polynomially many operations with those bounded lengths. This proves the claimed bit and time bounds. ∎

### Lemma 2.3: a nonempty residue slice of an equality coset has full rational hull

**PROVED — confidence 1.00.** Let \(E=\{t\in\mathbb Z^d:At=b\}\ne\varnothing\), with rational affine hull \(H\). If \(E\cap(r+m\mathbb Z^d)\) is nonempty, its rational affine hull is also \(H\). If finitely many affine disequalities are each nonzero somewhere on \(H\), removing their zero sets from this residue slice leaves a nonempty set with rational affine hull \(H\).

**Proof.** Write \(E=t_0+K\), where \(K=\ker_{\mathbb Q}A\cap\mathbb Z^d\). This equality follows by subtracting one integer solution. If \(t_1\) lies in the residue slice, that slice is

\[
t_1+(K\cap m\mathbb Z^d)=t_1+mK.
\]

Indeed \(mv\in K\) with \(v\in\mathbb Z^d\) implies \(Av=0\), since \(mAv=0\) in the torsion-free integer group. The integer kernel \(K\) spans \(\ker_{\mathbb Q}A\): multiply each vector of a rational basis by an integer denominator. Thus the slice has hull \(H\).

Every stated disequality is nonidentically zero on this coset, so Lemma 2.1 makes them simultaneously true. To prove that the remaining set has hull \(H\), suppose it lies in a proper rational affine subspace of \(H\). Choose a rational affine hyperplane containing that smaller subspace whose equation is not identically zero on \(H\), by the basis-extension construction used in Lemma 1.4. Append this one further disequality to the list and apply Lemma 2.1. The resulting point belongs to the remaining set but lies outside its supposed containing hyperplane, a contradiction. ∎

### Lemma 2.4: the generic dichotomy for one residue and affine space

**PROVED — confidence 1.00.** Let \(H\) be a nonempty rational affine space and let \(U\subseteq H\cap\mathbb Z^n\) be a nonempty affine integer coset with hull \(H\), on which every congruence in one basic fibre formula has fixed truth value. That fibre either contains all of \(U\) outside finitely many proper rational affine hyperplanes of \(H\), or is contained, on \(U\), in such a finite union.

**Proof.** Replace every congruence by its fixed truth value. Every remaining affine equation either holds identically on \(H\) or has a zero set contained in a proper affine hyperplane of \(H\); an equation with empty zero set contributes no exceptional points. Remove the finitely many proper hyperplanes so obtained. Every atomic predicate, and hence the whole Boolean formula, has a constant truth value on the remaining points of \(U\). If it is true, the first alternative holds. If false, the fibre on \(U\) is contained in the removed hyperplanes. Lemma 2.1 shows that the complement is nonempty, so the alternatives are incompatible. ∎

## 3. Persistent arithmetic data

### Definition 3.1: the current affine integer space

**PROVED — confidence 1.00; this is a definition.** Flatten the input pp sentence, renaming bound variables, so every variable is existential. Let \(x\) be the full tuple of its integer variables and \(\eta\) its full tuple of finite-sort variables. Identify variables joined by well-typed equality, and treat finite singleton pins as finite atoms.

The algorithm maintains a set \(\mathcal E\) of exact affine integer equations in the original integer variables. Initially it contains all explicit addition atoms, integer equalities, and integer pins. Its integer solution set is

\[
L_{\mathbb Z}=\{x\in\mathbb Z^n:\mathcal E(x)\},
\]

and its rational solution set is \(L\). If \(L_{\mathbb Z}\) is empty, reject. Every refinement adds only equations from positive equality literals of the original basic-fibre descriptions instantiated at original input atoms. Duplicates are removed.

At the beginning and after every refinement, \(L\) is a product across \(\Pi_*\). This invariant is initially true because the explicit arithmetic equations are within original sorts. Section 6 proves that it remains true.

### Lemma 3.2: a blockwise integer parametrization is computable

**PROVED — confidence 0.99.** If \(L_{\mathbb Z}\ne\varnothing\) and \(L\) is a product across blocks, one can compute a particular solution \(u\) and a block-diagonal integer matrix \(B\) with linearly independent columns such that

\[
L_{\mathbb Z}=\{u+Bt:t\in\mathbb Z^d\}.
\tag{3.1}
\]

Every parameter coordinate \(t_j\) can be placed in a chosen representative integer sort of its block. The map in (3.1) is injective and pp-definable within the blocks. Its coefficient lengths are polynomially bounded in the stored equation system.

**Proof.** Apply Lemma 2.2 to the stored system to obtain an integer point \(u\). Let \(V=L-L\) be its rational direction space. Since \(L\) is a product, \(V=\bigoplus_bV_b\), where \(V_b\) is supported in block \(b\). Obtain rational defining equations for \(V_b\) by restricting the stored homogeneous matrix to the columns of that block: a vector supported there belongs to the full kernel exactly when it satisfies those restricted equations. Apply Lemma 2.2 with right-hand side zero to compute an integer basis of \(V_b\cap\mathbb Z^{n_b}\). Put these bases in disjoint blocks of a matrix \(B\).

Every integer vector in \(V\) is the sum of its block components, each belonging to the corresponding integer kernel; conversely each such block vector belongs to \(V\). Therefore the columns of \(B\) form a basis of \(V\cap\mathbb Z^n\), proving (3.1). The bases are linearly independent, so \(t\mapsto u+Bt\) is injective. Each coordinate equation \(x=u+Bt\) uses only one block, so it is pp-definable by Definition 1.2. Polynomial output bounds follow from Lemma 2.2 applied to submatrices of the stored system. ∎

## 4. Exact residue images and bounded finite compression

### Definition 4.1: local cells and residue constraints

**PROVED — confidence 1.00; this is a definition.** For every fixed basic relation and every assignment to its finite arguments, expand its fixed Boolean fibre formula into disjunctive normal form. Replace a negated congruence modulo \(d\) by the finite disjunction of its other residues. Each resulting cell has:

* a conjunction \(E_j(x)\) of exact affine equations;
* a conjunction \(C_j(x)\) of positive affine congruences, with moduli dividing \(m\);
* a conjunction \(D_j(x)\) of affine disequalities.

The number of cells, and the numbers of equations, congruences, and disequalities in a cell, are constants depending only on the fixed template. A pure finite relation has cells with no integer predicates. Each input atom inherits its cell descriptions by substituting its variables into the fixed formulas.

For a current parametrization (3.1) and an input atom \(a\), define

\[
P_a(\bar t,\eta_a)\quad\Longleftrightarrow\quad
\exists t'\in\mathbb Z^d\,
\bigl(t'\equiv\bar t\pmod m\ \land\ R_a(u+Bt',\eta_a)\bigr).
\tag{4.1}
\]

Only the original argument coordinates of atom \(a\) are supplied to \(R_a\); notation suppresses that projection. Relation \(P_a\) is the exact residue image of a pp-definable relation, because the substitution \(u+Bt'\) is pp-definable within the blocks.

### Lemma 4.2: exact residue image of a single cell

**PROVED — confidence 0.99.** Substitute \(x=u+Bt\) into one cell. If its equality system has no integer solution, the cell is empty. If any listed disequality vanishes identically on the rational equality solution space, the cell is empty. In every other case its exact residue image is the intersection of the exact residue image of its equality system with its listed congruence conditions. It is described by a bounded number of affine congruences modulo \(m\), where the bound depends only on the original basic fibre formula.

**Proof.** Apply Lemma 2.2 to the equality system. It has at most the fixed number of rows in the cell, so the rank and the number of rows in (2.2) are bounded by that constant. Check each disequality on the resulting rational affine space by substituting a particular point and a rational direction basis. If it vanishes identically, no point satisfies that disequality.

Assume neither obstruction occurs. A residue vector satisfying the image conditions (2.2) lifts to an equality solution. Its entire compatible residue slice has the full rational equality hull by Lemma 2.3. Every listed disequality is nonidentically zero there, so Lemma 2.1 makes them true simultaneously. All listed congruences have fixed truth value on a residue vector, since their moduli divide \(m\). Thus exactly the residue vectors satisfying both the equality-image conditions and the listed congruences occur in the cell. A congruence modulo \(d\mid m\) can be written modulo \(m\) by multiplying its equation by \(m/d\). The resulting number of rows remains bounded. ∎

### Lemma 4.3: compression of \(P_a\) to bounded arity

**PROVED — confidence 0.99.** There is a template-dependent constant \(K\) such that, for every current space and every input atom \(a\), one can compute an integer matrix \(A_a\) with at most \(K\) rows and a finite relation \(T_a\) of arity at most \(K\) plus the finite arity of \(a\), satisfying

\[
P_a(\bar t,\eta_a)
\quad\Longleftrightarrow\quad
T_a(A_a\bar t,\eta_a).
\tag{4.2}
\]

Every row of \(A_a\) uses parameter coordinates from just one block. \(T_a\) is the actual image of \(P_a\) under the displayed map, not an unrestricted table on formal row values. The computation runs in polynomial time in the current matrix sizes.

**Proof.** For every finite argument assignment and every cell, run Lemma 4.2. Discard empty cells. Stack all rows describing the surviving exact residue images and their congruence conditions. There are only a fixed number of cells and finite argument assignments, so this stack has a bounded number of rows. Membership in \(P_a\) is the disjunction, over those cells, of the appropriate bounded conjunctions of row-value conditions.

A stacked row may involve several blocks. Replace it by its separate block contributions. Its original value is the sum of those contributions modulo \(m\). The number of blocks is fixed by the template, so the resulting row count is still bounded by one fixed constant \(K\). Call the resulting matrix \(A_a\). The cell membership formula now depends only on \(A_a\bar t\) and \(\eta_a\).

Define

\[
T_a=\{(A_a\bar t,\eta_a):(\bar t,\eta_a)\in P_a\}.
\tag{4.3}
\]

If \(P_a(\bar t,\eta_a)\), definition (4.3) gives the right side of (4.2). Conversely, suppose \(T_a(A_a\bar t,\eta_a)\). There is some \(\bar v\) with \(A_a\bar v=A_a\bar t\) and \(P_a(\bar v,\eta_a)\). Membership depends only on those row values and finite arguments, so \(P_a(\bar t,\eta_a)\). This proves (4.2).

To compute the table, enumerate all row-value tuples \(y\in(\mathbb Z/m)^{K_a}\) and all finite argument tuples, with \(K_a\leq K\). Their total number is a template-dependent constant. Check whether \(A_a\bar t=y\pmod m\) is solvable. This is an integer linear-system test after adjoining variables \(z\) and writing \(A_at-mz=y\), so Lemma 2.2 applies. If it is solvable, evaluate the finite disjunction of row-value conditions to determine membership. This includes the actual-image restriction automatically. The number of tests is constant and their matrices have polynomial size, proving the running-time assertion. ∎

### Lemma 4.4: all compressed tables have one fixed Taylor polymorphism

**PROVED — confidence 0.99.** Fix one sufficiently large prime \(p_0\) and a cyclic operation family from Proposition 1.3(5). On the finite residue sort \(\mathbb Z/m\), let the operation be the \(p_0\)-mean; on each original finite sort let it be the corresponding component of \(c_{p_0}\). Every table \(T_a\) arising in Lemma 4.3 is preserved by this same family.

**Proof.** Relation \(P_a\) is an exact pp image, so the chosen operation preserves it. Take \(p_0\) tuples in \(T_a\), and choose preimages \((\bar t^{,i},\eta_a^i)\in P_a\). Their image under the polymorphism is

\[
\left(p_0^{-1}\sum_i\bar t^{,i},\ c_{p_0}(\eta_a^1,\ldots,\eta_a^{p_0})\right)\in P_a.
\]

For every row of \(A_a\), linearity modulo \(m\) gives

\[
A_a\left(p_0^{-1}\sum_i\bar t^{,i}\right)
=p_0^{-1}\sum_i A_a\bar t^{,i}.
\]

The image of this tuple is exactly the componentwise operation applied to the original table tuples. It belongs to \(T_a\) by definition (4.3). Thus \(T_a\) is preserved.

The operation is cyclic and idempotent. Since \(p_0\geq3\), cyclic rotation makes all its expressions with one exceptional argument equal, so it is a weak near-unanimity operation. Alternatively, the explicit single-\(x\) versus rotated-single-\(x\) identities show directly that it is Taylor. ∎

### Proposition 4.5: one fixed polynomial finite solver handles every iteration and support query

**PROVED — confidence 0.99, using the cited finite-domain theorem.** Every finite constraint problem built from the tables \(T_a\), finite pins, and affine congruences modulo \(m\) can be solved in polynomial time, uniformly as these tables vary during the algorithm.

**Proof.** The row arity \(K\), original finite arities, modulus \(m\), and all finite domains are fixed. There are only finitely many relations of these bounded arities on those domains. Form the fixed finite language containing every such relation preserved by the operation of Lemma 4.4. Add the finite addition relation on \(\mathbb Z/m\), its singleton pins, and the original finite-sort singleton pins. These are also preserved: the numerical operation is an idempotent linear mean, and the finite operations are idempotent. Every table arising in the algorithm belongs to this one fixed language by Lemma 4.4.

An affine equation \(\sum_j a_jr_j=c\pmod m\) of unbounded input length is encoded with a chain of finite addition constraints and auxiliary variables. Reduce every coefficient modulo \(m\). Multiplication by a residue coefficient is implemented with at most \(m\) additions, a constant because \(m\) is fixed. Pin the last sum to \(c\pmod m\). This uses a number of variables and constraints linear in the row length. All numerical residue variables may use the same algorithmic finite sort \(\mathbb Z/m\): their mean operations are identical. This merging is a finite decision-device construction and does not assert a new pp relation between the original integer sorts.

To apply a one-sorted finite-domain theorem, take the Cartesian product \(A\) of these finitely many finite sorts. Replace every typed relation by its cylindrical relation on copies of \(A\), testing only the appropriate coordinate in each argument position. A sorted assignment lifts by choosing arbitrary values for unused coordinates. Conversely, projecting a satisfying assignment to the prescribed coordinates recovers a sorted assignment. The product operation acts coordinatewise and preserves every cylindrical relation. It is idempotent and weak near-unanimity. Add all singleton relations of \(A\), which it also preserves.

Bulatov (2017), *A Dichotomy Theorem for Nonuniform CSPs*, FOCS, Theorem 4, implication from condition (2), gives a polynomial-time algorithm for every fixed finite language with such a weak near-unanimity polymorphism. Apply it to this one fixed cylindrical language. Relation arities and tables have fixed bounds, so looking up the correct relation symbol for a computed table is a constant-size finite comparison. The arithmetic gadgets have polynomial length. This gives one polynomial bound for all iterations and all added affine support-query constraints. It does not apply a separate nonuniform theorem to a changing sequence of templates. ∎

## 5. The finite relaxation and pp support sets

### Definition 5.1: the exact finite relaxation

**PROVED — confidence 1.00; this is a definition.** With the current parametrization \(x=u+Bt\), form a finite instance \(F_L\) with variables \(\bar t\in(\mathbb Z/m)^d\) and the original finite variables \(\eta\). For every original non-arithmetic atom \(a\), require

\[
P_a(\bar t,\eta_a).
\tag{5.1}
\]

Represent this by its table \(T_a\) and equations \(y=A_a\bar t\pmod m\), using Lemma 4.3 and the arithmetic gadgets of Proposition 4.5. Explicit arithmetic atoms already stored in \(\mathcal E\) can be omitted; retaining their tautological relative constraints would make no difference. Pure finite atoms are included among the atoms \(a\).

Every actual solution of the original instance in \(L_{\mathbb Z}\) gives a solution of \(F_L\) by taking its unique parameter tuple modulo \(m\). Therefore an unsatisfiable \(F_L\) certifies unsatisfiability of the original instance.

### Definition 5.2: a supported numeric set for an atom

**PROVED — confidence 1.00; this is a definition.** For an atom \(a\), define \(S_a\subseteq\mathbb Z^d\) by

\[
\begin{split}
t\in S_a\quad\Longleftrightarrow\quad
\exists\eta\ \bigl[
&F_L(q_m(t),\eta)\\
&\land R_a(u+Bt,\eta_a)\bigr].
\end{split}
\tag{5.2}
\]

In (5.2), \(F_L\) denotes the semantic conjunction (5.1), not a particular choice of auxiliary arithmetic gadgets. Put

\[
X_a=\{u+Bt:t\in S_a\}\subseteq L_{\mathbb Z}.
\]

### Lemma 5.3: pp definability, period, and necessary containment

**PROVED — confidence 0.99.** Each \(S_a\) is pp-definable. It has an external Boolean arithmetic description whose congruence moduli divide \(m\). Every actual solution of the original instance has its parameter tuple in every \(S_a\). If \(F_L\) is satisfiable, every \(S_a\) is nonempty.

**Proof.** Expanding each \(P_b\) by its exact-image definition (4.1) gives the pp formula

\[
\begin{split}
S_a(t)\ \Longleftrightarrow\ \exists\eta\,(v_b)_b\ \bigl[
&R_a(u+Bt,\eta_a)\\
&\land\bigwedge_b\bigl(v_b\equiv t\pmod m\ \land\ R_b(u+Bv_b,\eta_b)\bigr)\bigr].
\end{split}
\tag{5.3}
\]

Every \(v_b\) is a full tuple of parameter variables typed by the same blocks as \(t\). All substitution equations and congruences are within blocks, hence pp-definable. The finite variables \(\eta\) are shared between all atoms exactly as in the original instance. Thus (5.3) is a pp formula.

For an external arithmetic description, expand the finite relation \(F_L\) as a finite disjunction over all its residue and finite-coordinate assignments. This expansion may be large, but it is used only as an existence proof, not as an algorithmic step. A disjunct fixes \(t\pmod m\) and \(\eta\), then conjoins the fixed fibre formula \(R_a(u+Bt,\eta_a)\). Every resulting congruence has modulus dividing \(m\). This gives the stated Boolean description without invoking quantifier elimination or introducing new periods.

An actual global solution satisfies \(R_a\) and all constraints (5.1), using itself as each image witness, so its parameter tuple belongs to \(S_a\). Finally, choose a solution \((\bar r,\eta)\) of \(F_L\). The constraint \(P_a(\bar r,\eta_a)\) supplies an actual \(t\equiv\bar r\pmod m\) with \(R_a(u+Bt,\eta_a)\). The same finite solution witnesses (5.2). Hence \(S_a\ne\varnothing\). ∎

### Lemma 5.4: exact polynomial computation of enabled cell hulls

**PROVED — confidence 0.99.** Assume \(F_L\) is satisfiable. For each atom \(a\), one can compute a fixed-size list of nonempty rational affine spaces \(H_{a,j}\subseteq L\) whose union has the same affine hull as \(X_a\). Each listed space is

\[
H_{a,j}=L\cap\{x:E_j(x)\},
\tag{5.4}
\]

where \(E_j\) consists of original positive equality literals from one fixed fibre cell of atom \(a\). The list and its affine hull are computable in polynomial time. Call its listed cells *enabled*.

**Proof.** Enumerate the fixed number of finite argument assignments and their fixed cells for atom \(a\). Substitute \(u+Bt\), and apply Lemma 4.2. If the equality system has no integer solution or a listed disequality vanishes identically on its rational hull, discard the cell.

For each remaining cell \(j\), its exact residue image \(Q_j\) is a bounded conjunction of affine congruences by Lemma 4.2. Ask whether

\[
F_L(\bar t,\eta)\ \land\ Q_j(\bar t)\ \land\ (\eta_a=\eta^{,j})
\tag{5.5}
\]

is satisfiable, where \(\eta^{,j}\) is the finite assignment of that cell. Proposition 4.5 answers this query in polynomial time. The extra relation \(Q_j\) is affine and thus preserved by the same mean operation, even though the original cell need not be pp-definable. Finite pins are also preserved. If (5.5) is satisfiable, call the cell enabled; otherwise discard it.

For an enabled cell choose one witnessing residue tuple \(\bar r\) and finite assignment. All parameter tuples in that cell with residue \(\bar r\) have a compatible solution of \(F_L\) and therefore belong to \(S_a\). Lemma 2.3 says that these tuples, after excluding the listed disequalities, have the full rational hull of the cell's equality system. Under the injective affine map \(t\mapsto u+Bt\), their hull is precisely (5.4). Thus \(X_a\) contains a subset with hull \(H_{a,j}\).

Conversely, a point of \(X_a\) has a finite witness in (5.2). Its local tuple satisfies at least one of the enumerated cells for that finite assignment. Its residue and the same finite witness satisfy (5.5), so that cell is enabled. The point belongs to its equality space (5.4). Therefore

\[
X_a\subseteq\bigcup_{j\text{ enabled}}H_{a,j},
\qquad
H_{a,j}\subseteq\operatorname{aff}_{\mathbb Q}X_a.
\]

Taking affine hulls gives the assertion. There are only a fixed number of cells per atom. Every query has polynomial size, and computing the affine hull of a fixed number of affine spaces is polynomial rational linear algebra: take one point and a direction basis for each, then span all direction vectors and differences of base points. The bit bounds are those of Lemma 2.2 and its determinant estimate. ∎

## 6. Refinement by original equations

### Lemma 6.1: one enabled original cell has the whole supported hull

**PROVED — confidence 0.99.** If \(F_L\) is satisfiable, then for each atom \(a\), at least one enabled cell has

\[
H_{a,j}=\operatorname{aff}_{\mathbb Q}X_a.
\tag{6.1}
\]

**Proof.** Transfer the spaces of Lemma 5.4 to the parameter coordinates using the injective affine map \(u+Bt\). Let \(H=\operatorname{aff}_{\mathbb Q}S_a\). Each transferred cell hull lies in \(H\), and together they cover \(S_a\). If every one were proper in \(H\), choose a rational affine hyperplane containing each whose equation is not identically zero on \(H\), using the construction in Lemma 1.4. There are finitely many such hyperplanes, and they cover the pp relation \(S_a\). Proposition 1.3(2) would put all of \(S_a\) in one of them, forcing its hull \(H\) into that hyperplane, a contradiction. Hence one transferred cell hull equals \(H\), which gives (6.1) after applying the affine map. ∎

### Lemma 6.2: the refinement preserves every true solution and the block invariant

**PROVED — confidence 0.99.** Suppose some atom has \(\operatorname{aff}_{\mathbb Q}X_a\ne L\). Choose an enabled cell satisfying (6.1), and add its original equality literals \(E_j\) to the stored set \(\mathcal E\). The new rational solution space is exactly \(\operatorname{aff}_{\mathbb Q}X_a\), is a product across blocks, and has strictly smaller dimension. It is nonempty over the integers. Every solution of the original instance still lies in it.

**Proof.** By (5.4) and (6.1), adding \(E_j\) replaces \(L\) by exactly \(\operatorname{aff}_{\mathbb Q}X_a\). Lemma 5.3 shows that every original solution belongs to \(X_a\), so the added equations are necessary. An enabled cell contains an actual integer witness by Lemma 5.4, so the new integer system is nonempty.

Lemma 5.3 gives a period-\(m\) Boolean description and a pp definition of \(S_a\). Lemma 1.4 makes its affine hull a product across parameter blocks. The map \(u+Bt\) is blockwise, so its image \(\operatorname{aff}_{\mathbb Q}X_a\) is a product across the original blocks. Finally, a proper affine subspace of a finite-dimensional affine space has smaller dimension: translating both through a point in the smaller space reduces this to a proper inclusion of finite-dimensional vector spaces, whose bases can be extended by at least one vector. ∎

### Proposition 6.3: persistent bit sizes are polynomially bounded

**PROVED — confidence 0.99.** Throughout the algorithm, the stored system contains only polynomially many rows with template-bounded original coefficients and constants. Every recomputed parametrization, cell system, and finite compression has polynomial bit length. There are at most \(n\) strict refinements, where \(n\) is the number of original integer variables.

**Proof.** Every stored row is either an explicit original arithmetic atom or one positive affine equation from a cell of one original atom. Each fixed fibre formula has a fixed finite number of literals, and the input has linearly many atom occurrences. Thus the union of all rows that could ever be stored has size \(O(n_{\rm in})\), where \(n_{\rm in}\) denotes the input length. Substituting repeated variables can sum at most the fixed number of coefficients in a literal, so coefficient and constant lengths remain bounded in terms of the fixed template. The algorithm stores only rows from this union, removing duplicates; it does not store iterated rational-elimination output as new persistent equations.

Lemma 3.2 therefore recomputes \(u,B\) from a matrix of polynomial size and bounded original coefficients, giving polynomial bit length. Substituting these into the fixed-arity cell formulas uses polynomially many integer additions and multiplications by fixed coefficients. Lemma 2.2 then computes the needed cell parametrizations and residue rows with polynomial output length. Lemma 4.3 has bounded row count and polynomial computation. None of these derived matrices is fed back as a new persistent equality row.

Each strict refinement reduces affine dimension by at least one by Lemma 6.2, and the initial dimension is at most \(n\). Therefore there are at most \(n\) refinements. ∎

## 7. Acceptance at a stable space

### Lemma 7.1: one list of finite rows supports spanning witnesses for every atom

**PROVED — confidence 0.99.** Suppose \(F_L\) is satisfiable and

\[
\operatorname{aff}_{\mathbb Q}X_a=L
\quad\text{for every atom }a.
\tag{7.1}
\]

For every sufficiently large prime \(p\), there exist \(p\) solutions \((\bar r^i,\eta^i)\) of \(F_L\) and, for every atom \(a\), integer assignments

\[
x_a^i=u+Bt_a^i\in L_{\mathbb Z}\quad(1\leq i\leq p)
\]

such that

\[
t_a^i\equiv\bar r^i\pmod m,
\qquad
R_a(x_a^i,\eta_a^i),
\tag{7.2}
\]

and the \(p\) assignments \(x_a^i\) have affine hull \(L\) for every \(a\).

**Proof.** A spanning subset of at most \(\dim L+1\) points can be selected from each \(X_a\): start with one point; if the current affine span is smaller than \(L\), choose a point of \(X_a\) outside it, which increases dimension, and continue. Condition (7.1) guarantees such a point whenever needed. For each selected point, choose the finite witness in Definition 5.2. It gives one solution of \(F_L\) whose residue matches that point.

List these finite solutions with a separate row for each selected witness of each atom. Choose \(p\) at least the length of the list, and fill any remaining rows by repetitions of an arbitrary solution of \(F_L\). For every row and every atom \(a\), its finite constraint \(P_a(\bar r^i,\eta_a^i)\) supplies an integer witness satisfying (7.2). On rows originally selected for atom \(a\), choose its designated spanning witness. Then the complete list of witnesses for that atom contains a set spanning \(L\), and all its points lie in \(L\), so its hull is exactly \(L\). The same construction supplies witnesses separately for every atom, while all finite rows and residues are shared. ∎

### Lemma 7.2: the common finite output is generically feasible for every atom

**PROVED — confidence 0.98.** Under the hypotheses of Lemma 7.1, there are a residue tuple \(\bar r^*\) and one common assignment \(\eta^*\) to all finite variables such that, for each atom \(a\), all points of

\[
U^*=\{u+Bt:t\equiv\bar r^*\pmod m\}
\tag{7.3}
\]

outside finitely many proper rational affine hyperplanes of \(L\) satisfy \(R_a(\cdot,\eta_a^*)\).

**Proof.** Choose a prime \(p\) sufficiently large for Lemma 7.1 and Proposition 1.3(5), and with \(p\nmid m\). Take its rows and witnesses, and set

\[
\bar r^*=p^{-1}\sum_{i=1}^{p}\bar r^i\pmod m,
\qquad
\eta^*=c_p(\eta^1,\ldots,\eta^p)
\tag{7.4}
\]

coordinatewise on the finite variables.

Fix an atom \(a\). Combine its full assignments \(x_a^i\) with independent permitted coefficient vectors in each block. Their rational blockwise affine-combination image is exactly \(L\). To verify this, the affine span of the full list is \(L\) by Lemma 7.1, so its projection to each block spans \(L_b\). Every point of \(L_b\) is therefore an affine combination of that block's list with coefficient sum one. Because different blocks use independent coefficients, every point of \(\prod_bL_b=L\) is obtained.

For integer coefficients satisfying (1.1), the combination belongs to \(U^*\). Indeed, on block \(b\),

\[
\sum_i\gamma_i^b x_{a,b}^i
=u_b+B_b\left(\sum_i\gamma_i^b t_{a,b}^i\right),
\]

and the parameter expression in parentheses has residue \(p^{-1}\sum_i\bar r_b^i=\bar r_b^*\), independently of \(a\). The set \(U^*\) is nonempty and has hull \(L\): choose any integer lift of \(\bar r^*\), and its direction lattice is \(mB\mathbb Z^d\), spanning the direction space of \(L\). Every original congruence has fixed truth value there because all integer coordinate residues modulo \(m\) are fixed.

Apply Lemma 2.4 to \(R_a(\cdot,\eta_a^*)\) on \(U^*\). Suppose its thin alternative held, so that the satisfying points were contained in a finite union of proper affine hyperplanes of \(L\). Pull their equations back along the blockwise coefficient map just described. That map is onto \(L\) over \(\mathbb Q\), so each pulled-back equation is a nonzero affine function on the coefficient space.

On the other hand, Proposition 1.3(5), applied to the actual tuples in (7.2), says that the combined local tuple belongs to \(R_a\) outside a finite union of proper coefficient hyperplanes. Collect those exceptional equations together with the pulled-back covering equations. The permitted coefficient set is a nonempty full-rank affine integer coset in its rational coefficient space: one coefficient vector is \((1-(p-1)c,c,\ldots,c)\), for \(c\equiv p^{-1}\pmod m\), and the directions \(m(e_i-e_1)\) span its sum-zero direction. Its product over blocks has the same property. Lemma 2.1 therefore gives permitted coefficients outside every collected hyperplane.

Their output is a tuple of \(R_a\) with finite part \(\eta_a^*\), by generic preservation. It lies in \(U^*\) but outside every proposed covering hyperplane, a contradiction. Thus the full generic alternative of Lemma 2.4 holds, which is exactly the assertion for atom \(a\). The finite output (7.4) and the coset (7.3) were chosen once and work for every atom. ∎

### Proposition 7.3: a stable satisfiable finite relaxation implies an actual solution

**PROVED — confidence 0.98.** If \(F_L\) is satisfiable and every supported hull equals \(L\), the original pp instance is satisfiable.

**Proof.** If there are no non-arithmetic atoms, any point of the nonempty integer set \(L_{\mathbb Z}\), together with arbitrary assignments to unconstrained finite variables, is a solution. Otherwise use Lemma 7.2. For each atom collect its finite family of exceptional proper hyperplanes in \(L\). Their total family is finite. The common coset \(U^*\) has hull \(L\), so each exceptional equation is nonidentically zero on it. Lemma 2.1 chooses one integer point in \(U^*\) outside all these hyperplanes simultaneously. That point, together with the single finite assignment \(\eta^*\), satisfies every atom. It also satisfies every explicit arithmetic atom because it lies in \(L_{\mathbb Z}\). Thus it is a solution of the whole original instance. ∎

## 8. The complete algorithm and its complexity

### Algorithm 8.1

**PROVED — confidence 0.98; this is the complete decision procedure for a fixed template satisfying \(Q\).**

1. Initialize the stored equation set \(\mathcal E\) from the explicit arithmetic atoms, as in Definition 3.1.
2. Test integer feasibility. If the stored system has no integer solution, reject. Compute its blockwise parametrization \(x=u+Bt\).
3. Compute the compressed exact finite relaxation \(F_L\), and solve it using Proposition 4.5. If it is unsatisfiable, reject.
4. For every input atom \(a\), compute all enabled cell hulls and their affine hull \(\operatorname{aff}_{\mathbb Q}X_a\) using Lemma 5.4.
5. If some supported hull is proper in \(L\), inspect its enabled cells in their fixed enumeration order and choose the first whose affine dimension equals the dimension of the computed supported hull. Every enabled hull is contained in that supported hull, so equal dimensions imply equality; Lemma 6.1 guarantees that such a cell exists. Append its original positive equality literals to \(\mathcal E\), remove duplicates, and return to step 2.
6. If every supported hull equals \(L\), accept.

### Theorem 8.2: correctness and polynomial running time

**PROVED — confidence 0.98.** Algorithm 8.1 decides \(\operatorname{CSP}(\mathcal M)\) in polynomial time whenever \(Q\) holds.

**Proof.** Initially every actual solution satisfies the stored equations. Lemma 6.2 preserves this property through every refinement. Therefore rejection at step 2 is sound. Every actual solution gives a finite solution of \(F_L\), by Definition 5.1, so rejection at step 3 is sound. Lemma 6.2 proves both that each update retains every actual solution and that the product-block invariant needed by step 2 is maintained. Proposition 7.3 proves acceptance sound. Thus every possible termination outcome is correct.

There are at most \(n\) strict refinements by Proposition 6.3, hence at most \(n+1\) passes. All persistent and derived arithmetic data have polynomial bit length by that proposition. Each pass makes polynomially many normal-form and rational-linear-algebra computations on polynomial-size matrices. There are linearly many atoms, and each has only a fixed number of cells and finite argument assignments. Consequently Lemma 5.4 makes only polynomially many calls to the one fixed finite solver of Proposition 4.5, each on a polynomial-size instance. All table enumerations have template-dependent constant bounds because \(m\), \(K\), and the finite domains are fixed. The total running time is polynomial in the pp input length.

The generic combinations in Section 7 are a correctness proof, not a computational search performed by the algorithm. Thus their use of a prime depending on the number of selected witnesses does not contribute an unbounded search to the decision procedure. ∎

### Corollary 8.3: the corrected tractability criterion

**PROVED — confidence 0.97.** In this finite-signature setting, \(Q\) implies polynomial-time tractability. Together with the stipulated implication \(\neg Q\Rightarrow\operatorname{CSP}(\mathcal M)\) NP-hard and the fully proved NP upper bound in the arithmetic appendix, Corollary A5, this yields a P/NP-complete classification by \(Q\). The block-generic certificate proved equivalent to \(Q\) in `N_amplification.md` gives a decidable criterion.

**Proof.** The positive implication is Theorem 8.2. The negative hardness implication is established item 3 in the problem statement. Corollary A5 of `N_arithmetic.md` proves NP membership by a polynomially sized finite-cell certificate and a polynomial integer-conjunction feasibility verifier. The negative branch is therefore NP-complete. The final equivalence and decidability are Theorem II.10 of the companion finite-certificate chapter. The equivalence between being in P and satisfying Q additionally assumes P differs from NP; the two branch implications themselves are unconditional under the stated hardness premise. ∎

## 9. Exact reproducibility description

### Proposition 9.1: boundary cases and repeated arguments

**PROVED — confidence 1.00.** The procedure covers an input with no non-arithmetic atoms, a current lattice with zero parameter dimension, and repeated finite or integer arguments in an atom.

**Proof.** If no non-arithmetic atoms remain, the finite relaxation is the empty conjunction. After integer feasibility succeeds, there is no supported-hull test to fail, and step 6 accepts. Proposition 7.3 explicitly supplies a solution in this case; unconstrained finite variables can take arbitrary elements of their nonempty fixed sorts.

If the parameter dimension is zero, the parameter set has its single empty tuple. The current integer set is one point. In Lemma 2.2, rank-zero systems are handled by checking that every right-hand side is zero; the empty identity matrix and the empty parameter tuple require no normal-form computation. Exact residue constraints then have no free residue parameters. A surviving cell either contains the fixed integer point or does not. Satisfiability of the finite relaxation supplies the same point as a numeric witness for every atom, with the compatible finite assignment. Each supported hull is that point, so acceptance is correct. The finite table computation still checks the actual image of its row map, which in this case has just one row-value tuple.

If an integer variable appears more than once in an atom, substitution reuses the same coordinate of the global tuple. Combining coefficients in a cell equation increases their absolute values by at most the fixed arity factor, and every arithmetic lemma applies to that resulting equation. If a finite variable appears in several argument positions, the table constraint is applied to those same repeated variable positions. A cell query that assigns inconsistent values to two occurrences of that variable has incompatible singleton pins and is rejected by the finite solver. Consistent repetitions are handled by the original shared variable. This is exactly the meaning of the shared finite tuple in formula (5.3), so no independence between repeated occurrences is assumed. ∎

**PROVED — confidence 1.00.** The algorithm requires no empirical classification of small residue moduli. Its fixed precomputation consists of the following finite data: the maximal pp-identity block partition; one cyclic operation family on the finite sorts and integer residues modulo \(m\); the bounded finite language preserved by that family; and a polynomial solver for that one finite language. Theorems II.10 and II.12 of `N_amplification.md` make the operation family and the actual maximal pp-identity partition obtainable by finite search when an effective implementation is desired.

For each input, the actual computations are the normal-form operations of Lemma 2.2, finite row-value table enumeration from Lemma 4.3, the exact finite relaxation (5.1), the cell-support queries (5.5), affine-hull computations, and addition of the selected original equality rows. Every loop condition and update appears in Algorithm 8.1. No check is restricted to bounded \(N\), and no computed result is used as a substitute for the uniform structural proofs.

## 10. References used by this chapter

**PROVED — confidence 0.99; exact statement uses are identified.**

1. Ravindran Kannan and Achim Bachem (1979), *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, SIAM Journal on Computing **8**(4), 499–507. DOI [10.1137/0208040](https://doi.org/10.1137/0208040). **Theorem 2 and Lemma 3** are used for the polynomial Hermite computation with a unimodular transformation in Lemma 2.2; the rectangular reduction and residue-image derivation are written out there.
2. Andrei A. Bulatov (2017), *A Dichotomy Theorem for Nonuniform CSPs*, 58th IEEE Symposium on Foundations of Computer Science. **Theorem 4, implication from condition (2)**, is used in Proposition 4.5 for a fixed finite language with a weak near-unanimity polymorphism. [Author's paper](https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf).
3. Libor Barto and Marcin Kozik (2012), *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*, Logical Methods in Computer Science **8**(1), article 07. **Theorem 4.1** is used in the companion structural proofs to obtain cyclic terms of all sufficiently large prime arities. [Published PDF](https://lmcs.episciences.org/673/pdf). The present algorithm uses the resulting proved Proposition 1.3(5).

## 11. Adversarial self-audit

### Audit 11.1: the actual image restriction in finite compression

**PROVED — confidence 0.99.** The table in (4.3) is restricted to row-value tuples actually attained by \(A_a\) on residue vectors. Removing this restriction could introduce tuples without pp-image preimages and destroy the common Taylor-preservation argument. Lemma 4.3 includes the image test explicitly, and Lemma 4.4 uses actual preimages.

### Audit 11.2: the pp definition of the support sets

**PROVED — confidence 0.99.** The temporary cell predicates need not be pp-definable. They are used only for finite support queries and arithmetic decomposition. The set to which the \(Q\) hyperplane-cover theorem is applied is \(S_a\), and its pp definition is the explicit formula (5.3) using original atoms, within-block substitutions, and coordinate congruences. This distinction is essential.

### Audit 11.3: finite support does not by itself give a global solution

**PROVED — confidence 0.98.** Individual exact residue compatibility for each atom is insufficient for acceptance. The additional stable-hull condition supplies spanning witnesses. Lemmas 7.1–7.2 then use one common list of finite solutions, the same finite cyclic operation, and one common output residue. Only after proving that every atom is generically true on the resulting common integer coset does Proposition 7.3 choose a single satisfying integer point.

### Audit 11.4: the bit-growth issue is addressed structurally

**PROVED — confidence 0.99.** Repeatedly storing arbitrary computed affine hull equations could create an unproved coefficient-growth problem. Lemma 6.1 uses \(Q\) to identify an enabled original cell with the whole supported hull. The algorithm stores that cell's original equality rows. Proposition 6.3 bounds all persistent input coefficients before any normal-form recomputation.

### Audit 11.5: the strongest external dependence

**PROVED — confidence 0.98.** The only classification theorem needed in the algorithm itself is the finite-domain weak-near-unanimity tractability statement. It applies to a single fixed bounded-arity language containing every compressed table, rather than separately to input-dependent templates. The arithmetic subroutine is explicitly reduced to the cited polynomial Hermite computation. The generic necessity and affine splitting statements must be retained with their full companion proofs; omitting them would turn the present proof into a conditional algorithm theorem.

### Audit 11.6: no claim that the original shared \(GC\) has been recovered

**PROVED — confidence 0.99.** Independent coefficient vectors are used in Lemma 7.2 exactly because the persistent affine space splits across the actual pp-linked integer blocks. The polynomial-time conclusion therefore supports \(Q\) and the corrected block-generic certificate as tractability criteria. It does not identify them with the original single shared-Boolean generic template in a setting where its affine forms mix genuinely independent blocks.

---

# Appendix A. Arithmetic and finite-algorithm foundations

This appendix supplies the precise algorithmic facts used by the finite test and by the general CSP algorithm. It uses two cited algorithmic theorems: Kannan–Bachem's polynomial Hermite normal-form algorithm, and Bulatov's finite-domain tractability theorem. Every reduction to these theorems is proved here.

## A1. Rational linear algebra and bit size

### Lemma A1 — PROVED, confidence 0.99

For a rational matrix and right-hand side given in binary, consistency, rank, an affine parametrization of its solution space, containment of one affine solution space in another, and the affine hull of finitely many explicitly parametrized affine spaces can be computed in polynomial time, with polynomially many bits in all returned data.

**Proof.** First clear denominators row by row. The product of the denominators in a row has binary length at most their total binary length, so this produces an integer matrix of polynomial encoding length. Let its dimensions be at most \(n\), and let the absolute values of its entries be at most \(H\), including its augmented right-hand-side column.

Perform elimination, interchanging rows and columns when a nonzero pivot is needed, and reducing every rational number to lowest terms. After a set of pivot rows and columns has been chosen, each entry of the remaining Schur complement is a determinant of a bordered pivot submatrix divided by the determinant of the pivot submatrix. This formula follows from block elimination: for an invertible pivot block \(P\), the remaining entry is \(a-vP^{-1}u\), while expansion of the bordered determinant gives

\[
\det\begin{pmatrix}P&u\\v&a\end{pmatrix}
=\det(P)(a-vP^{-1}u).
\]

The determinant identity follows by multiplying the block matrix on the left by \(\left(\begin{smallmatrix}I&0\\-vP^{-1}&1\end{smallmatrix}\right)\), whose determinant is one, and expanding the resulting block triangular determinant. Inductively, this identifies every Schur-complement entry after each pivot.

A determinant of order \(k\le n\) is a sum of \(k!\) products of \(k\) entries, so its absolute value is at most \(k!H^k\). Its binary length is at most \(1+k\log_2 H+k\log_2 k\). Thus the reduced numerators and denominators in elimination have polynomial binary length. Intermediate products and sums before reduction have at most a constant multiple of that length. Integer addition, multiplication, division with remainder, and greatest common divisors have polynomial bit complexity: long arithmetic gives the first three assertions; for Euclid's algorithm, after two remainder steps the positive remainder is at most half the preceding positive value, giving a number of steps linear in the bit length. Each arithmetic step therefore costs polynomial time. Elimination uses polynomially many such steps.

A row with zero coefficients and nonzero augmented entry detects inconsistency. Otherwise choose the nonpivot variables as free parameters and solve for the pivot variables. Setting all free parameters to zero gives a rational point, and setting them one at a time to one gives a rational direction basis after subtracting that point. These data have the determinant-ratio bounds just proved.

An affine functional vanishes on a parametrized affine space exactly when it vanishes at the chosen point and on every direction basis vector. This tests containment in an affine equation, and testing all equations tests containment of affine spaces. For an affine hull of nonempty spaces, collect their direction bases and the differences between their selected points and one base point, then compute the span by elimination. Empty spaces contribute nothing. These constructions use polynomially many operations on polynomially sized data. \(\square\)

## A2. Integer affine systems: an explicit rectangular reduction

The external normal-form input is the following exact cited result: **Ravindran Kannan and Achim Bachem (1979), Theorem 2 and Lemma 3**, give a polynomial-time algorithm computing the column Hermite form and a unimodular multiplier of a nonsingular square integer matrix, with polynomially bounded binary lengths. The paper is *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, SIAM Journal on Computing 8(4), 499–507, DOI [10.1137/0208040](https://doi.org/10.1137/0208040).

Only that square-matrix result is used. The reduction below proves the needed rectangular statement and avoids relying on the paper's unexpanded remark about arbitrary rectangular Smith forms.

### Lemma A2 — PROVED, confidence 0.99

Given an integer matrix \(A\in\mathbb Z^{r\times d}\) and \(b\in\mathbb Z^r\), one can decide integer feasibility in polynomial time. If feasible, one can compute

\[
\{t\in\mathbb Z^d:At=b\}=u+B\mathbb Z^{d-k},
\qquad k=\operatorname{rank}_{\mathbb Q}A,
\]

where \(B\) has independent columns forming a basis of the full integer kernel of \(A\). One also obtains a unimodular matrix \(U\in\mathrm{GL}_d(\mathbb Z)\) and an integer vector \(v\in\mathbb Z^k\) such that this solution set is

\[
\{U(v,w):w\in\mathbb Z^{d-k}\}.
\]

All returned integers have polynomial binary length.

**Proof.** Use Lemma A1 to test rational consistency and select \(k\) independent rows \(A'\), with the corresponding entries \(b'\). Rational consistency ensures that the omitted equations follow from these selected equations, including their right-hand sides. If \(k=0\), consistency says every right-hand side is zero; take \(U=I_d\), \(u=0\), and \(B=I_d\). If \(d=0\), this statement means the unique empty tuple is accepted exactly when every equation has right-hand side zero.

Suppose \(k>0\). Choose \(k\) independent columns of \(A'\). After a column permutation \(P\), write

\[
A'P=[C\ D],
\]

where \(C\) is a nonsingular \(k\times k\) matrix. Form the nonsingular square integer matrix

\[
E=\begin{pmatrix}C&D\\0&I_{d-k}\end{pmatrix}.
\]

Apply the cited Hermite algorithm to obtain a unimodular \(K\) with \(EK=H\) lower triangular. The first \(k\) rows of a lower triangular matrix have zero entries in columns greater than \(k\). Consequently, with \(U=PK\),

\[
A'U=[H_0\ 0],
\]

where \(H_0\) is a nonsingular integer \(k\times k\) lower triangular matrix. Because \(U\) is unimodular, \(t\mapsto U^{-1}t\) is a bijection of \(\mathbb Z^d\). The equation system is therefore equivalent to

\[
H_0 z_{1:k}=b',
\]

with the remaining coordinates unrestricted. Compute the unique rational vector \(v=H_0^{-1}b'\) using Lemma A1. If any entry of \(v\) is nonintegral, there is no integer solution. If every entry is integral, all solutions are exactly \(U(v,w)\) for \(w\in\mathbb Z^{d-k}\). Take \(u=U(v,0)\) and let \(B\) consist of the last \(d-k\) columns of \(U\).

The construction proves both completeness and uniqueness of the free coordinates. The cited Hermite result bounds \(K\), and Lemma A1 bounds the rational solve and all subsequent products. The input matrix \(E\) has polynomial encoding length. Hence the entire construction and all output bit lengths are polynomial. \(\square\)

### Lemma A3 — PROVED, confidence 0.99

For the nonempty system in Lemma A2 and any fixed \(m\ge2\), its exact image modulo \(m\) is defined by precisely \(k\) linear congruences:

\[
q_m\{t:At=b\}
=\{r\in(\mathbb Z/m)^d:(U^{-1}r)_{1:k}=v\pmod m\}.
\]

**Proof.** If \(t=U(v,w)\), reduction modulo \(m\) satisfies the displayed equations. Conversely, suppose \(r\) satisfies them. Choose integer values of the free coordinates \(w\) whose residues equal the last \(d-k\) coordinates of \(U^{-1}r\). Then \(t=U(v,w)\) is an integer solution and has residue \(r\). The inverse \(U^{-1}\) is integral because the determinant of \(U\) is \(\pm1\). It can be computed with polynomial bit complexity by Lemma A1; the cofactor determinant bound in that lemma also bounds its entries. \(\square\)

### Lemma A4 — PROVED, confidence 0.99

A conjunction of integer affine equations, affine congruences, and affine disequalities, with all coefficients written in binary, has a polynomial-time satisfiability test.

**Proof.** Replace each congruence \(\ell(x)\equiv a\pmod d\) by the equation \(\ell(x)-a=d y\) with a fresh integer variable \(y\). Call the resulting equality system \(E\). Use Lemma A2 to decide its integer feasibility. If infeasible, reject.

If feasible, let \(u+B\mathbb Z^e\) be its exact solution coset. For each disequality \(h(x)\ne0\), substitute this parametrization, including the auxiliary variables where relevant. The resulting affine function of the integer parameters is identically zero exactly when its constant term and every linear coefficient are zero. If any disequality becomes identically zero, reject. Otherwise the product of these nonzero affine functions is a nonzero polynomial. The polynomial-avoidance lemma in Part I provides an integer parameter point where every factor is nonzero, proving satisfiability. With no disequalities, feasibility of \(E\) already proves satisfiability.

The parametrization and all substitutions have polynomial bit length by Lemmas A1–A2. The algorithm need only test whether each substituted affine function is identically zero; it need not expand the product or search for its nonzero value. Thus the decision procedure runs in polynomial time. \(\square\)

### Corollary A5 — PROVED, confidence 0.99

Every finite Boolean combination of affine equations and congruences has a terminating integer satisfiability test. For a fixed template, CSP instances over its finite Boolean fibre presentations belong to NP.

**Proof.** Expand a Boolean formula into disjunctive normal form by enumerating its finite truth assignments. Replace a negated congruence \(\ell\not\equiv a\pmod d\) by the disjunction of the other \(d-1\) residue equations. Test every resulting conjunction with Lemma A4. This proves decidability; this conversion need not be polynomial for a general input Boolean formula.

For a fixed CSP template, precompute each finite fibre's finite disjunctive presentation once. On an instance, nondeterministically choose a value for every finite-sort variable and one disjunct for every relation occurrence. These choices have polynomial length because the template, finite sorts, and lists of disjuncts are fixed. Verify finite equalities and pins and assemble the chosen integer conjunction. Its encoding length is polynomial in the instance length. Lemma A4 decides whether it has an integer solution in polynomial time. A satisfiable instance has one successful choice; a successful choice supplies actual witnesses by the lemma. This is an NP verifier. \(\square\)

## A3. The precise finite CSP oracle

The external finite-CSP input is **Andrei A. Bulatov (2017), Theorem 4**, in *A Dichotomy Theorem for Nonuniform CSPs*, FOCS 2017, 319–330, DOI [10.1109/FOCS.2017.37](https://doi.org/10.1109/FOCS.2017.37). Its tractability direction states that the relations preserved by a finite idempotent algebra with a weak near-unanimity term yield polynomial-time finite CSPs. The primary author-hosted paper is [focs17.pdf](https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf).

A weak near-unanimity operation \(t\) is idempotent and satisfies equality of all expressions obtained by placing one \(y\) among otherwise identical \(x\)'s. A cyclic operation has these identities by successive rotations. Thus every finite cyclic idempotent operation used in this report satisfies the theorem's tractability hypothesis directly.

### Lemma A6 — PROVED, confidence 0.99

Fix finitely many finite sorts, a common cyclic idempotent operation family \(f\), and an arity bound \(K\). There is one polynomial-time solver for every many-sorted CSP whose constraints are explicitly listed relations of arity at most \(K\) preserved by \(f\). Addition and pins on a residue sort may be included whenever they are preserved by its component of \(f\).

**Proof.** Let \(A\) be the Cartesian product of the finite sort carriers. Equip it with the coordinatewise operation \(f_A\). It is idempotent and cyclic. For a typed relation \(R\subseteq S_1\times\cdots\times S_k\), define its cylinder \(\widehat R\subseteq A^k\) by requiring the designated \(S_i\)-coordinate of the \(i\)-th argument to form a tuple in \(R\), with all other coordinates unrestricted. Preservation of \(R\) by the sorted family implies preservation of \(\widehat R\) by \(f_A\): reading the designated coordinates commutes with the product operation.

Replace each typed variable by one variable over \(A\) and each relation by its cylinder. A typed solution extends to a product-domain solution by assigning arbitrary values to unused coordinates. A product-domain solution restricts to a typed solution by reading the prescribed sort coordinate of each variable. Hence this is an exact reduction. Repeated variables are kept as repeated occurrences of the same product variable, so the argument also handles repetitions.

There are only finitely many relations on the fixed finite product \(A\) of arity at most \(\max(K,3)\). The subcollection preserved by \(f_A\) is therefore a fixed finite constraint language. The cylindrical relations and the arithmetic gadgets belong to this language. Apply the cited finite tractability theorem to the algebra with sole basic operation \(f_A\); this operation is weak near-unanimity by cyclicity. Its fixed-language CSP has a polynomial-time algorithm. The cylinder conversion has constant expansion per table and polynomial size per instance because all carriers and the arity bound are fixed. This proves the claimed oracle. \(\square\)

## A4. No hidden arithmetic size assumption

The general algorithm persistently stores only equations already occurring in the original instance's fixed disjunctive fibre presentations, together with its original arithmetic atoms. It can recompute every temporary basis or multiplier from those stored original rows. Consequently all calls to Lemmas A1–A4 have inputs of polynomial binary length in the original instance. This point is proved in the refinement argument in Part III; polynomial running times in the current representation alone would not have been sufficient without it.

---

# Counterexample C. Failure of shared-coefficient GC

## C1. Complete specification

### Theorem C1 — PROVED, confidence 0.99

There is a finite-signature core \(\mathcal C\) with \(Q\), with \(\neg GC\) for every generic-template modulus, and with polynomial-time CSP.

Its sorts are two separate copies \(A,B\) of \(\mathbb Z\) and the finite sort \(F=\{a,b,\ast\}\). There are no torsion sorts. Its complete nonlogical signature is:

* the addition graph \(\operatorname{Add}_A\) and pin \(1_A\);
* the addition graph \(\operatorname{Add}_B\) and pin \(1_B\);
* the three unary pins \(\{a\},\{b\},\{\ast\}\) on \(F\);
* one relation \(R\subseteq A\times B\times F\), with fibres

\[
R_a=\{(0,0)\},\qquad
R_b=\{(1,1)\},\qquad
R_{\ast}=\{(x,y)\in\mathbb Z^2:x-y\ne0\}.
\tag{C1}
\]

Equality is the usual typed logical equality. No coordinate-identification relation between \(A\) and \(B\) is included. Every fibre in (C1) is an allowed Boolean affine fibre. The subtraction in the description of \(R_{\ast}\) is an external numerical description; it does not introduce a mixed-sort arithmetic operation into the signature.

**Proof that this is a core.** An endomorphism on either integer sort preserves its addition graph and pin \(1\). Preservation of addition makes it an additive group homomorphism: its value at zero is zero, its value on a sum is the sum of the values, and its value at a negative integer is the negative of its value at the corresponding positive integer. Since it sends \(1\) to \(1\), repeated addition gives its value \(n\) at every positive integer \(n\); the inverse identity gives its value at every negative integer. It is therefore the identity on both integer sorts. All finite elements are pinned, so its component on \(F\) is also the identity. The only endomorphism is the identity, which is an embedding. Thus \(\mathcal C\) is a core. \(\square\)

## C2. Uniform verification of \(Q\) for every modulus

On \(F\), define the binary operation \(\vee\) by

\[
a\vee a=a,\quad b\vee b=b,\quad \ast\vee\ast=\ast,
\quad a\vee b=a\vee\ast=b\vee\ast=\ast,
\]

and make it symmetric. Its \(k\)-ary iterate returns \(a\) if all inputs are \(a\), returns \(b\) if all inputs are \(b\), and returns \(\ast\) in every other case. This explicit description proves associativity, commutativity, and idempotence: a fold is a leaf exactly when every folded value is that leaf, irrespective of parenthesization or order.

### Lemma C2 — PROVED, confidence 0.99

For every \(N\ge1\), put \(k=N+1\). The operation family

\[
f_N^A(r_1,\ldots,r_k)=\sum_i r_i\pmod N,
\qquad
f_N^B(r_1,\ldots,r_k)=\sum_i r_i\pmod N,
\qquad
f_N^F=\bigvee_{i=1}^k
\tag{C2}
\]

preserves every relation of \(D_N^{\mathrm{pp}}\).

**Proof.** Fix an arbitrary pp relation \(S\), and choose \(k\) tuples in its mod-\(N\) image. For each choose one actual tuple in \(S\) and one complete witness assignment for a fixed pp definition of \(S\). Thus we have \(k\) full satisfying assignments of the same finite atomic diagram.

Choose two independent integer weight vectors \(\gamma^A,\gamma^B\), each satisfying

\[
\sum_i\gamma_i^A=\sum_i\gamma_i^B=1,
\qquad
\gamma_i^A\equiv\gamma_i^B\equiv1\pmod N.
\tag{C3}
\]

Such vectors exist: \((1-N,1,\ldots,1)\) has \(k=N+1\) entries and sum one. Adding \(N(e_i-e_1)\) supplies a full rationally spanning lattice of choices in each sum-one hyperplane. This also works for \(N=1\), where \(k=2\).

Combine all variables of sort \(A\) with \(\gamma^A\), all variables of sort \(B\) with \(\gamma^B\), and all variables of sort \(F\) with the \(k\)-ary join. Typed equalities are preserved because the same variable receives the same operation. Integer addition is preserved by linearity. The integer pin \(1\) is preserved by the coefficient sums, and each finite pin is preserved by idempotence.

Consider one \(R\)-atom. If its output label is \(a\), all input labels are \(a\), so all its integer input coordinates are zero and both output coordinates are zero. The output satisfies \(R_a\). If its output label is \(b\), all input labels are \(b\), so all integer input coordinates are one and both output coordinates are one. The output satisfies \(R_b\).

It remains to handle output label \(\ast\). Write its integer inputs as \((x_i,y_i)\). Its forbidden output equality is the affine equation

\[
\sum_i\gamma_i^A x_i-\sum_i\gamma_i^B y_i=0.
\tag{C4}
\]

This equation is not identically true on the two independent sum-one coefficient spaces. Indeed, if it were identically true, varying \(\gamma^A\) by \(e_i-e_j\) would imply \(x_i=x_j\) for all \(i,j\), and varying \(\gamma^B\) would imply \(y_i=y_j\) for all \(i,j\). Evaluating at coefficient projections would then imply that their two constant values are equal, say to \(t\). Each input tuple would have equal integer coordinates \((t,t)\). Such a tuple belongs to \(R\) only when \(t=0\) and its label is \(a\), or when \(t=1\) and its label is \(b\). In the first case all labels are \(a\), so the output label is \(a\). In the second all labels are \(b\), so the output label is \(b\). Both contradict output label \(\ast\). If \(t\notin\{0,1\}\), no input tuple belongs to \(R\), also a contradiction.

Thus each output-\(\ast\) atom forbids only a proper affine hyperplane in the joint coefficient space. The pp diagram has finitely many atoms. The polynomial-avoidance lemma gives one pair of weight vectors satisfying (C3) and avoiding all these forbidden hyperplanes simultaneously. Every atom then holds in the combined full assignment. Its free tuple belongs to \(S\).

Modulo \(N\), every coefficient is one, so the combined free tuple has exactly the numerical outputs in (C2); its finite coordinates are exactly the join outputs. It is therefore an actual lift of the componentwise result of (C2) on the selected tuples of \(q_N(S)\). This proves preservation of that relation. The argument applies to every pp relation \(S\), with the same finite operation family (C2). \(\square\)

### Corollary C3 — PROVED, confidence 0.99

The structure \(\mathcal C\) satisfies \(Q\).

**Proof.** The family (C2) is cyclic. It is idempotent on each integer residue sort because \(k=N+1\equiv1\pmod N\), and on \(F\) by the join definition. Its arity \(k\) is at least two. The explicit cyclic-to-Taylor identities in the opening definitions make it a Taylor family. Lemma C2 proves that it is a polymorphism of \(D_N^{\mathrm{pp}}\) for every \(N\), which is precisely \(Q\). \(\square\)

## C3. Complete failure of the old generic template

### Lemma C4 — PROVED, confidence 0.99

Every Boolean operation preserving the constants and

\[
T_3=\{000,011,101,110,111\}
\]

is an OR of a nonempty set of its arguments. If the operation is cyclic, it is the OR of all arguments.

**Proof.** Let \(f\) have arity \(k\). For Boolean vectors \(u\le v\), the three-column matrix \((u,v,v)\) has every row in \(T_3\). If \(f(u)=1\) and \(f(v)=0\), its output is \(100\), which is forbidden. Hence \(f\) is monotone.

For any \(u,v\), every row of \((u,v,u\vee v)\) belongs to \(T_3\). Therefore \(f(u)=f(v)=0\) implies \(f(u\vee v)=0\), since output \(001\) is forbidden. The zero set of \(f\) is closed under coordinatewise OR.

Let \(e_i\) be the Boolean unit vectors and put \(I=\{i:f(e_i)=1\}\). If \(x_i=1\) for some \(i\in I\), monotonicity gives \(f(x)=1\). If no such coordinate occurs, \(x\) is the OR of unit vectors on which \(f\) is zero; closure of the zero set gives \(f(x)=0\). For the empty OR use preservation of zero. Thus \(f(x)=\bigvee_{i\in I}x_i\). Preservation of one forces \(I\ne\varnothing\).

Conversely, OR on a nonempty set of arguments preserves \(T_3\). If its output had exactly one coordinate equal to one, some selected input row would have a one in that coordinate; every selected input row would have zeros in the other two coordinates. That row would have exactly one one, contrary to membership in \(T_3\). Pins are also preserved. Finally, cyclicity makes \(I\) invariant under the cyclic permutation of the \(k\) argument positions. A nonempty invariant subset of this transitive cycle is the whole set. \(\square\)

### Lemma C5 — PROVED, confidence 0.99

For every modulus used in the original shared-coefficient generic template, \(\mathbb T(\mathcal C)\) is non-Taylor.

**Proof.** Use the displayed fibre presentation (C1), whose exact zero forms include \(x-y\), \(x\), and \(x-1\), as well as the corresponding \(y\)-forms where needed. Suppose the finite generic template were Taylor. The finite-product application of Barto–Kozik Theorem 4.1, proved in Part II, supplies an idempotent cyclic polymorphism of some prime arity \(p\ge2\). By Lemma C4 its Boolean component is OR on all \(p\) arguments.

Feed it one realised \(R\)-type from \((0,0,a)\) and \(p-1\) realised \(R\)-types from \((1,1,b)\). For \(x-y\), all indicators are zero, so the output indicator is zero. For \(x\), at least one input indicator is one, so the output is one. For \(x-1\), the \((0,0,a)\) input has indicator one, so its output is one. Any realised output would therefore satisfy

\[
x=y,\qquad x\ne0,\qquad x\ne1.
\]

No label permits this. Label \(a\) requires \(x=0\); label \(b\) requires \(x=1\); label \(\ast\) requires \(x\ne y\). These are all three labels. The required output is not a realised type, contradicting preservation of \(\operatorname{Real}(R)\).

The contradiction is independent of the integer residue output and therefore of the modulus, including modulus one. Thus every such generic template is non-Taylor, proving \(\neg GC\). \(\square\)

## C4. Complexity and the correct interpretation

### Corollary C6 — PROVED, confidence 0.97

\(\operatorname{CSP}(\mathcal C)\in\mathrm P\).

**Proof.** The signature and all fibre presentations of \(\mathcal C\) satisfy the hypotheses of the general algorithm in Part III. Corollary C3 gives \(Q\) uniformly for all moduli. Applying the fully proved algorithmic theorem therefore gives a polynomial-time decision procedure for this exact template. No strict polymorphism on the original integer sorts is assumed. \(\square\)

The independent-sort character is intrinsic. If literal coordinate identity between \(A\) and \(B\) were pp-definable, the formula

\[
\exists y,\lambda\,[R(x,y,\lambda)\land x=y]
\]

would pp-define the unary set \(\{0,1\}\). Under \(Q\), the hyperplane-cover lemma applied to the cover by \(\{x=0\}\) and \(\{x=1\}\) would force that two-point set into one of these singleton hyperplanes, which is false. Hence no such pp identity exists.

A structure with \(Q\land\neg GC\) and a polynomial-time CSP disproves necessity of the old \(GC\). It does not disprove \(Q\) as a tractability condition. The general algorithm proved in this report establishes the positive direction for \(Q\); the question's stipulated hardness implication supplies its complementary hard direction.

---

# Final adversarial self-audit

## Verdict and confidence

**PROVED — confidence 0.94.** The complete report proves a decidable finite certificate equivalent to \(Q\), proves \(Q\Rightarrow\operatorname{CSP}(\mathcal M)\in\mathrm P\), and supplies a fully verified \(Q\land\neg GC\) example. The hardness conclusion uses exactly the implication stipulated as established item 3 in the question. NP membership is proved in Appendix A5. This report is a mathematical proof with independent internal audits; it is not a claim of formal verification or a claim about the literature's priority history.

## The step most likely to be wrong

**PROVED — confidence 0.95.** The most exposed step is the compression of an exact residue image relative to a changing integer affine space. It would be wrong to reduce the defining equations literally modulo \(m\), or to replace an image of a full atom plus its arithmetic environment by separate atom images.

For example, let the current arithmetic space satisfy \(x=2y\), and impose the atom \(x=0\). Modulo two, the literal equation \(x=0\) adds no restriction to the already forced residue of \(x\). But an actual integer solution has \(y=0\), so the exact relative image forces the residue of \(y\) to be zero as well. The algorithm retains this information: in the parameter \(t=y\), the exact equation is \(2t=0\), whose integer solutions have image \(t=0\pmod2\). Appendix A3 computes precisely that image using a unimodular coordinate system.

Why the proof survives this objection: each equality cell is solved over the integers first. Its exact image is then described by primitive coordinates, with at most as many rows as the fixed cell has equations. Congruences are added only after that exact image has been computed. Disequalities are handled on each full residue lattice by finite hyperplane avoidance. Finally, the table is the actual image under the bounded row map, including the restriction that its row values are attained. Every part of the common-polymorphism argument has actual preimages.

If this exact-image lemma failed, the polynomial-time theorem would fail at its finite stage. The algebraic equivalence between \(Q\) and the finite generic certificate would remain independently proved in Parts I–II. The two-sort counterexample's all-modulus verification would also remain independent of the algorithm.

## Why local compatibility is not mistaken for a global solution

**PROVED — confidence 0.96.** The finite relaxation is only an intermediate condition. Acceptance additionally requires that every supported pp set has the entire current affine hull. For each atom, the proof selects actual supported witnesses spanning that hull. It combines the finite rows for all atoms into one common list. Exact relative residue membership then supplies a witness for every other atom in every row at the same global parameter residue. The cyclic operation produces one common finite assignment and one common output residue. Only after proving generic satisfaction of every atom on that one coset does finite avoidance choose a single integer point satisfying the whole instance.

If the spanning requirement were omitted, individually compatible atoms could be accepted without a common integer solution. The algorithm never makes that inference.

## The pp-definition check

**PROVED — confidence 0.98.** The temporary DNF cells need not be pp-definable, and the proof does not apply the hyperplane-cover theorem to them. It applies that theorem to

\[
S_a(t)\iff\exists\eta,(v_b)_b\left[
R_a(u+Bt,\eta_a)\land
\bigwedge_b\bigl(v_b\equiv t\pmod m\land R_b(u+Bv_b,\eta_b)\bigr)
\right].
\]

This is an actual pp formula: each substitution is inside a pp-identification block, each congruence is coordinatewise, and every relation atom is original. The finite variables are shared. An external finite expansion of the residue relaxation proves the period-\(m\) Boolean description, without assuming quantifier elimination preserves a chosen period.

## The lattice-index check

**PROVED — confidence 0.98.** The direction extraction does not replace a subgroup by its saturation without justification. In one residue slice with affine direction \(V\), it proves the exact identity

\[
S-S=m(V\cap\mathbb Z^d).
\]

Without the one-residue hypothesis it proves the two inclusions sufficient for the scaled-difference formula to define exactly \(V\cap\mathbb Z^d\). This is the relation used by the minimal-support splitting argument. The proof never assumes that an arbitrary affine hull is pp-definable.

## The coefficient-growth check

**PROVED — confidence 0.98.** Polynomial time for each normal-form call would not by itself control repeated refinement. The proof establishes more: one enabled original cell has the entire supported affine hull. Each refinement can therefore append only original positive equality rows. The persistent matrix remains a subcollection of a polynomially sized original row pool. All temporary matrices are recomputed from that pool, so there is no recursion in coefficient lengths. Every strict update lowers dimension, giving at most the number of integer variables many updates.

## The fixed finite-language check

**PROVED — confidence 0.98.** The compressed tables vary with the current arithmetic space, but their arities and carriers have fixed bounds and all are preserved by the same cyclic operation. They therefore belong to one fixed finite language. The use of Bulatov's theorem is for that single language. Affine support queries are represented with finite addition and pins, which share the same mean operation. No uniformity theorem for an uncontrolled changing family of templates is assumed.

## The arity-amplification check

**PROVED — confidence 0.97.** A node's excluded hyperplanes may depend on its children. The term-tree induction first preserves a nonzero coefficient polynomial while choosing earlier nodes, then avoids the resulting nonzero polynomial and the current node's proper hyperplanes. This establishes density for all valid node assignments. Full affine span of the root map then suffices because every obstruction in a fibre is affine. Rational projection choices are used only to prove that a pullback polynomial is nonzero; actual witnesses are chosen from the prescribed integer coefficient lattice.

## Effectivity and what is actually computed

**PROVED — confidence 0.98.** The canonical block partition is recovered as the unique finest partition passing the finite certificate test. No algorithm decides non-pp-definability by an unbounded negative search. Explicit pp identity formulas are used only through their proved existence; their sizes do not enter the CSP running time. The computations use the supplied fibre formulas, integer matrices, finite tables, and a fixed finite CSP solver.

The CSP algorithm is a decision algorithm. Its correctness proof uses large-prime generic operations and spanning witnesses but does not enumerate them during execution. A separate polynomial-time construction of a complete integer solution is not claimed in this report.

## Reproducibility and computations

**PROVED — confidence 1.00.** No bounded-modulus experiment, random search, or unreported operation-table enumeration is used as evidence for any theorem. The all-\(N\) statements have uniform proofs. The finite certificate search and the CSP algorithm are specified symbolically and completely in Parts II and III. Arithmetic subroutines are reduced explicitly to a cited normal-form algorithm. The archive's CRC and SHA-256 checks verify file packaging only; they are not mathematical verification.

## What changes if a hypothesis is removed

**PROVED — confidence 0.97.** The finite-signature and finite-presentation assumptions make a common period \(m\), a fixed cell bound, and a bounded finite table language available. Arbitrary infinite signatures are outside the claim. The absence of order ensures that, after residues are fixed, a fibre has constant truth value off finitely many affine hyperplanes. Inequality half-spaces would invalidate that geometric step. Actual or pp-definable addition and the pin \(1\) are used both to force the residue means and to build the linear pp diagrams. These are hypotheses of the theorem, not optional properties inferred from first-order definability alone.

## Logical interpretation of the result

**PROVED — confidence 0.99.** The two-sort example with \(Q\land\neg GC\) and a polynomial-time CSP refutes necessity of the old shared-weight \(GC\), while supporting \(Q\) as the dividing condition. The final unconditional branch statements are “in P when \(Q\) holds” and, using the stipulated hardness implication, “NP-complete when \(Q\) fails.” A literal equivalence between membership in P and \(Q\) adds the usual assumption \(\mathrm P\ne\mathrm{NP}\).

---

# Precise references and dependency map

The report attributes no new lemma to an external source. The following numbered results are the only external mathematical algorithms or structural theorems used in the main proof. Their applications are explicitly reduced to their hypotheses in the relevant chapters.

1. **Libor Barto and Marcin Kozik (2012).** *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*. Logical Methods in Computer Science **8**(1), article 07. **Theorem 4.1.** Used to obtain a cyclic term of each prime arity exceeding the cardinality of a finite idempotent Taylor algebra. The sorted-to-product reduction, preservation of all pp-image relations under terms, and the reverse cyclic-to-Taylor identities are proved in Part II. [Primary published PDF](https://lmcs.episciences.org/673/pdf). DOI: [10.2168/LMCS-8(1:7)2012](https://doi.org/10.2168/LMCS-8(1:7)2012).

2. **Ravindran Kannan and Achim Bachem (1979).** *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*. SIAM Journal on Computing **8**(4), 499–507. **Theorem 2 and Lemma 3.** Used only for square nonsingular column Hermite form and its polynomially bounded unimodular multiplier. Appendix A2 and Part III Lemma 2.2 give the complete rectangular reduction, integer-solution parametrization, and exact residue-image derivation. No reliance is placed on the paper's unexpanded remark concerning general rectangular Smith forms. [Publisher and DOI](https://doi.org/10.1137/0208040). The theorem numbers were checked in the original-paper text reproduced at [Studyres](https://studyres.com/doc/14829602/paper---math-tamu) and [Studylib](https://studylib.net/doc/7924410/paper); these are mirrors of the original paper, not separate theorem attributions.

3. **Andrei A. Bulatov (2017).** *A Dichotomy Theorem for Nonuniform CSPs*. Proceedings of the 58th Annual IEEE Symposium on Foundations of Computer Science, 319–330. **Theorem 4, implication (2) to (1).** Used for polynomial-time finite CSP tractability under a weak near-unanimity term. The common cyclic operation is explicitly shown to be weak near-unanimity; all varying compressed relations belong to one fixed bounded-arity language; and the sorted-to-product finite CSP reduction is written out. [Primary author PDF](https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf). DOI: [10.1109/FOCS.2017.37](https://doi.org/10.1109/FOCS.2017.37).

The optional flat-join family chapter and the archival audit additionally use:

4. **Manuel Bodirsky, Barnaby Martin, Marcello Mamino, and Antoine Mottet (2018).** *The Complexity of Disjunctive Linear Diophantine Constraints*. 43rd International Symposium on Mathematical Foundations of Computer Science, LIPIcs **117**, article 33, 33:1–33:16. **Proposition 21** gives the fixed finite Horn-template CSP algorithm; **Theorem 22** gives the binary-parameter quantifier-free Horn arithmetic algorithm. The optional family chapter uses Theorem 22 for arithmetic feasibility and implication queries; the archival audit uses Proposition 21. The main new classification instead proves its needed equation/congruence/disequality verifier in Appendix A4. [Primary published PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.33/LIPIcs.MFCS.2018.33.pdf). DOI: [10.4230/LIPIcs.MFCS.2018.33](https://doi.org/10.4230/LIPIcs.MFCS.2018.33).

## Stipulated background used without external attribution

The NP-hardness implication \(\neg Q\Rightarrow\operatorname{CSP}(\mathcal M)\) NP-hard is established item 3 supplied by the user. It is not reproved or attributed to one of the papers above. The new positive implication and the finite decision criterion do not depend on it. The NP upper bound is proved directly in Appendix A5.

The relation between shared generic combinations and the original finite template \(\mathbb T(\mathcal M)\) is part of the question's definition of \(GC\). The counterexample chapter also gives a direct Boolean-indicator contradiction to Taylor in that template, including the full proof of the OR-clone property of \(T_3\).

The label-free “brief form” theorem is not invoked in the new proof. Its interpretation must respect the distinction between pp-linked coordinate sorts and independent sorts appearing together in external zero forms.
