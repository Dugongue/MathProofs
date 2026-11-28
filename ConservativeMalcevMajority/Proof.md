# Conservative balance from a conservative Mal'cev and a majority

**PROVED — A3 implies CB, over every finite domain and for arbitrary positive unary weights. Confidence: 0.99.**

Date: 27 November 2026.

All mathematical assertions in the proof and appendices are **PROVED**, with confidence 0.99, unless a different status is explicitly stated. The finite computation in Appendix B was actually executed using exact arithmetic; its reported finite checks have confidence 1.00. This document is a mathematical proof, not a Lean-checked formalization.

## 1. Statement and scope

Let D be finite. Suppose a constraint language Gamma, together with all unary relations, has a common conservative Mal'cev polymorphism m and a common conservative majority polymorphism q. Thus

\[
m(x,y,y)=m(y,y,x)=x,
\qquad
q(x,x,y)=q(x,y,x)=q(y,x,x)=x.
\]

For every pp-definable relation

\[
R\subseteq D^{X\sqcup Y\sqcup Z}
\]

and arbitrary positive unary weights w_i:D -> R_{>0}, i in Z, define

\[
M(a,b)=\sum_{c:(a,b,c)\in R}\prod_{i\in Z}w_i(c_i).
\]

**Theorem (PROVED; confidence 0.99).** Each nonzero support block of M has rank one. More precisely, on each rectangular block A x B of pr_{X,Y}R, there are positive functions F on A, G on B, and a positive scalar H such that

\[
\boxed{M(a,b)=F(a)G(b)H.}
\]

This factorization is a polynomial identity in the unary-weight variables. Boundary weights multiply rows and columns and therefore preserve the conclusion. All unary restrictions and all numbers of summed variables are covered. Thus A3 implies CB.

Using the converse CB implies A3 supplied in the question, this proves A3 iff CB. Together with the supplied CB implies VP theorem, it proves A3 implies VP. It does not assert the unconditional converse VP implies CB for unrestricted arithmetic circuits.

### Literature context

The structural ingredients are already present in Andrei A. Bulatov and Daniel Marx, *The complexity of global cardinality constraints*, Logical Methods in Computer Science 6(4:4), 2010, DOI 10.2168/LMCS-6(4:4)2010. Their Section 3 develops non-crossing equivalences, and Section 4 develops the associated decomposition. The argument below is a self-contained derivation of weighted block rank one; it does not infer balance merely from an algorithm or from a complexity separation.

Primary source: https://lmcs.episciences.org/1025/pdf

## 2. Two elementary preservation facts

### 2.1 Rectangularity and scalar kernels

**PROVED; confidence 0.99.** A relation preserved by a Mal'cev operation is rectangular across any bipartition of its coordinates. Indeed, from

\[
(a,c),(b,c),(b,d)\in T
\]

we obtain

\[
m((a,c),(b,c),(b,d))=(a,d)\in T.
\]

Here a,b or c,d may be tuples: the identities hold coordinatewise. Rectangularity says that nonempty neighborhoods are equal or disjoint. Therefore T is a disjoint union of complete bipartite blocks.

For a rectangular relation T between a tuple domain A and a scalar support E, define

\[
s\mathrel{\theta_T}t
\quad\Longleftrightarrow\quad
\exists a\in A:\ T(a,s)\wedge T(a,t).
\]

This is an equivalence relation on E, whose classes are the distinct nonempty scalar fibers T(a,-). It is preserved by m: for three pairs in theta_T, apply m coordinatewise to their three witnesses a. Both resulting scalar values have the resulting tuple as a common witness.

Crucially, conservativity will be used only on scalar sets E contained in D. The coordinatewise operation on a tuple domain is not assumed conservative as an operation on tuples.

### 2.2 Majority determines a relation from pairs

**PROVED; confidence 0.99.** If a relation S of positive arity is preserved by a majority operation, then membership in S is determined by its unary and binary projections. Nullary relations are handled separately as empty or as containing the single empty tuple.

Here is an elementary proof. The assertion is immediate for arity at most two. Induct on arity n. Let t have every pair in the corresponding projection of S. By induction, t restricted to any n-1 coordinates belongs to that projection of S. Choose three tuples of S that agree with t except possibly at coordinate 1, coordinate 2, and coordinate 3, respectively. Their coordinatewise majority is t. This proves t belongs to S.

Projections, conjunctions, and existential definitions preserve polymorphisms: witnesses can be combined coordinatewise. Hence these facts apply to every relation used below.

## 3. The scalar non-crossing and star lemmas

### 3.1 Non-crossing lemma

**PROVED; confidence 0.99.** Let alpha,beta be equivalence relations on the same scalar subset E of D, both preserved by the conservative Mal'cev operation m. An alpha-class and a beta-class are disjoint or one contains the other.

Suppose classes B,C cross. Choose

\[
a\in B\setminus C,\qquad
b\in B\cap C,\qquad
c\in C\setminus B.
\]

Set t=m(a,b,c). Preservation gives

\[
t\mathrel\alpha m(b,b,c)=c,
\qquad
t\mathrel\beta m(a,b,b)=a.
\]

Thus t is outside B, since c is outside B, and outside C, since a is outside C. But conservativity requires t in {a,b,c}, which is contained in B union C. Contradiction.

### 3.2 Star lemma

**PROVED; confidence 0.99.** Let P be a nontrivial partition of E into classes of one m-preserved equivalence. Let C be a class of another m-preserved equivalence on the same E. If C meets every class of P, then C=E.

For each P-class B, C meets B and also a different P-class. Therefore C is not contained in B. Non-crossing forces B to be contained in C. Taking the union of all B gives C=E.

This is the precise strengthening needed beyond the statement that two cross pairs stand or fall together: intersection with every class forces an entire neighbor class to be universal.

## 4. Restrict to one boundary-support block

**PROVED; confidence 0.99.** Assume R is nonempty and both X,Y are nonempty. The other cases give zero matrices or matrices with one row or one column.

The projection Q=pr_{X,Y}R is rectangular. Fix a nonzero block A x B of Q and put

\[
R_0=\{(a,b,c)\in R:a\in A,\ b\in B\}.
\]

R_0 is preserved by m and q. To justify the potentially delicate tuple restriction, fix b_0 in B. Then

\[
A=\{a:(a,b_0)\in Q\}.
\]

Both operations are idempotent. Applying either operation to three pairs (a_j,b_0) keeps the second tuple b_0, so A is preserved. The same argument preserves B. Consequently their joint restriction of R is preserved, and R_0 remains determined by its scalar binary projections.

For each hidden scalar coordinate i in Z, write T_i=pr_i R_0 and define

\[
U_i(a)=\{s\in T_i:(a,s)\in\operatorname{pr}_{X,i}R_0\},
\]

\[
V_i(b)=\{s\in T_i:(b,s)\in\operatorname{pr}_{Y,i}R_0\}.
\]

The distinct U_i(a) sets partition T_i, and so do the distinct V_i(b) sets. Each partition is the class partition of an m-preserved equivalence on the same scalar support T_i.

Every U_i(a) meets every V_i(b). This uses actual witnesses: since (a,b) belongs to A x B, some full tuple in R_0 realizes (a,b), and its i-coordinate is in the intersection. No assumption that pairwise witnesses can be combined is used here.

If the U-partition is nontrivial, each V-class meets every U-class, so the star lemma makes every V-class equal to T_i. Otherwise the U-partition is universal. Therefore the hidden coordinates split into exactly three types:

| Type | U-partition | V-partition |
|---|---|---|
| Z_L | nontrivial | universal |
| Z_R | universal | nontrivial |
| Z_0 | universal | universal |

Universal means U_i(a)=T_i for every a, or V_i(b)=T_i for every b, respectively.

## 5. The cross-pair step, in full

**PROVED; confidence 0.99.** For i in Z_L and j in Z_R union Z_0,

\[
\operatorname{pr}_{i,j}R_0=T_i\times T_j.
\]

Fix t in T_j. Because j is not in Z_L, its U-partition is universal. Thus for every a in A, the pair (a,t) belongs to pr_{X,j}R_0 and has an actual full-tuple witness in R_0.

Let

\[
N_i(t)=\{s\in T_i:(s,t)\in\operatorname{pr}_{i,j}R_0\}.
\]

The i-coordinate of the witness for (a,t) shows

\[
N_i(t)\cap U_i(a)\ne\varnothing
\qquad\text{for every }a\in A.
\]

Rectangularity makes N_i(t) a class of an m-preserved equivalence on T_i. The U_i partition is nontrivial because i is in Z_L. The star lemma therefore gives N_i(t)=T_i. Since t was arbitrary, the entire binary projection is full.

Exchanging X,Y gives full projections between Z_R and Z_0. The remaining cross projections are full directly:

* X versus Y: the boundary support is A x B.
* X versus Z_R or Z_0: the corresponding U-partition is universal.
* Y versus Z_L or Z_0: the corresponding V-partition is universal.

For tuple boundaries, these statements imply fullness of every scalar pair crossing the indicated groups.

Thus all scalar binary projections between the three coordinate groups

\[
X\cup Z_L,\qquad Y\cup Z_R,\qquad Z_0
\]

are full.

## 6. Exact product decomposition and weighted rank

**PROVED; confidence 0.99.** Define

\[
S_L=\operatorname{pr}_{X,Z_L}R_0,\quad
S_R=\operatorname{pr}_{Y,Z_R}R_0,\quad
S_0=\operatorname{pr}_{Z_0}R_0.
\]

Then

\[
\boxed{R_0=S_L\times S_R\times S_0.}
\]

The forward containment is automatic. For the reverse containment, combine arbitrary tuples from the three factors. A pair of coordinates inside one factor has a witness in R_0. A pair in different factors is allowed because the corresponding projection is full by Section 5. Unary values are supported as well. Majority's binary-determination property proves that the combined tuple belongs to R_0.

Now set

\[
F(a)=\sum_{u:(a,u)\in S_L}\prod_{i\in Z_L}w_i(u_i),
\qquad
G(b)=\sum_{v:(b,v)\in S_R}\prod_{i\in Z_R}w_i(v_i),
\]

\[
H=\sum_{t\in S_0}\prod_{i\in Z_0}w_i(t_i).
\]

Empty coordinate sets have the single empty tuple and empty product 1. Product decomposition gives

\[
M(a,b)=F(a)G(b)H
\qquad(a\in A,b\in B).
\]

All three factors are positive on their relevant supports. Hence each nonzero block has rank exactly one. Explicitly,

\[
M(a,b)M(a',b')-M(a,b')M(a',b)
=H^2F(a)F(a')\big(G(b)G(b')-G(b')G(b)\big)=0.
\]

This identity is symbolic in independent unary weights; there is no numerical approximation or division. Nonnegative weights are covered as well, although some rows, columns, or blocks can then vanish. Weights on X and Y only introduce additional row and column factors.

Every pp-definable relation is preserved by the common polymorphisms. If a weighted definition sums auxiliary witnesses, include those witnesses among Z and apply the same theorem to the complete solution relation. If it defines a relation by existential quantification, apply the theorem to that projected relation itself. Thus both support projection and weighted summation are covered, establishing CB exactly as requested.

## 7. Consequences and checks of scope

**PROVED; confidence 0.99.** The result holds for every finite |D| and every number of hidden variables. In particular, it explains the supplied three-element computations and extends them beyond the tested two hidden variables. No simplicity assumption or extra Chinese-remainder hypothesis is needed.

The role of majority is essential to product reconstruction. For comparison, on D={0,1}, the ternary even-parity relation is preserved by the conservative Mal'cev m(x,y,z)=x xor y xor z, but not by majority. With hidden-variable weights w(0)=1,w(1)=2, its boundary matrix is

\[
\begin{pmatrix}1&2\\2&1\end{pmatrix},
\qquad\det=-3.
\]

The three even-parity tuples 011,101,110 have majority 111, which is excluded. Thus this is outside A3 and shows precisely why full pair projections alone cannot replace majority.

The unconditional conclusions under the question's established converse are

\[
\boxed{A3\iff CB},\qquad
\boxed{A3\Longrightarrow\{P_\varphi\}\in VP}.
\]

An unqualified VP iff CB statement is not established by this argument. In particular, an algebraic hardness classification and an appropriate separation premise would be needed for the customary hardness-based converse. The proof here makes no claim to separate VP and VNP.

## 8. Adversarial self-audit

**Most vulnerable step:** asserting that N_i(t) meets every U_i-class on the same scalar support T_i. Non-crossing alone gives nesting, not universality.

The required extra premise is verified explicitly: j not in Z_L makes U_j(a)=T_j for every a; therefore each pair (a,t) has an actual tuple in R_0. Its i-coordinate belongs to both N_i(t) and U_i(a). Both partitions live on exactly T_i and are preserved by the same conservative m. Because the U_i partition has at least two classes, the star lemma applies and forces N_i(t)=T_i. This is the full cross-pair argument, with no uniform witness choice or tuple-level conservativity assumption.

## Appendix A. A stronger read-once formula corollary

**PROVED; confidence 0.99.** Every nonempty finite relation S preserved by common conservative m and q has a monotone read-once arithmetic formula for

\[
P_S=\sum_{s\in S}\prod_i x_{i,s_i}
\]

with exactly L=sum_i |pr_i S| variable leaves when n>=1. For fixed domain size this gives at most |D|n leaves and, after binarizing, at most L-1 addition/multiplication gates. Empty and zero-coordinate relations are represented by constants as appropriate. This is a formula-existence statement; it does not assert that an explicit table of an exponentially large relation must be computed.

Here are the structural details.

### A.1 Proper joins and non-full composition

The classes of all m-preserved equivalences on a fixed scalar support form a laminar family by Section 3. For a nonempty finite family of such equivalences, their union is already an equivalence: two classes meeting at the middle point of a two-step chain are nested. Each class of the join is an inclusion-maximal class in the family. Consequently a nonempty finite join of nonuniversal equivalences is nonuniversal.

Suppose T is a non-full subdirect rectangular relation on A x B and U is one on B x C, both m-invariant. Their scalar kernels on B are proper, so their join rho is proper. Choose b_1,b_2 in different rho-classes and choose T(a,b_1),U(b_2,c). If (a,c) belonged to T composed with U, a middle witness b would relate b_1 to b in the first kernel and b to b_2 in the second, a contradiction. Thus the composition is non-full.

### A.2 Product or a union separated in every coordinate

Put S_i=pr_i S and draw an edge ij when pr_{i,j}S is not S_i x S_j. Actual projections satisfy

\[
\operatorname{pr}_{i,k}S\subseteq
\operatorname{pr}_{i,j}S\circ\operatorname{pr}_{j,k}S.
\]

By non-full composition the graph is a disjoint union of cliques. If it has several components, binary determination gives S as the Cartesian product of its projections on those components.

Otherwise the graph is connected. Assume at least two coordinates. For each i, let alpha_i be the join of the left kernels of pr_{i,j}S for all j different from i. All are proper, so alpha_i is proper.

Now form a graph H whose vertices are tuples in S, adjacent whenever they agree in any coordinate. Along an H-edge, coordinate i either stays fixed or changes within one of the kernels defining alpha_i. Thus all i-values in one H-component lie in one alpha_i-class. Properness implies that H has more than one component and that each component has proper support at every coordinate.

Different H-components have disjoint supports in every coordinate: otherwise tuples in them would agree somewhere and be adjacent. If C is one H-component, then

\[
C=S\cap\prod_i\operatorname{pr}_i C.
\]

Indeed, any tuple of S using even one coordinate value from C already shares that coordinate with a tuple of C, so it lies in C. Each C is therefore a unary restriction of S and retains the two conservative polymorphisms.

Recursion terminates: a product split reduces the coordinate set, and a union split reduces every coordinate support. The leaves are unary relations.

### A.3 Formula size

Use multiplication for each product split, addition for each separated union, and sum_{a in S_i} x_{i,a} at a unary leaf. Product children have disjoint coordinate sets. Union children have disjoint value supports in every coordinate. Hence the sets of symbols (i,a) used by different children are disjoint at every split. Every supported symbol occurs exactly once, proving the stated read-once and linear-size bounds.

## Appendix B. Exactly verified four-element example

**PROVED by exact computation for the finite checks below; confidence 1.00.** This example illustrates the theorem; it is not a substitute for the proof and is not a counterexample search over all templates.

Let D={0,1,2,3}, A={0,1}, B={2,3}, and r(a)=floor(a/2). Define

\[
F=(A\times A)\cup\{(2,2),(3,3)\},
\quad
G=\{(0,0),(1,1)\}\cup(B\times B),
\]

and R(x,y,z) iff G(x,y) and F(y,z). Define m and q on an ordered triple as follows:

* If all three root bits r(a),r(b),r(c) agree, let m(a,b,c)=a xor b xor c, using the ordinary binary encodings of 0,1,2,3, and let q(a,b,c) be the value occurring at least twice.
* Otherwise let m choose the unique input in the minority root group, and let q choose the first input, in argument order, belonging to the majority root group.

Both operations are conservative. The exact checker enumerates all 64 input triples for each operation, all identity cases, all 16 unary relations, and every triple of tuples in F,G,R and the same-root relation E. All checks passed.

For w_y=(2,3,5,7), direct enumeration gives

\[
M(x,z)=
\begin{pmatrix}
2&2&0&0\\
3&3&0&0\\
0&0&5&7\\
0&0&5&7
\end{pmatrix}.
\]

Its two nonzero blocks have rank one even though their entries are unequal. The exact polynomial is

\[
P_R=(x_{0,0}x_{1,0}+x_{0,1}x_{1,1})(x_{2,0}+x_{2,1})
+(x_{0,2}+x_{0,3})(x_{1,2}x_{2,2}+x_{1,3}x_{2,3}).
\]

The checker verifies equality with all eight solution monomials. It also checks all 27 ordered assignments of the three coordinates to boundary groups X,Y and summed group Z. It checks rectangularity of each support block and all its 2-by-2 minors, symbolically in the twelve independent unary-weight variables, including boundary weights. There are 12 nonvacuous minor checks; every polynomial is identically zero.

Reproduce with Python 3 and no third-party dependencies:

```bash
python3 Verify.py
```

The script writes `results.json` beside itself. It uses exact integer coefficients in polynomial dictionaries, with no floating-point arithmetic or randomness. Its complete operation tables and check counts are in the accompanying JSON.

## Reference

Andrei A. Bulatov and Daniel Marx (2010), *The complexity of global cardinality constraints*, Logical Methods in Computer Science, volume 6, issue 4, article 4, pages 1-27. DOI: 10.2168/LMCS-6(4:4)2010. https://lmcs.episciences.org/1025
