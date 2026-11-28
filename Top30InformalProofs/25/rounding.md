# Rounding for the specified three-colour templates

The proof applies to the stated template classes. The arbitrary DF branch remains open.

Research result and proof audit — 26 November 2026

## What this answers

Problem 63 in Nakajima–Živný, *On the complexity of symmetric vs. functional PCSPs* (2024), asks whether an integer-affine rounding map to a finite ternary target always has a finite witness of the form

\[
\operatorname{Eqn}_{3^p,1}\times\operatorname{NAE}\longrightarrow B.
\]

The theorem below proves this assertion for every target with at most one allowed third value after a repeated pair (a,a). It strengthens the conclusion to a witness with at most 2|B| states, or an injective canonical witness with at most |B| states, and a recognition algorithm using quadratically many relation-membership queries.

This is a proved subclass result. The unrestricted Problem 63 and the stronger tractability-versus-hardness conjecture are not resolved here. The proof does not use the unverified portions of recent preprints or our earlier proposed homotopy-collapse theorem.

The target condition is weaker than full functionality: pairs of distinct colours may admit many third values. In particular, arbitrary rainbow triples are allowed, and every cyclic target C_k^+ belongs to the class.

The integer-midpoint lemma used below is a special case of the established work of Banakh, Banakh, Kolinko, and Ravsky; an elementary proof is included. We found no source stating this exact application and quantitative bound, but publication novelty has not been certified.

## Statement

Let Z_1 denote the ternary relational structure with universe Z and relation

\[
R^{Z_1}=\{(x,y,z)\in\mathbb Z^3:x+y+z=1\}.
\]

Let B be a finite nonempty ternary structure, with b elements, satisfying:

\[
\text{for every }a\in B,\quad
\#\{c\in B:(a,a,c)\in R^B\}\le 1.
\tag{DF}
\]

The diagonal transition T(a) is this unique c when it exists. It can be undefined for unused elements of B. No global symmetry assumption on R^B is needed.

For m>=1, define A_m by

\[
A_m=(\mathbb Z/m\mathbb Z)\times\{-,+\},
\]

with relation

\[
((r_1,s_1),(r_2,s_2),(r_3,s_3))\in R^{A_m}
\]

if and only if

\[
r_1+r_2+r_3=1\pmod m
\quad\text{and}\quad
(s_1,s_2,s_3)\text{ is not constant}.
\]

Equivalently, A_m is the relational direct product of the affine sum-one structure modulo m and Boolean NAE.

### Main theorem

The following are equivalent:

1. There is a homomorphism Z_1 -> B.
2. There is a homomorphism A_{3^a} -> B for some integer a>=0 satisfying 3^a<=b.
3. There is a homomorphism Z_1 -> B depending only on the sign class n<=0 versus n>=1 and on n modulo 3^a, for some 3^a<=b.

Moreover, existence of such a homomorphism can be decided with O(b^2) membership queries to R^B. A witness can be explicitly constructed.

The finite witness A_{3^a} has at most 2b elements. The membership-query bound assumes the relation can be queried; ordinary explicit relation representations give a polynomial-time implementation after appropriate indexing. The supplied implementation uses a dense relation table, whose allocation is O(b^3); the quadratic claim concerns relation probes. A sparse hash index gives expected total time O(|R^B|+b^2).

## 1. The affine endomorphism and cyclic normalization

Define

\[
F(n)=1-2n.
\]

It preserves the sum-one relation because

\[
x+y+z=1
\implies
F(x)+F(y)+F(z)=3-2=1.
\]

Let h:Z_1 -> B be a homomorphism. From the source tuple (n,n,F(n)) and (DF),

\[
h(F(n))=T(h(n)).
\tag{1}
\]

Thus T is defined on h(Z), and this finite image is closed under T.

Replace h by

\[
\widetilde h=h\circ F^b.
\]

This is still a homomorphism. Its image consists only of cyclic points of T: every forward orbit in a functional graph with at most b vertices has entered a cycle after b steps. On the set of all cyclic points, T is a permutation and hence injective.

We henceforth write h for this normalized homomorphism.

## 2. Midpoint closure

Suppose h(x)=h(y)=c and x+y is even. The source tuple

\[
(x,y,1-x-y)
\]

forces

\[
h(1-x-y)=T(c).
\]

On the other hand, (1) applied to (x+y)/2 gives

\[
h(1-x-y)=T\!\left(h\left(\frac{x+y}{2}\right)\right).
\]

Both arguments of T belong to the normalized image, where T is injective. Therefore

\[
h\left(\frac{x+y}{2}\right)=c.
\tag{2}
\]

Every colour fibre is closed under every midpoint that is an integer.

## 3. Elementary classification of midpoint-closed subsets of Z

### Lemma

If a nonempty subset S of Z is closed under integer midpoints and has at least two elements, then S is an arithmetic progression of odd step, truncated by an interval, a ray, or no boundary.

### Proof

Every gap between consecutive elements is odd. Otherwise, the integer midpoint of those two elements would be another element of S strictly inside the gap.

Take any three consecutive elements a<b<c. The two consecutive gaps are odd, so a and c have the same parity. Their midpoint belongs to S and lies strictly between a and c. The only such element of S is b. Consequently

\[
a+c=2b.
\]

All consecutive gaps are therefore equal. Their common value d is odd. This proves the claimed form.

The argument applies equally to finite, one-sided infinite, and two-sided infinite subsets of Z. Between any two elements there are finitely many integers, so consecutiveness is well-defined. A two-element set simply has one odd gap. QED.

## 4. Dynamics force exact periodicity on the two half-lines

Let c be a colour in the normalized image, and let ell be its T-cycle length. For every n>=0,

\[
F^{2\ell n}(x)
=4^{\ell n}x+\frac{1-4^{\ell n}}3
=\frac13+4^{\ell n}\left(x-\frac13\right).
\tag{3}
\]

Because T^{2 ell n}(c)=c, these iterates remain in the same fibre.

If x>=1, the sequence tends to positive infinity. If x<=0, it tends to negative infinity.

Thus every fibre is infinite. By the midpoint classification, it has some odd step d_c. A fibre meeting the positive half-line is unbounded above; a fibre meeting the nonpositive half-line is unbounded below. If it meets both, its interval is all of Z.

For each colour occurring on the positive half-line, let

\[
P_c=r_c+d_c\mathbb Z
\]

be its full containing residue class.

These full residue classes are pairwise disjoint. If two of them intersect, their intersection contains arbitrarily large integers; since both corresponding fibres contain their entire sufficiently positive residue-class tails, the two fibres would intersect.

They also cover all integers. Let D be the least common multiple of their finitely many moduli. For any integer x, choose a sufficiently large positive y congruent to x modulo D. The colour of y occurs on the positive half-line, and its containing residue class also contains x.

It follows that for each positive x, its colour is exactly the unique positive-side residue class containing it. In particular, the positive fibres have no exceptional initial segment: each is its full residue class intersected with {1,2,...}.

The identical argument on the nonpositive half-line gives the corresponding conclusion there.

Let m be the least common multiple of all the odd fibre steps. Then m is finite and odd, and h(n) depends only on

\[
n\bmod m
\quad\text{and}\quad
\sigma(n)=
\begin{cases}
-,&n\le0,\\
+,&n\ge1.
\end{cases}
\tag{4}
\]

No numerical bound on m is needed at this point; the cycle argument below gives a much stronger bound.

## 5. Factoring through the finite sign-and-residue structure

Define

\[
\gamma_m(n)=(n\bmod m,\sigma(n)).
\]

This is a homomorphism Z_1 -> A_m. Three nonpositive integers cannot sum to 1, and three positive integers have sum at least 3.

More strongly, every relation tuple of A_m lifts to a relation tuple of Z_1.

Indeed, take any three residues summing to 1 modulo m and any mixed assignment of signs. Choose one positive-sign coordinate and one negative-sign coordinate. Choose a representative with the required sign for the third coordinate. Choose the positive coordinate in its prescribed residue class sufficiently large. The remaining integer, defined by requiring the three to sum exactly to 1, lies in the prescribed residue class and is nonpositive when the chosen positive coordinate is large enough.

By (4), h factors as a function

\[
h=\phi\circ\gamma_m.
\]

Surjectivity on relation tuples proves that phi:A_m -> B is a homomorphism. This step is needed: function factorization alone would not suffice.

## 6. Removing every prime except 3

Write

\[
m=3^p q,\qquad \gcd(q,3)=1.
\]

Fix c in Z/qZ satisfying 3c=1. Under the Chinese remainder identification, the map

\[
r\longmapsto(r,c)
\]

is a homomorphism from the sum-one structure modulo 3^p into the sum-one structure modulo m.

Preserving the sign coordinate gives a homomorphism

\[
A_{3^p}\longrightarrow A_m.
\]

Composition produces a homomorphism

\[
\psi:A_{3^p}\longrightarrow B.
\tag{5}
\]

The conventions for q=1 and p=0 are the usual trivial one-element residue groups.

## 7. The diagonal transition is one cycle

The diagonal transition of A_{3^p} is

\[
S(r,s)=(1-2r,-s).
\tag{6}
\]

It is a single cycle of length 2*3^p.

To check this, let G(r)=1-2r on Z/3^p Z. Its iterate satisfies

\[
G^t(r)=(-2)^t r+\frac{1-(-2)^t}{3}.
\]

Hence G^t(r)=r modulo 3^p if and only if

\[
3^{p+1}\mid \bigl((-2)^t-1\bigr)(3r-1).
\]

The factor 3r-1 is a unit modulo 3. The standard elementary valuation identity

\[
v_3((-2)^t-1)=1+v_3(t)
\tag{7}
\]

shows that the least positive return time is 3^p, independently of r.

For completeness, (7) follows by first observing that the valuation is one when t is not divisible by 3, using a binomial expansion of (1-3)^t. Replacing t by 3t increases the valuation by exactly one: if u=1+3^j a with 3 not dividing a and j>=1, then

\[
u^3-1=3^{j+1}a+3^{2j+1}a^2+3^{3j}a^3
\]

has valuation j+1. Iterating proves (7).

The residue cycle length 3^p is odd, whereas the sign coordinate has period two. Therefore the full return time in (6) is 2*3^p, equal to the cardinality of A_{3^p}.

## 8. Compressing the exponent to the target size

Condition (DF) forces the homomorphism (5) to intertwine the diagonal transitions:

\[
\psi(S(a))=T(\psi(a)).
\tag{8}
\]

Since S is one cycle, the image lies on one T-cycle. Let its length be k. Then

\[
k\mid 2\cdot3^p.
\]

Consequently

\[
k=3^a\quad\text{or}\quad k=2\cdot3^a
\]

for some a<=p. Since the cycle lies in B,

\[
3^a\le k\le b.
\tag{9}
\]

Let

\[
\pi:A_{3^p}\longrightarrow A_{3^a}
\]

be reduction of the residue coordinate, with the sign unchanged. Every fibre is an orbit of S^{2*3^a}. Since k divides 2*3^a, (8) makes psi constant on these fibres. Thus

\[
\psi=\theta\circ\pi
\]

as functions.

The projection pi is surjective on relation tuples: given three residues modulo 3^a summing to 1, lift the first two arbitrarily modulo 3^p and choose the third to make the sum 1. Keep the mixed signs unchanged.

Therefore theta:A_{3^a} -> B is a homomorphism. Together with (9), this proves the bounded finite-witness implication.

The reverse implication follows by composition with gamma_{3^a}. This completes the main equivalence.

## 9. A quadratic-query finite test

Construct the partial functional graph T using the diagonal relation tuples.

Only its cycles whose lengths have the form

\[
k=3^a\quad\text{or}\quad k=2\cdot3^a
\]

need be considered.

For one such cycle, set d=3^a. If its length is d, use the unsigned sum-one structure modulo d; if its length is 2d, use A_d. In either case the source diagonal transition is a single cycle, and an intertwining map is determined by the image of one chosen source vertex.

Only one phase needs to be tested. The source transition is an automorphism of its entire relational structure: replacing all residues r by 1-2r preserves sum one, since 3-2=1, and flipping all signs preserves NAE. The residue map is invertible because d is a power of 3.

Let phi_0 be one intertwining map. Every other phase is phi_0 composed with a power of this source automorphism. Consequently either every phase is a homomorphism or none is. This removes phase enumeration entirely.

For each eligible target cycle:

1. Define the canonical phase map by following the source and target cycles.
2. Test every source relation tuple once.

The unsigned source has d^2 relation tuples. The signed source has 6d^2: choose the first two residues freely, the third is determined, and choose one of the six nonconstant sign triples.

Thus a cycle of length k requires k^2 probes in the odd case and (3/2)k^2 probes in the even case. In particular the number of probes is at most 6k^2.

The cycles are disjoint. Including construction of T gives the explicit loose bound

\[
b^2+6\sum_{\text{eligible cycles}}k^2\le7b^2.
\]

Using the unsigned source on odd cycles sharpens this bound to at most (5/2)b^2. Early rejection may use fewer probes. Thus the overall query count is O(b^2).

When the canonical map passes, it supplies an explicit sign-and-residue rounding map

\[
n\longmapsto
\theta(n\bmod d,\sigma(n)).
\]

This function is computable in polynomial time in the bit length of n, and its fixed lookup table has at most 2b entries.

## 10. Additional interpretation and limits

If the selected T-cycle has odd length d=3^a, the candidate intertwining map identifies the two signs at every residue. It yields an injective homomorphism from the sum-one structure modulo d into B.

If the selected cycle has length 2d, the map A_d -> B is injective.

These are injective homomorphisms, not necessarily embeddings that reflect all relations.

The theorem proves the finite-witness and computable-rounding assertion for targets satisfying (DF). It does not assert the same criterion for arbitrary finite targets. The injectivity of T on the normalized image is essential in the midpoint step.

The finite intermediate structure A_d has NAE as a factor; its own CSP need not be tractable. The result should therefore not be described as finite tractability. The efficient rounding map instead combines with solving the original integer linear equations.

Global periodicity cannot replace the two sign classes. For Boolean NAE, T swaps the two colours and the threshold map n<=0 versus n>=1 is a homomorphism. Any successful periodic finite-affine factor would have an odd diagonal orbit incompatible with this swap. The sign coordinate is mathematically necessary.

## 11. Exact classification for the cyclic family

Define C_k^+ on Z/kZ by including all permutations of

\[
(a,a,a+1\bmod k)
\]

and all triples with three distinct entries. For k=1 this convention includes a loop.

Its diagonal transition is one k-cycle. The theorem gives

\[
\boxed{
Z_1\longrightarrow C_k^+
\quad\Longleftrightarrow\quad
k=3^a\ \text{or}\ k=2\cdot3^a
\quad(a\ge0).
}
\]

Necessity follows because the image of a finite witness is an eligible successor cycle, and C_k^+ has only its one k-cycle.

For sufficiency, identify Eqn_{3^a,1} with that cycle if k=3^a, or identify Eqn_{3^a,1} times NAE with it if k=2*3^a. The identification follows the source and target diagonal cycles. A source tuple with a repeated vertex uses exactly the prescribed successor. A source tuple with three distinct vertices has three distinct images, and all such rainbow tuples are allowed in C_k^+. Thus the identification is a homomorphism.

The known characterization of AIP for approximate 1-in-3 SAT therefore gives

\[
\boxed{
\text{AIP solves PCSP(1-in-3, }C_k^+\text{)}
\iff k=3^a\text{ or }2\cdot3^a.
}
\]

Nakajima–Živný's Theorem 6 already establishes that AIP and BLP+AIP have the same applicability for this left template. The displayed criterion consequently classifies both algorithms on the whole cyclic family, and the general algorithm above classifies both on all targets satisfying (DF).

Failure of these algorithms is not a proof of NP-hardness. In particular, this work does not settle NP-hardness for C_4^+.

## 12. Effective search rounding

A positive certificate provides either one lookup row modulo d or two rows indexed by the sign class and the residue modulo d, with d<=b. Given an integer n in binary, comparison with zero and reduction modulo the fixed d evaluate the rounding map in polynomial time in the bit length of n.

For a promised satisfiable 1-in-3 instance, replace each constraint by an equation x+y+z=1 over the integers. A polynomial-time integer-linear-algebra procedure supplies an integer solution. Applying the certified rounding map to every coordinate gives a B-solution. This constructs the search solution, in addition to recognizing whether the affine relaxation applies.

The intermediary Eqn_d times NAE can have an NP-hard CSP of its own. The result is therefore about finite certificates for rounding, not a claim of finite tractability in the technical sandwich-CSP sense.

## 13. Finite implementation checks

The standalone C++17 implementation in rounding.cpp accepts a finite relation and returns the canonical witness table when one exists. Its dense representation has O(b^3) allocation; the theorem's sharper O(b^2) bound concerns relation-membership queries. With a preindexed sparse relation, the recognition procedure has the corresponding sparse-input implementation.

The executed verification run classified C_k^+ for 1<=k<=40 and examples with transients, missing rainbow relations, partial diagonal transitions, and invalid diagonal functionality. It validated nine returned certificates on every source relation tuple and on integer sum-one triples in a bounded interval. Full counts and output are in rounding_checks.txt.

These finite checks test the implementation. The universal infinite-source equivalence follows from the written proof.

## 14. The explicit minion correspondence

Let M_Z be the minion whose n-ary elements are coefficient vectors

\[
(a_1,\ldots,a_n)\in\mathbb Z^n,\qquad \sum_i a_i=1.
\]

A minor aggregates coefficients along the variable-identification map: for pi:[n]->[m], the j-th coefficient is the sum of the a_i with pi(i)=j. Zero coefficients and dummy variables are allowed.

There is an exact correspondence, valid for every ternary target B, between homomorphisms h:Z_1 -> B and minion homomorphisms

\[
\xi:M_Z\longrightarrow\operatorname{Pol}(1\text{-in-}3,B).
\]

Given h, define

\[
\xi_h(a_1,\ldots,a_n)(x_1,\ldots,x_n)
=h\left(\sum_i a_i x_i\right),\qquad x_i\in\{0,1\}.
\]

This preserves the ternary relation: if three Boolean input rows have exactly one 1 in each column, their three integer weighted sums add to sum_i a_i=1. Applying h gives a tuple of B. Aggregating coefficients is exactly substitution of repeated variables, so xi_h preserves every minor.

Conversely, given xi, define

\[
h(t)=\xi(t,1-t)(1,0).
\]

For x+y+z=1, the ternary polymorphism g=xi(x,y,z) obeys

\[
g(1,0,0)=h(x),\qquad
g(0,1,0)=h(y),\qquad
g(0,0,1)=h(z),
\]

by grouping the distinguished coordinate into the first variable and the other two into the second. Applying g to the three Boolean 1-in-3 tuples gives (h(x),h(y),h(z)) in R^B. Thus h is a homomorphism.

Finally, for any Boolean input vector, group the coefficients belonging to its 1 entries into the first variable and the remaining coefficients into the second. Minor preservation then gives xi=xi_h. These constructions are inverse.

This is an elementary explicit form of the established integer-affine free-structure correspondence, not a separate novelty claim. Combined with the main theorem, it yields, under (DF),

\[
M_Z\longrightarrow\operatorname{Pol}(1\text{-in-}3,B)
\quad\Longleftrightarrow\quad
\exists a\ge0:\ 3^a\le |B|\text{ and }A_{3^a}\longrightarrow B.
\]

The finite algorithm therefore decides existence of this specified minion homomorphism and constructs one by a lookup rule when it exists. A negative answer rules out the integer-affine minion; it does not by itself rule out every possible tractability mechanism or prove NP-hardness.

## References

1. Tamio-Vesa Nakajima and Stanislav Živný. *On the complexity of symmetric vs. functional PCSPs*. ACM Transactions on Algorithms 20(4), Article 33 (2024). DOI: 10.1145/3673655. Problem 63 and Theorem 6. Author version:
   https://www.cs.ox.ac.uk/people/standa.zivny/publications/nz24talg-preprint.pdf

2. Iryna Banakh, Taras Banakh, Maria Kolinko, and Oleksandr (Alex) Ravsky. *Midconvex sets in Abelian groups*. Theorem 4 (equivalently, Theorem 2 with g = 1), [arXiv:2305.12128](https://arxiv.org/abs/2305.12128).
   https://arxiv.org/abs/2305.12128
   https://publications.lnu.edu.ua/bulletins/index.php/mmf/article/download/12099/12442

3. Andrei Krokhin and Danny Vagnozzi. *Approximating 1-In-3 SAT by Linearly Ordered Hypergraph 3-Colouring Is NP-Hard*. ICALP 2026. Background on the approximate 1-in-3 conjecture and integer-affine rounding:
   https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.184/LIPIcs.ICALP.2026.184.html

No Lean formalization is claimed. The result has been checked by explicit mathematical arguments and independent proof audits in this research session.
