# Independent Informal Mathematical Audits
November 4, 2026. Independent informal mathematics; not a Lean certificate.

Reviewed draft: graph-state-certificates/P-UPGRADE.txt.
This audit is independent of the worker's implementation and finite controls.
The selected target is exact physical product-unitary equivalence of arbitrary
qubit stabilizer codes with fixed qubit correspondence and any logical rank.

## 1. Physical factors and input cases

A physical coordinate projector preserving the binary stabilizer label space
S induces S=P S direct-sum (I-P)S. The unique signed Pauli lift of each label
then factors as well, since disjoint physical supports commute. Conversely
the Pauli expansion of a product density factors its binary label space.
Thus the finest physical partition is LU invariant. RREF respects every
disjoint-coordinate direct sum, so joining qubits occurring in an RREF row
recovers that partition. Identity, singleton pure and Bell factors are handled
explicitly; no unproved indecomposability oracle is used.

An alternative verification computes the F2 algebra of physical scalar
projectors a with P_a S contained in S. It is specified by linear constraints
and is closed under coordinatewise multiplication. Its coordinate-signature
atoms give exactly the same finest factor partition. The independent control
checks this alternative against RREF on all subspaces of F2^6.

## 2. Supplied axes have actually been removed

Greedy deletion really finds a support minimal among stabilizers nontrivial
at a chosen qubit: infeasibility of deleting a coordinate is monotone under
later support restriction. At that support the nonzero Pauli-axis correlation
matrices for distinct axes are orthogonal (equal remaining labels would make
two stabilizers anticommute). Their rank is 1 or 3, hence invariant under LU.
A rank-one site has a forced source/target axis pair. A rank-three minimal
support has exactly four stabilizers, all nonidentity elements full-support;
its size is even. The size-two case is a Bell factor. At larger size, pair
flattenings recover the three rank-one lines of a matched diagonal space,
forcing Clifford maps. This is the classical minimal-support theorem.

After deterministic source and target axis alignments, every actual LU can
therefore be taken diagonal on T and Clifford on W, up to final local Paulis.
The possible sign of a forced axis is removed by X on the target; that changes
only stabilizer signs, which the final Pauli correction legitimately restores.

## 3. Critical orbit-rank safeguard

The diagonal orbit must keep D=ker(X_T on S) fixed and modify only a complement
with independent X_T labels. Without this safeguard, a pure Z_T generator
could be changed to identity while satisfying phase equations on the original
support, falsely reducing stabilizer rank. The current draft includes the
safeguard, so a complement combination cannot collapse into D or into identity.

Conjugation by a diagonal product on T preserves each Pauli-fiber subspace
with fixed (X_T,W label); it acts invertibly within that subspace. Nonzero
fibers remain nonzero, proving invariance of K=projection deleting Z_T. Every
actual diagonal image thus has representatives with exactly the required
Z_T-only correction, with D unchanged. Conversely the generator phase equations
over the original computational support give actual stabilizers of the rotated
code. They force Hermiticity and commutation, and unchanged binary rank makes
the resulting code have exactly the original dimension. Containment is then
equality, including arbitrary logical freedom.

## 4. Exact compression and finite image

The unknown corrections are encoded as alpha=ell/2 (2-torsion) and phase
offsets beta=delta/4 (4-torsion). The equations are linear on a torus, with
integer coefficient rows whose dependence on y_T is affine and signed.
Translation of the affine support acts by commuting integer involutions.
The recurrence L<-L+T_b L therefore computes the exact INTEGER orbit lattice,
not its rational span. HNF updates in polynomial dimension have polynomial
bit bounds from the bounded original orbit rows.

SNF parametrizes the complete torus kernel. Its continuous free part has zero
projection to alpha: an integer multiple of a circle cannot lie in a finite
2-torsion subgroup unless its coefficient is zero. The finite torsion
generators therefore span the entire binary alpha-image Omega. Binary basis
selection retains rational phase preimages. No enumeration of codewords,
logical operations or exponential cyclotomic field is hidden here.

## 5. The decisive determinant-projection lemma

For arbitrary binary 2 by 2 W blocks Q_w, adjugation is linear and
Q Q#=Q# Q=E has scalar blocks det(Q_w) I. The T blocks are fixed identity.
The two-way D and K containments imply E preserves both source D and K.
Put P=I-E. This is the physical projector onto zero-determinant W blocks.

For s in S, preservation of K supplies u in S with pi(u)=P pi(s). Its X_T
vanishes, so u lies in D. Preservation of D implies P u in D contained in S.
At W its coordinates agree with P s; at T both are zero. Hence P u=P s.
Therefore P preserves S and physically splits it. On an indecomposable
component with T nonempty, P must be zero; all W determinants are one.

This lemma is valid without isotropy assumptions on S, and has been checked
independently on every subspace of F2^6 and every permitted T/projector pair.
The finite checks supplement the direct proof above.

## 6. Joint solution and signs

Because corrections occupy Z_T and Q acts identically there,
(G+Delta)Q=GQ+Delta. Membership in S' is linear jointly in Q and binary
correction coordinates. All extra D/K containments are linear too. Every
solution is invertible by the determinant lemma; its rank-preserving diagonal
image therefore maps onto S'. Conversely every true LU satisfies all these
conditions. There is no lost invertibility constraint or source-dependent
search group.

If T is empty, two-way S/S' containments imply the determinant-flag projector
preserves S. An indecomposable factor permits only uniform flags. Trying the
six invertible values of one anchor block forces all flags nonzero, providing
a complete polynomial Clifford test rather than exponential enumeration.

Signed groups with the same unsigned independent labels differ by a character.
The nondegenerate ambient symplectic pairing surjects onto the dual of that
label space, so a physical Pauli corrects every possible sign discrepancy.
It is obtained by binary linear algebra, not an assumed logical operation.

## 7. Complexity and present conclusion

All auxiliary groups are explicit binary spaces or integer lattices/tori with
polynomial dimension and polynomial-bit coefficients. HNF and SNF with
transformations are established polynomial-bit algorithms. Output is a product
of exact rational-turn one-qubit phases and finite Clifford/Pauli factors;
expanded algebraic-number fields are unnecessary.

No mathematical gap was found in this assembly under the fixed-label qubit
stabilizer-code contract. The other two independent worker reviews and the
full-algorithm controls have now passed, including a mixed T/W fixture,
the known 27-qubit phase-image test and a coupled 25-qubit k=2 fixture.
None of this establishes Lean verification or publication priority.

## 8. Binding and exact finite-grid implementation

The reviewed frozen core has SHA256
391e9e1c81289533f9bdd3edb3caad385a7ccd57f880806205df2e108175245d.
The separately reviewed modular addendum has SHA256
1ca76903867b3fd8114a6d3489ab5959d21ad17dc6fa097d4b9271d2645f9a33.

For each fixed feasible alpha,beta, the theta equations have bounded integer
coefficient rows and quarter-integer right sides. Cramer's bound gives a
common denominator at most 4 max(1,t^(t/2)), t=|T|. Multiplying theta by
an integer divisible by its odd denominator part and congruent to one
modulo four preserves those equations with alpha,beta fixed. The resulting
dyadic denominator divides 2^(2+t ceil(log2(t+1))). Thus the entire finite
correction image is exactly the image of the kernel over this explicit
power-of-two modulus, with no numerical precision assumption.

Minimum-valuation pivots over Z/(2^B) can be normalized by odd units and
cleared by row/column additions, retaining invertible transformations.
Each diagonal pivot p gives a kernel generator q/p in modular coordinates;
a free coordinate gives one. Projecting these generators recovers the
same complete alpha image. The argument has polynomial bit complexity
in the original tableau size. The root independently checked both this
coverage proof and the explicit modular elimination description.


INDEPENDENT PEER AUDIT: ARBITRARY-k QUBIT STABILIZER-CODE LU IN P
Reviewer: Independent AI reviewer 1. November 4, 2026.
Informal mathematical audit, not a Lean or publication-priority certificate.

AUDITED DOCUMENT
Reviewed component: `P-UPGRADE.txt`.
SHA256: 391e9e1c81289533f9bdd3edb3caad385a7ccd57f880806205df2e108175245d
Detailed supporting fixed-code diagonal argument also read in that folder's PROOF.txt.

RESULT
No mathematical gap found in the complete proposed deterministic polynomial-bit-time decision algorithm, within its stated scope: valid signed stabilizer tableaux, qubits, the same labelled physical qubits, arbitrary logical dimension, physical product-unitary equivalence. Exact output gates are specified by finite Clifford labels and rational turns, not expanded cyclotomic number fields. This is a positive audit of the complete assembly, not merely of its diagonal or supplied-axis subcases. The proposal remains informal and its novelty/priority requires separate investigation.

## 1. PHYSICAL FACTORIZATION
The RREF support-joining algorithm does give the finest physical direct-sum partition. A preexisting disjoint-coordinate decomposition makes RREF block-supported, regardless of column ordering; conversely the computed row-supported components explicitly span a direct sum. For normalized code density rho=2^-n sum_{g in S} g, partial traces retain exactly supported stabilizers. Uniqueness of Pauli coefficients proves that density factorization is equivalent to the unsigned direct sum. Signs then factor by the stabilizer multiplication law. Physical product unitaries preserve every labelled product cut, so comparing partitions and factor ranks is necessary, and independent factor processing is sufficient. Identity, one-qubit pure and Bell factors are explicitly removed.

## 2. UNSUPPLIED AXES / UNIVERSAL COVERAGE
The greedy support search is valid with one deletion pass: deleting other coordinates can only shrink the available stabilizer subgroup, so a failed deletion can never become feasible later. The chosen support is minimal for a nontrivial action at i. For each reduced density, the traceless-at-i flattening has rank 0, 1 or 3 according to binary axis rank 0, 1 or 2. Different Pauli axes cannot share a rest label in an abelian stabilizer; their rest coefficient vectors are therefore orthogonal and nonzero whenever present. This proves LU invariance of both the feasibility tests and the rank classification, for mixed codes too.

In the rank-one case every transporter maps the unique source Pauli axis to the target axis up to sign. In the rank-two case, representatives g,g' and gg' have full chosen support, so the three axes are distinct at every site. If h were nonzero with identity at i, select any nonzero coordinate j of h and choose among g,g',gg' the element matching h_j. Their product remains nontrivial at i but loses j, contradicting minimality. Thus the reduced stabilizer has exactly four elements. Commutation forces even support size; size two is a Bell factor. For size at least four, flattening any pair of sites versus the rest gives a three-dimensional matched diagonal-matrix space with exactly three rank-one lines. Product rotations permute those lines and hence Pauli axes at each selected site. This proves the required Clifford restriction. Applying the argument to each i genuinely covers all supported nonexceptional qubits.

The minus sign on a forced T axis introduces an anti-diagonal X times a diagonal gate. Keeping that X as a final Pauli is legitimate; unsigned labels are unchanged by Pauli conjugation. No supplied flags or existential Clifford guess remains hidden here.

## 3. FIXED D, FIXED K AND COMPLETE DIAGONAL ORBIT
For T-aligned diagonal operations, D=ker X_T is fixed elementwise, including its signs. The diagonal channel preserves each operator fiber indexed by (X_T,W-Pauli label). Each nonzero fiber remains nonzero because the channel is invertible on it. Thus K=pi(S), with Z_T deleted, is an exact invariant. This is true even when conjugated individual stabilizer generators are not globally Pauli operators: the argument concerns the full projector's Pauli fibers.

Matching target representatives in each K fiber gives exactly Z_T-supported corrections to the chosen independent-X_T complement. No correction to D is necessary. The phase equations depend only on y_T, so projecting the original affine support to T is exact.

Their sufficiency includes validity of the otherwise unknown corrected code. Adding the equation at y and y+x_i yields delta_i=x_i dot ell_i mod 2, hence Hermiticity. Comparing the two translations x_i,x_j yields x_i dot ell_j=x_j dot ell_i mod 2, hence commutation. Unchanged D commutes with the corrections because X_T(D)=0. Any nonzero complement combination has nonzero X_T, preventing rank loss, -I, or a new full-X-zero stabilizer. The signed Z-only subgroup and original affine support therefore remain unchanged. The generator equations then telescope through every basis translation and prove equality of the complete projectors. This is a sufficient construction, not a test assuming an unknown valid target code.

## 4. EXACT OMEGA COMPUTATION
The row action on (x_T times sign(y_T), -y_T, -1) is genuinely integer linear: the affine change in the middle block uses the retained final coordinate. It remains valid on arbitrary integer combinations, including HNF basis rows whose last entry is no longer -1. The commuting-involution recurrence generates the exact integer orbit lattice, rather than only its rational span. All original rows have bounded entries, so standard minor/Hermite bounds give polynomial retained bit sizes despite exponentially many potential orbit points.

The complete system is a homogeneous torus kernel with explicit 2 alpha=0 and 4 beta=0 rows. In Smith coordinates, a free column has alpha coordinates zero as INTEGERS, since twice each such coordinate is zero in M V. Thus the finite alpha image is generated completely by the finite Smith torsion generators. Each projected alpha coordinate is exactly 0 or 1/2. Binary row reduction, carrying rational theta/beta preimages by addition, gives all of Omega. The independent-X_T complement is essential for the validity proof and is retained.

## 5. THE DETERMINANT-PROJECTION LIFT
From DQ subset D' and D'Q# subset D, composition gives D E subset D. The analogous K equations give K E subset K. Over F2, the block adjugate is linear and E=Q Q# has scalar block det(Q_w) I. Hence P_B=I-E is exactly a physical projection onto the zero-determinant W vertices and preserves D and K.

The lift from these flags back to S is sound. For s in S, choose u in S with pi(u)=P_B pi(s). This is possible by K invariance. Its X_T is zero, so u lies in D. Since P_B preserves D, P_B u lies in S. Its W coordinates equal P_B s, and both vectors vanish on T, giving P_B u=P_B s. Thus P_B S subset S. Physical indecomposability and nonempty T exclude every nonempty possible B. Therefore EVERY solution of the linear flags has all W determinants equal to one; no determinant constraints were silently dropped.

For T empty, the direct bidirectional S equations make E preserve S. Indecomposability forces all determinant flags equal. Enumerating the six invertible blocks at one anchor forces that common flag to one. This is a constant number of affine linear systems, not exponentially many local Clifford assignments.

## 6. MAIN AFFINE SYSTEM, SIGNS AND RUNTIME
Because corrections occupy Z_T while Q acts identically on T, (G+Delta)Q=GQ+Delta exactly. There are no epsilon-times-Q products. The main inclusion and all four flags are therefore jointly linear over F2. Soundness follows from the valid diagonal preimage, determinant propagation, invertibility of Q and matching ranks. Completeness follows from the universal axis/Clifford form, exact Omega coverage and the actual inverse Q# on invertible blocks.

Any lifts of accepted GL2(F2) blocks to one-qubit Cliffords give a valid signed stabilizer image. Two valid signed groups with the same unsigned space differ by a binary character. Nondegeneracy of the ambient symplectic form gives a physical Pauli realizing every such character, so final sign repair is a polynomial binary solve. This also handles the earlier anti-diagonal T factors.

The input validation, finite exceptions, factorization, support search, HNF/SNF transforms, binary correction systems, local Clifford lifts and Pauli repair all use polynomially many polynomial-bit operations. Rational-turn witnesses are explicit exact symbolic gates; no claim of polynomial expanded cyclotomic degree is needed for decision or this output convention. The old fixed-code Cramer bound is a valid existential short-witness refinement; the main algorithm only needs its polynomial Smith-preimage bit bounds. Arbitrary k and arbitrary induced joint logical action do not enter an exponential enumeration.

## 7. INDEPENDENT EXHAUSTIVE CONTROL
An independently written inline Fraction-free binary control enumerated ALL 2,825 linear subspaces of F2^6, not merely isotropic stabilizer spaces. For all of them it checked:
- 22,600 physical-factorization cases: RREF support components agree exactly with every physical coordinate projection preserving S.
- 53,675 choices of nonempty T and disjoint B for the D/K lift.
- All 23,795 cases where P_B preserves both D and K also satisfy P_B S subset S.
Every assertion passed. Elapsed time 0.507 seconds. These are finite corroborations of Sections1 and5, not the universal proof or a full-algorithm test. The owner is separately implementing full algorithm controls.

## 8. SCOPE / NONCLAIMS
No qubit permutations are solved by this labelled algorithm. The result is not automatically a qudit/continuous-variable statement. No Lean/kernel evidence or publication priority follows from this audit. The audited SHA matters: subsequent changes require appropriate rechecking. Parent CODE-LU-POLYTIME-AUDIT.txt was not yet present when this review was written; this peer argument was developed directly from P-UPGRADE.txt and the earlier fixed-code proof, with the full-source task outline as context.


PUBLICATION ASSEMBLY NOTE
These informal audits reviewed the frozen algorithm component identified by
its original source hash. PROOF.md is a mechanical assembly of that argument,
its exact diagonal foundation and its modular addendum, with internal references
renamed and Markdown headings added. The published proof has a different byte
hash; no claim of kernel verification or byte identity to the component is made.
Three independent AI reviews found no mathematical gap. Human review, formal
verification and publication-priority assessment remain pending.
