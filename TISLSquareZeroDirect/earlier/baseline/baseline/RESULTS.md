# Atlas of the strict special-linear tensor-isomorphism world

Let \(B\) be ordinary dense three-tensor isomorphism over \(\mathbb F_3\). Let \(A\) be the same problem with determinant one in each of its three modes. Write \(H\) for \(A\le_m^P B\), where the reduction is deterministic, polynomial-time, and many-one. Ordinary TI reduces in the other direction by adding unused mode lines. This atlas expands the strict-degree branch \(\neg H\), and tests it against results that already hold in both branches. The unrestricted strictness branch survives the tests below. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

## Strongest new conclusions

- **Ordinary TI compiles arbitrary-rank linear span programs on its own answers.** A true comparison permits a cyclic shift of a product of centrally indecomposable algebras. A false comparison pins that shift to zero. Linking shifts by explicitly represented additive maps solves a full linear system with one ordinary comparison, even when the tensor field and the coefficient ring have different characteristic. This yields arbitrary-rank aggregation of independent determinant profiles as soon as their atomic sign tests have ordinary compilers. It also captures a decoder with known superpolynomial monotone Boolean circuit complexity. [Proof](LinearSwitchCompiler.md)
- **Strictness survives in narrower algebraic families.** It persists in matrix spaces with a marked split symmetric or symplectic form, and in compact exponent-three groups with a marked extraspecial quotient. The determinant lives in the space of forms for the marked comparisons. A concrete cube-zero counterexample refutes odd-orthogonal-summand detection of signs when all scalar slices are singular. [Proof](AlgebraWorlds.md)
- **A sharper complexity separation.** The strict branch implies
  \[
  \mathrm P\subsetneq
  \mathrm{NP}\cap\mathrm{PZK}\cap\mathrm{coHVPZK}\cap \mathrm C_{=}\mathrm P\cap\mathrm{coC}_{=}\mathrm P .
  \]
  In the stronger nonuniform branch it also forces \(\mathrm{VP}_k\ne\mathrm{VNP}_k\) for every fixed finite arithmetic field. The uniform branch already yields a uniform lower bound for one explicit characteristic-zero transporter-count polynomial family. [Counting and search](ComplexityWorlds.md) · [Arithmetic circuits](ArithmeticCircuitWorlds.md)
- **A proved descent boundary.** Over \(\mathbb F_3\), once ordinary equivalence is available over the ground field, connected geometric ordinary stabilizers and the larger class with a normal Sylow two-subgroup in the component group have an exact power-of-two threshold for extension degrees. Every threshold occurs for full-support tensors with connected ordinary stabilizers and closed geometric signed orbits. Over arbitrary base fields, a separate exact norm compiler works for non-Galois cubics and for explicit towers with bounded step degree. [Proof](DescentAndNorms.md)

## I. Consequences of strictness alone

The following entries use \(\neg H\) and the unconditional comparisons cited in each group.

1. \(B<_m^P A\) is a strict degree comparison in both directions: null-padding gives \(B\le_m^P A\).
2. \(A\notin\mathrm P\), since an ordinary fixed YES and NO pair suffices after a polynomial-time decision of \(A\).
3. \(\mathrm P\subsetneq\mathrm{NP}\).
4. The separation already holds inside \(\mathrm{NP}\cap\mathrm{PZK}\), under perfect simulation with expected polynomial time.
5. The same language witnesses separation inside the intersection with \(\mathrm{coHVPZK}\); the complementary protocol exactly simulates an honest verifier.
6. The separating language lies in both the exact-zero and exact-nonzero GapP classes. This follows by considering the transporter count and the source-automorphism count minus the transporter count.
7. In quantum nonzero-acceptance terminology, the separating language can also be taken in \(\mathrm{NQP}\cap\mathrm{coNQP}\). This is an exact zero versus nonzero distinction.
8. No one-output bounded-error reduction with \(O(\log L)\) random bits suffices for input length \(L\). Enumerating and compiling majority would contradict strictness.
9. No polynomial list of ordinary comparisons with a uniformly constructible positive bounded-fan-in logarithmic-depth decoder suffices. AND/OR compilation produces a single comparison.
10. No polynomial list with a uniform polynomial-size monotone linear span decoder as in the new compiler suffices, including any decoder over a fixed prime coefficient field. This includes monotone linear decoders with superpolynomial monotone Boolean circuit complexity.
11. No deterministically computable list of polynomially many candidate witnesses can always contain a valid signed witness on every YES instance. A witness verifier would decide \(A\) directly.
12. No deterministic signed witness finder can use only \(O(\log L)\) adaptive binary oracle answers, even from an arbitrary decision language: enumerate all transcripts and verify the resulting candidates.
13. If complement TI is many-one reducible to TI, no \(O(\log L)\)-adaptive ordinary decision reduction suffices. Expand all transcripts, replace negative literals, and compile the balanced DNF.
14. Under that same complement hypothesis, no polynomial nonadaptive ordinary query list followed by deterministic logspace, parity-logspace, modular-logspace, or an exact polynomial-size branching-program path-count comparison gives signed decision. The statement also holds without complement closure for constructions with explicit complementary query pairs.
15. The concrete integer signed-transporter count polynomial does not have polynomial-time constructible polynomial-size constant-free arithmetic circuits. This follows by evaluating modulo enough small primes to detect a nonzero integer count.

[Former complexity proof and exact protocols](earlier/ComplexityWorlds.md) · [Counting audit](ComplexityWorlds.md) · [Linear decoders](LinearSwitchCompiler.md) · [Witness transcripts](OracleAndCharacteristic.md) · [Count polynomial](ArithmeticCircuitWorlds.md)

## II. Where the same strict degree reappears

The exact proofs in this group preserve the named comparison, input encoding, and reduction direction. Each signed-to-ordinary collapse mentioned here would imply \(H\).

16. It reappears in every fixed field \(\mathbb F_{3^r}\), because a reduction at any one such field reflects back to \(\mathbb F_3\).
17. The fixed extension degrees at which same-field equality holds are downward closed under divisibility. Under ternary strictness the set is empty.
18. For every fixed odd \(r\), a strict gap also survives if only the determinant norms to \(\mathbb F_3\) are constrained. The norm restricts to the identity on base-field signs when \(r\) is odd.
19. The one-mode determinant restriction is already sufficient to witness the gap. Weighted characters in the compiler recover the joint restrictions.
20. Arbitrary allowed subsets of the eight ternary sign patterns cannot admit a uniform ordinary compiler. Taking the singleton of all-positive signs would close \(H\).
21. One single-query compiler for arbitrary-rank affine restrictions on independent attainable profiles cannot exist for all ternary comparisons. Conversely, the new linear compiler makes this entire aggregation feasible if atomic collapse holds.
22. Strictness survives on explicit commutative scalar-residue local algebras with \(J^3=0\) and \(\operatorname{Ann}_J(J)=J^2\). The dimensions of the two layers satisfy the specified congruences modulo \(|F^\times|\).
23. It survives in marked symmetric matrix spaces under ambient isometry of a named split nondegenerate form, with determinant measured on the space of forms.
24. It survives in the unmarked split-regular symmetric class when orientation means the product of the ambient and forms-space determinants.
25. It survives in marked alternating matrix spaces containing a named nondegenerate alternating form, with determinant measured on the space of forms. Here the ambient symplectic isometry already has determinant one.
26. It survives for the unmarked alternating class admitting a nonsingular slice when orientation is the total determinant.
27. It survives for even versus ordinary isomorphism of compact special class-two exponent-three groups with an explicitly identified extraspecial quotient center.
28. It survives when only the central subgroup defining that extraspecial quotient is marked. Isomorphisms may change the scalar identification.
29. It survives in the unmarked compact class admitting such an extraspecial quotient under total orientation.
30. It survives for the full class of compact exponent-three groups of nilpotency class at most two; a free elementary-abelian direct factor, when present, is an orientation correction.
31. It survives for alternating versus symmetric permutation conjugacy of the regular images of the specified compact groups. Parity is calibrated in their compact additive frame, without expanding a Cayley table.
32. It survives for even versus ordinary isomorphism of the compact Alexander quandles in the earlier compiler. Translations do not change this parity.
33. It survives in the earlier dense unbounded-order determinant-norm comparison, in the uniform same-base problem.
34. It survives in the finite-state sign-policy problem and in the simultaneous semilinear norm problem of the earlier transfer, since each includes the one-comparison identity-sign test. Under \(H\) those variants have ordinary compilers.

[Field and cube-zero transfer](earlier/CubeZeroAndExtensions.md) · [Norm reflection](earlier/NormExtensionComparison.md) · [New algebra reductions](AlgebraWorlds.md) · [Regular group conjugacy](earlier/hypoworld/RegularGroupConjugacy.md) · [Quandles](earlier/hypoworld/LocalRingsAndQuandles.md) · [Norm and arity extensions](earlier/hypoworld/RESULTS.md)

## III. Distinct randomized, nonuniform and oracle branches

Let \(H_R\) be a bounded-error randomized polynomial-time many-one reduction and \(H_{\mathrm{adv}}\) a deterministic polynomial-size circuit many-one reduction. Always \(H\Rightarrow H_R\Rightarrow H_{\mathrm{adv}}\).

35. Strictness implies every finite external oracle preserves the gap: finite tables are hardcoded.
36. It implies every weakly 1-generic external oracle preserves the gap for these fixed languages. A clocked successful reduction is a closed condition with empty interior.
37. Under strictness the erasing oracles form a dense meager set, because storing \(A\) erases the gap and finite modifications preserve erasure.
38. Under strictness, every finite oracle prescription extends to a recursive preserving oracle by effective transcript diagonalization.
39. If \(H_R\) holds despite strictness, almost every fair independent oracle erases the gap even though every weakly 1-generic oracle preserves it.
40. If \(H_R\) fails, almost every fair independent oracle preserves the gap.
41. If \(H_{\mathrm{adv}}\) holds, some recursive tally oracle erases the gap by storing one canonical correct advice record per length.
42. If \(H_{\mathrm{adv}}\) fails, every sparse oracle preserves the gap, since its accessible table is polynomial advice.
43. Failure of \(H_{\mathrm{adv}}\) implies \(A\notin\mathrm{P/poly}\) and \(A\notin\mathrm{BPP}\). An ordinary fixed output again suffices after decision, now by circuits.
44. Failure of \(H_{\mathrm{adv}}\) rules out even nonuniform randomized polynomial-size ordinary transporter search with a uniform inverse-polynomial success guarantee per YES instance.
45. If \(H_R\) holds despite strictness, then for every \(J\in\mathrm E\) and every \(\eta>0\), infinitely many lengths \(n\) admit \(B\)-oracle circuits of size below \(2^{\eta n}\) for \(J\). The same conclusion holds with SAT oracle gates.
46. If \(H_R\) fails, then the polynomial-time uniform finite-field arithmetic collapse for verifier-count families fails over every fixed finite arithmetic field. Uniform collapse and randomized isolation would give \(\mathrm{NP}=\mathrm{RP}\) and hence \(H_R\).
47. If \(H_{\mathrm{adv}}\) fails then \(\mathrm{VP}_k\ne\mathrm{VNP}_k\) for every fixed finite arithmetic field \(k\), and \(\mathrm{VP}^0\ne\mathrm{VNP}^0\) in characteristic zero. The first proof uses randomized isolation and seed fixing, and the second evaluates the explicit integer count.
48. If \(P=RP\) in the strict world, there is no worst-case PPT ordinary witness search with verifiable inverse-polynomial success per YES instance. One-witness unblinding would yield signed decision in RP.
49. If \(P=BPP\) in the strict world, signed decision is outside BPP. The auxiliary-input orbit functions then have a recursive sequence of strongly inversion-hard indices.
50. If signed decision is outside \(\mathrm{BPP}^B\), the hard sequence can be chosen to consist entirely of pairs with ordinary transporters. The B oracle removes all ordinary-NO inputs from the decision contradiction.
51. If both MKTP and its complement reduce to ordinary TI, the randomized entropy route yields \(H_R\). If strictness also holds, this puts the two languages in the generic-oracle-versus-random-oracle case of Entry 39.
52. An all-length inverse-polynomial average decision lower bound under a fixed efficient signed-instance sampler yields a standard one-way function via a keyless orbit construction. Strictness alone gives worst-case, potentially inefficiently generated auxiliary indices.

[Oracle proofs](OracleAndCharacteristic.md) · [Randomness, counting and inversion](ComplexityWorlds.md) · [Arithmetic simulations](ArithmeticCircuitWorlds.md)

## IV. Positive and negative comparisons that hold in either world

These are independent checks on proposed contradictions. Each statement specifies which extra premise would actually connect it to \(H\).

53. One arbitrary ordinary transporter, returned after a hidden uniform source transformation, gives an exactly uniform ordinary transporter by undoing that transformation.
54. Consequently a signed witness can be sampled exactly on its YES promise with at most eight successful ordinary witness calls in expectation. Finite repetition gives a one-sided randomized search-to-search transfer.
55. Independent uniform stabilizer samples give an ordinary full generator list with exponentially small failure after polynomially many samples. Its completeness is probabilistic.
56. Given full coset and stabilizer generators, ordinary and signed full-coset search already have constant-query functional reductions to one another. Ordinary decision by itself does not supply those generators.
57. Both languages lie in \(\mathrm{NP}\cap\mathrm{PZK}\cap\mathrm{coHVPZK}\cap\mathrm C_{=}\mathrm P\cap\mathrm{coC}_{=}\mathrm P\); this upper bound is compatible with a strict degree gap.
58. For either tensor oracle, adaptive NP oracle computations are included in the exact-nonzero GapP class. Adaptive coNP oracle computations are included in the exact-zero class. The counting proof weights every guessed transcript and annihilates erroneous ones.
59. Both languages reduce randomly and nonadaptively to MKTP by the exactly flat orbit-swap entropy comparison. This common upper bound allows distinct deterministic many-one degrees.
60. Connected ordinary stabilizers support Shintani determinant norm transfer and therefore descend any prescribed signs from extension degrees coprime to their orders.
61. Disconnected ordinary stabilizers also suffice when the extension degree is coprime to the Frobenius action order on their component group or the relevant fixed component subgroup order. The latter case uses Schur–Zassenhaus.
62. A normal Sylow two-subgroup of the geometric ordinary component group suffices for odd-degree descent over \(\mathbb F_3\). All successful degrees, when there are any, are the multiples of one power of two.
63. In general the odd part of the least successful ternary extension degree divides the odd part of the Frobenius action order, and each of its primes divides the ordinary component group order. This assumes a rational ordinary transporter.
64. Every allowed power-of-two threshold occurs even when the geometric ordinary stabilizer is connected and the signed orbit is geometrically closed. The relevant signed stabilizer can still have disconnected determinant kernel.
65. Closed geometric signed orbits can coincide despite a superpolynomial first rational-equivalence degree. This rules out extension-compatible target transporters with only polynomially many geometric components.
66. Non-Galois cubic norms and norms along explicit bounded-step separable towers have one ordinary-TI compiler over the original field. This includes exact products and integer powers of such norms with the stated coefficient model.
67. For separable \(E/K\) and a base change \(L/K\) of coprime degree to \([E:K]\), norm membership descends. Transfer sends a newly attained norm \(c\) to \(c^{[L:K]}\).
68. Pointwise determinant correction for symmetric or alternating tuples over a fixed odd field is computable via the semisimple adjoint algebra, even with singular scalar slices.
69. When a symmetric tuple has an invertible scalar slice, an odd pointwise isometry exists exactly when the tuple has an odd-dimensional common orthogonal direct summand.
70. The explicit six-dimensional symmetric carrier over \(\mathbb F_3\) admits an odd pointwise isometry without any odd-dimensional orthogonal direct summand. Every scalar slice is singular. This refutes extending Entry 69 by using only a zero common radical.
71. Compact orientation in the indicated bimap models is decidable in polynomial time for output dimension \(O(\sqrt{\log L})\), by enumerating the output action and applying pointwise correction.
72. Forgetting the distinguished scalar form can turn a marked output-sign NO into an unmarked YES. The proof exhibits the missing scalar correction and explains why total orientation is used in the unmarked equivalences.
73. A field-uniform endpointwise exact unmarked cube-zero compiler that realizes an orientation-rigid character on nontrivial outputs needs dimension at least \(1+\lceil(|K|-1)/2\rceil\). The scalar grade action proves the bound. Two marked covectors allow a separate uniform construction with no such field-size padding, for the fixed-base problem.
74. Faithful transporter embeddings from ternary tensors into binary tensors require exponential side length already on matrix slices. Even projective target realizations keeping the source elementary abelian subgroup nontrivial have exponential side length. The binary degree equality therefore does not suffice through such embeddings.
75. Fixed ternary tensors exhibit a side-length-exponential lower bound in the specified opaque transporter query model while admitting a polynomial-time test from their written coefficients. This is a proved coexistence result on the same family.
76. A recursive external oracle can make the two fixed tensor languages equivalent in a world with \(\mathrm P^\Omega\subsetneq\mathrm{UP}^\Omega\cap\mathrm{coUP}^\Omega\cap\mathrm{SZK}^\Omega\). This tests a converse from class separation in that model.
77. An ordinary comparison can encode an undirected path of prescribed gain through edges labeled by TI instances, for an explicit finite gain group. The lift to the product vertex set and an incidence span program give the compiler.
78. The unrestricted-rank aggregation proof uses the affine coset property of attainable signs and the independence of the original transporters. A nonaffine allowed set already gives a spurious odd selection on two bits.

[Complexity and search](ComplexityWorlds.md) · [Arithmetic descent](DescentAndNorms.md) · [Earlier geometry obstruction](earlier/GeometryAndDescent.md) · [Algebra and explicit counterexamples](AlgebraWorlds.md) · [Cross-characteristic bounds](OracleAndCharacteristic.md) · [Opaque separation](earlier/FixedFieldOpaqueSeparation.md) · [Linear constraints](LinearSwitchCompiler.md)

## What would force a contradiction?

| Boundary tested | Sufficient theorem that would rule out strictness | Result of comparison |
| --- | --- | --- |
| Larger finite fields | Same-field equality over any one fixed characteristic-three field | Reflection proved. None of the available special cases proves the needed unrestricted equality. |
| Atomic sign in algebraic carriers | Remove forms-space orientation on all marked split-symmetric or all marked symplectic spaces, or remove total orientation on a specified compact group carrier | Exact equivalences proved. Pointwise tuple algorithms fix every output form; the unresolved variable forms-space action is absent from that algorithm. |
| Constraints on multiple comparisons | An ordinary compiler for each atomic value in the relevant determinant profiles | Arbitrary-rank aggregation proved independently. Optional cyclic shifts cannot create the missing signed predicate. |
| Descent | A full polynomial ordinary reduction for the geometric decision plus a full ordinary reduction for promised signed descent | Disconnected component phases occur with superpolynomial first extension degrees. Coprime norm transfer covers the stated stabilizers only. |
| Search and derandomization | Worst-case verifiable ordinary witness search in PPT together with \(P=RP\) | Uniform unblinding proved. The known opaque-model lower bound is about a weaker access model. |
| Binary field | A decision reduction through characteristic two with an independently proved back-transfer | Exact faithful transporter embeddings need exponential side length. This comparison does not constrain arbitrary decision maps. |
| Counting and proof complexity | Uniform arithmetic circuits for the explicit characteristic-zero signed witness count | The modular circuit evaluation argument is unconditional. A nonuniform circuit guarantee or a modulo-three count alone gives a weaker conclusion. |
| Relative norm solvers | A reduction of the whole signed problem to the exact norm models in the descent chapter | The norm models are solved for the specified presentations. An arbitrary varying forms-space action has no such proved decomposition. |

## Verification

The earlier cube-zero and extension reflection proof and all 110 lines of the previous complexity chapter were independently reviewed. The arithmetic descent audit identified the ordinary versus determinant-kernel connectedness distinction. The new linear compiler was independently challenged on the growing number of tensor constraints, and two polynomial packings with a fixed number of tensors are available. The finite controls test the switch action, normalized affine weights, coupled systems, and a sample of character orbits. Lean independently checked two additive-group lemmas used by the new compiler. The complete reductions and separation arguments are written proofs. [Verification record](Verification.json)
