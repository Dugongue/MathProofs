# Strict ternary tensor isomorphism atlas

Let \(A=\mathrm{TI}_{\mathrm{SL}}(\mathbb F_3)\), \(B=\mathrm{TI}(\mathbb F_3)\) and \(H=(A\le_m^{\mathrm P}B)\) for dense, ordered three-tensors with independent mode actions. The reverse reduction is unconditional by unused-line padding. The strict world means \(\neg H\).

The atlas has **520 technical entries**, including 219 additions. The unrelativized deterministic polynomial-time comparison remains open. [Previous 301-entry atlas](prior/RESULTS.md) · [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)

| Chapter | Added entries | Main result |
| --- | ---: | --- |
| Quotient volumes and probe families | 60 | Compile an ambient determinant from the Pfaffian or determinant of each probe quotient and the top lines of its actual radicals. This works for polynomial-size unordered families, moving projective lines, and locally logarithmic widths. An oriented-boundary test can complete missing sign measurements. |
| Algebra and group models | 52 | Socle-supported residue tensors carry the exact determinant profile in mixed characteristic. This gives a sign-preserving encoding over \(\mathbb Z/9\), as well as compact conjugacy transfers and exact matrix determinant stabilizers. |
| Arithmetic, geometry and descent | 52 | Signed TI over variable finite ternary extensions and polynomial quotients reduces to ordinary free TI over \(\mathbb F_3[t]\). A separate rational \(4\times4\times4\) example has exactly eight signed classes in one local genus within its rational ordinary orbit. |
| Complexity and proof systems | 55 | One directional sign difference on ordinary-positive inputs suffices for full signed TI. Complementary ordinary queries also support positivity of signed weighted branching programs in a single ordinary output. |

[Quotient volumes and boundary compilation](Volumes.md) · [Algebra](Algebra.md) · [Arithmetic](Arithmetic.md) · [Complexity](Complexity.md)

## What changes in the strict branch

- **A specific promise becomes hard.** On ordinary-isomorphic pairs, ask whether reflecting only the first target mode turns a signed NO into a signed YES. Applying this one promise test to reflections and mode permutations labels the boundary of the eight-point sign cube. A polynomial promise algorithm would collapse the full problem even if it behaves arbitrarily on ordinary-NO inputs. With additional quotient measurements, analogous results hold for specified multi-mode directions. [Directional proof](Complexity.md#c40-one-fixed-directional-difference-captures-a-hard-promise-under-strictness) · [Quotient refinement](Volumes.md#v55-a-subgroup-boundary-compiler)
- **Two back-transfers would contradict strictness.** An ordinary-to-ordinary reduction back from the explicit \(\mathbb F_3[t]\) or free integral image family would finish the full ternary reduction. A new algebraic equivalence says that deciding full determinant-one comparison by ordinary comparison on the socle-supported \(\mathbb Z/9\) input family is exactly as strong as \(H\). In the same mixed-characteristic family the principal-unit factors alone are always freely correctable. [Function-ring bridge](Arithmetic.md#a02-uniform-transfer-from-all-explicitly-represented-ternary-extensions) · [Mixed-characteristic profile](Algebra.md#a02-the-entire-socle-determinant-profile-is-a-pullback) · [Earlier integral bridge](prior/DescentWorlds.md)
- **The weakest incompatible branches are often conjunctions.** The model enumerator identifies 10 inclusion-minimal incompatible pairs and three triples among positive named premises, under the listed rules. Examples include \(\mathrm P=\mathrm{RP}\) together with \(\mathrm{MCSP}\in\mathrm P\), \(\mathrm P=\mathrm{ZPP}\) together with \(\mathrm{MKTP}\in\mathrm P\), and complementary ordinary TI together with a uniform PL decoder for signed TI. The bounded-error one-output reduction is excluded if ordinary TI is in P and P=BPP. [Full comparison table and proof paths](Worlds.md)
- **Classical conjectures can affect an auxiliary step without deciding the ternary reduction.** GRH supplies specific arithmetic or interactive bounds and does not by itself supply the missing polynomial map. A positive or negative answer to rational Hilbert's tenth problem addresses a different computational task. The Hasse counterexample is a direct theorem over \(\mathbb Q\) and is valid in both ternary worlds. The classical and Weak ETH branches are treated separately and the posted ETH result is shown as a separate literature scope. [Arithmetic worlds](Arithmetic.md) · [Classical and Weak ETH comparisons](Complexity.md) · [Machine-readable branch counts](WorldCounts.json)

## Joint hypotheses

Across the new chapters, **130 entries present paired cases**. The joint comparison uses **48 Boolean axes and 40 proved implication rules**. It tests every assignment symbolically, records both branches of each axis, and extracts explicit rule chains for short incompatible conjunctions. It retains **26,286,336** assignments with strictness under those rules, or **547,632** when omitting the arithmetic axes. These counts measure the encoded implications. They do not assert consistency or logical independence for the mathematical conjectures.

[All premise comparisons and minimal conflicts](Worlds.md) · [Rules](world_rules.json) · [Verifier](world_count.py) · [Exact counts](WorldCounts.json)

## Verification

The reduction and comparison proofs are written proofs. Lean independently verifies the covariance and dual-projective-normalization identities used in the quotient-volume compiler. Tests over \(\mathbb F_3,\mathbb F_5,\mathbb F_7\) check rectangular, alternating and symmetric calibrations. The logical model counter has an independent brute-force check on a smaller projection and checks both branches of every individual axis against Horn propagation. [Verification and source hashes](Verification.json) · [Lean source](QuotientVolumes.lean) · [Finite controls](volume_controls.py)
