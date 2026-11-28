# Taylor operations and Postnikov spaces

These AI-assisted written proofs study pointed homotopy operations and H-space structures. A normalized operation restricts on the diagonal to the identity up to homotopy.

- [Two-stage characterization and local-to-global gluing](TwoStageAndGluing.md). For a simple two-stage CW complex with rational-vector-space lower homotopy group and arbitrary abelian upper homotopy group, a normalized Taylor operation exists exactly when the Postnikov invariant vanishes, equivalently when the space is an H-space. A factorial-resolution construction gives local splittings and an integral obstruction in every lower degree. Part III proves finite-prime H-space gluing for spaces whose higher homotopy groups are torsion supported on a fixed finite prime set. Corollary 6.1 explicitly invokes a local Taylor-to-H-space input.
- [Taylor operations on finite Postnikov pieces](FinitePostnikovTaylor.md). Every pointed connected CW complex of finite Postnikov height with finitely generated homotopy groups is an H-space if it admits a normalized Taylor operation. The argument combines the Gemini/Claude local cyclic-term argument, rational vanishing, and the finite-type gluing theorem.
- [Equal axes](EqualAxes.md). A normalized operation with equal axis maps yields an H-space, with no finiteness hypothesis.
- [Postnikov tower compactness](PostnikovCompactness.md). H-structures on all finite stages yield an H-structure on the limit when the specified relative cohomology groups are finite.
- [Finite-type local-to-global theorem](LC/LC_FullProof.md). Prime-local H-structures plus vanishing rational Postnikov invariants give an integral H-structure for simple spaces of finite Postnikov height with finitely generated homotopy groups.
- [Rational fundamental group](RationalFundamentalGroup.md), [Taylor obstructions](NoTaylorObstructions.md), and [examples from Pan’s construction](PanExamples.md) give the earlier proofs and supporting arguments.

The accompanying `python verify_arithmetic.py` replay agrees with the archived results for 2,600 local recurrences and 100 rational recurrences. The infinite and topological assertions are established by the written arguments. The manuscripts use LaTeX math delimiters.
