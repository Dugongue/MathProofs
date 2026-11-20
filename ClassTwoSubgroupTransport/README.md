# Class-two subgroup transport

These reductions take finite Cayley tables with ordered actual subgroup marks and use an ordinary class-two group isomorphism decision oracle. They return a witness, exact transporter counts, and stabilizer generators within their stated scope.

- [Exponent-four groups](EXPONENT-FOUR-TRANSPORT.md) covers every tuple of up to three actual subgroups, including intersecting and nonnormal marks. It also covers any fixed number with simultaneous coordinate central intersections. Ordered-product square records detect linear relations among projections, and a separate overlap map detects the plane components for three marks.
- [Bounded-rank relations](BOUNDED-RANK-RELATIONS.md) covers any fixed number of marks with elementary abelian kernel and quotient when bounded-rank tensors generate the relation kernel. The hypothesis is recognizable in polynomial time for each fixed rank and mark count. A four-mark family shows that the required ranks can grow without bound.
- [Mixed exponents](MIXED-EXPONENT-TRANSPORT.md) gives polynomial-size queries for independent quotient images with relative purity and for one mark under the stated height and splitting conditions. It includes one arbitrary mark for any class-two $p$-group whose abelianization is killed by $p^2$, and for any class-two $2$-group whose derived subgroup is killed by two.
- [Discrepancy orbits](DISCREPANCY-ORBITS.md) gives a separate polynomial reduction when the relevant orbit has polynomial size and computes the exact count by an orbit index and a linear shift factor.

The reductions and their complexity bounds are written proofs. Two supporting linear statements have independent Lean and transitive-axiom checks. The attached Python replay checks an elementary common-central-intersection suite, 300,763 three-mark cases, and all 65,536 local discrepancy profiles for a four-mark instance. The four-mark test has 16,384 feasible profiles, and the rank-two relations distinguish exactly those profiles. The unrestricted mixed-exponent marked transporter remains open in this work.

## Reproduce

Run the Lean source in Lean 4.33.0 with the Mathlib revision in its receipt. Run the finite controls with Python 3.10 or later, using only the standard library.
