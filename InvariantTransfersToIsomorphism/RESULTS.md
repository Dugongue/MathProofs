# Four isomorphism results from localized invariants

These are informal proofs. The four results use different parts of the early invariant work. Ley suggests replacing an object by a ternary incidence structure. Rune and Sigil separate phase gauge from actual permutation data. Ward and Trellis motivate keeping each constraint indexed until one joint transporter has been verified.

| Proof | Result |
| --- | --- |
| [Smooth cubic hypersurfaces](Geometry.md) | GI-hardness of smooth cubic hypersurface isomorphism in characteristic zero and in characteristic two. The characteristic-zero construction also gives GI-hardness for independent-mode tensor actions, including determinant one, on symmetric polarizations with scalar pair adjoints. It computes the exact transporter signs and realizes every finite group as the full geometric automorphism group of a smooth cubic over the rationals. |
| [Parallel group cores](Group.md) | Deterministic uniform NC computes cores and hypercenters in arbitrary permutation-group quotients. It also computes full normal-closure chains in solvable quotients. Each upper-central membership test is in NC for arbitrary quotients, and the algorithm gives subgroup generators when the Sylow subgroups are all metabelian. |
| [Determinant-one monomial transport](Determinant.md) | A deterministic polynomial GI-oracle algorithm uniform in the finite field size. The support module has a checkable local relation-generation condition, or a compatible rational pseudoinverse. Determinant classes are computed directly from the input coefficients, using field powering and small-prime arithmetic. |
| [Butson and cyclic gain equivalence](Phase.md) | An exact direct $n^{O(\log n)}\operatorname{poly}(\log m)$ bit-time algorithm for extended Butson equivalence in the binary phase model. For connected bounded-degree cyclic gain graphs, switching equivalence with one shared unit is in deterministic polynomial time for arbitrary binary moduli. |

The group proof uses the earlier [parallel quotient centralizer](QuotientCenterDependency.md) and [lower central series](ParallelGroups.md) proofs. The latter two files are included as dependencies. Babai–Luks–Seress's question about generating every intermediate upper-central term on arbitrary nilpotent permutation inputs remains open here. The determinant result assumes monomial actions in the specified bases. It does not settle unrestricted special-linear tensor isomorphism.

Exact computational controls checked 480 determinant comparisons by enumerating small diagonal and permutation lifts. The phase tests checked 11,248 normalization and prime-power lifting identities. These are controls for the informal proof arguments. Publication priority remains unverified.
