# Four determinant results for multiplication tensors

For a unital associative multiplication tensor, a transporter $(X,Y,Z)$ in the bilinear-map convention induces an algebra isomorphism with determinant $\det X\det Y/\det Z$. This yields four applications of determinant ratios and orbit counts.

| Result | Main conclusion |
|---|---|
| [Tensor Isomorphism reduces to determinant-one correction](D.md) | The unrestricted reduction is uniform in the field size. Over each fixed odd finite field a second reduction supplies an ordinary transporter and can encode the answer as $q-1$ versus $(q-1)/2$ determinant-one orbits. The proof also gives an exact count for all acyclic path algebras and a sharp dimension bound. |
| [Exact finite étale descent](A.md) | For two nonisomorphic based finite étale algebras, the determinant-one extension spectrum is the full ordinary spectrum when their trace discriminants agree, and empty when they differ. The proof gives sharp first dimensions for prescribed collections of tests. |
| [Composition factors and modular group algebras](B.md) | The two unit determinant images of any finite algebra follow from its regular composition multiplicities. For every finite group algebra the images are both full. A socle identity controls the remaining determinant for finite $p$-groups. |
| [Pure-power complete intersections](C.md) | Coordinate scalings and permutations compute the exact determinant-one orbit count and give complete fingerprints within each ordinary orbit. The formula works in every characteristic. |

Each article contains a written proof and references. The Lean files independently check component statements used in the arguments. The [audit summary](Audit.json) binds those checks to source hashes and records the separate finite computational controls. Priority for the combined results remains open.
