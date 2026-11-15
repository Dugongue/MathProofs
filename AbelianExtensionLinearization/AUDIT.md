# Scope and checks for the abelian extension encoding

The manuscript gives an informal proof of polynomial-time simultaneous isomorphism of finite diagrams of abelian group extensions over supplied quotient isomorphisms. It is not a Lean certificate.

The main improvement over the earlier abelian-kernel lifting manuscript is an explicit reduction to one finite-module isomorphism instance. It simultaneously handles arbitrary specified arrows and marks, gives a polynomial bit bound for binary-encoded kernels, and recovers the full Cayley-table solution coset using marked searches instead of finite-ring unit groups.

The following issues were checked in the written argument:

- Composite annihilators. The common scalar is a unit because it acts invertibly on a separate cyclic anchor; it is not inferred to be a unit from its action on a cocycle.
- Reduction modulo the annihilator. The module is constructed directly with the cocycle in its action matrices. The action law and recovery formulas are proved explicitly, so no unproved preservation assertion about reduction of integral extension classes is required.
- Shared choices. All arrows are included in the same module-isomorphism instance and all quotient blocks use the same anchor.
- False positives. Every compiled module isomorphism normalizes to group isomorphisms with the prescribed quotient maps, and every group solution produces a compiled module isomorphism.
- Binary size. The generated ring is stored by additive generators and multiplication coordinates; neither its elements nor those of the compiled modules are enumerated.
- Search and counting. The finite-module algorithm supplies a witness. Exact counts in the table model follow from a point-stabilizer chain on original group elements.
- Remaining restriction. Unknown quotient isomorphisms are not solved by fixing quotient basis labels. A tower with unknown intermediate maps cannot be substituted for a diagram with prescribed quotient maps.

The reproducible script `check_small.py` compares module intertwiners against independently enumerated fiber-preserving group permutations. It reports 180 pair comparisons, 540 marked comparisons, 12 nonminimal-annihilator comparisons, and 31 diagram-loop controls. The pair sample contains 39 isomorphic pairs and 141 nonisomorphic pairs. Inputs include cyclic and noncyclic abelian kernels, nontrivial quotient actions, cyclic and noncyclic quotients, and composite annihilators. These finite controls do not implement the general polynomial-time module-isomorphism algorithm and do not prove the asymptotic theorem. The complete output is in `CHECKS.json`.

The diagram-loop controls check compatibility of the recovered group maps with supplied loops. They are not an exhaustive implementation of the generated-ring compiler for arbitrary diagrams. The latter is justified by the general proof.

The literature check confirms that Grochow–Qiao Open Problem 8.1 explicitly asks first for extending Theorem 6.11 to general abelian radicals and then, more ambitiously, for polynomial-time isomorphism of all such groups. Only the first request is answered here. Skresanov explicitly asks whether the quotient-generator restriction in his fixed-quotient lifting theorem can be removed; the one-vertex theorem answers that question. Classical augmentation-ideal translation, finite-module isomorphism, and stabilizer-chain recovery receive attribution in the proof. No claim is made that the translation functor or module-isomorphism algorithm originated here, or that the targeted search establishes publication priority.
