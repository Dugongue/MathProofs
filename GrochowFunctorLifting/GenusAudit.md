# Independent audit of genus-two Frobenius-source epimorphisms

Status: mathematical audit passes for the exact stated sufficient source class. This is an informal independent review, not Lean verification or a novelty determination. The unrestricted published genus-two epimorphism question remains open.

## Sources actually read

Read every section of Genus.md and the inherited PriorGenus.md proof. In particular the latter explicitly proves that every prime-field-linear self-adjoint operator of the flat bimap is scalar multiplication by its local centroid ring. That stronger property, not just commutativity of the centroid, is the ingredient needed for epimorphism descent.

## Ring algorithm

The source remains exactly K[x_i]/(x_i^{p^{e_i}}), with no relaxation of the Frobenius complete-intersection promise. Every generator image lies independently in N_e. These are K-subspaces despite Frobenius semilinearity. Their head images are nested, and head spanning is equivalent to algebra generation by nilpotence plus the coefficient field. Thus the rank-only dynamic program has exactly q^a rank-preserving head choices and q^{u_i}-q^a increasing choices; the independent lift multiplier q^{sum(n_i-u_i)} is correct. Reachable states have a at most u_i, so there are no negative transition counts.

The compact-input bound is legitimate. Powers above the target nilpotence bound impose no further restriction, so the algorithm never expands a source ring of exponential dimension merely to count maps into a small target. Count bit length is at most r log |S|. Kernel calculations over the prime field and K-basis extraction use polynomial-size explicit target arithmetic.

## Recognition

The coefficient field in a finite commutative local characteristic-p ring is the unique q-th-root fixed field, where q is residue-field order. The derivative of X^q-X is minus one, so unique lifting is valid. An adapted head basis lifted through the N_e gives a surjective homomorphism from the proposed truncated algebra. Dimension equality proves it is an isomorphism. Conversely monomial Frobenius images are distinct when nonzero, so no nonlinear term can cancel a surviving powered variable in the head test. The recovered lengths are correct. The field case has an empty variable list.

For prime-field algebra epimorphisms, nilpotent variables add no residue elements, so source and target residue fields must be isomorphic. Their f field isomorphisms give disjoint maps with equal tuple counts.

## Genus transfer and exact counts

The inherited scalar-self-adjoint lemma makes multiplication descend along the input epimorphism to a unique unital ring map alpha. It then forces output semilinearity. The two output columns span the free rank-two target module and hence form an invertible matrix; pulling back by that matrix forces alpha onto. No ring-map overlap remains.

For each fixed alpha the pseudo-isometry input matrix preserves the free wedge-kernel line, equivalently its coordinate plane. Its exact form is [a 0; c D], with a a unit, c in S^2 and D invertible. The output matrix is forced to aD. Thus the factor |S^times| |S|^2 |GL_2(S)| is correct. Reduction of GL_2 to the residue field has kernel cardinality |J_S|^4. The central additions are all prime-field linear maps A^3 -> S^2, numbering p^{6as}; odd-characteristic half-bracket coordinates make this exact. All of these maps remain surjective because the quotient and derived maps are surjective.

## Raw table complexity

The centroid-dimension identities bound centroid-ring enumeration by a polynomial in the group table size before it is attempted. Searching |V|^3 triples is polynomial table time, and prime-field rank verifies free centroid bases. Together with vanishing b(v_2,v_3) and a free output pair, this is an exact flat-bimap recognition, by centroid bilinearity. Arbitrary local target radical length and socle dimension introduce no hidden enumeration beyond the explicit table bound.

## Formatting issue only

The version initially audited contains malformed LaTeX such as ldots, qquad, e_ige1, the set fragment sin J, and #operatorname; commas appear where products were intended. These are presentation errors, not mathematical counterexamples. The owner was notified to repair the displayed formulas before publication. No mathematical repair or weaker source promise is requested.
