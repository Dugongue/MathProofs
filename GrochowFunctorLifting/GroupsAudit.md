# Independent audit of complement-filtration epimorphism algorithms

Verdict: PASS for the exact stated sufficient results. The unrestricted two-prime, Abelian Sylow tower, and tame-tower questions are not closed. This review is informal mathematical verification, not Lean certification or a novelty determination.

Audited source revision: Groups.md, SHA256 783EFEA93699885883316C8D79B53C6F313CCDDF18B15A91E97268CC533A9829.

## 1. Fixed-action count and torsion-image flags

The condition alpha Theta_t contained in Gamma_t is both necessary and sufficient for a homomorphic complement lift: source cyclic generators can be lifted independently at their required orders. The head-column variations U_t are nested, and their uniform completion factors are correct.

The identification S_t/U_t with Gamma_t/Lambda_t is exact. Its well-definedness uses ell L intersect L[ell^t] = ell L[ell^{t+1}], and its kernel is precisely the head image of ker sigma at that torsion level. The quotients are elementary abelian.

The displayed d_t^- and d_t^+ formulas correctly remove the torsion contributed by higher-order cyclic source factors: those terms lie in ell K, and their images belong to ell L intersect L[ell^t], whose marks lie in Lambda_t. Within a fixed exponent block one may reorder ordinary cyclic generators to put projected pivots first. Their choices force rank increases; subsequent rank-preserving counts ell^{r-d_t^+} follow from the intersection with U_t. Thus the exact count depends only on the transported flag pair and the alpha-independent orders and variation dimensions. The claimed count bit bound is valid.

## 2. Orbit method and exact normalization

Coprime module quotient types can indeed be listed with at most |A| candidates before the abstract-type filter. Per simple type, size-at-most-e partitions are bounded by 2^e; multiplying these bounds stays below |A|. The faithful action semidirect products have sizes at most the original input groups.

The projected automorphism group U acts on the relevant flags. The smaller-orbit enumeration can be performed without knowing which side is smaller by alternating breadth-first searches. A representative source state gives alpha = u alpha_0. For the target-state formulation alpha = u inverse alpha_0 is the correct choice; simultaneous flag invariance then identifies its complement count. Fiber cardinalities are uniform by orbit-stabilizer.

The count formula includes the correct quotient-identification division by Aut_K(B'). Its complement normalization factors cancel because the action of L on B factors through D and B^L = B^D. Distinct K-module quotient types remain disjoint. The nonsplit shifted-exponent example has exactly the stated characteristic torsion-image flag, and its non-splitting argument is valid.

## 3. Code-subfamily signature algorithm

The weighted-matching recurrence has precisely 2^r 2^{ab} states, counts each permutation once, and has only polynomial additional arithmetic overhead. Each integer has at most log_2(r!) plus one bits. Consequently ab = O(r) gives polynomial time in the exponential-size Cayley-table model.

The large-orbit comparison is also correct. For sufficiently large r, dimension floor(sqrt r) permits r distinct nonzero columns containing a basis. Distinct columns make a code permutation determine at most one row transformation. Thus the stabilizer size is at most 2^{max(a,b)^2}, and both coordinate-permutation orbits can have size 2^{Omega(r log r)}. This does not imply a universal bound when ab is quadratic in r.

## 4. Matched-flag algorithm: primary-source hypotheses

The finite path algebra for a flag diagram has polynomially many cyclic additive generators and polynomial modulus bit length. Diagram modules are given by cyclic coordinates and inclusion maps. Its vertex idempotents force a module isomorphism to respect every node, so its terminal map is exactly a plain flag isomorphism. No enumeration of the exponentially large ring or the direct-sum module is needed in this compact input model.

This matches the primary module-isomorphism statement: Ciocanea-Teodorescu's theorem, also stated as Skresanov Proposition 4.1, accepts finite rings and modules given by cyclic generators and returns an explicit isomorphism in polynomial time.

The ring of flag-preserving endomorphisms is unital and closed under addition and multiplication. Its units are exactly the additive automorphisms preserving the whole flag, because an injective map of a finite subgroup into itself is onto. Its additive group is an ell-group and its cyclic-generator description is polynomial in the input coordinates. Skresanov Proposition 4.2 explicitly has complexity polynomial in log |R| and the largest prime dividing |R|. Here that prime is ell, at most the explicit group-table order. Therefore a huge ring cardinality does not create an exponential table-time cost.

Skresanov Proposition 3.9 has exactly the required representation-transport scope: a subgroup P of Aut(D) given by permutation generators, an abelian p-group B, and a p-prime group D acting on B. In this application D is an ell-group with ell different from p. Both representations are written on the same additive B after an explicit additive identification. Thus the coset computation applies to the full flag-preserving P, including its possibly large order.

For a fixed accepted action isomorphism alpha, choosing one intertwiner identifies all lower epimorphisms with the a_epi maps to B'. Therefore the Section 5 formula correctly counts action isomorphisms only. It needs no extra Aut_K(B') factor: varying intertwiners would produce that multiplicity and then cancel it. Restoring the selected image complement gives precisely |B|/|B^D|. The formula is exact.

## 5. Bounded deficit

Every subgroup of index ell^d in Gamma_t is the annihilator of a dual subgroup of order ell^d. Such a subgroup needs at most d generators. Enumerating d-tuples, filtering their generated order, and deduplicating annihilators therefore lists every candidate Gamma'_t in at most |Gamma_t|^d choices up to polynomial overhead. The case d = 0 gives the unique whole subgroup.

Multiplying these bounds over t gives N^{O(1+Delta)}. Chains are checked explicitly. The action-isomorphism coset method uses Gamma' for equality, while the actual complement count still uses the original Gamma. This is correct: Section 1 makes that count constant on each such transported source flag. Distinct Gamma' families are disjoint because each alpha determines exactly one image flag. No small-orbit assumption is needed.

## 6. Equal-order complements

When |K| = |L|, every complement epimorphism is an isomorphism and maps all torsion subgroups bijectively. Thus every relevant branch has matched flags, or is rejected.

The independent direct proof is also valid. The kernel of a group epimorphism lies in A, hence gives a K-invariant quotient type B'. An equivariant quotient A -> B' followed by any group isomorphism B' semidirect K -> H gives every epimorphism. Each fixed epimorphism has exactly Aut_K(B') identifications of its kernel quotient with B'. The displayed contribution a_epi times Iso divided by a_aut is therefore exact. Since the isomorphism need not preserve the selected complement, no additional complement multiplier belongs in this direct formula.

All constructed intermediate groups have order at most the original source or target order. The Babai-Qiao or Skresanov group-isomorphism/coset algorithm is polynomial on these Cayley-table inputs. Standard trivial-group cases are handled directly, without invoking a largest prime divisor for a zero endomorphism ring.

## 7. Scope and source record

The results are sufficient algorithmic advances for the exact families claimed; they do not resolve all of Open Question 3(4). Runtime statements are in the Cayley-table model. They must not be transferred to logarithmic compact group input without redoing the estimates, particularly the dependence on ell and explicit table permutations.

Primary statements directly checked:

- Skresanov, Proposition 3.9, representation-transporting automorphisms: https://arxiv.org/html/2605.26748v2#S3.SS2 .
- Skresanov, Propositions 4.1 and 4.2, compact finite-module isomorphism and unit generators: https://arxiv.org/html/2605.26748v2#S4 .
- Ciocanea-Teodorescu, The Module Isomorphism Problem for Finite Rings and Related Results: https://arxiv.org/abs/1512.08365 .

No mathematical repair to the audited frozen source is requested.
