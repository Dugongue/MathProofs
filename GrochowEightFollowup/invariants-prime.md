# Symmetry-characterized graphs on a prime number of vertices

For every prime \(p\), the symmetry-characterized simple graphs of order \(p\), up to isomorphism and complementation, are exactly the following. At orders two and three the list is interpreted without duplicating equivalent types.

1. The empty graph.
2. The star \(K_{1,p-1}\).
3. The graph on \(\mathbb F_p\) joining \(x,y\) when \(y-x\) is a nonzero square, if \(p\equiv1\pmod4\).
4. The graph on \(\mathbb F_p\) joining \(x,y\) when \(y-x\) is a nonzero cube, if \(p\equiv1\pmod6\).

This yields deterministic polynomial-time recognition and promised isomorphism at prime orders, and proves that multiplicity obstructions distinguish the prime-order family up to complementation. These are prime-order answers to GP071, GP072, and GP070 respectively. The general-order problems remain open. [Grochow–Urisman, definition and Open Questions 1.8 and 1.9](https://arxiv.org/html/2606.26244v2#S1.SS3)

## Classification

A graph is symmetry-characterized when every graph invariant under its full automorphism group is isomorphic to it, its complement, the empty graph, or the complete graph. Write \(r\) for the number of full-automorphism orbits on unordered pairs. The [orbital criterion](invariants.md) says that the graph qualifies automatically for \(r\le2\) and never for \(r\ge4\). If \(r=3\), it qualifies exactly when all three single-orbit graphs are isomorphic. In that case every orbit has size \(\binom p2/3\).

First separate the intransitive cases. For three vertex orbits the three distinct cross-pair classes are all nonempty and internally disjoint. If \(r\le3\), this leaves no internal pairs, so the order would be three and all vertex orbits would be singletons. No simple graph on three vertices has trivial full automorphism group. Four or more vertex orbits give more than three cross classes. Suppose then that there are two vertex orbits \(A,B\) of respective sizes \(a,b\). If both sizes exceed one, the three types of pair, internal to \(A\), internal to \(B\), and across, are nonempty. The case \(r\le2\) is impossible. If \(r=3\), each type is a single orbit, and equality of the internal sizes forces \(a=b\). The cross size \(ab\) then exceeds either internal size, so the three orbital graphs cannot all be isomorphic. If \(A\) is a singleton, transitivity on \(B\) gives one cross orbit, whose graph is the star and has no isolated vertex. Every internal orbital graph has the vertex of \(A\) isolated, so \(r=3\) is again impossible for a characterized graph. With at most two orbits the only nontrivial union is the star or its complement. These intransitive cases do qualify because the star has symmetric leaves and two unordered pair orbits whenever \(p\ge3\).

Now assume a nontrivial graph is vertex-transitive. The automorphism group's order is divisible by \(p\), so it has a \(p\)-cycle. Label vertices by \(\mathbb F_p\) so this cycle is translation by one. Burnside's prime-degree theorem gives containment of the full group in the normalizer \(\operatorname{AGL}_1(p)\) of these translations, since a nonempty, noncomplete graph cannot have a doubly transitive automorphism group. Thus the graph is specified by a connection set \(D\subsetneq\mathbb F_p^\times\), with \(D=-D\), and its full group is
\[
 \mathbb F_p\rtimes H,\qquad H=\{a\in\mathbb F_p^\times:aD=D\}.
\]
As \(-1\in H\), the unordered pair orbitals correspond to the cosets of \(H\) in the multiplicative group. All their orbital graphs are isomorphic by rescaling. Therefore \(r=[\mathbb F_p^\times:H]\le3\) is necessary and sufficient. The index-one case is trivial. Index two means \(D\) is a single coset of the subgroup of squares, and index three means \(D\) is a single coset of the subgroup of cubes or its complement in \(\mathbb F_p^\times\). Conversely these connection sets have the claimed multiplier subgroup because setwise preservation of a single coset of a subgroup in an abelian group forces the multiplier to lie in that subgroup. The condition \(-1\in H\) gives \(p\equiv1\pmod4\) for squares and \(p\equiv1\pmod6\) for cubes. This proves the classification. [Burnside–Schur theorem](https://arxiv.org/abs/math/0310373)

## Algorithms and multiplicity obstructions

For recognition, check the trivial and star types directly. Otherwise use Muzychuk–Tinhofer's deterministic polynomial-time recognition algorithm for prime-order circulant graphs. It either reports failure or gives a cyclic vertex labeling. In the latter case recover the connection set and test each nonzero \(a\) for \(aD=D\). The classification says exactly when to accept. This is a uniform algorithm in the ordinary adjacency input model. For promised isomorphism, apply recognition to both inputs. If both pass, compare their types and vertex degrees. Each type consists of one class up to complementation, and the degree distinguishes the two classes whenever they differ. The square-residue case in its two cosets is self-complementary by rescaling. The trivial, star, and cube cases all either have different degrees under complementation or coincide in the small cases handled directly. This gives exact deterministic polynomial-time isomorphism even when only one input is promised symmetry-characterized. [Muzychuk–Tinhofer's recognition and labeling theorem](https://doi.org/10.37236/1363)

At the same prime order, the possible orders of the full automorphism group in the four complement types are respectively
\[
       p!,\qquad (p-1)!,\qquad p(p-1)/2,\qquad p(p-1)/3.
\]
The star type is distinct when \(p\ge3\), and its order is never divisible by \(p\). The nontrivial transitive orders are smaller than \(p!\) and differ when both exist. Therefore group order alone distinguishes the different noncomplementary classes. In particular their cycle indices differ, so Grochow–Urisman's multiplicity criterion proves the claim. These are paper proofs. [Cycle-index criterion for multiplicity obstructions](https://arxiv.org/html/2606.26244v2#S1.SS1)
