# Nonadaptive determinant-profile assembly for intrinsic tensor summands

Informal mathematics over a fixed finite field $F$. Put $D=(F^\times)^3$, and let $N$ be the total number of summands in the two block lists. Suppose the tensor decompositions into concise indecomposable summands are supplied or computed, and ordinary transporters act precisely by compatible block matches and independent local transporters. The primitive centroid decomposition of a concise tensor has these properties. Support defects introduce independent free determinants on their nonzero complement modes and are handled after the supported calculation.

Assume a deterministic polynomial many-one reduction that takes two local tensors and a prescribed determinant triple and gives an ordinary TI test over $F$. Then the exact global determinant profile is computable using $O(N)$ nonadaptive ordinary TI calls, with polynomial total query size, without restrictions on the number of unknown ordinary types or their multiplicities. If the number of ordinary types in the combined lists is supplied, one ordinary TI instance tests any prescribed triple. Exact multiplicity quotas for every row also suffice for one instance. An object-wise local compiler gives another one-instance case based on a bounded number of orientation corrections, described below.

## 1. Count ordinary types with a linear-range monotone statistic

Order the combined list of summands as $1,\ldots,N$. Write $E_{ij}$ for ordinary equivalence of two local tensors, including same-side pairs. It is a positive OR of all local prescribed determinant tests. Treat dimension mismatches as false and diagonal entries as true. On this equivalence relation define
$$
 B_i=\bigvee_{j<i}E_{ij},\qquad R(E)=\sum_i B_i .
$$
Only the first member of each equivalence class contributes zero, so $R(E)$ is $N$ minus the number of ordinary types. Its range is at most $N$. The predicate $R(E)\ge r$ has a positive bounded-fanin circuit of depth $O(\log N)$: feed the $B_i$ to a logarithmic-depth sorting network and read the $r$-th Boolean output. A comparator on Boolean wires has AND and OR as its two outputs. [Ajtai–Komlós–Szemerédi, An $O(n\log n)$ sorting network](https://doi.org/10.1145/800061.808726)

For any indices $a,b$, define a new equivalence relation by merging their classes. Its entries have the positive expression
$$
 E^{a,b}_{ij}=E_{ij}\ \lor\ (E_{ia}\land E_{jb})\ \lor\ (E_{ib}\land E_{ja}).
$$
If $E_{ab}$ holds the relation is unchanged. Otherwise two classes merge, increasing the statistic by exactly one. Consequently when the rank value $r=R(E)$ is known, the negative equivalence literal $\neg E_{ab}$ has a positive implementation as
$$
 R(E^{a,b})\ \ge\ r+1 .
$$
In particular, if the exact number of classes is supplied, both polarities of all equivalence bits have positive logarithmic-depth simulations. It also suffices to give only the source number of classes if the computation conjoins an ordinary whole-tensor equivalence test: on that true branch the combined and source type counts agree.

A different sufficient input is a known exact multiplicity quota $c_a$ for the class of each block $a$ in the combined list. It is enough if a polynomially computable invariant of each block determines that quota, even if arbitrarily many ordinary isotypes have the same invariant. In that case $\neg E_{ab}$ is equivalent to $\sum_{j\ne b}E_{aj}\ge c_a$. Monotone sorting gives the same circuit size and depth. For example every ordinary class can have the same supplied multiplicity, with the groupings wholly unknown.

## 2. Read the exact transporter profile from both polarities of equivalence

Choose any order of the input blocks within each side. Give a source block $i$ its rank within its ordinary type by counting equivalent predecessors, and do the corresponding calculation for a target block $j$. They are canonical partners if $E_{ij}$ is true and these two ranks agree. Check that each block on both sides has a partner. This is equivalent to equal multiplicities of all ordinary types, and then the partner assignment $\pi$ is a unique bijection.

All these partner predicates have binary-fanin Boolean depth $O(\log N)$ from the $E$ literals. For an explicit count circuit, carry-save compression replaces three binary words by two in constant depth per stage, reducing $N$ summands to two in $O(\log N)$ stages. The words have $O(\log N)$ bits, and binary addition and equality can be completed by parallel prefix carry computation. For every Boolean gate, keep its positive and negative copies using De Morgan duals. This converts the Boolean depth bound to positive depth once both polarities of the elementary equivalence bits are available.

For each source block and each $d\in D$, OR over target indices $j$ the conjunction of its canonical partner flag and its local prescribed-$d$ test for $i\to j$. On the matching branch this gives exactly its possible determinants in the canonical partner. Multiply these constant-size tables using a balanced tree with positive OR–AND convolution in $D$. The product set does not change if a different ordinary matching is used, provided its block permutation sign is computed separately. Indeed within each type choose reference isomorphisms $f_i:A_i\to R_0$ and $g_j:B_j\to R_0$. A matching $\pi$ is realized there by $g_{\pi(i)}^{-1}f_i$. The product of its determinants equals $\prod_i\det f_i\prod_j(\det g_j)^{-1}$, independently of the matching. All other local maps yield its coset by the product of the local stabilizer determinant groups. Conjugation preserves those groups.

In each mode, the block permutation contributes the sign of the crossings of the coordinate intervals. Compute its inversion parity in the canonical matching by counting each pair $i<i'$ with $\pi(i)>\pi(i')$ for which both source blocks have odd dimension in that mode. The inversion predicates and parity have logarithmic depth with both polarities available. For each dimension parity vector $p$, a positive OR of same-side equivalence tests between distinct source blocks of that parity enables the sign triple $((-1)^{p_1},(-1)^{p_2},(-1)^{p_3})$. This is exact: switching the images of two equivalent blocks swaps intervals of equal lengths, leaves the pre-sign coset unchanged, and accounts for the determinant of a transposition on each mode. Every other matching differs by permutations within ordinary classes, which are generated by such transpositions. Multiply the canonical sign, enabled corrections, and coset, and use the known change of concatenated basis determinants. Support defect modes with nonzero complement permit arbitrary independently chosen determinant corrections.

The exact profile tests use only positive local prescribed determinant tests. All negation is confined to Boolean computations on ordinary equivalence. The supplied-rank or quota mechanism implements those negative literals. Thus any requested global determinant triple has a positive polynomial-size binary circuit of depth $O(\log L)$ over ordinary TI leaves, for dense input length $L$.

Such a circuit compiles to one ordinary TI pair. Ordered pairing implements AND. OR uses the equality of the unordered two-item multisets $\{(A,C),(B,D)\}=\{(A,D),(B,C)\}$, holding exactly if the type of $A$ equals that of $B$, or the type of $C$ equals that of $D$. Unfold into a logarithmic-depth term tree polynomial in $L$. Its tensor leaves and incidence relations can be represented as one fixed-signature typed system: tree nodes and role incidences are coordinate algebras with incidence maps, the tensor mode spaces are separately tagged leaf summands, and the tensor is the sum of the leaf tensors. A system isomorphism is exactly a term isomorphism carrying local tensor leaves to their mates, and conversely. The fixed-signature ordinary TI compiler finishes the reduction. This uses the MathProofs positive packing method and the ordered and unordered pairing construction of [Jenner, Köbler, McKenzie and Torán](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/completeiso.pdf). [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4.Thmtheorem1)

## 3. Remove the supplied statistic with one nonadaptive round

For each $0\le r\le N$, prepare all of the following queries before seeing any answer: the rank threshold $R(E)\ge r$, and the final global-profile test of Section 2 with $r$ substituted for the unknown rank. Prepare the latter for every requested determinant triple if the full profile is the output. Each prepared final profile circuit is a valid positive circuit even on a wrong rank guess, although its profile semantics are guaranteed only for the actual rank. The maximal true rank threshold gives $R(E)$. Read only the profile answers at that rank. Thus the reduction is deterministic and nonadaptive, with $O(N)$ ordinary TI queries because $|D|$ is fixed. All query lengths together are polynomial. The empty list is directly decidable.

Earlier packing counted all ordered pairs of equivalent summands, whose statistic has quadratic range. The rank statistic here is linear-range and uses class merging instead of single-edge deletion to dualize an equivalence bit. Binary search on the rank thresholds also gives a logarithmic-query adaptive version. The new nonadaptive algorithm leaves one-instance assembly for arbitrary unknown types without any side information unresolved.

## 4. One instance for sparse discrepancies with an object-wise local compiler

This section uses a stronger local interface. For each single block $A$ and charge $a\in D$, suppose one can compute an ordinary TI object $O(A,a)$ such that
$$
 O(A,a)\cong O(B,b)\quad\Longleftrightarrow\quad
 ba^{-1}\in\mathrm{DetIso}(A,B).
$$
The object on the left depends on $A,a$ alone. The definition allows any fixed-signature tensor system that compiles to such an ordinary object. Marking a local volume line and scaling its marked volume by $a$ has this interface when the auxiliary structures can be chosen per object and project to the actual block transporters. A many-one reduction that only takes the pair $(A,B)$ does not by itself provide these separate objects.

Let $H_0\le D$ be the product of the determinant images of the ordinary stabilizers of every source block. It accounts only for local maps, before adding block permutation signs. Choose independently computable baseline charges $r_i$ on source blocks and $s_j$ on target blocks, or take them all equal to one. Suppose that whenever an ordinary matching exists, one can choose a matching and local maps such that all but at most $k$ of the local determinants lie in $s_{\pi(i)}r_i^{-1}H_0$. Require $k$ to be a fixed constant, or that a computed set of $O(\log L)$ source indices contains every exceptional position for one such matching. Then one ordinary TI instance suffices for an exact global prescribed determinant test, with arbitrarily large buckets and no bound on the number of unknown ordinary isotypes.

For any subgroup $H\le D$ form the unordered object
$$
 O_H(A,a)=\{\,O(A,ah):h\in H\,\},
$$
as a multiset, keeping its multiplicities. The multiset equality $O_H(A,a)\cong O_H(B,b)$ holds precisely when $\mathrm{DetIso}(A,B)\cap ba^{-1}H\ne\varnothing$. In one direction local equality for the item $O(A,a)$ supplies a determinant in this coset. In the other direction a given determinant $ba^{-1}h_0$ supplies all item equalities with $h\mapsto h_0h$, which is a bijection of $H$.

Enumerate the constantly many subgroups $H\le D$, and require $H\subseteq H_0$ using positive local self-tests. Compute the Boolean membership table of $H_0$ by multiplying local self-profile tables in a balanced tree. Separately enumerate correction vectors $a_i$ of representatives of $D/H$, equal to the identity coset off at most $k$ indices or off the computed set. This enumeration is polynomial under the stated bounds. For a candidate, compare the two multisets
$$
 \{O_H(A_i,r_i a_i^{-1}):i\}
 \quad\hbox{and}\quad
 \{O_H(B_j,s_j):j\}.
$$
They are isomorphic exactly when there is a compatible bijection with a charge in $s_{\pi(i)}r_i^{-1}a_iH$ at each matched pair. The test compiles to one ordinary TI pair by the same label-algebra construction as above, now using permutable item tags in place of the term tree. Each label has independent tensor leaves, so the multiset condition is exact. A successful comparison yields a matching with pre-sign product in the coset
$$
 \left(\prod_j s_j\right)\left(\prod_i r_i^{-1}a_i\right)H.
$$
Since $H\subseteq H_0$, multiplying by $H_0$ gives exactly the available pre-sign determinant coset. Indeed the exhibited matching covers that entire coset by arbitrary local stabilizer corrections, and the reference argument in Section 2 shows that all other ordinary matchings have the same pre-sign coset. On a feasible input the promise ensures a successful enumerated comparison by taking $H=H_0$.

The possible block signs can be read from positive tests independently of the comparison. Sort all blocks by their common dimension parity vector, paying the known basis-change determinant, so signs between buckets are already included. Within each bucket the positive repeat predicate gives both signs whenever a repeated ordinary type occurs and a matching exists. Otherwise every partner is unique. For $i<i'$ use the positive OR over $j>j'$ of two compatible ordinary partner predicates to detect an inversion, and use $j<j'$ to detect a non-inversion. Both flags are exact when partners are unique. A balanced parity composition and the repeat predicate give all feasible signs. Since the pre-sign coset is independent of the matching, the sign choices can be multiplied with it. The compatibility tests are positive local queries, using either the pair-level local compiler or the OR over object-wise charges.

Convolve the sign tables, $H_0$, the known baseline, and the product of corrections, and impose the prescribed calibrated determinant. OR all successful candidate circuits and apply the logarithmic-depth positive packing. Everything uses one ordinary TI instance with the stated object-wise interface and discrepancy promise. If only the pair-level interface is available, the unrestricted $O(N)$-query theorem still applies. The methods do not give a one-instance solver for arbitrary unknown types without either the supplied statistic, the stated discrepancy promise, or another source of positive matching information.

The unconditional preprocessing to unpadded indecomposable multiplication tensors gives a separate assembly path when the local solver already covers the entire synthetic local class. This note treats determinant tests on the actual input summands and keeps their original local solver coverage.
