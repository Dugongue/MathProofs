# Even matching of independent tensor orbits reduces to ordinary TI

Work over the field with three elements. An input consists of two ordered lists, each of length m, of explicit three-tensors. Their indices are ordered. The comparison asks for a permutation π of even parity such that each source tensor T_i is ordinarily isomorphic to S_(π(i)). The component isomorphisms are independent. List length and tensor sizes are unbounded. Tensors can have one common format or can carry individual explicit format tags.

**Theorem.** This comparison and ordinary TI are equivalent under deterministic polynomial-time many-one reductions. In particular the upper reduction produces a single ordinary tensor pair, without first solving any ordinary comparisons. A reduction to one-sign TI also exists which preserves the actual permissible matching permutations on a labelled role.

## Represent matching without choosing a permutation

Use the split algebra D=F^m, with its primitive idempotents e_i given in the listed order. Form the three mode spaces by taking direct sums of the corresponding spaces of the list entries. Keep their D-actions, where e_i acts as projection onto the i-th summand. Include the diagonal sum tensor. In bilinear-map notation all products between input summands of different indices are zero, and a product within index i is exactly the output in its i-th summand. This can be written as one bounded-order tensor system including D multiplication and the three action maps. Its size is polynomial in the total input array length. Format tags, or the dimensions of the D-summands themselves, ensure comparisons between incompatible formats fail.

An algebra isomorphism on D must permute the primitive idempotents, and the three mode maps must take the corresponding input and output summands by that same permutation. Restriction of the diagonal tensor equation is precisely ordinary TI on that matched pair of entries. Conversely any matching and independent entrywise tensor transporters extend to a system transporter, with the corresponding permutation on D. Thus comparing the systems without a sign test represents any matching. The ordinary bounded-order system compiler turns this into a single ordinary comparison, denoted M below. Testing the determinant on D instead gives the even matching problem, because the map on D is a pure permutation in its specified frames. The signed compiler supplies the one-sign version. [Ordinary system compiler](https://arxiv.org/html/2306.03135v2#S4) · [Signed compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorDeterminantIntervals/SignedCompiler.md)

These systems have a fixed number of roles and maps. They can be written directly even where zero tensors or repeated tensor entries occur, because the D-actions identify all the summands regardless of their supports. If the lists have unequal lengths, a fixed negative instance suffices. When both lists are empty, use a fixed positive instance.

## Get the sign by a monotone formula of ordinary comparisons

Write M_ij for the ordinary comparison of T_i,S_j. Its verdict is a Boolean variable for this construction. Write Dup for the disjunction of ordinary comparisons T_i,T_(i') over i<i'. Thus Dup says there are two source entries in the same ordinary orbit.

On a positive M instance, a duplicate source pair lets any successful permutation be changed to one of the opposite sign by swapping those two source indices. This swap preserves matching because their ordinary orbits agree. For M true and Dup false, the matching permutation is unique. Indeed each source ordinary orbit occurs exactly once and must be matched to its unique target occurrence. The matrix of verdicts M_ij is then the permutation matrix. The following formulas will read its sign using only positive ordinary comparisons.

For each i<i' define

    E_(i,i') = OR over j<j' of (M_ij AND M_(i'j')),
    O_(i,i') = OR over j>j' of (M_ij AND M_(i'j')).

When the matching is unique, its entry images are distinct and exactly one formula is true. The odd-labelled formula is true exactly when the index pair is an inversion. Aggregate these pairs in a balanced binary tree. For a node with child formula pairs (E_1,O_1),(E_2,O_2), use

    E = (E_1 AND E_2) OR (O_1 AND O_2),
    O = (E_1 AND O_2) OR (O_1 AND E_2).

On complementary pairs this computes the parity of the combined inversion count. Empty inversion lists are even. At each level the size of the two expanded formulas together is at most twice the sum of the children's sizes, plus a constant. With a balanced tree on N=binom(m,2) leaves, depth O(log N) gives polynomial expansion. Every leaf pair above has size O(m²). Thus the final even formula Even has polynomial size even as a formula with no gate reuse.

The desired verdict is precisely

    M AND (Dup OR Even).

For M false it rejects. For a matching with repeats, swapping equal source orbits makes the verdict positive irrespective of Even. In the remaining case Even computes the parity of the unique permutation. All leaf comparisons are ordinary TI, including M. The formula uses only conjunction and disjunction, so the earlier monotone formula packing gives one ordinary TI comparison in polynomial time. [Polynomial-size monotone formula packing](https://github.com/Dugongue/MathProofs/blob/main/OneSignTensorComparison/Disjunction.md)

For completeness, the monotone packing used here can be implemented directly with the split label algebra construction. Use the disjoint union of named roles for AND. For binary OR, suppose the inputs compare X to Y and U to V, with matched signatures in each pair. Build a two-element list of paired systems on each side, with lists

    [(X,U),(Y,V)]   and   [(Y,U),(X,V)].

Each pair has separately tagged first and second systems. The identity matching tests X≅Y, while the transposition tests U≅V. In either case the other coordinates compare objects to themselves. An arbitrary list match chooses one of these two permutations. Use the D-actions for every component role and the diagonal copy of every mark, so the two-element list of systems is itself a typed system with the same fixed upper bound on tensor order. A mismatch of a leaf signature can first be replaced by a fixed negative pair of matching signatures. This construction composes on the system descriptions and calls the ordinary tensor-system compiler only once at the root. The formulas used here have depth O(log m) when the disjunctions are balanced. Each level grows total coordinate dimension, number of roles and number of marks by at most a constant factor times the sum of the child bounds. There are polynomially many leaves, hence everything at the root and its bounded-order dense tables have polynomial size.

The reverse reduction uses singleton lists, whose only index permutation is even. The proof establishes equivalence for all list lengths. It also covers the width-restricted case where a known label partition forces every entry to match inside its corresponding block, simply by including the colour sums in D, defining duplicates only within a matching colour, and omitting forbidden comparisons from the two inversion formulas. There is no need to enumerate permutations inside a wide block.

## Several parity constraints on the same relabelling

The same construction handles any fixed number k of sign conditions on possibly overlapping marked index sets, using one ordinary TI comparison. Give each index its membership pattern in the marked sets as a colour, together with any other required colour. Demand that the matching preserve colours. A colour belongs wholly to each of the marked sets or wholly to its complement. If cross-endpoint colour counts disagree, reject by a fixed negative instance. Otherwise write the colour blocks in the same fixed colour order on both endpoints. For each marked set, grouping its original ordered indices in this way changes the sign constraint by a known ordered-frame sign, computed from the two reorderings. After this calibration the parity on a marked set is the sum, in additive bits, of the within-colour parities on its included colours.

Let c be a colour and let u_c be the binary vector of its marked-set memberships. Use M for colour-preserving ordinary list equivalence. Conditional on M, the attainable parity of the permutation within c is either a single bit, when there are no same-orbit duplicates within that colour, or both bits, when there are such duplicates. For each parity bit b form the formula

    D_c OR P_(c,b),

where D_c is the source duplicate formula within colour c and P_(c,b) is its inversion parity formula. Conditional on M this is exact for each b. Thus the attainable contributions in the k sign coordinates from colour c are precisely the values b u_c for which the formula is true. Because entries of distinct colours use independent component transporters, these contributions may be chosen independently.

Combine the colour formulas in a balanced tree, with one formula per vector γ in the k-bit group. A node's formula for γ is the disjunction over α+β=γ of the conjunction of its children's formulas at α and β. This describes addition of the colour contribution sets exactly on one common matching. With k fixed, the polynomial formula-size estimate still holds. Conjoin M and the formula at the requested calibrated sign vector. Monotone packing again gives one ordinary comparison. Thus independent factor relabellings can enforce several simultaneous orientation bits without a signed oracle in this setting.
## Cost of using only unmodified pair queries

There is a nearly quadratic nonadaptive query bound in a separate opaque-comparison model. Suppose the only input-specific information read by an algorithm is the yes or no verdict of an unmodified pair T_i,S_j, and the unknown list match matrix is promised to be a permutation matrix. A nonadaptive algorithm distinguishing its even and odd cases must query at least

    m² − (m/2)(1+sqrt(4m−3))

distinct entries. Otherwise its graph of unqueried source-target pairs contains a four-cycle. The two opposite matchings on that four-cycle extend by the same permutation on all other rows and columns, so they yield opposite total parity and agree on every queried location. For the bound, if the unqueried column degrees are d_j and there is no four-cycle, then Σ_j binom(d_j,2)≤binom(m,2), since a pair of source indices appears in at most one unqueried column. Cauchy–Schwarz with q=Σ_j d_j gives q²/m−q≤m(m−1), hence the displayed limit on unqueried positions. The permutation promise is realized by actual lists of same-format tensors. Choose m tensors of distinct flattening ranks and let the target list permute those tensors.

This query bound concerns only reading unmodified pair verdicts as opaque bits. The one-instance reduction uses a constructed ordinary comparison, and does not conflict with that scope. The results are informal, and publication priority for the combination of list packing and the monotone sign computation remains unverified.

## Add a graph that constrains the shared permutation

Here is a related comparison where the duplicate-transposition proof no longer applies. The two lists are vertex decorations on two vertex-coloured graphs. An eligible matching must be a colour-preserving graph isomorphism of even permutation parity and transport each tensor decoration independently. This problem E_G has the raw many-one bounds

    ordinary TI ≤ E_G ≤ one-sign TI.

For the lower bound use two one-vertex graphs. For the upper bound use the split algebra D and the three D-action maps as above. On D include the adjacency operator in the basis of primitive idempotents and mark each colour sum of primitive idempotents. An algebra map on D already acts as a permutation. Intertwining the adjacency operator gives exactly graph isomorphism, and preserving the colour sums gives exactly the colour constraints. The determinant on D is the desired vertex parity. The one-sign tensor-system compiler supplies one raw tensor pair. If parity is only required on a marked union of colours, put that summand of D in a named role and include its embedding map.

E_G is polynomial-time Turing equivalent to ordinary TI. To see the upper bound, ignore parity and compile the displayed diagram to ordinary TI. Marking corresponding primitive idempotents adds a test for extension of any partial vertex matching, also in ordinary TI. On a positive instance, greedily extend a partial matching to find one graph-isomorphism permutation carrying the decorations. To compute the possible parity corrections, fix vertices of the source in their displayed order. At each point-stabilizer level, use the marked queries to find every possible image of the next vertex. For every such image, greedily extend to a full permutation fixing the earlier vertices. These choices give one representative for each coset of the next point stabilizer in the current point stabilizer, in the projected permutation group. Induction down the stabilizer chain shows the resulting polynomial-size list generates that group. The parity image is nontrivial exactly when some generator is odd. The initial transporter can therefore be chosen even precisely when its own bit is zero or one of the generators is odd. The same argument tests parity on a marked union of colours.

This is a candidate below one-sign TI with graph-coupled relabellings. A duplication among the decorations need not supply an odd graph automorphism. The reduction above leaves open a single ordinary comparison for this graph-constrained problem. The graph-free collapse and the polynomial Turing bound on the coupled problem are separate statements.
