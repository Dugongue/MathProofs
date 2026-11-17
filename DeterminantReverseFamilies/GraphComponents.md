# Graph parity across arbitrarily many connected components

All reductions here are deterministic polynomial-time many-one reductions. Consider finite vertex-colored graphs, with a marked union of colors and a specified order on the marked set at each endpoint. The decision asks for a color-preserving graph isomorphism that is even on the marked set. Let L be the complete written length.

**Theorem.** Suppose every connected component meets each marked color in at most C log(2+L) vertices, for a fixed C. Then the parity question reduces to one ordinary graph isomorphism instance. The total size of a marked color and the number of connected components are unbounded. More generally the construction works with any polynomial-time compiler to ordinary GI for the two local parity values on each type of connected component. No matching or classification of components into isomorphism types is required as input or obtained through oracle calls.

The proof uses the earlier logarithmic color-class orientation graph for a local comparison. The main new issue is the parity of the unknown matching between components. Even-length marked blocks can have arbitrarily large multiplicity. They are handled without selecting a matching.

## Local queries and available sign changes

Let G_i and H_j be the ordered lists of connected components at the two endpoints. Choose the component order by any deterministic rule, for example first displayed vertex. Each component inherits the marked order from its graph. Calculate the signs of changing the two full marked orders into component-concatenated orders. Write η for their sum in binary parity bits.

Let E be the ordinary colored GI comparison of the full pair. For each pair of components let E_ij be the ordinary colored GI comparison and let E_ij^s be the local marked comparison of sign s∈{0,1}. The latter compiles to ordinary GI by the logarithmic-color hypothesis. Both local targets on different ranks or types simply compare with the inherited colors, which preserve the marks. If an ordinary component comparison changes order the parity is still measured in the chosen local frames. Empty lists behave as usual, and even and odd give the two possible bits.

There is an ordinary GI comparison D, formed by disjunction, that tests whether the source graph has an odd marked automorphism. Include the local odd self-comparison of every component. Also include ordinary isomorphism of every pair of distinct source components whose marked sizes are odd. A local odd automorphism extends by identity. For two isomorphic odd-marked components, exchange them using inverse witnesses. The two within-block signs cancel and the block transposition is odd. Conversely an arbitrary automorphism permutes components inside ordinary isomorphism classes. Choose a conceptual common marked frame for each class, identifying each component by an isomorphism to its representative. If there is no local odd automorphism, the within-component signs are determined by those frame shifts. They sum to zero for any global automorphism. If there are no repeated odd-marked types then the induced permutation of odd-marked component positions is also the identity. Even-marked blocks contribute no block-permutation parity. This proves the characterization of D.

## The local signs without a perfect matching computation

For each available option (i,j,s) create a binary unknown x_ijs that may be 1 only if the ordinary comparison E_ij^s holds. Require, over F₂,

    Σ_(j,s) x_ijs = 1 for every source component i,
    Σ_(i,s) x_ijs = 1 for every target component j,
    Σ_(i,j,s) s x_ijs = t.

Let L_t be the resulting feasibility question. It reduces to a single ordinary GI instance as follows. For a gate X≅Y, create a two-slot variable with a copy of X attached on one side and Y on the other. The slot vertices use one private color, while the attached graph vertices use a separate palette retaining their input colors. Attach each old graph vertex to its slot. Put the same rooted pair of slots on both endpoints. A slot swap is possible exactly when X≅Y. Redundant private nodes can be omitted, including for empty graphs. In every equation these two vertices encode the variable's reuse. Split long equations by prefix bits with always-positive gates. For each at most ternary equation create the small graph of satisfying assignment records with three ordered incidence roles, as in the earlier graph parity compiler. Preserving all equation gadgets is exactly translating the variables by a solution, since translation matches the even and prescribed right-hand-side assignment sets if and only if that equation holds. Both implication directions use the same private slot colors. This gives the indicated ordinary instance with polynomial size.

Suppose E is true and D is false. Every matched type has rigid local signs. In any such type choose a conceptual fixed reference and let a_i and b_j be the signs of some isomorphisms from it to the components. All available edges have s=a_i+b_j, independent of the matched isomorphism. In an odd-degree selection the last row therefore equals Σ_i a_i+Σ_j b_j. This is also the local contribution of any actual full matching. Conversely every actual matching yields a feasible odd-degree selection with that same bit. Consequently, in this branch L_t tests exactly the true local contribution, with no perfect matching computed.

## The sign of the component permutation

With E true and D false, the odd-marked components have pairwise distinct ordinary types on each endpoint, with the same types on the two endpoints. Thus there is a unique bijection between the lists of odd-marked components, determined by the E_ij. The sign of permuting all marked component blocks is the sign of this bijection. Indeed an adjacent exchange of two blocks of sizes m,n contributes mn modulo two. Only exchanges of two odd sizes survive.

For every ordered pair of odd-marked source indices i<k, build two positive formulas in ordinary GI atoms. The formula for inversion is the disjunction of E_ij∧E_kℓ over target odd indices j>ℓ. Its partner for noninversion uses j<ℓ. In the branch under consideration exactly one formula is true. Use balanced binary parity recursion on these pairs of formulas to obtain P_0 and P_1, for even and odd inversion parity. The zero parity of a sum of two bits is (00)∨(11), and the one parity is (01)∨(10). Treat an empty list as parity zero. The recursion has logarithmic depth, so positive formulas have polynomial size even when expanded as trees.

Ordinary GI comparisons are closed under conjunction via independent colors on a tagged disjoint union. For disjunction of G≅H and K≅L, compare the unordered collections of ordered pairs

    {(G,K),(H,L)}   and   {(G,L),(H,K)}.

The objects can be encoded with colored roots and ordered slot nodes. This disjunction is correct because the two matching possibilities test exactly one of the two original comparisons. It has constant overhead per operand occurrence. Balanced reduction of all disjunctions and conjunctions above, with depth O(log L), therefore gives a polynomial-size GI pair for each P_t. Final colors are removed by the ordinary color-to-GI reduction.

The final test is

    E AND ( D OR (P_0 AND L_η) OR (P_1 AND L_(1+η)) ).

If E fails there is no transporter. If E and D hold, every ordinary transporter can be corrected by an odd source automorphism. If E holds and D fails, the total parity is exactly the component permutation bit plus the local sign bit plus η. Thus the acceptance formula is exact on every input under the local compiler hypothesis. All formulas are finite graph constructions, without calls to an isomorphism oracle.

For example, take arbitrarily many copies of a nontrivial small colored graph in one common palette. The marked color may grow linearly in the total vertex count, and component sizes marked odd can produce genuine block transpositions. The construction also handles arbitrarily many pairwise different types, in which case the sign can depend on the unknown matching. The prior global width bound on a marked color is unnecessary for these inputs. A single connected graph with a large unresolved active color remains outside this theorem.

The optional-edge argument adapts the project's previous determinant assembly across tensor centroid blocks. Here the odd block sizes must be tracked because a permutation of their positions can itself change orientation. The local graph parity compiler and GI OR construction are included as a companion note. [Local graph parity](GraphParity.md)


## Simultaneous parity constraints and signed comparison problems

The component theorem also handles an arbitrary list of independent graph transports, including self-comparisons, with a fixed number r of binary parity equations. Each marked set in each slot remains a union of colors. For the entire list, the set of achievable r-bit left-hand sides is empty or an affine space. A prescribed right-hand side belongs to a nonempty affine space exactly when its value is achievable for every nonzero linear functional on those r bits. This uses linear separation in the quotient by the direction of the affine space. There are 2^r−1 tests and r is fixed. With r=0 use the ordinary conjunction.

For each linear functional put distinct palettes on the original graph slots and take their disjoint union. Inside a slot, add parities of the classes kept an odd number of times in the linear functional's combination. Reordering each original mark by color gives an explicitly computed constant, so this sum is a single marked-set parity on the disjoint union with a known bit shift. A tag by slot keeps all transporters independent and does not merge connected components. The component theorem gives a single ordinary GI query for each nonzero functional. The conjunction of that fixed list is one ordinary GI instance. Thus the projection tests preserve correlations among the r equations, even though the witnesses selected for separate projection tests can differ. In particular the bounded-local-color hypothesis suffices for the graph analogues of the full three-sign tests and their affine stabilizer corrections.
