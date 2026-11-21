# From graph-edit profiles to symmetric separating circuits

## Literature and the bridge

Grochow and Urisman relate the size of square-symmetric separating circuits to Weisfeiler–Leman (WL). Their reconstruction results characterize full edge and vertex decks using degree or support-degree cutoffs. The question here is different: given a deck whose cards are represented only by prescribed motif statistics, what WL width suffices to retain the **entire multiset of joint responses**? Representing each card by selected statistics lets the bound depend on pattern treewidth and the number of edited vertices, even when the host is large. [Grochow and Urisman, §§5 and 7](https://arxiv.org/html/2606.26244v2)

- **Motif counting.** Curticapean, Dell and Marx express subgraph and induced-subgraph counts in the homomorphism basis and relate computational complexity to the treewidth of the support. For an injective or induced motif coordinate, use the maximum treewidth of the graphs actually needed in its homomorphism expansion. Even a matching has easy detection and hard parameterized exact counting. The width in the theorem below belongs to homomorphism patterns, so the original treewidth of an injective pattern cannot be substituted without justifying the expansion. [Homomorphisms Are a Good Basis for Counting Small Subgraphs](https://arxiv.org/abs/1705.01595), [Curticapean and Marx on the vertex-cover dichotomy](https://arxiv.org/abs/1407.2929)
- **Detection and enumeration.** Color-coding uses random colors to isolate injective copies and admits deterministic perfect-hash derandomization. Its success for finding bounded-treewidth patterns does not turn a colorful count into the exact uncolored count for one arbitrary coloring. This is a useful distinction when choosing a fast proposal heuristic and then certifying the actual edit score. [Alon, Yuster and Zwick](https://doi.org/10.1145/195058.195179)
- **Refinement.** Dell, Grohe and Rattan show that equality of homomorphism counts from all patterns of treewidth at most k is equivalent to indistinguishability by k-WL. Homomorphism counting is the route from pattern-level edit operations to an exact bound on a graph-isomorphism filter. [Lovász Meets Weisfeiler and Leman, Theorem 2](https://arxiv.org/html/1802.08876)
- **Learning on graph decks.** Frasca, Bevilacqua, Bronstein and Maron bound a family of subgraph GNNs using 3-WL, with node marking and deletion among their policies. Bounded WL expressivity of subgraph methods therefore precedes this work. The transfer below concerns arbitrary prescribed joint homomorphism coordinates, ordered edits at several vertices, guarded edit eligibility, and an exact coefficient encoding. Its proof expands graph homomorphisms explicitly. [Understanding and Extending Subgraph GNNs by Rethinking Their Symmetries](https://arxiv.org/abs/2206.11140)
- **Graph edit heuristics.** The Delta-DRESS preprint applies a continuous refinement to each vertex-deleted card and tests the resulting fingerprints empirically. Here the card features are exact homomorphism counts. The theorem bounds their joint information for all host pairs at the stated WL width, independently of any test corpus. [DRESS: A Continuous Framework for Structural Graph Refinement](https://arxiv.org/abs/2602.20833)
- **Circuit bounds.** Dawar, Pago and Seppelt characterize polynomial-size matrix-symmetric circuits using bounded-treewidth homomorphism polynomials. The construction below gives an explicit square-symmetric compilation for the edit deck. It also gives the WL width directly, without deriving a coefficient-dependent width from a generic circuit support theorem. [Symmetric Algebraic Circuits and Homomorphism Polynomials](https://arxiv.org/html/2502.06740v2)

## The edit-deck theorem

Fix integers r ≥ 0 and t ≥ 1 and choose a finite list of edit rules. An edit rule takes an ordered injective r-tuple a of vertices of a finite simple graph G. Its eligibility may be any Boolean function of the original adjacency bits among those r vertices. The rule may delete specified vertices of the tuple and set, clear, or flip specified edges whose endpoints are retained tuple vertices. Its edit choices may depend on the original adjacency bits among the tuple. All other vertices and edges survive. Rules may also use ordered labels as part of their output type.

For a fixed finite collection of integer linear combinations of homomorphism counts of graphs of treewidth at most t, record the resulting score vector of each eligible edited card. For several rules on the same tuple, form a joint vector, with a flag and zero scores for an ineligible rule. Take the multiset as the ordered tuple varies. If two n-vertex graphs are indistinguishable by (t + r)-WL, they have identical multisets. In particular, a difference in exact edit profiles certifies nonisomorphism and is detected by (t + r)-WL. This includes the distribution of motif damage, any threshold on a joint score, and the optimal or worst score after an eligible edit.

For a fixed list of graphs and edit rules over the rationals, the multiset has a complete invariant encoding with a square-symmetric arithmetic circuit of size

$$
O\!\left(n^{r+t+1}+n^{2r}\right).
$$

Constants may depend on the rules and patterns. Circuit size counts gates and wires with unbounded fan-in symmetric sums. The multiset itself can also be computed by enumerating the tuples and running tree-decomposition dynamic programming for each edited graph. The arithmetic bound for that algorithm is O(n^{r+t+1}) for the fixed list, before comparison or sorting of score vectors.

### Proof

Write A for the Boolean adjacency matrix of G and label r anchors by their positions in a. Fix an original anchor adjacency pattern σ. The indicator that a realizes σ is the product of A(a_i,a_j) or 1 − A(a_i,a_j) for each anchor pair, with the choice determined by σ. For this σ the rule has a fixed set of deleted vertices and a fixed edge update at each edited pair. Sum over the possible σ to implement a guard or a data-dependent rule.

For one pattern F, write its homomorphism count after the edit as a sum over maps φ from V(F) into V(G). For each vertex u multiply by

$$
1-\sum_{i\text{ deleted}}[\phi(u)=a_i].
$$

For each pattern edge uv start with A(φ(u),φ(v)). For every edited anchor pair ij, add two correction terms, one for each orientation. They have the form

$$
[\phi(u)=a_i][\phi(v)=a_j]\bigl(b_{ij}+c_{ij}A(a_i,a_j)\bigr).
$$

Here the updated adjacency at that pair is b_ij + (1+c_ij) A(a_i,a_j). Setting, clearing and flipping use (1,−1), (0,−1) and (1,−2), respectively. Original tuple injectivity ensures that at most one oriented correction is active per pattern edge. Eligibility flags themselves require only anchor adjacency factors.

Expand the product. Each summand is a constant times a graph count with some pattern vertices pinned to specified anchors, together with some anchor–anchor edges. Incompatible pins give zero. For a monomial in several score coordinates, start with disjoint copies of the pattern graphs and share the r anchors among all copies. Add the anchors to every bag of each starting tree decomposition, and add a central bag with just the anchors. After substituting anchors for pinned vertices, this is a decomposition of width at most t + r. Anchor edges occur in the central bag. Vertices pinned to the same anchor can be merged because that anchor is already in every bag. Parallel edges collapse on Boolean adjacency inputs. Loops give zero. The central bag also covers the case of a constant monomial.

Now sum over injective anchor images. Inclusion–exclusion over the equalities a_i = a_j expresses this as an integer linear combination of unpinned graph homomorphism counts: an equality identifies the two anchors in all bags. Identifications preserve the same width bound, because every anchor already occurs in every bag. Thus **every mixed power sum** of the deck entries is a finite integer linear combination of ordinary homomorphism counts of width at most t + r. By Dell–Grohe–Rattan these moments agree on the two hosts.

To recover the multiset for a fixed finite panel, choose a common n-dependent bound L on the absolute scores. Shift by L and pack the score and flag coordinates into a single integer z in base B > 2L + 1. This is an injective encoding on the allowed range. For M = n(n−1)···(n−r+1), the power sums of z of orders 1 through M agree, since each is a linear combination of mixed moments. Over the rationals, Newton identities give every coefficient of ∏(T−z), with one factor per tuple. Equality of the polynomials gives equality of roots with multiplicity and decodes the joint distribution. When n < r both multisets are empty. The same WL implication holds for the full vector of all width-t homomorphism counts, because a finite restriction distinguishes the finitely many different vectors appearing across any two fixed decks.

For the circuit, instantiate a copy of the tree-decomposition recurrence for each ordered injective tuple, using the guarded updated edge and vertex factors above. Each assignment to a bag, tuple position, and local pattern operation has its own gate index. A permutation of the n host vertices permutes these indices and preserves all wires. The diagram of a single copy uses O(n^{t+1}) gates and wires for fixed patterns and edit rules, by the introduce, forget, and join recurrences, with each edge evaluated in one bag. Use a common base B and shift to encode each output vector. Compute the first M powers of each encoded value in a chain and sum symmetrically over tuples for each power. Use Newton identities on these invariant power sums. The last two steps use O(M²) gates and wires, including coefficients 1/j. All coefficient outputs are fixed by permutations. The resulting polynomials are graph invariants and can serve as one-dimensional test modules in Grochow–Urisman's framework.

### Width check and use as an algorithmic filter

Take G = C₆ and H = C₃ ⊔ C₃. Both are 2-regular on six vertices, so 1-WL does not split them. On deleting one vertex, every card of G is P₅ and every card of H is P₂ ⊔ C₃. The number of homomorphisms from the four-vertex path P₄ is twice the sum of deg(u)deg(v) over undirected edges uv. This gives 24 and 26, respectively. Thus the additive unit for r = 1 is necessary when t = 1. This tests strict improvement over baseline 1-WL, with 2-WL as the proved upper bound.

For a cheap filter, evaluate a few low-order mixed moments or sample edits before computing the full table. A certified difference in any invariant moment suffices to reject isomorphism. A difference between independently sampled, incomplete decks does not certify it. For an edit optimization instance, the full profile gives the optimum and an achieving tuple by direct enumeration within the stated bound. The theorem covers edits supported on r vertices. An operation such as local complementation, which modifies adjacency between unmarked neighbors, would need a separate analysis.

### Scope of the contribution

The result is an informal deduction using the homomorphism characterization of WL and Newton identities. The [Lean lemma](EditDeckEncoding.lean) verifies recovery of the multiset from the root-factor polynomial. The closest comparisons are graph-reconstruction invariants, subgraph-GNN bounds, and bounded-treewidth homomorphism circuit constructions. The contribution here is the joint guarded edit-deck statement, its exact width proof and the explicit coefficient circuit. The search did not establish publication priority. The original reconstruction conjectures and the unrestricted symbolic subgraph-circuit question are outside the theorem's scope.
