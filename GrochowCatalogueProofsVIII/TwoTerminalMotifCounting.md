# Exact induced motif counting across one- and two-terminal pieces

## GP-0939

There is an exact induced-motif counting algorithm for a host with a displayed core of order $c$, a collection of rooted tree pieces meeting it by single bridges, and a collection of path interiors whose only external neighbors are their designated core terminals. All the pieces are vertex-disjoint off the core, with no edges between their interiors. The path terminals may belong to the same core vertex when the resulting graph is simple. For a $k$-vertex motif $F$, including disconnected motifs, the algorithm takes
$$
(c+1)^k 3^k \operatorname{poly}(k,c)
\bigl(1+\sum_j |P_j|+b\log(N+1)\bigr)
\operatorname{poly}(\log(N+1))
$$
bit operations. Here the input may list each rooted or terminal-marked piece type $P_j$ once, give $b$ binary multiplicities grouped by type and chosen attachment vertices, and describe a host of expanded order $N$. For explicit inputs one can take one multiplicity-one group per piece. Thus the method is fixed-parameter tractable in $c,k$ with linear dependence on the displayed peripheral lengths up to bit factors. It supports parallel ears with arbitrarily long interiors and avoids enumerating their positional combinations. [One-shell motif reuse and the proposed two-shell extension](https://arxiv.org/html/2609.38686v1#S5)

### Boundary conditions after the core assignment

First count injective induced maps from the labeled motif to the host. Division by $|\operatorname{Aut}(F)|$ converts this to a count of vertex-set occurrences, with an additional cost depending only on $k$ as described below.

Enumerate a partial injection that sends each motif vertex either to an actual core vertex or to the symbol “outside.” There are at most $(c+1)^k$ assignments. Check the induced adjacencies among the vertices assigned to the core. For one fixed assignment put $W$ equal to the remaining motif labels. For each piece compute a table indexed by subsets $S\subseteq W$, counting induced injections of $S$ into that piece's interior with exactly the prescribed adjacencies to the already mapped core vertices. Such adjacencies can be checked locally at each prospective assignment of a label to an interior vertex. A tree piece allows only its root to have any core neighbor, and a path piece allows only its first and last interior vertices to meet a terminal. Nonadjacency to all other already used core vertices must hold too.

### Linear-in-length tables for each piece

For a path, scan its vertices in order. Store the used label subset and the label, if any, put on the previous path vertex. A vertex may be skipped, or may receive a previously unused label. When assigning a label, its adjacency to already used labels must equal exactly the possible edge to the previous occupied vertex. The assigned label must pass the core compatibility test above. Thus a table of at most $(k+1)2^k$ states suffices, with polynomially many operations per state and per path vertex.

For a rooted tree, work upward from the leaves. For each subtree store the set of used labels and the label assigned to the subtree root, allowing omission. Fixing the parent root choice, merge the child tables one child at a time. The label sets must be pairwise disjoint, there can be no motif edge between different child sets, and the edges between the root label and a child set must be exactly the possible edge to that child's root label. The last comparison uses a state already recorded by the child. Each merge considers at most $3^k$ disjoint subset pairs, times a polynomial factor for root labels. Summing over the piece vertices builds its table in the claimed size bound. This induction also handles placements skipping internal vertices, which can yield disconnected induced motifs.

### Assembly and repeated types

For two disjoint unions of pieces with aggregate tables $f,g$, define
$$
(f*g)(S)=
\sum_{\substack{L\sqcup R=S\\E_F(L,R)=\varnothing}}f(L)g(R).
$$
No graph edge crosses these interiors, so the condition is exactly induced compatibility. This product is associative: either bracketing counts triples of disjoint sets with no cross edges between any two. Its identity is the table supported on the empty set with value one. Combine multiplicities with identical type and terminals first. Each type has at most $(c+1)^2$ distinct attachment groups, so rescanning its representative for these groups costs only a further polynomial factor in $c$. For a group of $m$ identical pieces attached to the same specified core vertices, take the $m$th power of its table by repeated squaring using this product. Each copy is separate even when identical, so the coefficient correctly counts choices of copies. Combine every group by the same product and read the entry on $W$. Sum over the core assignments. Each induced injection appears exactly once, by its unique core assignment and division into pieces.

Every table entry is bounded by $N^k$ or by that bound with $N$ replaced by the maximum represented partial host size; exponentiation can avoid computing powers larger than the requested multiplicity. All arithmetic lengths are polynomial in $k\log(N+1)$. If vertex-set counts are requested, compute $|\operatorname{Aut}(F)|$ by the same counting algorithm on the host whose entire $k$-vertex graph is the core, or by enumerating the $k!$ permutations. This adds $k!\operatorname{poly}(k)$ operations, independently of the host and without changing the stated bound for labeled counts. The exact division is valid because the action of $\operatorname{Aut}(F)$ on injections with one given image is free and transitive.

For fixed motif size and small core this gives near-linear processing of long displayed path interiors and tree pieces. Binary repetition groups need only logarithmically many merges even if the expanded shell is exponentially larger than the description. The conclusions apply to the stated terminal-separated decomposition, including any such decomposition supplied inside a host's actual two-shell.
