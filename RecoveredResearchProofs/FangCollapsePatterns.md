# Counterexamples to Fang’s collapse-pattern conjectures

This is an informal proof. It recovers two counterexamples from earlier research notes and extends the same construction to two more conjectures. The problems are Caishi Fang’s Conjectures 2.5, 2.7, 2.11, and 2.13 in *Accelerations for Graph Isomorphism* (2017), §2. The separate vertex-transitivity conjecture, 2.9, was previously documented in [the Lean example](https://github.com/Dugongue/MathProofs/blob/main/FangCounterexample.lean). The classical Tutte 12-cage also contradicts 2.9 and thus 2.7; the construction below gives a smaller direct witness and an entire family. No publication-priority claim is made. [Original preprint](https://arxiv.org/pdf/1706.09230#page=7)

## The invariant

For a vertex $v$ of a connected graph $G$, its collapse layers are the sets of vertices at successive distances from $v$. Its collapse tomography records the vertex-degree multiset and the edge-property multiset of each induced layer after the first singleton. In a bipartite graph each layer is independent, so the recorded vertex degrees are all zero and the edge-property multisets are empty. The tomography then depends only on the sequence of layer sizes.

For an unrooted graph the collapse pattern is the multiset of all its vertex tomographies. For a graph with a distinguished vertex or set $S$ of vertices, called nails in the paper, group the original vertex tomographies by distance to $S$. The collapse pattern is the resulting ordered list of multisets, starting with distance zero. For a directed edge $u\to v$ the paper uses the ordered triple consisting of the pattern of $G$ nailed at ${u,v}$, then the patterns of $G-uv$ nailed at $u$ and at $v$, respectively.

## Dense bipartite complements

Give $K_{n,n}$ parts $A,B$ and remove the edges of a spanning 2-regular bipartite graph $H$. Denote the result by $G$, and take $n\ge 5$. Every vertex of $G$ has degree $n-2$. Distinct vertices in the same part have a common neighbor because their two neighborhoods each have $n-2$ elements and (2$n-2$>n). Their distance is two. For opposite-part nonneighbors $v,w$, choose a neighbor $x$ of $v$. The vertices $x,w$ lie in the same part and have a common neighbor $y$, giving a path $v,x,y,w$ of length three. Bipartiteness rules out any shorter path for that nonedge.

Thus $G$ is connected and every vertex has layer sizes $(1,n-2,n-1,2)$, including distance zero. Its bipartition is unique up to swapping the two sides. An isomorphism between two such graphs preserves the set of cross-part pairs, so it induces an isomorphism of the corresponding missing-edge graphs. In particular, an automorphism of $G$ preserves the component sizes in $H$.

## Conjectures 2.5 and 2.7

**Equal unrooted patterns need not imply isomorphism.** For every $n\ge 5$, take the two missing-edge graphs
$$
H_1=C_4\sqcup C_{2n-4},\qquad H_2=C_{2n}.
$$
They both span $n$ vertices in each bipartition part and have degree two. Both complements have the same tomography at each of their $2n$ vertices, so their unrooted collapse patterns match. The complements are nonisomorphic because their missing-edge graphs have different numbers of connected components. This refutes Conjecture 2.5.

**Equal rooted patterns need not imply rooted isomorphism.** In the complement of $H_1$ place the two roots in different components of $H_1$. Since every tomography is equal and the layer sizes agree at the two roots, the rooted patterns match. The components have distinct sizes and no automorphism maps one root to the other. This refutes Conjecture 2.7. Taking $n=5$ gives ten vertices in both examples.

## Conjectures 2.11 and 2.13

**Matching all edge patterns need not imply edge-transitivity.** Keep the complement of $H_1$. For an edge $uv$ of $G$, with $u\in A$ and $v\in B$, the edge-nailed layers consist of the endpoints, the $n-3$ other neighbors of each endpoint, and the four remaining vertices. The remaining vertices have distance two to the endpoint in their own part. The layer sizes are therefore ((2,2$n-3$,4)) for every edge. All original vertex tomographies are identical, so the edge-nailed patterns match.

There is an edge with endpoints in different components of $H_1$ because every such cross-part pair was preserved. There is also an edge with both endpoints in its larger component, whose cycle has $n-2\ge 3$ vertices on each side but removes only two neighbors per vertex. The two edge types cannot be exchanged by an automorphism, which preserves the components of $H_1$. This refutes Conjecture 2.11.

**Matching all directed-edge patterns need not imply arc-transitivity.** Take $n\ge 6$ and delete an arbitrary edge $uv$ of $G$. In $G-uv$ the endpoints have degree $n-3$ and all other vertices have degree $n-2$. There is at most one depleted vertex in each part. Thus the sum of the degrees of any two distinct same-part vertices is at least $2n-5>n$. As before, every same-part pair has distance two, and every cross-part nonedge has distance three. For any vertex of degree $d$, the layer sizes are $(1,d,n-1,n-d)$. In particular the deleted graph has just two types of vertex tomography, distinguished by the degree $d$.

The layers from $u$ now have sizes $(1,n-3,n-1,3)$. The only depleted vertices are $u$ in layer zero and $v$ in layer three. Every other vertex contributes the tomography for degree $n-2$. The rooted collapse pattern therefore depends only on $n$, and the same description holds for the root $v$. Together with the calculation for edge nails, this makes the full ordered arc pattern independent of the directed edge. The two different edge types already rule out arc-transitivity. This refutes Conjecture 2.13. Taking $n=6$ gives a twelve-vertex witness.

The archive supplied the unrooted and rooted counterexamples. The edge and arc deductions are the extension established during the archive audit. All four proofs concern exactly the collapse patterns defined in §2 of the cited preprint.
