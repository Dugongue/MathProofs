# A signed game and a faster algorithm for dense Weisfeiler–Leman refinement

Curticapean, Neuen, Nikabadi, Seppelt and Young introduced dense Weisfeiler–Leman refinement. They characterized its distinguishing power by both the logic $\mathsf{CW}^k$ and homomorphism counts from graphs of cliquewidth at most $k$. Their Theorem 1.2 gives a $4^{kn}\operatorname{poly}(n,k)$ algorithm. Their conclusion asks for a Spoiler–Duplicator game for the logic and for improvements to the exponential base. Below is an informal proof of a game characterization and a $2^{(k+1)n}\operatorname{poly}(n,k)$ algorithm for $k\ge 2$. The latter bound concerns the stable coloring and the resulting graph decision. The optimal base remains open. [Original paper, Sections 3, 4, 8 and 9](https://arxiv.org/html/2608.13382v1)

## The refinement being computed

All graphs here are finite, undirected and simple. For a graph $G$, take the state space $\Omega_G=\mathcal P(V(G))^k$. A state $D=(D_1,\ldots,D_k)$ initially has color $(|D_1|,\ldots,|D_k|)$. For each ordered pair $i\ne j$, there are two integer-weighted transition operators. A recoloring transition has one successor of weight $1$, obtained by replacing $D_i$ with $D_j$. A join transition has weight zero from $D$ to $S$ unless the inactive coordinates coincide and $S_i\subseteq D_i,\ S_j\subseteq D_j$. In the remaining cases its weight is

$$
E^{ij}(D,S)=
\sum_{\substack{S_i\subseteq A_i\subseteq D_i\\ S_j\subseteq A_j\subseteq D_j}}
(-1)^{|A_i\setminus S_i|+|A_j\setminus S_j|}\,\beta_G(A_i,A_j).
$$

Here $\beta_G(A,B)=1$ exactly when $A,B$ are disjoint and all edges across them are present. In each synchronous round, a state retains its previous color and records, for each operator and each previous color class, its total outgoing weight into that class. To compare two graphs, refine their *tagged disjoint union of state spaces* using block-diagonal operators. This gives the same cross-graph comparisons as shared color names with missing colors assigned weight zero. The distinguished state of each graph is the tuple all of whose entries are its entire vertex set. These are the operators and graph comparison in the authors' equations (5), (6) and (10)–(11). [Definition and characterization](https://arxiv.org/html/2608.13382v1#S4)

## Theorem 1. A game for $\mathsf{CW}^k$

Starting at the two distinguished states, Duplicator can play forever exactly when the graphs are $\mathsf{CW}^k$-equivalent. More precisely, survival for $r$ rounds from any two tagged states is equivalent to equality of their round-$r$ refinement colors.

A position is an ordered pair $(x,y)$ of tagged states. Unequal initial colors lose immediately. In a round, Spoiler can pass, leaving the position unchanged, or choose a transition operator. For each state $x$, form positive and negative bags $P(x),M(x)$ of successor tokens for that operator. A token carries its tagged successor. For recoloring there is one positive token. For a join, each summand with $\beta_G(A_i,A_j)=1$ in the formula gives one token labeled by $S$, with the sign in the formula. Equivalently, first cancel opposite tokens at each *individual* successor and keep the absolute value of its total weight there. Either convention gives the same winning positions.

Duplicator must give a bijection between the following two bags:

$$
P(x)\uplus M(y)\qquad\text{and}\qquad M(x)\uplus P(y).
$$

Failure to give a bijection loses. Spoiler selects any matched pair, and its two successor tags give the next position. If both bags are empty, this challenge ends in Duplicator's favor. A matched pair can have two tags from the same graph. This permits the cancellations required by integer weights. The moves use only the two graphs and the current subsets.

**Proof.** At round zero the rule compares the initial colors. Assume the assertion for $r$ rounds. To survive an operator challenge followed by $r$ rounds, Duplicator must and can match tokens with identical round-$r$ successor colors. For a color class $B$, write $p_x(B),m_x(B)$ for positive and negative token counts with successors in $B$. A matching exists separately for every $B$ precisely when

$$
p_x(B)+m_y(B)=m_x(B)+p_y(B).
$$

This identity says exactly that the two operator sums to $B$ agree. The pass tests equality of the old colors. Taking all challenges proves the induction step. The finite refinement stabilizes. From equal stable colors, Duplicator can fix a color-preserving matching for each operator and position and reuse it indefinitely. Different stable colors separate after finitely many rounds. The paper's graph-level Theorem 1.3 now identifies survival from the distinguished states with $\mathsf{CW}^k$-equivalence and with equality of all bounded-cliquewidth homomorphism counts. ∎

This gives a subset game. No claim about a fixed number of ordinary vertex pebbles is required. Games for general coalgebraic systems and weighted partition refinement provide broader methodological precedents. [König and Mika-Michalski on bisimulation games](https://doi.org/10.4230/LIPIcs.CONCUR.2018.37)

## Theorem 2. A smaller upper bound for stable refinement

For $k\ge 2$, stable dense $k$-WL on an $n$-vertex graph can be computed deterministically in $2^{(k+1)n}\operatorname{poly}(n,k)$ time on a random-access machine, allowing polynomial bit cost per operation. The same bound decides equivalence of two input graphs, taking $n$ as the larger order. This gives a uniform exponential base of at most $\sqrt 8$ raised to $kn$ for $k\ge 2$. For $k=1$ there are no join or recoloring operators, and the size of the vertex set determines the graph decision.

**Generating the transitions.** Fix an operator $E^{ij}$, and temporarily suppress the $k-2$ inactive coordinates. A nonzero column must have $S_i\cap S_j=\varnothing$. Fix such a disjoint pair and take the tagged ground set $U=(V\setminus S_i)\uplus(V\setminus S_j)$. For a subset $B\subseteq U$, write $B_i,B_j$ for its pieces. Initialize

$$
f(B)=(-1)^{|B|}\beta_G(S_i\cup B_i,S_j\cup B_j).
$$

The subset zeta transform at $C\subseteq U$ sums $f(B)$ over $B\subseteq C$. This is exactly the desired entry with $D_i=S_i\cup C_i,\ D_j=S_j\cup C_j$. To compute the entire transform, process each element $v$ of $U$ once. For each mask containing $v$, add to its array entry the entry at the mask with $v$ removed. A direct induction on the processed elements verifies the formula. This takes $2^{2n-|S_i|-|S_j|}\operatorname{poly}(n)$ time including initialization. The total over disjoint $S_i,S_j$ is $8^n\operatorname{poly}(n)$, since each vertex contributes four possibilities when in neither successor set and two possibilities when in either specified successor set. All intermediate sums have absolute value at most $4^n$.

Each active transition repeats for $2^{(k-2)n}$ assignments of inactive coordinates. Record incoming adjacency lists of nonzero transitions for all labels, including the single outgoing transition per state per recoloring label. The number of labels is $2k(k-1)$. Construction time, storage in bits, and the number $M$ of labeled edges are all bounded by $2^{(k+1)n}\operatorname{poly}(n,k)$. Two tagged state spaces cost at most twice as much. For unequal graph orders the distinguished states already differ at the initial color.

**Refining signed weights.** Let $N$ be the number of tagged states. Put all initial blocks in a queue. Remove a splitter $B$ and compute, for each predecessor $x$, the vector of its signed sums into $B$, with one component per label. Split each current block by equality of that vector. When a block already in the queue splits, replace its entry by all children. When a block outside the queue splits, append every child except one of largest size.

For correctness, keep an abstract history of the popped splitters as sets. The span over the rationals of indicators of historical and queued sets contains all current block indicators. Initially this follows from initialization. Popping moves an indicator to the history. Replacing a queued block by all children preserves its indicator as their sum. For an unqueued split, subtract all queued child indicators from the parent's indicator to obtain the omitted one. By construction the eventual partition is stable with respect to every popped splitter. At exhaustion the span argument and linearity give stability with respect to every final block. Conversely, throughout the algorithm a stable partition refining the initial coloring also refines every current partition. Indeed, each splitter is a union of its blocks, so its signed weights are constant within each of those blocks. This proves that the computed partition is the coarsest stable one.

At a pop, scan the incoming lists for vertices of $B$. Untouched vertices have the zero vector. Touched predecessors whose weights cancel in every coordinate also belong to the zero group. For implementation, store vertex lists and sizes for each block, use deterministic sorting to group touched vertices by block and sum vector, and leave untouched elements in place. If the zero group is largest, its list is retained without scanning it. When the zero group is small, its existing list is already available for queuing. All blocks resulting from genuine splits, over the entire run, form a forest with at most $N$ leaves and no unary internal node. Queue updates therefore create only $O(N)$ block records.

A vertex belongs to at most $1+\lfloor\log_2 N\rfloor$ popped splitters. After a splitter containing the vertex is popped, the next time that vertex acquires a queued ancestor, the ancestor must be a newly enqueued child of size at most half that of its parent. Replacing that queued ancestor by descendants before its pop can only decrease the size further. Thus splitter membership scans and incoming-edge visits cost $O((N+M)\log(2N))$ before sorting and polynomial arithmetic factors. Vertex addresses and vector entries use $\operatorname{poly}(n,k)$ bits, since $N\le 2\cdot 2^{kn}$ and each scalar sum has absolute value at most $N4^n$. These estimates establish the bound. ∎

Smaller-half refinement and efficient weighted bisimulation are established methods. The graph-specific gain comes from the $8^n$ disjoint-successor column construction and the untouched-coordinate factor, combined with signed refinement. [Dorsch, Milius, Schröder and Wißmann on partition refinement](https://doi.org/10.4230/LIPIcs.CONCUR.2017.32)

## A separate dense-to-sparse transfer

Let $\mathcal F$ be a class of finite simple graphs closed under loopless vertex quotients. Such a quotient partitions the vertices into independent blocks and places an edge between blocks exactly when there is an edge between them in the source. Let $\mathcal X$ be any class closed under taking subgraphs. For targets $G,H\in\mathcal X$, equality of homomorphism counts from $\mathcal F\cap\mathcal X$ implies equality from all of $\mathcal F$.

**Proof.** For any source $F$, partition its homomorphisms by the partition $\pi$ of vertices into fibers. This gives
$$
\operatorname{hom}(F,G)=\sum_{\pi}\operatorname{inj}(F/\pi,G),
$$
where $\operatorname{inj}$ counts injective edge-preserving maps, and the sum runs over all partitions into independent blocks. Any quotient outside $\mathcal X$ makes zero contribution, since an injection exhibits it as a subgraph of the target. If $F\in\mathcal F\cap\mathcal X$, isolate the discrete partition in this identity and induct on the number of vertices. All other contributing quotients have fewer vertices and belong to $\mathcal F\cap\mathcal X$. Thus the two targets agree on every injective count for sources in that intersection. Apply the identity again to any $F\in\mathcal F$ to obtain the assertion. ∎

In particular, for complete bicliques with positive sides, and for complete multipartite graphs, every loopless quotient stays in the same family. On $K_{t,t}$-subgraph-free targets, sources already free of that very same $K_{t,t}$ suffice. This is a sufficient closure property in the authors' Section 9 dense-to-sparse question. A classification of all qualifying source classes remains open.
