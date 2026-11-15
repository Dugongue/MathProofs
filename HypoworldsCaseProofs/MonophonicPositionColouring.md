# Monophonic position colouring is Θ₂ᴾ-complete

A vertex set is in monophonic position if no induced path contains three of its vertices. Chandran, Di Stefano, Haritha, Thomas and Tuite introduced colourings in which each colour class is in monophonic position, and the independent variant with the additional requirement of a proper colouring. They classified general position colouring, based on shortest paths, in Section 8. [Colouring a graph with position sets, Definition 2.3 and Section 8](https://arxiv.org/html/2408.13494v2)

**Theorem.** Both Monophonic Position Colouring and Independent Monophonic Position Colouring are $\Theta_2^{\mathrm P}$-complete under deterministic polynomial-time many-one reductions. The result holds even for connected graphs of diameter exactly two. The allowed number $k$ of colours is part of the input.

Write $\chi_{\rm mp}$ and $\chi_{{\rm mp},i}$ for the two minimum colour numbers. We use the characterization of $\Theta_2^{\mathrm P}$ as deterministic polynomial time with a polynomial number of nonadaptive NP queries. [Hemaspaandra–Spakowski–Vogel, Section 3](https://doi.org/10.1016/j.tcs.2005.08.031)

## 1. The parallel NP upper bound

Call an unordered triple bad if an induced path contains it, and let $p$ count all bad triples. For $k$ colours, let $q$ be the largest number of distinct bad triples made nonmonochromatic by a single colouring, required to be proper in the independent variant. A valid colouring exists exactly when the admissible colourings are nonempty and $q=p$.

For each integer $0\le t\le \binom{|V|}{3}$, ask whether there are $t$ distinct bad triples, and whether there are $t$ distinct bad triples together with one admissible colouring making each of them nonmonochromatic. Both predicates are in NP by supplying the triples and induced paths witnessing them, together with the colouring for the second query. At $t=0$ the second query detects if there is any admissible colouring. This computes the original decision in a single parallel batch of polynomially many queries.

## 2. A graph whose optimum is a constant plus an NP answer bit

In Three-in-a-Path, the input is a graph $D$ and three distinct marked vertices $a,b,c$, and the question is whether an induced path contains all three in any order. We use the NP-completeness of this problem. It remains NP-complete with independent marked vertices. If $a,b$ are adjacent, they must occur consecutively and, up to reversing the path, $c$ appears before them. To test the order $c,\ldots,a,b$, delete $b$ and all its neighbours except $a$. The order is feasible exactly when $c$ survives and is connected to $a$ in the remaining graph. Indeed, append $b$ to a shortest surviving path. Conversely, truncate a given induced path at $a$. Interchange $a,b$ for the other possible order. Thus any input with adjacent marks can be decided in polynomial time and mapped to a fixed independent-mark yes or no instance. The alternating triple of a five-vertex path and the three leaves of a claw give respective examples. [Three-in-a-Path, Fiala–Kamiński–Lidický–Paulusma, introduction](https://doi.org/10.4230/LIPIcs.STACS.2010.2469)

For independent marked vertices, write $n=|V(D)|$ and adjoin a palette clique $Q$ on $b_0=n-2$ vertices. It has one special vertex $q_0$ and one token $q_v$ for each unmarked vertex $v$. Each terminal is adjacent to every ordinary token. Each unmarked $v$ is adjacent to every ordinary token except $q_v$. Give $q_0$ exactly the old neighbours of $a$. In the resulting graph $P(D)$, the distinct vertices $q_0,a$ are nonadjacent and have identical open neighbourhoods.

Two such false twins on an induced path must be its two ends, with a single common neighbour between them. They cannot occur consecutively because they are nonadjacent. The neighbour of one along the path is also adjacent to the other, forcing a distance of two along the path, and any extra vertex following either twin would give a chord. Thus an induced path through $a,b,c$ avoids $q_0$. It also avoids every $q_v$, since such a token is adjacent to all three marks and an induced path has maximum degree two. So the existence of the path through the marks is unchanged.

Let $x$ be the Three-in-a-Path answer bit. A proper colouring with $b_0$ colours uses all of them in $Q$, whereupon each terminal must use $q_0$'s colour. If $x=1$ this violates monophonic position. If $x=0$, colour each unmarked $v$ like $q_v$, and all terminals like $q_0$. The class $\{q_0,a,b,c\}$ is independent and monophonic. A violating path through $a,b,c$ is ruled out by hypothesis. A path through $q_0,a$ and another mark would have to have the other mark as the middle of a two-edge path, but that mark is nonadjacent to the twins. A path through $q_0,b,c$ omitting $a$ would remain induced if $q_0$ were replaced by $a$, contradicting the hypothesis again. Every other class has size two. When $x=1$, give $b$ a fresh colour and use the same assignment otherwise. The class $\{q_0,a,c\}$ is monophonic by the false-twin argument and is independent. This proves
$$
 \chi_{{\rm mp},i}(P(D))=b_0+x.
$$
By reducing any NP predicate to Three-in-a-Path first, we obtain such a graph with a computable baseline for any NP answer bit.

## 3. An exact negative answer bit

For disjoint graphs $G,H$, their join $G\vee H$ has every cross-edge. An independent colour class lies entirely in one side, and an induced path using both sides has at most two vertices per side. If it had three on one side, a vertex on the other would be adjacent to all three. Together with the preservation of induced paths entirely within a side, this gives
$$
 \chi_{{\rm mp},i}(G\vee H)=\chi_{{\rm mp},i}(G)+\chi_{{\rm mp},i}(H).
$$

Variable-threshold Colouring is NP-complete on $P_5$-free graphs. On such graphs every independent set is monophonic, since an induced path containing an independent triple needs at least five vertices. Consequently $\chi_{{\rm mp},i}(G)=\chi(G)$ on this class. Reduce any NP input to $(G,k)$ with $G$ a $P_5$-free graph of order $n$ and $1\le k\le n$. Invalid or trivial bounds can be mapped to fixed instances. Put $h=\chi(G)$ and $y_j=\mathbf1_{\{h\le j\}}$. [Král–Kratochvíl–Tuza–Woeginger colouring dichotomy](https://doi.org/10.1007/3-540-45477-2_23)

For each $1\le j\le n$ except $j=k$, construct the graph of Section 2 for the NP input $(G,j)$, with exact score $b_j+y_j$. Join these graphs with $G$. The exhaustive threshold identity $h+\sum_{j=1}^{n}y_j=n+1$ gives the exact score
$$
 n+1+\sum_{j\ne k}b_j-y_k.
$$
The baseline and all graphs are computable without access to the bits. This constructs a known constant minus the answer bit of any NP predicate, complementing the known constant plus the answer bit from Section 2.

## 4. The many-one reduction

The problem $\omega(A)\le\omega(B)$ for equal-order graphs is $\Theta_2^{\mathrm P}$-complete under polynomial-time many-one reductions. Spakowski and Vogel's Min Card Vertex Cover Compare is complete on equal-order graphs. Take graph complements and swap the inputs, using $\tau(X)=|V(X)|-\omega(\overline{X})$ for minimum vertex cover size $\tau(X)$. [Hemaspaandra–Spakowski–Vogel, Definition 4.10 and Lemma 4.11](https://doi.org/10.1016/j.tcs.2005.08.031)

For each $j=1,\ldots,|V(A)|$, apply Section 2 to the NP predicate $\omega(A)\ge j$. For each $j=1,\ldots,|V(B)|$, apply Section 3 to $\omega(B)\ge j$. Joining all the graphs yields the independent monophonic position chromatic number
$$
 C+\sum_{j=1}^{|V(A)|}\mathbf1_{\{\omega(A)\ge j\}}
   -\sum_{j=1}^{|V(B)|}\mathbf1_{\{\omega(B)\ge j\}}
 = C+\omega(A)-\omega(B),
$$
where $C$ is the sum of baselines. The threshold $C$ gives exactly the comparison. To guarantee diameter two, join the resulting nonempty graph with a graph of two nonadjacent vertices and increase $C$ by one. The new vertices need one colour, remain nonadjacent, and are both adjacent to every old vertex. This gives diameter exactly two. Empty comparator graphs and thresholds at least the vertex count can be handled by outputting fixed diameter-two instances with the appropriate answer. Every construction and number of graph factors is polynomially bounded. This proves the lower bound for the independent variant.

## 5. The ordinary variant

Given a graph $G$ and threshold $1\le k\le |V(G)|$, replace each vertex $v$ by a fibre $F_v$ of $k+1$ pairwise nonadjacent vertices. Add all edges between two fibres exactly when their original vertices are adjacent. Every induced path on distinct original vertices lifts through any representatives of its vertices, and every induced path with at most one vertex per fibre projects to an induced path of $G$. The vertices of a fibre are false twins.

Suppose the enlarged graph has a monophonic position colouring with at most $k$ colours. For each original vertex, choose a colour appearing at least twice in its fibre. Adjacent original vertices cannot choose the same colour, since two representatives of that colour from one fibre and one from the other would induce a monochromatic two-edge path. The chosen colouring of $G$ is also monophonic since any violating induced path lifts through representatives of the chosen colours. It is thus an independent monophonic position colouring.

Conversely, lift an independent monophonic position colouring to a uniform colouring of each fibre. A violating path with distinct fibres would contradict the original monophonic position condition by projection. An induced path using two vertices from the same fibre has exactly three vertices by the false-twin property. Its middle vertex belongs to an adjacent fibre and thus has a different colour. This proves equivalence. The blow-up is polynomial and preserves diameter two on connected graphs of diameter two. Distances between different fibres are at most the original distances, and two vertices of the same fibre are nonadjacent and have a common neighbour.

This proves the ordinary lower bound. Together with the parallel-query upper bound it gives both classifications. In particular, either problem belongs to NP exactly if NP equals coNP. This is an informal proof. Targeted literature searches did not locate a prior matching classification of the two monophonic variants.
