# Three sharp precision regimes for graph homomorphism counts

Let two hidden finite, simple, uncolored connected graphs have the same public order $n$. For a chosen simple graph $F$ and modulus $m$, one query returns the two residues of the numbers of homomorphisms from $F$ to the two targets. The precision is the largest value of $\lceil\log_2 m\rceil$ used on any query. The number of queries and computation between queries are unrestricted. The worst case below ranges over $n\le N$.

**Theorem.** On the single class of connected graphs of maximum degree at most 6 and pathwidth at most 19, the following precisions suffice and are necessary up to the indicated accuracy.

| Permitted moduli | Worst-case precision in bits |
|---|---|
| Powers of 2 | $\Theta(N)$ |
| Powers of any one fixed prime $p>6$ | $\log_2 N+O_p(1)$ |
| Any modulus, even chosen adaptively | $\log_2\log N+O(1)$ |

For the last upper bound a *single prime determined by the public order alone* suffices for every probe at that order. The upper bounds hold without a pathwidth bound. The binary upper bound holds even without connectedness or a degree bound. The lower bounds permit arbitrary, disconnected, arbitrarily large probes. This is a result about the information carried by homomorphism counts. Computing those counts is outside the cost model.

## Upper bounds

Write $\operatorname{ind}(G,Y)$ for the number of induced embeddings. This is an integer linear combination of $\operatorname{hom}(F,Y)$ with $|V(F)|\le |V(G)|$. First use inclusion-exclusion to enforce nonedges on injective homomorphisms, then inclusion-exclusion on collisions to express each injective count using quotient graphs. Terms with a loop contribute zero and parallel edges may be merged. For nonisomorphic equal-order graphs $G,H$, taking $Y=G,H$ gives $|\operatorname{Aut}G|$ and zero. Thus some probe distinguishes them modulo any $m$ that does not divide $|\operatorname{Aut}G|$. This proves the upper bounds as actual finite procedures by enumeration of probes up to order $n$.

First $2^{1+v_2(n!)}$ always suffices. Second, in a connected graph of maximum degree $\Delta <p$, an automorphism of order $p$ fixing a vertex must fix all its neighbors and hence every vertex by induction. By Cauchy's theorem each vertex stabilizer has order prime to $p$. A Sylow $p$-subgroup therefore acts freely, so its order divides $n$. We may choose $m=p^{1+v_p(n)}$, of width at most $\log_2 n+O_p(1)$.

Third, choose a prime $p>\Delta$ not dividing $n$. One can take $p=O_\Delta (\log(n+2))$, since the product of the primes between $\Delta$ and $C_\Delta \log(n+2)$ exceeds $n$ for a suitable constant by Chebyshev's estimates. Now $v_p(|\operatorname{Aut}G|)=0$, so $m=p$ works simultaneously for all pairs at that order.

## A cubic pair for the last two lower bounds

For $L\ge 4$ compare the prism $C_L\square K_2$ with the cycle $C_{2L}$ augmented by the matching of antipodal vertices. Both have $2L$ vertices and degree 3. They are respectively bipartite for even and odd $L$, so they are nonisomorphic. Write each as a string of $L$ matching pairs with either straight or twisted closure. Keeping the first pair and two consecutive pairs gives a path decomposition of width at most 5. Each graph admits a free cyclic vertex action of order $L$, by rotation on the prism and rotation by two positions on the augmented cycle. That action is also free on maps from every nonempty probe, by evaluating a fixed probe vertex. All those counts vanish modulo every divisor of $L$. Empty probes give one on both sides.

For fixed $p>6$ take the largest $p$-power $L\le N/2$. Distinguishing requires a modulus at least $pL$ when only powers of $p$ are permitted. For arbitrary moduli take $L=\mathrm{lcm}(1,\dots,s)$. Chebyshev's estimate $\log L=O(s)$ lets us take $s=\lfloor c\log N\rfloor$ with $2L\le N$. Every allowed answer at every modulus at most $s$ agrees. Adaptivity cannot separate identical transcripts.

## An exact divisibility construction for the binary lower bound

Let $A$ be any finite abelian group of order $r\ge 2$. Orient the edges of a finite connected simple base graph $B$ with no isolated vertices. A charge $\alpha:V(B)\to A$ defines a simple uncolored target $H_\alpha$. A vertex above $v$ assigns values to the incident edges with signed sum $\alpha(v)$, using opposite signs at the two ends of each edge. Vertices above adjacent base vertices are linked when their values on the common edge agree. The projection to $B$ is a graph homomorphism. Compare charge zero with a charge $\alpha$ of nonzero total supported at one vertex. Let $\beta=|E(B)|-|V(B)|+1$.

For every uncolored probe $F$, group its homomorphisms by the composite map $f:F\to B$. If $f$ misses a vertex $w$, modify the charge there to make the total zero. Every charge of total zero is the boundary of an edge assignment, as seen by peeling a spanning tree. Translation by that assignment gives a bijection between lifts of $f$ in the two graphs. If $f$ is onto vertices, translations by zero-boundary assignments act freely on each lift set. Such an assignment is arbitrary on the $\beta$ off-tree edges and extends uniquely along the tree. Freeness follows because a lift above every vertex reads every incident value. Hence every Hom-count difference is divisible by $r^\beta$.

For $F=B$ the surjective endomorphisms are precisely the automorphisms. Every one has exactly $r^\beta$ lifts for charge zero and none for the charge of nonzero total. The difference at $B$ equals $|\operatorname{Aut} B|r^\beta$. In particular, a rigid $B$ gives *exactly* $r^\beta$ as the gcd of all integer Hom-count differences.

Take the two-row ladder with $s\ge 3$ columns and attach one leaf at a corner. Its unique leaf fixes that corner. Removing the leaf recovers the ladder; the corner's two neighbors there have different degrees. Fixing the first column and the adjacent vertex on the first rail forces the second column by completing its square. Successive columns are then forced. Thus the base is rigid and $\beta=s-1$.

The two targets have the same order $\sum_v r^{\deg(v)-1}\le (2s+1)r^2$, maximum degree at most $3r$, and pathwidth at most $5r^2-1$. For the last bound take all fibers over consecutive pairs of columns and include the leaf in the first bag. The targets are connected. Start at an interior degree-three vertex with two nonleaf neighbors. Assignments in its fiber agreeing on one of those two incident coordinates can be joined by a two-step walk through the corresponding neighbor: a prescribed single value extends at any vertex of degree at least two. Differences preserving the first coordinate and differences preserving the second generate the whole signed-zero-sum fiber, by using the third coordinate to balance each change. Thus the initial fiber belongs to one component. Across an edge between nonleaves every assignment on the far side has a neighbor on the near side. All nonleaves of the ladder base form a connected subgraph, and the leaf assignment extends at its nonleaf neighbor. This proves connectedness.

Set $r=2$ and choose $s$ proportional to $N$ within the vertex bound. Every single binary residue of width at most $s-1$ agrees for this nonisomorphic pair. More generally any fixed finite palette of primes requires linear precision in the worst case on a connected bounded-degree, bounded-pathwidth class whose constants may depend on the palette: take $r$ their product, and observe that every palette-supported modulus at most $2^{s-1}$ divides $r^{s-1}$.

## Relation to earlier work

The cycle-space multiplicity in the binary construction has a direct antecedent. Curticapean uses two colorful CFI targets with normalization $2^{|E|-|V|+1}$, and evaluates the signed count on the base. The modular Lovász principle and reductions by automorphisms of prime order also precede this work. The claims here concern the precise comparison of measurement policies on one sparse *uncolored* graph class and the exact gcd argument for finite abelian charges on rigid bases. Priority for this combination has not been established. [Curticapean, Lemma 3.1](https://arxiv.org/abs/2305.04767) · [Faben and Jerrum](https://arxiv.org/abs/1309.4033) · [Roberson on CFI constructions and homomorphism indistinguishability](https://arxiv.org/abs/2206.10321)
