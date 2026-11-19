# The degree threshold for modular homomorphism probes

Fix a maximum degree $\Delta\ge3$ and a nonempty finite set $S$ of primes. A probe specifies an arbitrary finite simple uncolored graph $F$ and an integer $m>1$ supported on $S$. It returns $\operatorname{hom}(F,G)$ modulo $m$ for each of two hidden connected simple uncolored targets of the same known order $n\le N$ and maximum degree at most $\Delta$. Charge the maximum answer width $\lceil\log_2 m\rceil$ used. Probe size, computation and the number of queries are unrestricted. Define $W_{\Delta,S}(N)$ as the minimum worst-case width for deciding isomorphism. Put

$$k=\#\{p\in S:p\ge\Delta\}.$$

**Theorem.** If $k=0$, then $W_{\Delta,S}(N)=\Theta_{\Delta,S}(N)$. If $k>0$, then

$$W_{\Delta,S}(N)=\frac{\log_2 N}{k}+O_{\Delta,S}(1).$$

The upper bounds allow all connected targets. All lower bounds have witnesses of bounded pathwidth depending only on the fixed parameters, and apply to adaptive queries and compound moduli. The borderline prime $p=\Delta$ belongs to the logarithmic regime. Binary probes already require linear precision at degree three. The theorem concerns precision, even when obtaining each residue is free.

## Upper bounds from point stabilizers

For equal-order nonisomorphic $G,H$, the number of induced embeddings of $G$ into the two targets is $|\operatorname{Aut}G|$ and zero. Inclusion-exclusion first on nonedges and then on identified vertices expresses this count as an integral combination of homomorphism counts from graphs of order at most $n$. Loops contribute zero. Hence one can separate the targets by enumerating such probes modulo any integer not dividing $|\operatorname{Aut}G|$. Any fixed prime $p\in S$ with exponent $1+v_p(n!)$ suffices, which gives linear width.

Take $p\ge\Delta$ and a Sylow $p$-subgroup $P$ of $\operatorname{Aut}G$. The stabilizer $P_v$ of a vertex acts faithfully on its neighbors. Indeed, the kernel fixes the vertex and all its neighbors. Once it fixes a vertex and one of its neighbors, it acts on at most $\Delta-1<p$ remaining neighbors. Every such action of a $p$-group is trivial. Induct outwards using connectedness. Consequently $|P_v|$ divides the $p$-part of $\Delta!$. Each $P$-orbit has size $|P|/|P_v|$. Summing all orbit sizes shows

$$v_p(|\operatorname{Aut}G|)\le v_p(n)+v_p(\Delta!).$$

For the $k$ primes $p\ge\Delta$ in $S$, the sum of $v_p(n)\log_2 p$ is at most $\log_2 n$. Choose a prime minimizing this summand and take exponent $v_p(n)+v_p(\Delta!)+1$. The modulus depends only on the common order and the fixed parameters and gives the asserted upper bound.

## Lower bound with only large primes

Write $Q=\{p\in S:p\ge\Delta\}$. For $Q=S$, take $L$ to be the product of $p^{\lfloor\log_p(N/2)/k\rfloor}$ over $p\in Q$, and assume $N$ sufficiently large that $L\ge4$. Compare the prism $C_L\square K_2$ and the cycle $C_{2L}$ augmented by the antipodal matching. They are cubic and exactly one is bipartite. Both admit a free cyclic vertex action of order $L$ (on the augmented cycle rotate by two). Thus both Hom counts from any nonempty probe are zero modulo $L$. Empty probe counts agree as well. Any $S$-supported modulus smaller than $\min_{p\in Q} p^{1+v_p(L)}$ divides $L$. The logarithm of this minimum is at least $\log_2(N/2)/k$. Both targets have pathwidth at most five by retaining the first matching pair and two consecutive pairs in each bag.

## A bounded-valence flow construction that hides all small primes at once

Suppose $T=S\setminus Q$ is nonempty. Put $r=\prod_{p\in T}p$ and $A=\mathbb Z/r\mathbb Z$. Pick a subgroup chain $0=A_0<A_1<\cdots<A_h=A$ whose successive indices belong to $T$. Let the base $B=C_L\square K_2$ have coherently oriented circular rails and rungs oriented top to bottom. Assign rotation-invariant cyclic orders to the three incidences at each base vertex. A charge $\alpha:V(B)\to A$ specifies the target below. Compare charge zero with charge one at each top vertex and zero at each bottom vertex. Choose $L$ coprime to $r$ so the second charge has nonzero total.

* Above a site $v$ put all triples of edge values with signed incidence sum $\alpha(v)$. There are $r^2$. For each of its three incidences $e$, write $e'$ for the next edge at $v$.
* The port at $(v,e)$ has nodes labelled $(x,y+A_j)$ at each level $j=0,\ldots,h$, with $x\in A$ and $y+A_j\in A/A_j$. Join levels by their natural quotient maps. Join the site triple to the leaf $(x_e,x_{e'}+A_0)$. At level $h$ only $x$ remains. Join the two level-$h$ nodes with the same $x$ on opposite ends of a base edge.

These are ordinary uncolored graphs. A level-zero node has one site neighbor since specifying two coordinates determines the third. An internal node has at most $\max T$ children and one parent. The top node has its children and one neighbor across the base edge. The degree bound is therefore $\max(3,1+\max T)\le\Delta$. This use of cosets is essential when $r$ itself exceeds the degree cap.

Every site fiber is connected inside its surrounding port trees. For any chosen first coordinate $x_e$, all triples sharing it reach the same top node. Differences of triples sharing their first coordinate and differences sharing their second generate the whole signed-zero-sum subgroup of $A^3$, as the third coordinate can balance either change. Every port node reaches a site, and the links across the connected base then connect the whole target. The two graphs have identical order $C_T L$ for a constant $C_T$ independent of charge and $L$. For example, if $b=r^2+3r\sum_j|A/A_j|$, there are $b$ vertices per base site and $C_T=2b$. Replacing each base vertex of a width-five path decomposition by its site and three entire ports gives pathwidth at most $6b-1$.

## Why arbitrary uncolored probes cannot bypass the construction

Forgetting the data coordinates gives a homomorphism from each target to the same graph $D$, obtained by replacing each edge of $B$ by a path of length $2h+3$. For any probe $F$, sort its maps to a target by their composite $f:F\to D$.

If $f$ misses a base site, compensate the entire charge difference at that site to give a charge of total zero. A spanning-tree calculation gives edge values $z$ with this corrected boundary. Addition by $z$ on site triples, and by $(z_e,z_{e'}+A_j)$ on the port nodes, bijects the lifts of $f$: the compensation at the absent site is never read.

If $f$ meets every base site, the zero-boundary edge assignments act freely on each lift set. A translation fixing a lift must vanish on every edge read at every site. There are $r^\beta$ such assignments, where $\beta=|E(B)|-|V(B)|+1=L+1$: prescribe off-tree edges freely, then extend uniquely along a spanning tree. Thus for every $F$ the difference is divisible by $r^{L+1}$. In addition, both targets admit a free vertex rotation of order $L$, since orientations, incidence orders and charges are rotation-invariant. Both counts from nonempty probes are multiples of $L$. Coprimality gives divisibility of every difference by $Lr^{L+1}$.

The targets really are nonisomorphic. For fixed $f$, its lifts solve equations in a product of finite abelian groups: site boundary conditions, equality of edge labels, and compatibility with coset projection. Every nonempty inhomogeneous solution set is a coset of the homogeneous kernel. Hence the zero-charge target always has at least as many lifts as the charged target. Take $F=D$. For $f$ the identity, lifts are precisely global edge assignments with the prescribed boundary, of which there are $r^\beta$ for zero total and none for the nonzero total. The total uncolored Hom-count difference is strictly positive. This argument requires no assumptions about automorphisms respecting the ports.

## Selecting the order

If $k=0$, take $L\equiv1\pmod r$ as large as possible with $C_T L\le N$. Every $S$-supported modulus below $2^{L+1}$ divides $r^{L+1}$. This proves linear necessity for arbitrarily large order caps.

If $k>0$, set $X=N/C_T$ and take

$$L=\prod_{p\in Q}p^{\lfloor(\log_p X)/k\rfloor}.$$

Then $X/\prod_{p\in Q}p<L\le X$ and $L$ is coprime to $r$. Every $S$-supported modulus at most $X^{1/k}$ divides $Lr^{L+1}$ once $N$ is large. At large primes its valuation is covered by $L$, while at small primes it is $O_S(\log N)$ and is covered by $r^{L+1}$. Every query below this width has the same transcript on the distinct targets as on an identical pair. This proves the lower bound including its leading constant.

## Context

Previous results gave three precision scales at one degree cap. The sharper point here is the exact boundary between primes and the degree, including equality, and the coefficient $1/k$ even when the algorithm can mix arbitrarily many copies of every small prime into composite moduli. The construction adapts CFI-type charged fibers by resolving their incidence stars into successive prime-index cosets. Bounded-valence automorphism groups, modular Hom invariance, and the binary cycle-space multiplicity all have prior sources. Priority for the palette theorem has not been established. [Luks](https://ix.cs.uoregon.edu/~luks/iso.pdf) · [Faben and Jerrum](https://arxiv.org/abs/1309.4033) · [Curticapean](https://arxiv.org/abs/2305.04767)
