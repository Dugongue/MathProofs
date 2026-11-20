# GP139 — Restriction and degeneration on complete uniform tensor networks

**Theorem.** Fix an order $k\ge 2$ and two nonzero complex $k$-tensors $T,S$. For the complete $k$-uniform hypergraph on $N$ vertices, let $a_{\mathrm R}(N)$ and $a_{\mathrm D}(N)$ be the least dimensions of a global GHZ tensor that permit restriction or degeneration, respectively, from its $T$-network to its $S$-network. Write $E_N$ for the number of edges. Then both limits below exist and satisfy
$$
\lim_{N\to\infty}\frac{\log_2 a_{\mathrm R}(N)}{E_N}
=
\lim_{N\to\infty}\frac{\log_2 a_{\mathrm D}(N)}{E_N}
=
\inf_{s\ge k}\frac{\log_2 a_{\mathrm D}(s)}{E_s}.
$$
This holds when each edge has increasing vertex order and when each ordered orientation appears once. In particular the two preorders with GHZ dimension $2^{o(E_N)}$ coincide, which answers catalog question GP139 in Christandl's edge-count normalization. The same rate equality holds for the sequence of balanced blow-ups of every fixed finite ordered $k$-uniform hypergraph with at least one edge, with the infimum over positive block sizes.

Christandl places one copy of the tensor on each ordered edge and groups together its legs incident at the same vertex, producing one party per vertex. The restriction maps are linear maps at the vertices. The degeneration maps are polynomial one-parameter local maps whose first nonzero output coefficient is the intended target. A global $\operatorname{GHZ}_a$ supplies, at every vertex, an index shared across all vertices and ranging from $1$ to $a$. The assistance dimensions are finite. One can contract each resource copy $T$ to a nonzero scalar and then generate $S$ from a GHZ tensor of dimension equal to its ordinary tensor rank for each edge. [Christandl's model, Definition 8, and Open Problem 3](https://doi.org/10.1093/pnasnexus/pgae254)

## 1. Synchronous interpolation on packed blocks

Suppose a host $H_N$ has $\nu$ edge-disjoint copies of one fixed smaller hypergraph $H_s$, with $r=E_N-\nu E_s$ edges left over. The copies may share vertices. Choose local maps witnessing a degeneration on $H_s$ with auxiliary dimension $a=a_{\mathrm D}(s)$. Their output polynomial has the form
$$
z^d\left(S_{H_s}+zU_1+\cdots+z^D U_D\right)
$$
for some finite $d,D$. On the disjoint union of $\nu$ copies, use the same variable $z$ for all maps. After normalization by $z^{\nu d}$ the output polynomial has degree at most $\nu D$. Its constant term is the disjoint union target. Evaluate at $\nu D+1$ distinct nonzero complex scalars and take a fixed linear combination using Vandermonde interpolation. This converts the whole degeneration to an exact restriction. Each evaluation gives a tuple of local maps. Store the common evaluation index in an additional global GHZ tensor of dimension $\nu D+1$, and include the interpolation scalar at a single fixed vertex.

The global GHZ index can carry independently chosen labels for every copy, with exactly $a^\nu$ choices. At a vertex, the local map reads the copy labels for copies incident there and takes the tensor product of their separate local maps. Such copying and projection of the index basis implements the tensor product of GHZ tensors over the different vertex subsets, even with overlapping subsets. The same applies to target preparation on the $r$ uncovered edges. On each uncovered edge contract $T$ with product covectors to 1 and prepare $S$ from a rank decomposition of length $R(S)$. All these maps can be applied at the original vertices by grouping the relevant legs. The resulting explicit bound is
$$
a_{\mathrm R}(N)\le
a_{\mathrm D}(s)^\nu\,(\nu D+1)\,R(S)^r.
$$
The interpolation degree overhead is additive in the number of copies before taking the logarithm. An independent interpolation label for each block would have yielded a different rate.

Assume, for every fixed $s$ in an infinite set of block sizes, that such packings leave $r/E_N\to 0$ as $N\to\infty$. Assume also that $E_N\to\infty$. For each such $s$, the displayed bound implies
$$
\limsup_{N\to\infty}\frac{\log_2 a_{\mathrm R}(N)}{E_N}
\le \frac{\log_2 a_{\mathrm D}(s)}{E_s},
$$
since $D$ is fixed and $\nu\le E_N/E_s$. The proof fixes the block size before passing to large $N$. It requires no quantitative estimate for the error degree as the block size grows. In the two sequences below every block size with at least one edge qualifies. The inequalities
$$
\limsup_N\frac{\log_2 a_{\mathrm R}(N)}{E_N}
\le
\inf_s \frac{\log_2 a_{\mathrm D}(s)}{E_s}
\le
\liminf_N\frac{\log_2 a_{\mathrm D}(N)}{E_N}
\le
\limsup_N\frac{\log_2 a_{\mathrm R}(N)}{E_N}
$$
then prove the theorem and the existence of both limits. The last inequality follows from $a_{\mathrm D}(N)\le a_{\mathrm R}(N)$.

## 2. Complete uniform hypergraphs

For each fixed $s>k$, Rödl's packing theorem gives a family of $s$-subsets of $[N]$ of size
$$
(1-o(1))\,\frac{\binom Nk}{\binom sk}
$$
such that any two selected subsets intersect in fewer than $k$ vertices. Therefore the copies of the complete $s$-vertex hypergraph supported on these subsets are edge-disjoint and cover a $1-o(1)$ proportion of the host edges. Increasing embeddings preserve the edge order in the increasing convention. In the all-orientations convention the same block covers every orientation of each of its covered subsets. For $s=k$ the individual edges or orientation bundles give an exact packing. This supplies all the fixed block sizes used above. [Rödl, On a Packing and Covering Problem](https://doi.org/10.1016/S0195-6698(85)80023-8)

## 3. Balanced blow-ups of any fixed ordered hypergraph

Fix a finite ordered $k$-uniform hypergraph $F$, with distinct vertices within each edge and at least one edge. Replace every vertex by a part of size $N$. Each original edge induces all choices of one new vertex at each of its positions, with the given ordering. The resulting $F[N]$ has $|E(F)|N^k$ edges. Parallel edges of $F$ can be carried with their original identities.

For fixed $s$ and large $N$, select an integer $q\le \lfloor N/s\rfloor$ congruent to 1 modulo $|V(F)|!$, with $\lfloor N/s\rfloor-q<|V(F)|!$. In each part keep $q$ cells of size $s$, indexed by $\mathbb Z/q\mathbb Z$. Assign distinct integers from $0$ through $|V(F)|-1$ as points $a_v$ for the base vertices. Their pairwise differences are units modulo $q$.

For every polynomial $P$ over $\mathbb Z/q\mathbb Z$ with degree less than $k$, select cell $P(a_v)$ at part $v$. This selects a copy of $F[s]$. For a given original edge and any prescribed list of cells in its positions, the Vandermonde determinant is a unit, so there is exactly one such $P$ realizing those cell choices. Consequently these copies partition the edges entirely in retained cells. The uncovered count is
$$
|E(F)|\bigl(N^k-(qs)^k\bigr)=O_{F,s,k}(N^{k-1}).
$$
This is a vanishing fraction and supplies the fixed-block condition, using only finite-ring interpolation. Complete multipartite uniform networks are an example.

## 4. Stability under edge edits and unequal part sizes

For ordered hypergraphs $G,H$ on the same vertex set, let $G\setminus H$ and $H\setminus G$ count edge differences with multiplicity. For either assistance parameter $a_\star$ we have
$$
a_\star(H)\le a_\star(G)R(T)^{|G\setminus H|}R(S)^{|H\setminus G|}.
$$
First contract away the copies of $T$ on $H\setminus G$, then prepare copies of $T$ on $G\setminus H$ using rank decompositions. Apply the transformation on $G$ and contract away the copies of $S$ on $G\setminus H$. Prepare copies of $S$ on $H\setminus G$. Contractions use product covectors normalized to give 1 on each nonzero designated edge tensor. Preparation and all shared labels work as in Section 1. For a degeneration the extra maps are constant in the parameter and leave the leading coefficient equal to the desired tensor. Exchanging $G$ and $H$ shows
$$
\left|\log_2 a_\star(H)-\log_2 a_\star(G)\right|
\le C |E(H)\mathbin{\triangle} E(G)|,
\qquad C=\max\{\log_2 R(T),\log_2 R(S)\}.
$$
Isolated vertices may be added to place both networks on a common vertex set. Adding such a party leaves the assistance dimension unchanged because it can sum all the GHZ indices, and any scalar output coefficient at the extra party can be absorbed at another vertex.

Now give each part $v$ of a fixed motif $F$ a possibly different size $n_v(N)$, with $n_v(N)/N\to p_v\ge 0$. Suppose $\sum_{e\in E(F)}\prod_{v\in e}p_v>0$. For rational approximations $q_v=c_v/d$ to the $p_v$, compare with the blow-up having part sizes $c_v\lfloor N/d\rfloor$. The rational comparison is a balanced blow-up of a fixed larger motif obtained by replacing each vertex $v$ first by $c_v$ clones. For fixed $q$, Section 3 gives a common limit for both log assistance dimensions divided by $N^k$, since its number of edges divided by $N^k$ has a limit as well.

Nest the two versions of each vertex part in a common set. For a fixed labeled edge of $F$, every edge in the symmetric difference has some vertex in the difference of its two parts. Since each part size is $O(N)$, the edge-edit count is bounded by $O_F(N^{k-1})\sum_v |n_v(N)-c_v\lfloor N/d\rfloor|$, with a uniform constant for $q$ in a bounded neighborhood of $p$. The stability bound and the common limit for the rational comparison give
$$
\limsup_N \frac{\log_2 a_{\mathrm R}(H_N)}{N^k}
-\liminf_N \frac{\log_2 a_{\mathrm D}(H_N)}{N^k}
\le O_{F,T,S,p}(\|p-q\|_1).
$$
Letting $q\to p$ shows both limits coincide and exist. Dividing by the positive limiting edge density establishes the same per-edge rate equality for these unequal blow-ups. The edge-edit bound also transfers the conclusions about existence and equality of rates to sequences differing from any of these dense families by $o(N^k)$ ordered edge edits.
## Further scope

With a scalar resource $T=1$, the two assistance dimensions are the ordinary tensor rank and border rank of the network tensor $S_{H_N}$. Their logarithms per edge have the same limit, which gives asymptotic rank–border rank equality for these dense families. Zero tensors in the preorder are immediate by zero maps or the fact that an all-zero resource cannot yield a nonzero target.

The result controls the number of global GHZ labels relative to the number of edges. A bound of $2^{o(N)}$ with $N$ the number of vertices would be stronger for these dense families. Arbitrary dense hypergraph sequences remain outside the theorem. The proof is written and relies on the cited packing theorem. No claim is made that the packing theorem or Christandl's entropy accounting is new.
