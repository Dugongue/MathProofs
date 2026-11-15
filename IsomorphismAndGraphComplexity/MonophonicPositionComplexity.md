# Monophonic Position Set is Theta-two-P-complete

Thomas, Chandran, Tuite and Di Stefano proved NP-hardness for Monophonic Position Set and left open whether the unrestricted problem is NP-complete. The 2026 survey repeats this question. We prove that the problem is $\Theta_2^{\mathrm P}$-complete under polynomial-time many-one reductions, even on graphs of diameter exactly two. Consequently the unrestricted problem is NP-complete if and only if $\mathrm{NP}=\mathrm{coNP}$. [Thomas et al., Section 6](https://doi.org/10.1016/j.dam.2023.02.021) · [Chandran–Klavžar–Tuite survey, Section 4.1](https://arxiv.org/html/2501.19385v5#S4.SS1)

## Definitions and the parallel-query upper bound

All graphs are finite, simple and undirected. A path is induced if no two of its nonconsecutive vertices are adjacent. A vertex set is in monophonic position if every induced path meets it in at most two vertices. The maximum size of such a set in a graph $G$ is $\operatorname{mp}(G)$. The decision problem asks whether $\operatorname{mp}(G)\ge k$, given $G$ and $1\le k\le |V(G)|$. We use the characterization of $\Theta_2^{\mathrm P}$ as deterministic polynomial time with a polynomial number of nonadaptive NP queries. [Hemaspaandra–Spakowski–Vogel, Section 3](https://doi.org/10.1016/j.tcs.2005.08.031)

Call an unordered triple $B$ of vertices bad if some induced path contains $B$. Write $p$ for the total number of bad triples. Given $k$, let $q$ be the maximum, over $S\subseteq V(G)$ with $|S|\ge k$, of the number of bad triples $B$ with $B\nsubseteq S$. We have $q\le p$, with equality exactly when there exists a monophonic position set of size at least $k$.

For every $t=0,\ldots,\binom{|V(G)|}{3}$, ask whether $p\ge t$ and whether $q\ge t$. The first query is in NP by supplying $t$ distinct triples and an induced path witnessing each. The second query has the same witnesses, together with an $S$ of size at least $k$ that contains none of the supplied triples in full. Each path is an ordered list of distinct vertices, and all required edges, nonedges and containments can be checked in polynomial time. These two polynomial-size batches of queries can be submitted together, and the answers recover $p,q$ exactly. This proves membership in $\Theta_2^{\mathrm P}$.

## True-twin replacement and two graph constructions

Given a graph $G$, replace each vertex $v$ by a nonempty clique $C_v$. For distinct $v,w$ put all edges between $C_v,C_w$ if $vw\in E(G)$, and no edges otherwise. Any two distinct members of one $C_v$ are adjacent with identical neighbors outside their pair. If an induced path contains both, they must be consecutive. Any third vertex next to either of them along the path is adjacent to both and gives a chord. Consequently an induced path on at least three vertices projects to an induced path of $G$, using at most one member of each $C_v$. Conversely, an induced path of $G$ lifts to an induced path for every choice of representatives on it.

First consider a graph $D$ with three designated vertices $a,b,c$. Replace these three vertices by cliques of a common size $M$ and every other vertex by a singleton. Denote the result by $D_M$. Let $x=1$ if $D$ has an induced path through $a,b,c$ in any order, and set $x=0$ otherwise. If $x=0$, the union of the three marked cliques is in monophonic position by projection, contributing $3M$. If $x=1$, a monophonic position set cannot meet all three marked cliques, since the marked path lifts through any choice of three representatives. The union of any two marked cliques is in monophonic position, since an induced path on at least three vertices meets each clique at most once. Hence in both cases
$$
\operatorname{mp}(D_M)=M(3-x)+e,\qquad 0\le e\le |V(D)|-3. \tag{1}
$$
We use the NP-completeness of Three-in-a-Path with the three vertices in any order, which holds even for graphs of maximum degree three by Derhy and Picouleau's application of Bienstock's construction. [Fiala–Kamiński–Lidický–Paulusma, introduction](https://doi.org/10.4230/LIPIcs.STACS.2010.2469)

For the second construction, start with a graph $A$ and replace every vertex by a clique of size $M$, obtaining $A_M$. Every clique projects to a clique of $A$ and has at most $M$ vertices over each vertex of $A$, and a maximum clique of $A$ lifts to a clique of size $M\omega(A)$. Thus $\omega(A_M)=M\omega(A)$. Join $A_M$ to a clique on $s>|V(A_M)|$ new vertices, adjoining all edges between $A_M$ and the new clique. Denote this graph by $J$. A monophonic position set of maximum size must use a new vertex, since the new clique alone has size $s$. With a new vertex in the set, two nonadjacent old vertices would give an induced path of length two with that vertex in the middle. Thus its old vertices form a clique. The new clique together with a maximum clique of $A_M$ is itself a clique and is in monophonic position. We obtain
$$
\operatorname{mp}(J)=s+M\omega(A). \tag{2}
$$
The universal-clique join is the construction underlying Thomas et al.'s NP-hardness proof. [Thomas et al., Theorem 6.2](https://doi.org/10.1016/j.dam.2023.02.021)

## Many-one hardness on graphs of diameter two

The problem of deciding whether $\omega(A)\ge\omega(B)$ for graphs of equal order is $\Theta_2^{\mathrm P}$-complete under polynomial-time many-one reductions. Indeed, Spakowski and Vogel's Min Card Vertex Cover Compare is complete even with equal orders, as stated in Hemaspaandra–Spakowski–Vogel, Lemma 4.11. On equal-order graphs $G,H$, comparison of their minimum vertex cover sizes $\tau(G)\le\tau(H)$ is equivalent to comparison of $\omega(\overline G)\ge\omega(\overline H)$, by $\tau(G)=|V(G)|-\omega(\overline G)$. [Hemaspaandra–Spakowski–Vogel, Definition 4.10 and Lemma 4.11](https://doi.org/10.1016/j.tcs.2005.08.031)

Given $A,B$, let $b=|V(B)|$. For each $j=1,\ldots,b$, use a fixed polynomial-time many-one reduction from Clique to Three-in-a-Path on the input $(B,j)$, giving a graph $D_j$ with a specified triple. Since Three-in-a-Path is NP-complete, this is an ordinary polynomial-time transformation with no oracle calls. Its answer bit $x_j$ is one exactly when $j\le\omega(B)$, and $\sum_j x_j=\omega(B)$. Set
$$
M=3+\sum_{j=1}^{b} (|V(D_j)|-3),\qquad s=M|V(A)|+1.
$$
Construct $J$ from $A$ and construct $(D_j)_M$ for all $j$. Take their disjoint union $K$. Any path lies in one component, so the monophonic position number of a disjoint union is the sum over its terms. Equations (1) and (2) give
$$
\operatorname{mp}(K)=k+M(\omega(A)-\omega(B))+e,\qquad
k=s+3Mb,\qquad 0\le e\le M-3.
$$

To produce diameter exactly two, add a vertex $u$ adjacent to all of $K$ and a vertex $z$ adjacent only to $u$. Call the resulting graph $H$. The graph $K$ is nonempty because it contains the new clique in $J$. Thus $z$ and a vertex of $K$ are nonadjacent at distance two, and $u$ gives distance at most two for every pair. An induced path using $u$ has at most three vertices, so it contains at most two vertices of $K$. Any path using $z$ and any vertex of $K$ also uses $u$. This proves that a monophonic position set of $K$ remains valid in $H$. Conversely the restriction to $K$ of a monophonic position set of $H$ is valid in $K$ because the induced subgraph on $K$ is unchanged. Then
$$
\operatorname{mp}(K)\le\operatorname{mp}(H)\le\operatorname{mp}(K)+2.
$$
If $\omega(A)\ge\omega(B)$, then $\operatorname{mp}(H)\ge k$, including the equality case. If $\omega(A)<\omega(B)$, then $\operatorname{mp}(H)\le k-M+(M-3)+2=k-1$. The map $(A,B)\mapsto(H,k)$ is polynomial because the number and orders of the $D_j$, the clone multiplicity $M$, and the join size $s$ are all polynomial in the input length. All output graphs have diameter exactly two and $1\le k\le |V(H)|$. This proves the claimed $\Theta_2^{\mathrm P}$-hardness.

## Consequences for the published question

Because $\mathrm{coNP}\subseteq\Theta_2^{\mathrm P}$, NP membership of Monophonic Position Set would imply $\mathrm{NP}=\mathrm{coNP}$. Conversely, under $\mathrm{NP}=\mathrm{coNP}$, a proposed monophonic position set has a polynomial-size certificate of validity. Indeed invalidity is in NP because an induced path meeting the set in at least three vertices is a polynomial witness. Guessing the set and its validity certificate shows the existential decision problem belongs to NP in that case. Its NP-hardness follows from the completeness above, giving the exact equivalence about NP-completeness. The same argument applies to the diameter-two restriction. Validity of a supplied set is itself coNP-complete already for sets of size three, by complementing Three-in-a-Path.

The completeness classification is unconditional. The conclusion that the problem lies outside NP assumes the separation of NP and coNP. The cited 2026 survey records the earlier NP-hardness, including for diameter two, and parameterized hardness. Targeted searches for the exact problem alongside coNP-hardness, parallel access to NP and $\Theta_2^{\mathrm P}$-completeness did not locate a prior matching classification. This is an informal proof.
