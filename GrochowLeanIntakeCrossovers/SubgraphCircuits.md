# Symbolic subgraph circuits on hosts of bounded cut rank

## Theorem

Let $H$ be a simple graph on $k$ vertices with $m$ edges. Define $\rho_3(H)$ as the largest number of edges crossing a partition of its vertices into three possibly empty parts. Let $T$ be a rooted binary tree with $n$ leaves, one per host vertex. For each internal node with children $A,B$, supply a matrix $C_{A,B}$ of size $r\times r$. For each child $A$, supply a transfer matrix $M_A$ of the same size, and give each leaf $i$ a row $U_i$ of length $r\ge 1$. Treat these entries as independent indeterminates over a field $K$, or substitute any elements from a commutative $K$-algebra. The matrices specify a symmetric weighted host off the diagonal by the rules below.

The sum of the edge monomials over all injective maps from $H$ into the host has a uniform arithmetic circuit of size

$$
O\bigl(n\,3^k(m+1)r^{\rho_3(H)+1}\bigr).
$$

The same bound includes arbitrary pattern-vertex-specific host weights, with one additional factor per image vertex. Grochow–Urisman's subgraph polynomial $S_H$ counts distinct edge monomials. For that polynomial delete isolated vertices from $H$, set the optional weights to one, and divide by the order of the resulting pattern's automorphism group in a field where that order is invertible. Each edge image then comes from exactly that many injections, and any placement of the nonisolated vertices extends to the isolated vertices when $k\le n$. When $k>n$ the original polynomial is zero. The unrestricted adjacency-variable circuit-size question remains open. [Grochow–Urisman, Question 1.11 and §3.3](https://arxiv.org/html/2606.26244v2#S1.SS3)

Every symmetric host matrix whose cuts along $T$ have rank at most $r$ over $K$ admits this parametrization. It follows that the theorem covers adjacency matrices of binary rank width at most $w$, including their exact characteristic-zero counts, with $r=2^w$ and a supplied rank decomposition. The algorithm also computes the symbolic induced-copy polynomial, with the original isolated vertices retained and division by the automorphism-group order of the original pattern. Its bound replaces $m,\rho_3(H),r$ by $\binom{k}{2},\rho_3(K_k),r+1$. The labeled, optionally vertex-weighted versions work over any commutative ring.

## Host coordinates

Identify each tree node with its cluster of leaves. Recursively define the row matrices $U_S$, starting with the leaf data. If $S=A\sqcup B$, define $U_S|_A=U_A M_A$ and $U_S|_B=U_B M_B$. Define $W[A,B]=U_A C_{A,B}U_B^{\mathsf T}$ for the sibling cut at $S$, and transpose for $W[B,A]$. Each off-diagonal entry is specified exactly once, at the least common ancestor of its endpoints. Every column of $W[S,V\setminus S]$ is a linear combination of $U_S$'s columns using the transfers up to the applicable ancestor. These are symbolic substitution rules. The circuit below never expands the full host matrix.

Conversely, let $W$ have cut rank at most $r$ at each tree node. Before padding to width $r$, take $U_S$ to be any column basis for $W[S,V\setminus S]$. Each column of $U_S|_A$ lies in the column span of $W[A,V\setminus A]$, since $V\setminus S\subseteq V\setminus A$. Thus $U_S|_A=U_A M_A$, and the same holds for $B$. The column span of $W[A,B]$ is contained in that of $U_A$, and its row span is contained in the transpose of the span of $U_B$, by symmetry. If $L_A,L_B$ are respective left inverses, then $C_{A,B}=L_A W[A,B]L_B^{\mathsf T}$ works. Padding all bases and coefficient charts with zeros gives width $r$. This construction from a dense $W$ costs polynomial time by elimination. The linear dependence on $n$ in the theorem concerns the circuit on the supplied factor coordinates.

For a graph adjacency cut of binary rank at most $w$, each of its rows is one of at most $2^w$ distinct binary vectors. This bounds its rank by $2^w$ over any field. Rooting a subcubic rank-decomposition tree by subdividing an edge preserves its cuts.

## Boundary tables

For $P\subseteq V(H)$, write $\partial P$ for pattern edges with exactly one endpoint in $P$. If $e\in\partial P$, write $u_e\$ for that endpoint. At cluster $S$, we keep one tensor $F_S(P)$ with an index $a_e\in[r]$ for each $e\in\partial P$. Its entry is

$$
\sum_{f:P\hookrightarrow S}
\left(\prod_{u\in P}w_{u,f(u)}\right)
\left(\prod_{uv\in E(H[P])}W_{f(u),f(v)}\right)
\left(\prod_{e\in\partial P} U_S[f(u_e),a_e]\right).
$$

For a singleton host cluster the values for $P=\varnothing$, $P=\{u\}$, and $\lvert P\rvert>1$ are respectively one, the prescribed leaf-row products times $w_{u,i}$, and zero. At the root choose $P=V(H)$, whose boundary is empty.

At a merge fix a split $P=P_A\sqcup P_B$ and put $Q=V(H)\setminus P$. A parent injection restricts uniquely to independent injections of $P_A\$ into $A$ and $P_B\$ into $B$. On each index for an edge from $P_A$ to $Q$, multiply the left table in that mode by the transfer $M_A$, replacing the child index by the parent index. Do the analogous transfers on the right. For each edge from $P_A$ to $P_B$, apply $C_{A,B}$ to the left index to put it in the coordinates of the right index. Contract the transformed tensors by summing over their matching $P_A\$–$P_B\$ indices. The result is the contribution of this split. Sum over all splits to obtain $F_S(P)$.

Indeed, expanding the contraction installs a factor $\sum_{b,d}U_A[f(u),b]C_{A,B}[b,d]U_B[f(v),d]$ on each crossing pattern edge, which is $W_{f(u),f(v)}$. Each external edge installs the corresponding $U_A M_A$ or $U_B M_B$ factor, namely the required $U_S$ entry. Every remaining factor already appears in exactly one child. Finite distributivity allows regrouping the sums, and the injection decomposition counts each map exactly once. This establishes the boundary invariant by induction.

Let $a,b,c$ count edges between $P_A,Q$, $P_B,Q$, and $P_A,P_B$, respectively. Transforming one mode of an order-$d$ tensor costs $O(r^{d+1})$, applying an $r\times r$ matrix to each of the $r^{d-1}$ fibers. The child orders are $a+c$ and $b+c$. The final contraction costs $O(r^{a+b+c})$. Since $a+b+c\le\rho_3(H)$, each split uses $O((m+1)r^{\rho_3(H)+1})$ gates including its addition into the parent. There are $3^k$ disjoint assignments of pattern vertices to $P_A,P_B,Q$. The leaf initialization fits the same bound, giving the stated circuit size.

For induced copies, put an interaction edge on every pattern pair. Use $W$ on original edges, and $1-W$ on original nonedges. Append the constant column one to each row chart, extend transfers by a diagonal $1$, and use the padded block matrix $\operatorname{diag}(C,0)$ or $\operatorname{diag}(-C,1)$ on each sibling interaction according to the pair type. This evaluates the standard induced-copy polynomial with the same boundary invariant.

## Imported contraction and scope

The November intake's TNLean graph-contraction work supplies the construction model for the merge. In the pinned module TNLean.PEPS.GraphOpenRegionContraction, the declaration TNLean.PEPS.graphOpenRegionNetwork_eq_sum_internal expresses the open-region network as a sum of products over internal indices with boundary indices held fixed. Here the pattern placement tables play the role of the two open-region tensors and the mode transfers reconcile their boundary coordinates. The argument above derives its own finite identity over a commutative ring. The pinned TNLean source is a separate environment. [Pinned TNLean graph contraction](https://github.com/LionSR/TNLean/blob/447d52333f9238c7fc2370b9ea9756835024082c/TNLean/PEPS/GraphOpenRegionContraction.lean#L90)

Weighted symbolic circuits with dense low-rank cuts are the result here. Fixed-parameter evaluation for ordinary bounded-clique-width hosts already follows from MSO enumeration, a separate numerical host-graph result. [Courcelle, Makowsky, and Rotics, graph enumeration in MSO](https://doi.org/10.1016/S0166-218X(00)00259-4)

The companion checker compares the recurrence against direct weighted injection sums in 144 finite cases, including induced interactions. The accompanying Lean source kernel-checks the expansion of the crossing-edge indices over commutative semirings. The complexity theorem and injection decomposition have an informal proof. [Checker](check_subgraph_circuits.py) · [Lean source](CutContraction.lean)
