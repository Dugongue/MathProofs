# Two-cut chromatic symmetric reconstruction of separated diameter-six trees

## GP-0873

Root a diameter-six tree $T$ at its unique center. Let $B_1,\ldots,B_d$ be the sizes of the branches starting at its children, and let $B_{\max}=\max_i B_i$. Suppose that for some integer $K\ge 1$ the $B_i$ are distinct, all exceed $2K$, all subtrees starting at depth two have size at most $K$, and $B_{\max}+K<n/2$. The coefficients of the power-sum terms of lengths two and three in $X_T$, together with $n$, distinguish $T$ from every other tree. No diameter, separation, or branch-size hypothesis is imposed on the competing tree. Depth-two subtree sizes of $T$ can repeat arbitrarily subject to its stated assumptions. [Zeng, diameter-six reconstruction problem and a star-basis result](https://arxiv.org/abs/2608.18179)

## Cut coefficients and centroids

Let $a(\lambda)$ be the number of edge deletions whose component-size partition is $\lambda$. Inclusion-exclusion gives $X_T=\sum_\lambda(-1)^{n-\ell(\lambda)}a(\lambda)p_\lambda$: select the edges whose endpoints are required to have the same color, and each component of the selected forest contributes a single power sum. A partition of length $\ell(\lambda)$ corresponds to $\ell(\lambda)-1$ deletions. [Gonzalez, Orellana and Tomba, tree reconstruction and chromatic symmetric functions](https://arxiv.org/abs/2507.15986)

Suppose a competing tree $T'$ has the same displayed data. Every edge split in $T$ has smaller side at most $B_{\max}<n/2$, so there is no equal split in $T'$ either. Root $T'$ at its unique centroid, namely the vertex whose deletion leaves components of size at most $n/2$. For either rooted tree, call the size on the far side of a directed edge its descendant size. All descendant sizes are less than $n/2$, since a centroid is used in $T'$ and the center of $T$ also meets the centroid size condition. The length-two coefficients give the common histogram $h(s)$ of descendant sizes by selecting the smaller part. Call an edge large if its descendant size exceeds $K$, and small otherwise. The large sizes are exactly the $B_i$, each occurring once in either tree.

## The large edges are forced to be disjoint

If a pair of deletions with descendant sizes $u,v$ is disjoint in the rooted tree, its partition is $\{u,v,n-u-v\}$. For any partition $\lambda$ with three parts greater than $K$, the histogram gives the number $D(\lambda)$ of unordered large-edge pairs with this prospective disjoint partition. In $T$ every large edge is a top edge, and any cut using at least one small edge has at least one small component. Consequently $a(\lambda)=D(\lambda)$ for every such $\lambda$.

Process the large sizes $b$ in descending order. We claim that the edge of size $b$ in $T'$ is disjoint from every other large edge. For any such pair with sizes $b,u$, consider $\lambda=\{b,u,n-b-u\}$, all of whose parts exceed $K$ because $n-2B_{\max}>2K$. A nested pair contributing to $\lambda$ has partition $\{v,w-v,n-w\}$, with inner size $v$ and outer size $w>v$. Both edges are large, since $v>K$. Its root component is $n-w>n/2>b$, so $b$ would have to be $v$ or $w-v$, and in either case $w>b$. By induction the outer edge of size $w$ is already disjoint from all other large edges. The first step has no larger size at all. Thus no nested pair can contribute to this $\lambda$. Since $a(\lambda)=D(\lambda)$, every prospective disjoint pair for $\lambda$ must in fact be disjoint, including the chosen pair. This completes the induction. The large edges in $T'$ therefore start at the root, since an ancestor of a large edge would have a strictly larger size.

## The small descendant subtrees are forced to be stars

For the unordered pairs of small edges, the histogram determines the sum $S_0$ of their two descendant sizes over all such pairs. In either tree the actual sum $S$ of the two small parts over the observed three-part partitions having two small parts is recoverable from $a(\lambda)$. These partitions arise exactly from pairs of small edges. Indeed the root component for two small edges is larger than $K$, two large edges are now known to be disjoint, and a large edge nested with a small one leaves a branch piece of size greater than $K$ since the large size exceeds $2K$. A disjoint pair contributes the same amount to $S$ and $S_0$. A nested pair of small edges with inner size $v$ and outer size $w$ contributes $v+(w-v)=w$ to $S$ and $v+w$ to $S_0$. So $S_0-S$ is the sum of inner sizes over nested small pairs.

For each outer small edge of size $w$, there are exactly $w-1$ inner edges in its descendant subtree, each of size at least one. Thus $S_0-S\ge\sum_{w\le K}h(w)(w-1)$, with equality precisely when every outer small descendant subtree is a star rooted at its first vertex. Equality holds in $T$ because its height is three and its small edges start below the top level. It follows in $T'$ as well, since all quantities are shared.

## Assigning the stars to branches

For $1\le a\le K$ and $K<b\le B_{\max}$, let $F_a(b)$ denote the observed deletion count for $\{a,b,n-a-b\}$. The third part exceeds $n/2$. Write $N_a(b)$ for the number of edges of descendant size $a$ beneath a top edge of size $b$, and set it to zero when $b$ is not a top size. Only a small plus a large deletion can have this partition. Among the $h(a)h(b)$ candidate pairs of these sizes, $N_a(b)$ are nested and must be subtracted. A nested pair does contribute if its upper branch piece has size $b$, so its top edge originally has size $b+a$. Therefore
$$
F_a(b)=h(a)h(b)-N_a(b)+N_a(b+a).
$$
Starting with zero above $B_{\max}$, downward recursion recovers all $N_a(b)$ for large $b$. Since in $T$ every small edge is beneath a large one, $\sum_{b>K}N_a(b)=h(a)$, forcing the same in $T'$. This excludes all additional small root branches.

For $a\ge2$, $N_a(B_i)$ counts the child stars of size $a$ in branch $i$, since deeper edges of star subtrees have size one. The number of singleton children in branch $i$ is $B_i-1-\sum_{a=2}^K aN_a(B_i)$. This determines every centered branch and proves the claimed reconstruction. The full chromatic symmetric function also distinguishes $T$ from a competing simple graph: the coefficient of $p_{2,1^{n-2}}$ gives the edge count up to sign, and a nonzero coefficient of $p_n$ requires a connected spanning subgraph. A competitor would thus be a tree with $n-1$ edges.

For an infinite family with repeated nonsingleton stars, take any $K\ge 3$ and five branches of sizes $3K+i$ for $1\le i\le 5$. Give each branch root two depth-two child stars of size two and fill the remaining positions with leaf children. All five branches reach depth three, and $B_{\max}+K=4K+5<(15K+16)/2=n/2$.
