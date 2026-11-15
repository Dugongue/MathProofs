# The sharp amount of symmetric-group padding needed to recover occurrences

Grochow and Urisman ask after Lemma 6.11(2) whether symmetric-group padding is reversible for occurrence sets. An earlier counterexample answered the unrestricted converse negatively. Here the sufficient threshold improves from $k-1$ to $k-2$, and the new threshold is exact for every even $k\ge4$. When the two subgroups are even, one recovers the original occurrence sets from much smaller padding.

## Theorem

For $H\le S_k$, write $O(H)$ for the set of partitions $\lambda\vdash k$ such that the corresponding complex Specht module has a nonzero $H$-fixed vector. For $m\ge0$, let $H\times S_m\le S_{k+m}$ act on disjoint blocks.

1. For all $k\ge2$ and $m\ge k-2$, equality of the padded occurrence sets forces equality of the original occurrence sets for every pair of subgroups of $S_k$.
2. For every even $k\ge4$ and every $1\le m\le k-3$, there are subgroups of $S_k$ with different original occurrence sets and equal padded occurrence sets.
3. If both subgroups lie in $A_k$, then $m\ge \lfloor(k+1)/2\rfloor$ always suffices. For any $m\ge1$, the padded occurrence set determines whether a subgroup lies in $A_k$.

The case $m=0$ is the identity. The lower bound in part 2 uses permutation subgroups in the scope of Lemma 6.11(2).

## Exact test for one partition

By transitivity of induction, Frobenius reciprocity and the Pieri rule, the padded occurrence set is the union, over $\lambda\in O(H)$, of the partitions $\nu\vdash k+m$ satisfying
$$
\nu_i\ge \lambda_i\ge \nu_{i+1}\quad\text{for all }i.
$$
Refer to such a partition $\nu$ as a successor of $\lambda$. A successor is private if no other partition of $k$ has it as a successor. A private successor makes the presence or absence of $\lambda$ decidable from the padded occurrences, regardless of the other original constituents.

For $m>0$, a partition $\lambda\vdash k$ has a private successor exactly in the following two cases.

- $\lambda_1\le m$.
- $\lambda$ is obtained by shortening only the last row of a rectangular partition by $m$, deleting a zero last row if necessary.

To prove this, fix $\nu$. Its possible predecessors $\beta$ are exactly the independent choices of integers in $[\nu_{i+1},\nu_i]$ with sum $k$. The choices are automatically nonincreasing by interlacing. The sums of the lower and upper endpoints are respectively $k+m-\nu_1$ and $k+m$. If $\nu_1=m$, the sum condition forces the lower endpoint in every row. For any $\lambda_1\le m$, this provides the private successor $(m,\lambda_1,\lambda_2,\ldots)$.

If a successor has $\nu_1>m$, the required sum lies strictly between the two endpoint sums. If at least two intervals have positive length, then from any feasible choice one can transfer one unit from a coordinate above its lower endpoint to a distinct coordinate below its upper endpoint. Indeed both the above-lower and below-upper sets are nonempty. If there were no distinct pair, both sets would have to be the same singleton, and all other intervals would have length zero. This contradicts the two-positive-interval assumption. Hence a private predecessor in the interior case requires that only one interval have positive length. This means that $\nu$ is rectangular. Its unique predecessor has just the last row shortened, as claimed. The upper endpoint sum cannot equal $k$ since $m>0$.

The criterion is exact for recovering a single occurrence uniformly over arbitrary sets of partitions. If there is no private successor, the set of all partitions and the set with just $\lambda$ removed produce the same padded set. The proof below of part 2 realizes such a loss by actual group occurrence sets.

## Large padding forces recovery

It suffices to consider positive $m$. The trivial partition $(k)$ always occurs. If $m\ge k-1$, every other partition has first row at most $m$ and has a private successor. For $m=k-2>0$ there is one extra partition, $(k-1,1)$. Its private successor is $(k-1,k-1)$: shorten the second row by $k-2$. This proves part 1.

## Small padding loses information for all even degrees

Let $k\ge4$ be even. Compare $H=\langle(12)\rangle$ and $K=\langle(1\,2\,\cdots\,k)\rangle$. Write $s=(1^k)$ for the sign partition and $a=(k-1,1)$ for the standard partition. Pieri induction of the trivial representation from $S_2\times S_1^{k-2}$ gives precisely the support of partitions with first row at least two. In fact one starts at $(2)$ and adds $k-2$ boxes one at a time. Every partition containing $(2)$ is reachable this way, by extending a standard tableau or by a chain of Young diagrams. Thus $O(H)$ consists of all partitions except $s$.

The Kraśkiewicz–Weyman major-index theorem and Swanson's zero-residue classification imply that the support for $K$ consists of all partitions except $s$ and $a$ when $k$ is even. [Swanson, Theorems 2 and 3](https://arxiv.org/abs/1701.04963)

For $1\le m\le k-3$, the partition $a$ has no private successor by the criterion. Its first row exceeds $m$. A rectangle with $a$ as predecessor would have to be $(k-1,k-1)$, whose added width is $k-2$. Nor can $s$ be a predecessor of any successor $\nu$ of $a$ in this range. Such a common successor would have first row at least $k-1$ and at least $k$ nonzero rows, forcing $|\nu|\ge 2k-2>k+m$. Therefore every successor of $a$ already comes from a partition in $O(K)$. The padded occurrence sets coincide while $O(H)\ne O(K)$, proving part 2.

## The alternating-group case

For $m\ge1$, $s$ has a private successor by $s_1=1$. The sign module has a fixed vector for a subgroup exactly when the subgroup lies in $A_k$. Consequently equality of padded supports eliminates the mixed case in which exactly one subgroup lies in $A_k$.

For $H\le A_k$, the sign character is trivial on $H$. Since conjugating a Specht partition twists by sign, $\lambda\in O(H)$ if and only if its transpose $\lambda'\in O(H)$. The first row and first column satisfy $\lambda_1+\lambda'_1-1\le k$, so at least one of $\lambda,\lambda'$ has first row at most $\lfloor(k+1)/2\rfloor$. For padding of this size, its private successor recovers the occurrence of both. This proves part 3.

Source and scope. [Grochow and Urisman, Lemma 6.11 and Corollary 6.12](https://arxiv.org/html/2606.26244v2#S6.SS5) establish the forward implication and ask about the converse. The proof here combines Pieri interlacing with the known long-cycle occurrence classification. Sharpness for each odd $k$ in the unrestricted subgroup setting is not claimed.
