# What symmetric-group padding preserves about occurrences

Grochow and Urisman [ask after Lemma 6.11](https://arxiv.org/html/2606.26244v2#S6.SS5) whether their implication about representation occurrences can be reversed. The unrestricted converse is false already for subgroups of $S_4$ with one extra point. The converse does hold whenever at least $k-1$ points are added to subgroups of $S_k$. In particular, it holds throughout the range of their graph-padding application in Corollary 6.12.

For $\Gamma\le S_k$, let $O_k(\Gamma)$ be the set of partitions $\lambda$ of $k$ for which the complex Specht module $V_\lambda$ has a nonzero $\Gamma$-fixed vector. By Frobenius reciprocity this is the occurrence set of $\mathbb C[S_k/\Gamma]$. Write $\Gamma^{[k+m]}=\Gamma\times S_m$ in $S_{k+m}$, acting on disjoint subsets. Transitivity of induction and the Pieri rule give
$$
O_{k+m}(\Gamma^{[k+m]})
=\{\nu\vdash k+m\mid \text{some }\lambda\in O_k(\Gamma)
\text{ has }\nu/\lambda\text{ a horizontal strip}\}.
$$
Indeed the permutation module being induced is $\mathbb C[S_k/\Gamma]\boxtimes\mathbf 1_{S_m}$. In the displayed formula a horizontal strip means exactly that $\nu_i\ge \lambda_i\ge \nu_{i+1}$ for every $i$, with partitions padded by zeros.

## One extra point can erase an occurrence obstruction

Use $\Gamma_1=\{1\}\le S_4$ and $\Gamma_2=\langle(1\,2\,3)\rangle\le S_4$. The first subgroup admits fixed vectors in all five irreducible representations. The second admits fixed vectors in all except $V_{(2,2)}$. This can be checked without a character table. The trivial and sign representations are fixed because the generator is even. The standard three-dimensional representation is the sum-zero subspace of the natural four-dimensional permutation representation. Its generator-fixed subspace is one-dimensional, because the generator has two orbits on the four points, and the single sum-zero equation removes one dimension. The other three-dimensional irrep is its sign twist, which has the same restriction to $\Gamma_2$. Finally $V_{(2,2)}$ is the two-dimensional sum-zero representation on the three perfect matchings of four points. Those matchings form a 3-cycle under $(1\,2\,3)$, so it has no fixed vectors.

Set $m=1$. In the formula above, the only partitions of five reachable from $(2,2)$ are $(3,2)$ and $(2,2,1)$. The former also comes from $(3,1)$, and the latter also comes from $(2,1,1)$. Both of these source partitions occur for $\Gamma_2$. Dropping $(2,2)$ therefore changes the original occurrence set but leaves the padded occurrence set identical. This disproves the unrestricted converse of Lemma 6.11(2).

## Large padding is reversible

Let $m\ge k-1$. For every partition $\lambda\ne(k)$ of $k$, we have $\lambda_1\le m$. Form the partition $\nu=(m,\lambda_1,\lambda_2,\ldots)$. If a partition $\beta$ of $k$ satisfies the horizontal-strip condition for this $\nu$, then $\beta_i\ge \nu_{i+1}=\lambda_i$ for every $i$. Both sides sum to $k$, so $\beta=\lambda$. Conversely $\lambda$ itself satisfies the strip condition. Thus a single padded occurrence, for $V_\nu$, tests whether $V_\lambda$ originally occurred. The partition $(k)$ is the trivial representation and always occurs for every subgroup, so no test is needed for it.

The small counterexample and the recovery argument concern irreducible occurrence sets. They apply in the characteristic-zero representation model of the paper.

[Grochow–Urisman, Geometric Complexity Theory and Graph Isomorphism, Lemma 6.11 and Corollary 6.12](https://arxiv.org/html/2606.26244v2#S6.SS5)
