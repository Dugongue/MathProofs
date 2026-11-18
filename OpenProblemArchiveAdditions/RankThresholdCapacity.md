# Exact zero-error capacity of finite-ring rank-threshold channels

**Theorem.** Let $R$ be a nonzero finite unital ring with Jacobson radical $J$, and write $R/J\cong\prod_i M_{n_i}(\mathbb F_{q_i})$. For thresholds $1\le d_i\le n_i$, declare two distinct ring elements confusable if their difference has rank below $d_i$ in at least one simple factor. At each block length $t\ge 1$, the exact zero-error message count, with or without entanglement assistance, is
$$
\left(\min_i q_i^{\,n_i(n_i-d_i+1)}\right)^t.
$$
Consequently the classical and assisted zero-error capacities in bits per use are both $\min_i n_i(n_i-d_i+1)\log_2 q_i$. This is an informal theorem recovered from the archive. It is a specialization to the stated channel model using classical rank-metric codes and graph capacity bounds.

## Independent code and clique partition

Set $C_i=q_i^{n_i(n_i-d_i+1)}$ and $C=\min_i C_i$. In factor $i$ there is a rank-metric code of size $C_i$ with distance at least $d_i$. In detail, identify $\mathbb F_{q_i}^{n_i}$ with the extension of degree $n_i$, and use the matrices of the linearized polynomials $\sum_{j=0}^{n_i-d_i}a_j X^{q_i^j}$ with coefficients in that extension. A nonzero difference has at most $q_i^{n_i-d_i}$ roots. Its kernel has dimension at most $n_i-d_i$, so its rank is at least $d_i$. The same bound ensures that distinct coefficient tuples give distinct linear maps. This is the standard linearized-polynomial construction of maximum-rank-distance codes. [Gabidulin, Rank-metric codes and applications](https://iitp.ru/upload/content/839/Gabidulin.pdf)

Select $C$ codewords from each factor, index them by the same $C$ labels, take the product tuple for each label, and lift it to $R$. Two different labels yield a difference of rank at least $d_i$ in every factor. Thus they are independent in the confusability graph $G$ on $R$.

Choose a factor attaining $C$. Partition $R$ by the first $n_i-d_i+1$ rows of its projection to that factor. There are exactly $C$ classes by surjectivity. Within a class a difference has at most $d_i-1$ nonzero rows, so a class is a clique of $G$. Hence $\alpha(G)=C$ and $\vartheta(G)=C$ by the Lovász sandwich theorem.

## Exact counts at every block length

The graph for $t$ uses is the strong power $G^{\boxtimes t}$. The Cartesian product of the one-use code is independent and has $C^t$ elements. The product of the clique partitions is a partition into $C^t$ cliques, giving $\vartheta(G^{\boxtimes t})\le C^t$ by the same sandwich bound. The entanglement-assisted message count is at most the theta number of this graph by Beigi's bound, and at least the classical count because the sender and receiver can use the classical code. All three counts therefore equal $C^t$. [Beigi, Entanglement-assisted zero-error capacity is upper bounded by the Lovász theta function](https://arxiv.org/abs/1002.2488)
