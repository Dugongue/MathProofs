# The sharp rank window for independent anchors and split-simple Grams

## GP-0168

Let a commuting tuple of Grams have a specified common eigenbasis over a finite extension $K$ of $\mathbb F_q$, with all joint eigenvalue tuples distinct. In that eigenbasis choose $A$ uniformly from rank-$r$ matrices over $\mathbb F_q$, for $1\le r\le n$, and form the generated algebra over $K$. Then it is the full matrix algebra with probability
$$
 (1-q^{-r})^{2n}+o(1)
$$
as $n\to\infty$, uniformly in $q$, the rank and the chosen tuple. In particular the success probability tends to $e^{-2\lambda}$ if $nq^{-r}\to\lambda\in[0,\infty)$, and to zero if $nq^{-r}\to\infty$. When the joint eigenbasis is defined over the base field, this is the usual uniform rank-$r$ anchor in any coordinates. This includes a single split-simple Gram when $q\ge n$. At fixed $q$ the commuting tuple formulation is nonvacuous, using for example $\lceil\log_q n\rceil$ diagonal Grams distinguishing the coordinates. For smaller base fields the distribution in a specified eigenbasis over an extension is part of the hypothesis. The anchor laws are conditional on the fixed Gram and eigenbasis. [Tensor covariance and Gram context](https://arxiv.org/html/2604.00591v2)

### Matrix units and a random support graph

Work in the specified joint eigenbasis. Polynomials in the Gram tuple give the diagonal matrix units: to isolate coordinate $i$, for every other coordinate $j$ choose a Gram whose eigenvalues at $i,j$ differ and multiply the corresponding normalized linear factors equal to one at $i$ and zero at $j$. Multiplying $A$ by those units isolates its nonzero entries, and multiplying isolated units concatenates directed paths. Thus the generated algebra is full exactly when the directed support graph of $A$ is strongly connected. If the graph has a proper nonempty sink set, every generated matrix preserves its coordinate subspace. Conversely strong connectivity obtains every matrix unit along paths.

Sample $A=UV^{\mathsf T}$ with $U,V$ independent uniform $n$ by $r$ matrices conditioned to have full column rank. This gives uniform rank $r$: every rank-$r$ matrix has the same number $|\mathrm{GL}_r(q)|$ of such factorizations. First work before the rank conditioning. A zero row of $U$ or $V$ gives a zero row or column of $A$ and obstructs strong connectivity for $n\ge2$. The probability of no such zero rows is $(1-q^{-r})^{2n}$. We show that the probability of a failed cut despite no zero rows is $o(1)$, uniformly in $r$.

A failed directed cut has one side of $s$ rows of $U$ orthogonal to the complementary $n-s$ rows of $V$. By swapping the matrices and the sides when needed, assume $s\le n/2$. This only doubles the union bound.

### Small ranks

For $r=1$, all entries are nonzero if and only if no row of either factor is zero, so after the full-rank conditioning the success probability is exactly $(1-q^{-1})^{2n}/(1-q^{-n})^2$. Also, when $r=q=2$ the no-zero probability is already $o(1)$. Now suppose $2\le r\le32\log_q n$ in the remaining cases. For $s\le(\log n)^3$, no zero rows implies that one row among the $s$ rows of $U$ is nonzero. Conditioning on them, the probability that all $n-s$ opposite rows are orthogonal is at most $q^{-(n-s)}$. The number of these cuts is at most $n^{1+(\log n)^3}$, so their union contributes $o(1)$.

For larger $s$, if all rows are nonzero and the cut fails, the two row sets lie respectively in a subspace $W$ of dimension $h$ and in $W^\perp$, with $1\le h\le r-1$. A fixed subspace and cut contribute at most
$$
 q^{-(r-h)s-h(n-s)}\ \le\ q^{-n-(r-2)s}.
$$
The number of subspaces is at most $(r+1)C_q q^{r^2/4}$, using the Gaussian binomial formula with $C_q\le C_2$ an absolute bound. The number of cuts is at most $2^n$. In this rank range $q^{r^2/4}\le n^{8r}=\exp(O((\log n)^2))$. At $r=2$, the factor $(2/q)^n$ tends exponentially to zero for $q\ge3$. At $r\ge3$, the extra factor $q^{-(r-2)(\log n)^3}$ beats the subspace count also at $q=2$. This completes the small-rank union bound.

### Large ranks and conditioning

Suppose $r\ge32\log_q n$. For a fixed $s$-cut, let $h$ be the rank of its $s$ by $r$ submatrix of $U$. If $h\ge\min(r,s)/2$, orthogonality of the other rows has conditional probability at most $q^{-\min(r,s)(n-s)/2}\le q^{-rs/4}$. If $h<\min(r,s)/2$, the standard rank count gives probability at most $(n+1)C_q q^{-rs/4}$, since the rank-$h$ probability is at most $C_q q^{-(s-h)(r-h)}$. The count follows by choosing the row space and then the row coordinates. Summing over the at most $2n^s$ cuts of size $s$ gives $o(1)$ because $q^{-r/4}\le n^{-8}$. In this rank regime the probability of any zero row is itself $o(1)$.

Full column rank for each sampled matrix has probability $\prod_{j=0}^{r-1}(1-q^{j-n})$, bounded below by a positive constant uniformly for $q\ge2$. Hence events of probability $o(1)$ remain so under conditioning. For the small ranks the full-column-rank probability is $1-o(1)$ uniformly, and for the large ranks the no-zero probability is already $1-o(1)$. The claimed uniform formula follows, including the exact critical-window limit.


### Rank one for a nonsplit squarefree Gram over the base field

Let $G$ be an $n$ by $n$ matrix over $\mathbb F_q$ with squarefree characteristic polynomial, and let the irreducible factors have degrees $d_1,\dots,d_j$. For a uniform rank-one anchor over $\mathbb F_q$, the full algebra probability is exactly
$$
 \frac{\prod_{i=1}^j(1-q^{-d_i})^2}{(1-q^{-n})^2}.
$$
Indeed write $A=uv^{\mathsf T}$ with independently uniform nonzero $u,v$. If $u$ is cyclic for $G$ and $v$ for $G^{\mathsf T}$, the matrices $G^a A G^b$ span the full matrix algebra by the two cyclic bases. If $u$ is not cyclic, the proper nonzero span of its Krylov vectors is preserved by $G$ and $A$. If $v$ is not cyclic, use the transposed argument. By squarefreeness, a uniform vector is cyclic exactly when its projection to every irreducible factor space is nonzero. The fraction before conditioning on a nonzero vector is the product $\prod_i(1-q^{-d_i})$. This includes nonsplit irreducible Grams, for which every nonzero rank-one anchor generates the full algebra.
