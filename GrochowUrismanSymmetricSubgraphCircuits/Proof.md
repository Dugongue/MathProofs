# A negative answer to the symmetric-circuit form of Grochow–Urisman Question 1.11

Informal deduction from Dawar, Pago and Seppelt. Grochow and Urisman ask in [Open Question 1.11](https://arxiv.org/html/2606.26244v2) whether the subgraph polynomial $S_H$ has symmetric algebraic circuits of size $f(H)n^{O(\operatorname{tw}(H))}$ on $n$ host vertices. Over the rationals the answer is no, even when every pattern $H$ is a matching and the circuits can be nonuniform. This argument uses the symmetric computational model considered in the question.

## Proof

For $k\ge1$, let $H_k$ be a disjoint union of $k$ edges. Its treewidth is one. For the directed-variable convention for $S_H$ in Grochow and Urisman, take a matching with one arc on each edge. When $S_H$ is written with a single variable per undirected edge, take the same undirected matching. Its subgraph polynomial sums the monomials of all $k$-edge matchings with coefficient one.

Assume the proposed bound. There are an absolute exponent $C\ge0$ and finite constants $c_k\ge1$ such that $S_{H_k}$ on $N\ge 2k$ vertices has a vertex-permutation-symmetric circuit of size at most $c_k N^C$. A pattern-specific threshold on $N$ can also be absorbed by increasing $c_k$.

Partition the $N=n+m$ variables' vertex labels into two fixed sets of sizes $n,m$. In the undirected convention, set all within-part edge variables to zero and name the cross-edge variables $z_{ab}$. For directed variables retain only the arcs directed from the first part to the second and set all other variables to zero. The polynomial becomes the bipartite $k$-matching polynomial, with the two parts distinguished. The substitution is equivariant for $\mathsf S_n\times\mathsf S_m$, since the retained input variables are permuted under exactly this action and the discarded ones all get the same constant. Hence the inherited circuit automorphisms make the specialized circuit matrix-symmetric, at no increase in size. If one uses the labeled-embedding normalization of the subgraph polynomial, multiply by the pattern-dependent scalar $k!$, which adds at most two gates.

Choose strictly increasing integers $N_k\ge\max\{2k,k^2,c_k+2\}$. For each $n,m$ define $k(n,m)$ to be the largest $k$ with $N_k\le \min\{n,m\}$, or zero if there is no such $k$. For $k=0$ use the empty pattern and constant polynomial $1$. Let $F_{n,m}$ be the bipartite matching with $k(n,m)$ edges. The specialized circuits now have size bounded by a single polynomial in $n+m$, since $c_{k(n,m)}\le n+m$ for $k(n,m)>0$. This diagonal choice is where the factor $f(H)$ is handled. Applying a lower bound only at $n=m=k$ would give no such conclusion.

On the other hand, $F_{n,m}$ has unbounded vertex cover number $k(n,m)$ as both part sizes grow. Its vertex count is at most $2\sqrt{\min\{n,m\}}$, so it satisfies the sublinear pattern hypothesis of [Dawar, Pago and Seppelt, Theorem 8.8](https://arxiv.org/html/2502.06740v2). Explicitly, for every pair of fixed positive integers $u,v$,
$$
 |F_{un,vm}|
 \le 2\sqrt{\min\{un,vm\}}
 \le 2\sqrt{\max\{u,v\}\min\{n,m\}}
 \le \min\{n,m\}
$$
once both $n,m$ are sufficiently large. Theorem 8.8 implies that a family satisfying this hypothesis and admitting polynomial-size matrix-symmetric circuits has bounded vertex cover number. This contradicts the matching family above.

The lower bound is a consequence of the published symmetric-circuit classification for sublinear patterns; the step here is its application to the quantifiers in Question 1.11 and the change from vertex symmetry to matrix symmetry. The question of size bounds in the unrestricted algebraic-circuit model is separate.\n
