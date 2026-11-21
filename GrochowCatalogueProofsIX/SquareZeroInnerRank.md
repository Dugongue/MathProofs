# GP-0088 — Exact inner rank over a commutative square-zero algebra

Let $R=k\oplus J$ be a split local $k$-algebra with $J^2=0$ and a given $k$-basis $(\epsilon_h)$ of $J$. For a rectangular matrix $A$ over $R$, its inner rank is the least $r$ such that $A=P Q$ with inner dimension $r$. Let $a$ be the rank of its reduction modulo $J$. Reduce $A$ by invertible row and column operations to $I_a\oplus N$ with $N=\sum_h\epsilon_h B_h$. Then
$$
\operatorname{irank}_R A
=a+\min_{\substack{K\leq k^m,\ U\leq k^n\\B_h K\subseteq U\ \forall h}}
  (\operatorname{codim}K+\dim U),
$$
where $N$ is $n\times m$. In particular, deterministic polynomial-time noncommutative rank gives the exact inner rank over explicit finite fields. For $R=k[x,y]/(x,y)^2$ the minimum is the ordinary rank of $B_1+zB_2$ over $k(z)$.

## Splitting off the residue-field rank

Lift ordinary elimination modulo $J$, choose the resulting invertible $a\times a$ pivot block, and clear its block row and column using its inverse. The retained block reduces to zero. Inner rank is invariant under these invertible operations.

The upper bound $\operatorname{irank}(I_a\oplus N)\leq a+\operatorname{irank}(N)$ follows by adjoining identity factors. For the reverse bound, let $P Q=I_a\oplus N$ with inner dimension $r$, and use $P_0$ for the top rows of $P$, $Q_0$ for the first columns of $Q$. Then $P_0Q_0=I_a$, and $R^r=\operatorname{im}Q_0\oplus\ker P_0$. In this splitting the second summand is free of rank $r-a$. Explicitly complete the reduced columns of $Q_0$ to a basis modulo $J$, lift the added columns, and apply $I_r-Q_0P_0$ to them. The resulting columns together with $Q_0$ form an invertible matrix because their reductions form a basis. The off-diagonal zero blocks of $P Q$ then ensure $N$ factors through the second summand alone.

## Inner rank of the radical block

Write a factorization of $N$ in constant and radical coefficients as $P=P_c+\sum_h\epsilon_h P_h$, $Q=Q_c+\sum_h\epsilon_h Q_h$. Then $P_c Q_c=0$ and $B_h=P_cQ_h+P_hQ_c$. Set $K=\ker Q_c$, $U=\operatorname{im}P_c$. Each $B_hK\subseteq U$ and
$\operatorname{codim}K+\dim U=\operatorname{rank}Q_c+\operatorname{rank}P_c\leq r$, since $\operatorname{im}Q_c\subseteq\ker P_c$.

Conversely suppose $B_hK\subseteq U$ for every $h$. Choose an inclusion with image $U$, written $L:k^{\dim U}\to k^n$, and a quotient $M:k^m\to k^{\operatorname{codim}K}$ with kernel $K$. Lift $B_h|_K$ through $L$ and extend to $C_h$ on $k^m$. Then $B_h-L C_h$ vanishes on $K$, and equals $D_h M$ for some $D_h$. Now
$$
N=[\,L\quad \textstyle\sum_h\epsilon_hD_h\,]
  \begin{bmatrix}\textstyle\sum_h\epsilon_h C_h\\M\end{bmatrix}.
$$
The inner dimension is precisely $\dim U+\operatorname{codim}K$.

## Algorithm and pencil specialization

The displayed minimum is the compression characterization of noncommutative rank. Rectangular coefficient spaces may be padded by zeros to square ones without changing the minimum. A compression for the original matrices extends by adding the dummy domain to $K$. Conversely intersect the padded $K$ with the original domain and project $U$ to the original codomain, neither increasing the relevant codimension or dimension. This yields the algorithmic claim from the [Fortin–Reutenauer compression criterion](https://www.mat.univie.ac.at/~slc/wpapers/s52reut.html) and the [Ivanyos–Qiao–Subrahmanyam algorithm](https://arxiv.org/abs/1512.03531v6).

When there are two coefficient matrices, any compression bounds the $k(z)$-rank of $B_1+zB_2$ from above by extending $K$ and $U$ to $k(z)$. For the reverse inequality apply Kronecker decomposition over $k$ to the pencil. Each rectangular singular block has normal rank the smaller dimension, and each regular square block has normal rank its dimension. A block attains that value in the compression objective by taking either $K$ to be its full domain and $U$ its full codomain, or $K=U=0$, choosing the cheaper. Take direct sums. This gives equality and an especially simple deterministic algorithm via polynomial-matrix rank. The [canonical-form reference](https://kzmurota.fpark.tmu.ac.jp/mybooks/KronFormProofEng.pdf) records the pencil block infrastructure.

The result allows arbitrary matrix dimensions and any square-zero embedding dimension. It makes no claim for higher nilpotency.
