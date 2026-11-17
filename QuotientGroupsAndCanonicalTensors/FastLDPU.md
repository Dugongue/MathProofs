# Fast canonical LDPU for exact tensor-train normalization

Vilmart asks whether canonical LDPU can match the exponent of matrix multiplication and whether it admits a Four Russians speedup over the binary field. Both answers are affirmative. The first algorithm uses rank-profile-revealing PLUQ and factors one triangular block. The second works directly with binary panels and has a worst-case bound. [Vilmart, §3.1 and the two questions after Theorem 19](https://arxiv.org/html/2607.06271)

## The required factorization

Let $A$ have $m$ rows, $n$ columns and rank $r$. The desired factors satisfy $A=LDPU$. The $r$ columns of $L$ have leading entries one, and their pivot rows $i_1<\cdots<i_r$ increase. The $r$ rows of $U$ have leading entries one, and their pivot columns $j_1<\cdots<j_r$ increase. The diagonal $D$ is nonsingular, and $P$ is a permutation matrix. Write $c_a$ for the row of $U$ routed by $P$ to column $a$ of $L$, so $P_{a,c_a}=1$. Vilmart's extra condition is

$$
 L_{i_a,b}=0\quad\text{when }c_b>c_a.
$$

Vilmart proves that these conditions specify a unique factorization. A rank-zero matrix has empty factors. [Vilmart, Definitions 4–5 and Proposition 7](https://arxiv.org/html/2607.06271#S3.SS1)

## The multiplication exponent

**Theorem.** If deterministic square matrix multiplication over a field takes $O(s^\beta)$ field operations, for $\beta>2$, canonical LDPU takes $O(mn\max(1,r)^{\beta-2})$ field operations.

Use a rank-profile-revealing PLUQ and Dumas–Pernet–Sultan's conversion to lower and upper triangular factors around the rank-profile subpermutation matrix. The pivot rows $I=(i_1,\ldots,i_r)$ and pivot columns $J=(j_1,\ldots,j_r)$ are the nonzero rows and columns of that subpermutation matrix. Retain the indicated columns and rows of the two triangular factors. Normalize their leading entries and move the scalings to the middle. This gives $A=L_0DP U_0$, with the required unit echelon properties. The core $B=L_0[I,*]$ is lower unitriangular. The extra zero condition may still need to be imposed. Rank-sensitive PLUQ costs $O(mn\max(1,r)^{\beta-2})$ field operations. Retaining, permuting and scaling costs $O(mn)$. [Dumas–Pernet–Sultan, tile-recursive algorithm and Theorem 21](https://arxiv.org/html/1601.01798) · [Rank-sensitive bound](https://arxiv.org/abs/1301.4438)

Split the strict lower triangle of the core into

$$
 \mathcal{K}=\{(a,b):a>b,\ c_a>c_b\},\qquad
 \mathcal{M}=\{(a,b):a>b,\ c_a<c_b\}.
$$

Each pattern is transitive. Matrices of the form identity plus a matrix supported on one pattern are closed under multiplication and inversion. For inversion, use the finite geometric series for a strictly triangular matrix.

Factor $B=KM$, where $K,M$ are unitriangular with their strict entries supported on $\mathcal K,\mathcal M$, respectively. Split the indices into initial and final halves and recursively factor both diagonal blocks as $B_{ii}=K_{ii}M_{ii}$. On the lower-left rectangle the equation becomes

$$
 K_{22}^{-1}B_{21}M_{11}^{-1}
   =K_{22}^{-1}K_{21}+M_{21}M_{11}^{-1}.
$$

The two terms on the right have disjoint supports in their assigned patterns, by transitivity. Project the left side to each pattern by copying the indicated entries into two zero matrices. Multiply the first projection on the left by $K_{22}$ to recover $K_{21}$. Multiply the second on the right by $M_{11}$ to recover $M_{21}$. The reconstructed blocks stay in their patterns by transitivity. This solves the whole block equation. Size one is immediate. Triangular inversion uses recursive block inversion and matrix products. The recursion has two half-size calls and a bounded number of products and triangular inversions per node, for cost $O(r^\beta)$.

Return

$$
 L=L_0 M^{-1},\qquad U=P^{-1}D^{-1}M D P\,U_0,
$$

with the same $D,P$. Right multiplication of $L_0$ by a lower unitriangular matrix preserves its leading entries and pivot rows. Its restriction to pivot rows is now $K$, with the required extra zeros. Conjugating $M$ by $DP$ gives an upper unitriangular matrix in pivot-column order. Its left multiplication preserves the unit echelon form of $U_0$. The inserted factors cancel in $LDPU$. Thus the result is the canonical factorization. In the final thin products, block the longer dimension into chunks of size $r$. The cost is $O((m+n)r^{\beta-1})$, which is $O(mnr^{\beta-2})$ since $r\leq\min(m,n)$. Inspect the input for the rank-zero case and return empty factors.

This gives the usual arithmetic interpretation of matching the exponent, for every attainable exponent above two. It can replace each LDPU call in Vilmart's tensor-train normalizer with the same output.

## Direct Four Russians elimination over the binary field

**Theorem.** Canonical LDPU over $\mathbb F_2$ can be computed deterministically in $O(N^3/\log(N+1))$ time on $N\times N$ matrices in a random-access model with word addresses of $O(\log(N+1))$ bits. The bound also counts individual bit additions and copies, with word-size addresses and panel indices.

First use elementary column-by-column elimination without row exchanges. A row remains active until selected as a pivot. At each column, take the first active row with entry one there, if any. Freeze that row and clear the column from the remaining active rows by adding the frozen row where needed. Active rows earlier than the pivot row already have entry zero there, so use of the pivot only occurs below its original row index. Keep the frozen rows as $U$, in increasing pivot-column order, and record each original row's clearing coefficients, including coefficient one on its own pivot if it freezes. At termination the unfrozen rows have zero residual. Each original row is reconstructed from its recorded coefficients and the frozen rows. Sorting coefficient columns by original pivot row gives $L$ in unit column-echelon form. The routing $P$ matches coefficient columns to frozen rows. Every frozen row has coefficient zero on future column pivots, so $L$ is $P$-conditioned. The diagonal is identity. This elementary algorithm returns the specified canonical factorization for every rank.

Process adjacent columns in panels of width $k=\max(1,\lfloor\log_2 N\rfloor)$, with the last panel possibly shorter. Run the elementary algorithm on the panel bits only, recording pivot choices and clearing coefficients. Pivot decisions depend only on the panel bits and the frozen-row list. For each row that freezes in this panel, reconstruct its suffix beyond the panel from its original suffix on entering the panel and its recorded combination of earlier pivot suffixes in the panel. Compute these suffixes in pivot order. There are at most $k$ of them, giving cost $O(k^2N)$.

For the rows still active after the panel, update the suffixes by their recorded combinations of the newly frozen suffixes. Tabulate all combinations in Gray-code order, adding one row per entry, at cost $O(2^k N)$. For each active row read its combination index and add the corresponding table entry to its suffix, at total cost $O(N^2+Nk)$. A panel with no pivots leaves suffixes unchanged. Internal panel elimination and recording costs $O(Nk^2)$. The frozen rows and active state at each boundary therefore agree with the elementary algorithm.

There are $O(N/k+1)$ panels. Using $2^k\leq N$ for $N\geq2$, the total is $O(N^3/\log(N+1))$. Handle size one directly. The worst-case bound also gives the requested average-case speedup over scalar cubic elimination. The table technique reuses Four Russians multiplication. [Albrecht–Bard–Hart](https://arxiv.org/abs/0811.1714)

The triangular input machinery is due to Dumas, Pernet and Sultan, and the canonical output specification is Vilmart's. Remark 22 and Corollary 31 of Dumas–Pernet–Sultan identify the extra triangularity for generalized Bruhat factors and obtain it with a special reverse-lexicographic pivot strategy. The conversion here instead applies directly to the factors produced by the rank-sensitive tile recursion. Both proofs are informal. Exhaustive finite checks matched the binary panel output to row-by-row canonical elimination on all 73,728 binary matrices of sizes $3\times4$, $4\times3$ and $4\times4$. The triangular splitting formulas passed reconstruction and support tests for all 873 pivot permutations through size six, with one sampled lower triangular matrix over $\mathbb F_7$ per permutation. Publication priority for these exact LDPU constructions remains unverified. [Dumas–Pernet–Sultan, §6](https://arxiv.org/html/1601.01798#S6)
