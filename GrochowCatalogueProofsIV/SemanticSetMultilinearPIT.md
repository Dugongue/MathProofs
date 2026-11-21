# Faster semantic set-multilinear identity testing over the integers

## GP-0679

Let $t$ be the total number of input variables, partitioned into $d$ nonempty blocks of maximum size $m$. Given a size-$s$ integer circuit promised to compute a set-multilinear polynomial of type $[d]$, there is a deterministic test using
$$
t^{5d/6}\operatorname{poly}(s,d,\log(2t))
$$
arithmetic operations. With a supplied bound $2^L$ on the coefficient $\ell_1$ norm of every original gate and encoded constants of bit length at most $L+1$, the same bound holds in bit operations with an additional factor polynomial in $L$. For maximum block width $m$ above an absolute constant the bound holds with $m$ in place of $t$. The coefficient-height qualification is the one used in the source for integer bit complexity.

### Speedup for syntactically set-multilinear circuits

Use the heavy-gate decomposition of Chukhin–Gajulapalli–Golovnev–Mihajlin. A syntactic circuit can be expressed as a sum of at most its size many terms $g_S h_{\bar S}$, with disjoint matched block types and $d/3<|S|\le 2d/3$. The coefficient arrays of both factors of every summand can be computed in size-polynomial time times $m^{2d/3}$. Indeed, light-gate coefficient arrays are built by disjoint-type products and same-type addition. Heavy gate path polynomials use fewer than $d/3$ blocks. The second factor is one light child times the corresponding path polynomial, with fewer than $2d/3$ blocks. This is the recurrence in their Lemma 8.4 and proof of Theorem 5. The remaining task is to compute the squared coefficient norm by pairwise inner products. [Source, Section 8.2](https://eccc.weizmann.ac.il/report/2026/313/download/)

Take two terms with partitions $S,\bar S$ and $S',\overline{S'}$. Write $(a,b,c,e)$ for the cardinalities of $S\cap S'$, $S\setminus S'$, $\overline{S\cup S'}$, and $S'\setminus S$, respectively, in cyclic order. Every adjacent sum is between $d/3$ and $2d/3$, inclusive. The inner product is a scalar contraction of a four-cycle of matrices with index dimensions $m^a,m^b,m^c,m^e$. We can first eliminate either opposite pair of indices, each by one rectangular matrix multiplication, and take an entrywise inner product of the two resulting arrays. This gives a naive exponent
$$
d-\mu,\qquad \mu=\max\{\min(a,c),\min(b,e)\}.
$$
The adjacent-sum condition gives $\mu\ge d/6$. Indeed a smaller $\mu$ yields an adjacent pair both smaller than $d/6$.

Set $\eta=1/40$. When $\mu\ge d/6+\eta d$, the naive bound already has exponent at most $(5/6-\eta)d$. Otherwise choose one small index from each opposite pair. They are adjacent and are each at most $(1/6+\eta)d$, hence at least $(1/6-\eta)d$ by their sum. Each of the remaining indices is adjacent to one of the chosen two, so it also has size at least $(1/6-\eta)d$.

In the latter case both matrix multiplications save a uniform exponent by blocking. For an $A$-by-$B$ matrix times a $B$-by-$C$ matrix, partition all indices into blocks of the smallest dimension $M=\min(A,B,C)$ and zero-pad the last block in each direction. Multiply each pair of square blocks by Strassen's algorithm and sum their products. The cost is $O(ABC/M^{3-\log_2 7})$, including block addition. For each of the two contractions $ABC$ is at most $m^{5d/6}$ if we start with the better opposite pair, and $M\ge m^{(1/6-\eta)d}$. Since $(3-\log_2 7)(1/6-\eta)>\eta$, the same better exponent $(5/6-\eta)d$ follows. The numerical inequality follows from $7^{17}<2^{48}$, which gives $3-\log_2 7>3/17$. The two resulting arrays have at most $m^{2d/3}$ entries because the contracted pair both had size at least $d/6$ when choosing the better opposite pair. This also bounds their final entrywise contraction. Thus the full syntactic test has the improved exponent $5/6-\eta$.

### Applying the bound to semantic inputs

For each original gate $g$ and block subset $B$, compute the component of its polynomial using exactly one variable from each block of $B$ and no other variables. For addition combine like subsets. For multiplication split $B$ into disjoint subsets and sum the corresponding products. There are $O(3^d s)$ resulting syntactically typed gates. This transformation computes the desired output by the promise and discards all unneeded components. Each new gate has coefficient $\ell_1$ norm at most $2^{2L}$ if the original gate bound holds, since sums over disjoint splits are bounded by the product of the original norms.

The preceding syntactic algorithm for this circuit costs at most $C^d m^{(5/6-\eta)d}\operatorname{poly}(s,d,\log(2m))$ for an absolute constant $C$. To see the absolute bound also in bit complexity, path computations have polynomial-bit coefficients in the expanded circuit size and $L$. In each Strassen recursion level intermediate linear sums increase bit size by a constant, and final block additions add logarithmically many bits in the number of blocks. All heights therefore enter the estimates through fixed polynomial factors in expanded circuit size, $d$, $L$, and $\log(2m)$. If $m\ge C^{1/\eta}$ the extra factor is absorbed in the gained exponent.

For the remaining bounded values of $m$, enumerate assignments that activate a single variable from each block with value one and set every other variable to zero. By the output promise, a returned value is exactly the corresponding coefficient. This takes at most $m^d$ evaluations. If $t\ge m^{6/5}$ then $m^d\le t^{5d/6}$. Together with $d\le t$, the remaining cases have both $t$ and $d$ bounded by absolute constants and can be absorbed in the constant of the running time. Evaluating directly on these zero-one points respects the supplied height bound. This gives the stated uniform estimate in terms of total variable count, including constant block widths. A missing block gives the zero promise automatically, and $d\le1$ is handled by elementary coefficient extraction.
