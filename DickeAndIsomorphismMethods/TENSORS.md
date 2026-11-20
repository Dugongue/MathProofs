# Exact asymptotic subrank for small fixed-type Dicke supports

Let $K$ be a field and let $\lambda=(\lambda_0,\ldots,\lambda_{a-1})$ be a tuple of positive integers with sum $k$. Consider any $k$-tensor in $(K^a)^{\otimes k}$ whose support in the displayed standard basis is exactly the set $\Phi_\lambda$ of words with $\lambda_b$ occurrences of each symbol $b$. All coefficients on that support may be chosen independently in $K^\times$.

**Theorem.** The monomial and ordinary asymptotic subranks of every such tensor are both $2^{H(\lambda/k)}$ in each of the following ranges.

- $a=2$, $5\le k\le11$, and $\min_b\lambda_b\ge2$.
- $a=3$ and $4\le k\le8$.

Here $H$ denotes base-two Shannon entropy. Over an algebraically closed field, the asymptotic border subrank has the same value. The proof gives 19 binary and 15 ternary fixed-type cases up to relabeling. For instance, type $(3,2)$ has asymptotic subrank $5/(3^{3/5}2^{2/5})$, and type $(2,1,1)$ has asymptotic subrank $2^{3/2}$.

This establishes a finite range of Christandl–Vrana–Zuiddam's Question 1.3.3. Their theorem supplies the lower-bound framework, and Arunachalam–Vrana–Zuiddam reduce balanced binary supports to counting modulo two. In the range here, counting separately in the shared-symbol cells suffices for most subspaces. The remaining subspaces are determined by a subset of active coordinates. A Gibbs weight on those coordinates uses the stipulated single-leg marginals and gives a sharp enough entropy bound there. The argument also permits reduction modulo three. Known cases include the one-excitation family, type $(2,2)$, and balanced binary types for sufficiently large order. The theorem's count is a count of proved cases in the displayed ranges. [Christandl–Vrana–Zuiddam, Theorem 1.2.4 and Question 1.3.3](https://arxiv.org/abs/1609.07476) · [Arunachalam–Vrana–Zuiddam, Theorems 1.2–1.4](https://arxiv.org/abs/1905.03148)

## Entropy bounds for collisions

Write $P$ for the uniform law on $\Phi_\lambda$, $N=|\Phi_\lambda|$, $p_b=\lambda_b/k$, and $h=H(p)$. Fix a leg $i$. In the remaining $n=k-1$ positions, the number of words conditional on leg $i$ having symbol $b$ is
$$N_b=\binom{n}{\lambda-e_b}.$$
Thus $\log_2 N=h+\ell$, where $\ell=\sum_b p_b\log_2 N_b$.

Take a pair law $Q$ admitted by the Christandl–Vrana–Zuiddam bound. Both words $X,Y$ have single-leg marginals $p$ and $X_i=Y_i$. The labels $0,\ldots,a-1$ give an integer tightness map after subtracting $\sum_b b\lambda_b$ from the last leg. This shift disappears from differences. Let $r_{\mathbb Q}$ be the rank over $\mathbb Q$ of the associated integer differences. We bound every admissible $Q$ using differences from the full pair set under consideration, which also covers subsets having smaller probability support.

Set $d=k-2$ and reduce the differences modulo $a$, which is prime in both ranges. The shared coordinate vanishes and the other $n$ differences sum to zero. Let $W$ be their span inside the zero-sum subspace of $\mathbb F_a^n$, with $r=\dim_{\mathbb F_a}W$. Then $r\le r_{\mathbb Q}$ by the minors criterion for rank. Deleting the last one of these $n$ coordinates identifies the zero-sum subspace with $\mathbb F_a^d$. Reduction of the alphabet preserves the distinct symbols. If $r=0$ then every pair is diagonal, so its entropy is at most $\log_2 N$.

For each shared symbol $b$, let $C_b(W)$ count the ordered pairs of conditional words whose difference modulo $a$ belongs to $W$. The shared symbol has law $p$, so
$$H(Q)\le h+\sum_b p_b\log_2 C_b(W).$$
Consequently the following exact integer test suffices for $H(Q)\le\log_2 N+(r/d)\ell$:
$$
\prod_b C_b(W)^{d\lambda_b}\ \le\
\left(\prod_b N_b^{\lambda_b}\right)^{d+r}.
\tag{1}
$$

For the additional weighted test, suppose the union $S$ of the coordinate supports of $W$ has size $s=r+1$. The space of zero-sum vectors supported on $S$ also has dimension $r$, so equals $W$. Therefore a pair is admissible precisely when its two conditional words agree outside $S$. They have identical symbol counts within $S$. Choose a set of symbols $J$ and put $L=\sum_{b\in J}\lambda_b$. For $x$, write $f(x)$ for its number of symbols in $J$ within $S$. The marginal constraints give $\mathbb E_Q f(X)=sL/k$. For fixed shared symbol $b$, assign each pair mass proportional to $2^{-f(x)}$ and denote its partition function by $Z_b$. Nonnegativity of relative entropy within each shared-symbol cell yields
$$H(Q)\le h+\sum_b p_b\log_2 Z_b+sL/k.$$
To compute $Z_b$, sum over within-$S$ type vectors $u$:
$$
Z_b=\sum_{\substack{0\le u\le\lambda-e_b\\\sum_j u_j=s}}
 \binom{s}{u}^{2}\binom{n-s}{\lambda-e_b-u}2^{-\sum_{j\in J}u_j}.
$$
Apply $J=\{1\}$ for binary types and $J=\{1,2\}$ for ternary ones, putting a most frequent symbol first. Multiplying each $Z_b$ by $2^{L-\mathbf 1_{b\in J}}$ yields an integer $Z'_b$. The weighted upper bound is at most $\log_2 N+(r/d)\ell$ whenever
$$
\prod_b (Z'_b)^{d\lambda_b}\ \le\
2^{dL(n-s)}\left(\prod_b N_b^{\lambda_b}\right)^{d+r}.
\tag{2}
$$

## Finite integer certificate

The accompanying [checker](check_tensors.py) enumerates all nonzero subspaces of $\mathbb F_a^d$ in unique reduced row-echelon form. For each choice of pivot columns a row has entry one in its pivot, zero in the remaining pivot columns and to the left of its pivot, and unrestricted entries in the other columns to its right. For each rank the checker also verifies the Gaussian binomial count.

For binary words, each deleted coordinate is restored as parity. A codeword of weight $2u$ is the difference of
$$\binom{2u}{u}\binom{n-2u}{j-u}$$
ordered pairs of weight $j$ in $n$ coordinates. Indeed $u$ of the $2u$ differing positions must be ones in the first word, and $j-u$ common ones are selected from the remaining positions. Thus $C_b(W)$ depends only on the weight histogram of $W$. Every active coordinate appears in exactly $2^{r-1}$ codewords, so the histogram also determines $s$. The checker groups by rank and weight histogram.

For ternary words, the fixed conditional type means that the deleted symbol is uniquely determined by the $d$ retained symbols. The checker generates every retained word of the prescribed type and counts ordered pairs by their difference in $\mathbb F_3^d$. Summing these frequencies over the subspace gives $C_b(W)$. The last coordinate of a difference vector is restored as minus the sum of the others modulo three. The union of supports of a basis gives all the active coordinates.

The checker tests (1) for every type and subspace. Whenever (1) fails, it verifies $s=r+1$ and tests (2). These checks use arbitrary-precision integer arithmetic throughout.

| Alphabet | Order | Nonzero subspaces | Types | Reweighted tests after grouping |
| --- | ---: | ---: | ---: | ---: |
| Binary | 5 | 15 | 1 | 0 |
| Binary | 6 | 66 | 2 | 0 |
| Binary | 7 | 373 | 2 | 0 |
| Binary | 8 | 2,824 | 3 | 0 |
| Binary | 9 | 29,211 | 3 | 2 |
| Binary | 10 | 417,198 | 4 | 3 |
| Binary | 11 | 8,283,457 | 4 | 5 |
| Ternary | 4 | 5 | 1 | 0 |
| Ternary | 5 | 27 | 2 | 0 |
| Ternary | 6 | 211 | 3 | 0 |
| Ternary | 7 | 2,663 | 4 | 1 |
| Ternary | 8 | 56,631 | 5 | 2 |

## From the certificate to subrank

The finite certificate establishes $H(Q)-\log_2 N\le(r/d)\ell\le (r_{\mathbb Q}/d)\ell$ for every admissible pair law. The higher-order Coppersmith–Winograd bound therefore gives a base-two logarithmic asymptotic induced matching number at least
$$
H(P)-d\,\frac{\ell}{d}=\log_2 N-\ell=h.
$$
An induced matching in a tensor power's support gives a monomial restriction to a diagonal tensor. Each retained diagonal entry is nonzero and can be scaled to one in a single leg. The support argument and this rescaling work over every field. [Arunachalam–Vrana–Zuiddam, Theorem 1.3](https://arxiv.org/abs/1905.03148)

For the reverse inequality, let $T^{\otimes t}$ be the $t$-th Kronecker power. A leg now carries a word of length $t$. Take symbol weights $w_b=-\log_2 p_b$. Along any nonzero entry, the total weight across all $k$ legs is $kt h$, since each of the $t$ columns has type $\lambda$. At least one leg word therefore has weight at most $th$. Each such word has product probability at least $2^{-th}$ under $p^{\otimes t}$, so there are at most $2^{th}$ of them. Assign each nonzero tensor entry to the first leg with this property and decompose by its leg word. This writes $T^{\otimes t}$ as at most $k2^{th}$ slices.

Slice rank is monotone under local linear maps and equals $v$ for a $v$-dimensional unit tensor. For completeness, in a slice decomposition of a $v$-dimensional diagonal tensor with nonzero diagonal entries, let $q$ slices use the last leg. Their last-leg vectors have an annihilator of dimension at least $v-q$. Some functional in that annihilator has at least $v-q$ nonzero coordinates, since projection to a set of independent coordinates is surjective. Contracting with it kills the last-leg slices and gives a diagonal tensor of order one less with at least $v-q$ nonzero entries. Induct on order, with the matrix rank as the base case. Hence ordinary asymptotic subrank is at most $2^h$.

Over an algebraically closed field, the slice-rank-at-most-$u$ locus is closed. For fixed slice counts $u_i$ of sum at most $u$, the set consists of tensors that vanish under the tensor product of the quotients by some $u_i$-planes in the respective legs. This is the projection of a closed incidence locus over a product of projective Grassmannians. Take the finite union over $u_i$. The slice bound also applies to any diagonal degeneration, proving the border assertion.

## Verification

Run the companion checker with Python 3.10 or later. The entropy and tensor steps above are mathematical proofs. The finite range uses the exhaustive integer certificate, and the result has an informal proof with a reproducible computation.
