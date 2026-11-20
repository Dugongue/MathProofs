# Exact partition rank of the determinant

**Theorem.** Let $K$ be any field and $n\ge 2$. Regard the determinant as the multilinear form on the $n$ columns of an $n\times n$ matrix. Its partition rank over $K$ is

$$
\operatorname{prk}_K(\det_n)=
\begin{cases}
n-1 & \text{if } n\ge 4 \text{ is even},\\
n & \text{if } n=2 \text{ or } n \text{ is odd}.
\end{cases}
$$

Partition rank counts summands of the form $f(v_I)g(v_{I^c})$, where $I$ is a nonempty proper subset of $[n]$ and each factor is multilinear in its indicated columns. Transposition gives the same formula for the row-separated convention. This resolves GP143, including the complex-field case. The proof below uses standard Chow-ring results and elementary counting. It is a written proof.

## 1. Upper bounds

Laplace expansion gives $\operatorname{prk}_K(\det_n)\le n$. For $n=2m$, take the block-diagonal alternating matrix $J$ with $m$ copies of $\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, so $\operatorname{Pf}(J)=1$. If $X=[v_1\ \cdots\ v_n]$, then

$$
\det(X)=\operatorname{Pf}(X^{\mathsf T}JX).
$$

Over characteristic zero this is the change-of-basis identity for the top exterior power of the alternating two-form with matrix $J$. Both sides are polynomials with integer coefficients in the universal matrix entries, so the identity holds over every field, including characteristic two. Put $B=X^{\mathsf T}JX$. Expanding along the first Pfaffian row gives

$$
\det(X)=\sum_{j=2}^n (-1)^j (v_1^{\mathsf T}Jv_j)\,
                 \operatorname{Pf}(B_{[n]\setminus\{1,j\}}).
$$

Each summand factors across $\{1,j\}$ and its complement. The Pfaffian of the complementary submatrix is multilinear in the remaining columns, since each perfect matching pairs each remaining index once. Thus the expansion gives at most $n-1$ terms for $n\ge4$ even. When $n=2$ the determinant itself splits as an alternating bilinear form of matrix rank 2, so its partition rank is **2**, with both factors in each admissible term linear in one column.

## 2. A Chern-class consequence of any short decomposition

Assume $K$ algebraically closed for the lower bounds. This suffices because a decomposition over $K$ remains a decomposition over its algebraic closure. Let $U$ be the smooth open subvariety of $(\mathbb P^{n-1})^n$ parametrizing ordered lines $(\ell_1,\ldots,\ell_n)$ whose direct sum is $K^n$. Let $M_i$ be the $i$-th tautological line bundle on $U$. The map

$$
p:U\longrightarrow \mathrm{Fl}_n,\qquad (\ell_i)_{i=1}^n\longmapsto
 (F_i=\ell_1+\cdots+\ell_i)_{i=1}^n
$$

has fibers the choices of splittings of all tautological sequences
$0\to F_{i-1}\to F_i\to L_i\to0$, where $L_i=F_i/F_{i-1}$. These choices form a Zariski-locally trivial torsor under the vector bundle $\bigoplus_i\operatorname{Hom}(L_i,F_{i-1})$. Indeed, any choice of local splittings identifies all alternatives with the corresponding bundle of linear maps by taking differences. We have $M_i\simeq p^*L_i$. Affine bundle invariance identifies the integral Chow ring of $U$ with that of the complete flag variety. Taking $x_i=c_1(M_i^*)$, the flag-bundle formula gives

$$
\mathrm{CH}^*(U)=\mathbb Z[x_1,\ldots,x_n]/(e_1,\ldots,e_n),
$$

where $e_j$ is the $j$-th elementary symmetric polynomial. Using the dual tautological lines only changes the signs by degree. [Fulton, *Intersection Theory*, Section 3.3, affine bundle invariance](https://doi.org/10.1007/978-1-4612-1700-8) · [Chen–Zhao, Lemma 3.1, flag variety Chow ring](https://arxiv.org/html/2607.21015v1#S3)

Suppose there is a decomposition

$$
\det_n(v_1,\ldots,v_n)=\sum_{a=1}^r f_a(v_{I_a})\,g_a(v_{I_a^c}).
$$

On $U$, the first factors $f_a$ define sections of $N_a=\bigotimes_{i\in I_a}M_i^*$ by restricting the multilinear forms to the lines. They have no common zero because any nonzero representatives of the lines form a basis with nonzero determinant. Their tuple is therefore a nowhere-vanishing section of $\bigoplus_{a=1}^r N_a$ and gives a trivial rank-one subbundle. The quotient has rank $r-1$, so the Whitney formula forces the top Chern class to vanish. In the displayed ring this gives the relation

$$
\prod_{a=1}^r\left(\sum_{i\in I_a} x_i\right)=0.
\tag{1}
$$

The use of the ordered column-line space retains a distinct Chern class for every column. The resulting obstruction keeps track of each entire factor subset in the decomposition. [Chen–Zhao, Section 4, Chern-class approach for strength](https://arxiv.org/html/2607.21015v1#S4)

## 3. Nonvanishing by roots of unity

Let $\Omega$ be the $n$ complex $n$-th roots of unity. For any bijective labeling $\alpha_i$ of $\Omega$ by $[n]$, the assignment $x_i\mapsto\alpha_i t$ defines a ring map

$$
\mathbb Z[x_1,\ldots,x_n]/(e_1,\ldots,e_n)\longrightarrow \mathbb C[t]/(t^n).
$$

Indeed, $e_j(\alpha_1,\ldots,\alpha_n)=0$ for $1\le j<n$ by $\prod_i(z-\alpha_i)=z^n-1$, and the relation of degree $n$ maps to a multiple of $t^n$. The complex numbers here are coefficients in a test ring for an integral Chow-ring identity. This step applies regardless of the characteristic of $K$.

We bound the chance that a uniformly random $s$-subset of $\Omega$ sums to zero. Singleton sums are nonzero, and the same holds for subsets of size $n-1$ because $\sum_{a\in\Omega}a=0$. For $2\le s\le n-2$, draw an edge between two subsets if one is obtained from the other by a single swap. Every zero-sum subset has exactly $s(n-s)$ neighbors, all of nonzero sum. If $B$ has sum $z\ne0$, a zero-sum neighbor must replace $b\in B$ by $a\notin B$ with $b-a=z$. On a unit circle there are at most two ordered pairs $(b,a)$ with this difference, since $a$ belongs to both the circle and its translate by $-z$. For odd $n$ there is at most one such ordered pair in $\Omega$. When there are two circle solutions, the partner of $(b,a)$ is $(-a,-b)$, while odd-order roots contain no antipodal pair. If the partner is the original solution, $|z|=2$ and the circles are tangent.

Double counting the edges incident to zero-sum subsets gives, with $c=2$ for even $n$ and $c=1$ for odd $n$,

$$
\mathbb P\left(\text{a random }s\text{-subset sums to zero}\right)
\le\frac{c}{s(n-s)+c}.
$$

For even $n\ge4$ this is at most $1/(n-1)$, using $s(n-s)\ge2(n-2)$. For odd $n$ it is strictly smaller than $1/(n-1)$ whenever the size range is nonempty. These bounds also hold for singletons and their complements with probability zero. For each fixed $I_a$, a uniformly random bijective labeling draws a uniformly random $|I_a|$-subset of $\Omega$. The union bound shows there is some labeling for which every $\sum_{i\in I_a}\alpha_i$ is nonzero if $r\le n-2$ for even $n\ge4$, or if $r\le n-1$ for odd $n$. At this labeling the left side of (1) maps to

$$
t^r \prod_{a=1}^r\left(\sum_{i\in I_a}\alpha_i\right)\ne0,
$$

since $r<n$. This contradiction proves the two lower bounds. For $n=2$, grouping the two variables is exactly the matrix-rank problem for $J$, which has rank 2 over every field.

## Prior results

Lampert–Moshkovitz proved the four-column case by a three-term quadratic expansion and gave a logarithmic general lower bound. Chen–Zhao used the Chow ring of the projective invertible matrix variety to determine the strength in prime sizes, then obtained the largest-prime lower bound on determinant partition rank. Here the parity formula follows from column-line Chern classes and the roots-of-unity calculation above. [Lampert–Moshkovitz, Theorems 2–3](https://doi.org/10.4230/LIPIcs.ITCS.2026.90) · [Chen–Zhao, Theorems 4.2 and 5.2](https://arxiv.org/abs/2607.21015)
