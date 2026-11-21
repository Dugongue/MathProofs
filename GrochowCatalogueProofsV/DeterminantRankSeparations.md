# Determinant partition rank and the raw analytic-rank ratio

## GP-0251, GP-0252, and GP-0253

Chen and Zhao's theorem gives partition rank $d-o(d)$ for the $d$-linear determinant over every field, with an error uniform in the coefficient field. It gives a linear partition-to-geometric rank separation. For the catalogue's analytic-rank question as written, a rank-one form over $\mathbb F_2$ already gives an exponential separation. An exact count for the determinant gives a linear separation at each fixed finite field with analytic rank bounded strictly between one and two for all $d\ge 3$.

### Partition rank and geometric rank

Let $D_d(v_1,\ldots,v_d)=\det[v_1\ \cdots\ v_d]$. Over every algebraically closed field Chen and Zhao prove that the partition rank of $D_d$ is at least the largest prime $\ell\le d$, using their exact prime-size theorem and partition-rank monotonicity. Extending scalars to an algebraic closure cannot increase partition rank, so the same lower bound holds over every field. Laplace expansion gives the upper bound $d$. Consecutive prime ratios tend to one, hence the asymptotic $d-o(d)$ holds uniformly. This supplies the asymptotic growth and shows that characteristic does not affect the leading term. [Chen–Zhao, §5](https://arxiv.org/html/2607.21015v1#S5)

The contraction $D_d(v_1,\ldots,v_{d-1},-)$ vanishes exactly when the first $d-1$ columns are linearly dependent. This variety of $d\times(d-1)$ matrices of rank at most $d-2$ has codimension two. Indeed the rank-$r$ stratum has dimension $r(d+d-1-r)$, by first choosing its image and then a full-rank map to the image, and the maximum arises at $r=d-2$. Thus $G(d)\ge(d-o(d))/2$. Both catalogue answers are consequences of Chen and Zhao's published preprint, which also treats the separation with rounded analytic rank. [Chen–Zhao, §7.3](https://arxiv.org/html/2607.21015v1#S7.SS3)

### Raw analytic rank

For a $d$-linear form $T$ over $\mathbb F_q$, let $\operatorname{arank}(T)=-\log_q(\mathbb E\chi(T))$ for a nontrivial additive character $\chi$. Averaging in the last slot gives exactly the probability that the contraction in that slot is zero, by character orthogonality.

The form $T(x_1,\ldots,x_d)=x_1\cdots x_d$ on one-dimensional spaces has partition rank one, because it is nonzero and factors across a nontrivial partition. Its bias is $1-(1-1/q)^{d-1}$. For $q=2$ and $d\ge 2$, writing $\varepsilon=2^{1-d}$, its ratio is
$$
\frac{1}{-\log_2(1-\varepsilon)}
\ \ge\ (\log 2)\frac{1-\varepsilon}{\varepsilon},
$$
because $-\log(1-\varepsilon)\le \varepsilon/(1-\varepsilon)$. This proves $A(d)/\log d\to\infty$ for the catalogue's raw-rank definition. The same observation does not apply to the formulation in Lampert–Moshkovitz, whose denominator is $\lceil\operatorname{arank}\rceil$. [Lampert–Moshkovitz, §1.1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.90/LIPIcs.ITCS.2026.90.html)

The determinant gives a nonvanishing analytic-rank limit and an explicit fixed-field coefficient. The probability that $d-1$ random columns are independent is $\prod_{j=0}^{d-2}(1-q^{j-d})$ by choosing columns successively. Hence
$$
\operatorname{arank}_{\mathbb F_q}(D_d)
=-\log_q\!\left(1-\prod_{i=2}^d(1-q^{-i})\right).
$$
Its limit $\eta_q$ is strictly between one and two. The complementary probability is strictly larger than $q^{-2}$ by retaining the first two factors. It is strictly smaller than $\sum_{i=2}^{\infty}q^{-i}=1/(q(q-1))\le 1/q$ since even the first two events have positive overlap. The same bounds hold for each $d\ge 3$. In particular, as $d\to\infty$ at each fixed $q$,
$$
\frac{\operatorname{prk}_{\mathbb F_q}(D_d)}{\operatorname{arank}_{\mathbb F_q}(D_d)}
=\bigl(\eta_q^{-1}+o(1)\bigr)d,
\qquad
\frac{\operatorname{prk}_{\mathbb F_q}(D_d)}{\lceil\operatorname{arank}_{\mathbb F_q}(D_d)\rceil}
=\bigl(\tfrac12+o(1)\bigr)d.
$$
The bias formula and exact coefficients follow from the elementary probability calculation together with the cited partition-rank theorem.
