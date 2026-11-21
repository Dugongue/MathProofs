# GP-0215 — Exact binary divided-power tensor rank

Let $k$ be algebraically closed, let $a\geq b\geq1$, and let $D_{a,b}\in(k^2)^{\otimes(a+b)}$ be the sum of all words with $a$ copies of $x$ and $b$ copies of $y$. This is the invariant tensor itself, with coefficient one on each word. Its ordinary tensor rank is $a+1$, except that the rank is $a+2$ when $a=b\geq2$ and $\operatorname{char}k$ divides $a+1$. Its symmetric rank agrees, except for $a=b=1$ in characteristic two, where the ordinary rank is two and the symmetric rank is three. Here symmetric rank allows scalar multiples of pure powers. When $b=0$ the rank is one.

## Lower bound over any field

Suppose there is an ordinary decomposition with $r\leq a$ terms. Make a bipartite graph on the terms and the $a+b$ modes, with an edge when the local factor of the term has nonzero $y$-coordinate. Choose a maximal matching of size $t$. In each matched mode contract with a covector killing its matched factor. This covector has nonzero $x$-coordinate, since the factor has nonzero $y$-coordinate. Every surviving term is all-$x$ in the remaining modes. Indeed, an unmatched term has no edge to an unmatched mode by maximality. But there are $a+b-t\geq b$ remaining modes, and the coefficient of any word with exactly $b$ copies of $y$ there is the product of the matched covectors' $x$-coordinates. That coefficient is nonzero. This contradiction gives rank at least $a+1$.

## Upper bounds

Write $d=a+b$ and $f_j=\mathbf1_{j=b}$ for $0\leq j\leq d$. The coefficient of any word with $j$ copies of $y$ in $(x+ty)^{\otimes d}$ is $t^j$. Suppose a squarefree monic polynomial $g(z)=\sum_{i=0}^R g_i z^i$ satisfies $\sum_{i=0}^R g_i f_{j+i}=0$ for $0\leq j\leq d-R$. Over $k$, use the Vandermonde matrix of its $R$ roots to represent the first $R$ moments by a linear combination of root powers. The monic recurrence then gives all $d+1$ moments. If $R=d+1$, the Vandermonde step already gives every moment.

For $R=a+1$, the conditions are $g_1=\cdots=g_b=0$. Use $z^{a+1}-1$ when the characteristic does not divide $a+1$. When $a>b$ and the characteristic divides $a+1$, use $z^{a+1}+z^a+c$. Its derivative is nonzero, so only finitely many $c$ cause a repeated root. When $a=b$ and the characteristic divides $a+1$, take $R=a+2$. The constraints then kill only $g_2,\ldots,g_a$, and $z^{a+2}+z+c$ has nonzero derivative and works for generic $c$.

## Balanced lower bound in the inseparable case

Take $a=b$ and characteristic $p$ dividing $a+1$. The middle flattening has rank $a+1$. Each side has image the span of the $a+1$ linearly independent word sums $D_{a-j,j}$ of length $a$, because the corresponding coefficient matrix is antidiagonal with entries one.

If an ordinary decomposition has $a+1$ terms, the grouped left factors and grouped right factors must be bases of their respective images. A nonzero product tensor invariant under every permutation of its modes has proportional factors, as follows by exchanging any two modes and contracting away the others. Each term therefore has grouped factors $v_i^{\otimes a}$ and $w_i^{\otimes a}$, up to scalars. The $v_i$ determine distinct projective points by independence. Fix one term. On the first $a$ modes contract by $a$ covectors, each annihilating one of the other $v_i$. These covectors have distinct projective kernels, and the contraction is a nonzero scalar multiple of $w_i^{\otimes a}$.

Write the covectors as $\alpha_j x^*+\beta_j y^*$ and $w_i=u x+v y$. The coefficient of an output word with $k$ copies of $y$ is the coefficient of $X^kY^{a-k}$ in $\prod_j(\alpha_j X+\beta_j Y)$. Consequently this squarefree homogeneous polynomial is proportional to $\sum_{k=0}^a u^{a-k}v^k X^kY^{a-k}$. If either $u$ or $v$ is zero, the latter is a pure power. Otherwise it is projectively equivalent to $(X^{a+1}-Y^{a+1})/(X-Y)$. If $a+1=p^e m$ with $p\nmid m$, all roots of the numerator have multiplicity $p^e$, and division removes just one occurrence at $X=Y$. For $a\geq2$ there is still a repeated root. This contradicts the distinct kernels and completes the lower bound.

For $a=b=1$ the ordinary rank is the rank of the alternating matrix with off-diagonal entries one in characteristic two. If it were a sum of two scaled squares, the two column vectors and both scalars would be nondegenerate, and the associated bilinear form would be congruent to an invertible diagonal matrix. That is impossible for a nonzero alternating form. The upper bound gives three.

The positive-characteristic statement concerns divided-power word sums. The related characteristic-zero polynomial rank problem is discussed in [Carlini, Catalisano and Geramita](https://arxiv.org/abs/1110.0745). This proof is independent of their polynomial Waring formula.
