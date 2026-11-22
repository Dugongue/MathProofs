# How many power tests recover a prime-power cycle profile?

Suppose the only permitted cycle lengths are $1,p,\ldots,p^k$ for a prime $p$. These restrictions also describe finite étale algebras whose field-factor degrees are powers of $p$. The integer $a_i$ counts length-$p^i$ cycles and the dimension is $\sum_{i=0}^k p^i a_i$.

## The first missing fixed-point count has an exact dimension cost

The number of points fixed by the $p^t$-th power is $F_t=\sum_{i\le t}p^i a_i$. Suppose the total dimension is known, and the first unavailable $F_t$ is $F_j$ with $j<k$. Then the available counts uniquely determine the profile below dimension $p^{j+1}$, even if every subsequent count is also unavailable. In dimension $p^{j+1}$, one cycle of length $p^{j+1}$ and $p$ cycles of length $p^j$ have the same dimension and agree on **every** power mark $F_t$ except $F_j$. Appending common fixed points gives witnesses in all larger dimensions.

The lower bound follows because cycles of length at least $p^{j+1}$ cannot occur below that dimension. Taking differences of the observed marks recovers each $a_i$ for $i<j$. The total dimension then determines $a_j$. The same proof works for any integer $p>1$ when only powers of $p$ are permitted.

## Power nullities recover the profile over any field

Let $P$ be the permutation matrix. Then
$$
K_t=\dim\ker(P^{p^t}-I)=\sum_{i=0}^k p^{\min(i,t)}a_i .
$$
The kernel of a permutation minus the identity consists of vectors constant on its orbits, in every characteristic. The $p^t$-th power cuts each $p^i$-cycle into $p^{\min(i,t)}$ orbits. Thus $K_0$ is the number of cycles, and
$$
\frac{K_{t+1}-K_t}{(p-1)p^t}=\sum_{i>t}a_i.
$$
Successive differences of those tails recover each multiplicity from $K_0,\ldots,K_k$. These are integer dimensions. The formula uses integer division outside the input field.

Full permutation cycle recovery from similarity is classical. Here these $k+1$ specific power nullities suffice on the restricted family, with a direct inverse. The first theorem gives a different threshold for fixed-point observations on the same family. Both arithmetic theorems are independently checked in Lean. The application to actual permutations follows from the orbit counts given above. [Cherniavsky and Sklarz](https://arxiv.org/abs/math/0411554) · [Lean source](D.lean)

The numeric shortlist was frozen with seed 7933883 before reveal. Positions 30, 62, 130 and 171 join factorization and divisibility ports. The prime-power chain restricts the divisor observations arising from these joins. The two choices of observation and the reconstruction arguments were developed after reveal. [Frozen shortlist](D-Frozen.json)
