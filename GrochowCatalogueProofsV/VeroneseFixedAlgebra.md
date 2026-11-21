# The first nonsmoothable squarefree third Veronese algebra

## GP-0184

Let $A_n=\mathbb C[x_1,\ldots,x_n]/(x_1^2,\ldots,x_n^2)$ and let a generator of the cyclic group of order three multiply every $x_i$ by a primitive cube root of unity. The invariant algebra is the third Veronese $B_n=\bigoplus_{3\mid j}(A_n)_j$, with grading divided by three. The algebra $A_n$ is smoothable for every $n$. Its invariant algebra is smoothable for $n\le 6$ and nonsmoothable for $n=7,8$. Consequently the first nonsmoothable member of this squarefree third-Veronese family occurs at $n=7$ and has length $1+35+7=43$.

Flavi, Jelisiejew and Michałek already use $n=9$ in this family to show that a smoothable algebra may have nonsmoothable invariants, with invariant length $1+84+84+1=170$. The refinement here gives the exact first failure, two smaller examples, and an independent finite-rank certificate. The minimum concerns this family. [Flavi–Jelisiejew–Michałek, §1.1](https://arxiv.org/html/2408.02754v2#S1.SS1)

### The smoothable members

The equations $x_i(x_i-t)=0$ give a flat smoothing of $A_n$, with squarefree basis over $\mathbb C[t]$ and distinct reduced coordinate points for $t\ne 0$. For $B_n$ with $n\le 5$, the positive-degree part has square zero. The algebra with square-zero basis $z_1,\dots,z_b$ is the special fibre of the free family with $z_i^2=t z_i$ and $z_i z_j=0$ for $i\ne j$. Its general fibre is the coordinate ring of the origin and the $b$ points $t e_i$ in affine $b$-space. This includes $b=0$.

For $n=6$, $B_n$ has Hilbert function $(1,20,1)$. Multiplication in degree one is a nondegenerate symmetric form with values in the line spanned by the six-variable monomial $s$, since triples pair with their complements. Diagonalizing and rescaling over $\mathbb C$ gives $e_i e_j=0$ for $i\ne j$, $e_i^2=s$, $e_i s=s^2=0$. This algebra is smoothable for every positive number of $e_i$. For one basis vector it is $\mathbb C[e]/(e^3)$, smoothed by $e(e-t)(e-2t)=0$. For more than one, deform only $e_b^2$, replacing it with $s+t e_b$. The displayed rules define an associative algebra on the same free basis over $\mathbb C[t]$. For $t\ne 0$, the nonzero idempotent $e_b/t+s/t^2$ cuts out a point, and the complementary unital subalgebra has the same rules on $e_1,\ldots,e_{b-1},s$. By induction the general fibre is smoothable, and hence so is the special fibre. In an affine embedding, the disjoint union of a smoothable scheme with a point is smoothable by moving a smoothing inside the open set disjoint from the point. The smoothable locus is the closure of the reduced locus and is closed.

### The nonsmoothable members

For $n=7,8$ write $R=\mathbb C[z_S: S\subseteq[n], |S|=3]$ and $z_S\mapsto \prod_{i\in S}x_i$. Its kernel $I$ has integral quadratic generators of two types:

1. $z_Az_B$ when $A\cap B\ne\varnothing$.
2. $z_A z_B-z_C z_D$ for each noncanonical disjoint unordered pair with a given union of size six, where $(C,D)$ is the canonical pair for that union.

These quadrics give the correct basis in degrees zero, one and two. Every cubic monomial has an overlapping pair since $n<9$, so the quadrics already kill all higher degrees. In particular there are no generators in higher degree.

The negative embedded tangent space is the sum of the negative graded pieces of $\operatorname{Hom}_R(I,R/I)$. An element of degree $-2$ or $-1$ sends each quadratic generator to a scalar or a degree-one element, respectively. These images are subject to the relations below. A map of degree at most $-3$ vanishes because the generators have degree two.

* If a cubic monomial has two expressions $z_i g$ and $z_j h$ using overlap generators $g,h$, impose $z_i\phi(g)-z_j\phi(h)=0$.
* If $g=m-m'$ is a binomial generator, express each of $z_i m,z_i m'$ as a variable times an overlap generator, say $z_j h,z_k h'$. Impose $z_i\phi(g)-z_j\phi(h)+z_k\phi(h')=0$.

Each imposed relation is an actual syzygy. It suffices to upper bound the dimension using this set. Grade finely by the multiplicity vector of the original $x_i$. Because each nonzero graded basis element of $R/I$ is the squarefree monomial of its fine weight, each of the displayed relations splits into one coefficient equation for each weight shift of $\phi$. The companion checker implements these two families exactly, multiplying basis monomials with value zero on overlap and with the common union monomial otherwise. Sparse Gaussian elimination normalizes each first unused pivot to one and subtracts earlier normalized pivots to clear already used columns. Each weight shift may be treated on its own.

| $n$ | Degree | Unknowns | Rank modulo 101 |
|---|---:|---:|---:|
| 7 | $-2$ | 623 | 623 |
| 7 | $-1$ | 21805 | 21770 |
| 8 | $-2$ | 1568 | 1568 |
| 8 | $-1$ | 87808 | 87752 |

A nonzero minor modulo 101 is a nonzero minor over $\mathbb C$. The negative tangent space therefore has dimension at most $35$ for $n=7$ and at most $56$ for $n=8$. All translations occur in degree $-1$ and are independent, since constant derivations on the variables send $z_S^2$ to $2c_S z_S$. The resulting negative tangent space consists exactly of translations.

Jelisiejew's trivial-negative-tangents theorem places such punctual schemes on elementary components, whose general members have support at one point. The smoothable component of this length has general members consisting of distinct points and hence cannot pass through the scheme. This embedded obstruction also excludes abstract smoothings: in a finite flat deformation, lift the chosen algebra generators and use Nakayama on the cokernel of the span of sufficiently many lifted monomials. After localizing at the special fibre the generators give a closed embedding into the same affine space. [Jelisiejew, Elementary components of Hilbert schemes of points, Theorem 1.2](https://arxiv.org/abs/1710.06124)

The computations are exact over the prime field and independently replayable with Python 3.8 or newer using [CheckVeroneseFixedAlgebra.py](CheckVeroneseFixedAlgebra.py). The transfer to characteristic zero and the geometric deduction are ordinary proofs.
