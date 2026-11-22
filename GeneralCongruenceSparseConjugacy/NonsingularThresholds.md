# Least dimension for hard nonsymmetric matrix congruence

Fix an odd characteristic $p$ and a target minimum ordinary Polynomial Calculus degree $D\ge4$ for the original matrix congruence equations. Write $r=D-2$ and $g=p^e$, where $e$ is the least nonnegative integer with $2p^e\ge D$. The least possible side lengths are

| Matrices required | Least side |
|---|---:|
| Arbitrary | $2r+g$ |
| Both nonsymmetric, with singular inputs allowed | $2r+g+2$ |
| Both nonsingular | $3r+2g$ |
| Both nonsymmetric and nonsingular | $3r+2g$ |

These minima allow all coordinates and coefficients. Geometric noncongruence and the stated minimum degree are required. Each result holds over any field of the specified characteristic. [Exact congruence degree](GeneralCongruenceDegree.md)

Every mismatched canonical congruence block over the algebraic closure has smaller multiplicity at least $r$ and gap a positive multiple of $g$. On the side where one such type has excess, another type has a deficit, since total dimensions are equal. The two types give side at least $2r+g$. If some mismatched type has block dimension at least two, take the side on which that type is in excess. Its contribution alone is at least $2(r+g)$, and any opposite type contributes at least $r$ more on that same side. In particular this bound is mandatory for nonsingular inputs, since there is only one nonsingular one-dimensional type over the algebraic closure. If all mismatched types have side one and the matrices are nonsymmetric, their common part must include a nonsymmetric summand of side at least two. Symmetry is invariant under congruence. This proves the lower bounds, using $3r+2g\ge2r+g+2$.

For unrestricted matrices take the complementary idempotents of side $2r+g$ with one and zero multiplicities $r,r+g$ in opposite orders. Adding a common copy of
$$
 U=\begin{pmatrix}0&1\\-1&1\end{pmatrix}
$$
makes both nonsymmetric. For the nonsingular minimum use $r+g$ copies of $U$ and $r$ of $[1]$ on one side, and $r$ copies of $U$ and $r+2g$ of $[1]$ on the other. The cosquare $U^{-T}U$ is a single Jordan block of side two at $-1$ in every odd characteristic, so $U$ is an indecomposable congruence block in all the cases used. Every mismatch has smaller multiplicity at least $r$ and a gap divisible by $g$. Both matrices are nonalternating and nonsymmetric in the latter constructions, so the raw degree-two exceptions cannot apply. The exact degree formula gives the claimed threshold. Adding shared copies of $[1]$ gives every larger side in each construction.

There is a simultaneous version for reductions with stable canonical multiplicities. Let $\mathcal P$ be a finite nonempty set of odd primes, assign $D_p\ge4$ to each, and set
$$
 r=\max_{p\in\mathcal P}(D_p-2),\qquad
 g=\prod_{p\in\mathcal P}p^{e_p},\qquad
 e_p=\min\{j\ge0:2p^j\ge D_p\}.
$$
In the table require degree at least $D_p$ at each selected prime. Assume the two lists of block types admit consistent common labels with the same dimensions and multiplicities at those primes, and that the specified nonsymmetry and nonsingularity conditions hold at each prime. The table with these $r,g$ is again exact. Indeed the universal multiplicity lower bounds apply to the same gaps at every prime, so their absolute values are multiples of $g$. The integral constructions just given keep their canonical types throughout odd characteristic, achieving all thresholds simultaneously. This statement permits independent target degrees at the different primes. The stable-label hypothesis matters when eigenvalues or elementary divisors can change at a prime.
