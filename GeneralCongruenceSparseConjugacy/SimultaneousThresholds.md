# Exact dimensions at independently prescribed characteristics

Let $S$ be a nonempty finite set of primes, including two if desired. Prescribe a minimum PC degree $D_p\ge4$ at each $p$ for the raw matrix-congruence equations. Put $r_p=D_p-2$ and let $g_p$ be the least power of $p$ with $2g_p\ge D_p$. A single pair of integer matrices can realize **exactly** these degrees after reduction. The least common matrix dimension in each class is the maximum, over the chosen primes, of the corresponding entry below.

| Conditions on both reduced inputs | Minimum dimension at $p$ |
|---|---:|
| Arbitrary | $2r_p+g_p$ |
| Nonsymmetric | $2r_p+g_p+2$ |
| Nonsingular | $3r_p+2g_p$ |
| Nonsymmetric and nonsingular | $3r_p+2g_p$ |

These conditions are imposed at all listed primes. There is no requirement that the canonical decompositions be the same at different primes. Each entry is also sharp for a degree *at least* $D_p$. For a single prime the corresponding minimum holds over every field of that characteristic.

**Lower bounds.** In either congruence-degree formula, attaining degree $D_p\ge4$ excludes any missing positive type or mismatch of alternating flags. Every discrepant normalized block type has smaller multiplicity at least $r_p$ and gap a multiple of $g_p$. Two discrepancies must have opposite signs because the two dimensions are equal and corresponding blocks have the same side. This gives the first bound. For any mismatched block of dimension at least two consider the matrix containing more copies of it. Its dimension is at least $2(r_p+g_p)+r_p$. Nonsingular inputs must have such a mismatch: there is only one nonsingular type of side one over the closure. If all mismatches use one-dimensional blocks, nonsymmetric matrices must also contain a common nonsymmetric block of side at least two, giving the second bound. These arguments apply in characteristic two, where the alternating flag counts a doubled block as one. [Odd-characteristic formula and thresholds](NonsingularThresholds.md) · [Characteristic-two formula](BinaryCongruence.md)

**Uniform construction.** Work at one prime and write $r=r_p$, $g=g_p$. In the unrestricted case use diagonal matrices whose multiplicities of one and zero are $(r,r+g)$ and $(r+g,r)$, respectively. For nonsymmetry append a common copy of
$$
 U=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$
For the nonsingular cases use $r+g$ copies of $U$ and $r$ of $[1]$ in the first matrix, and $r$ copies of $U$ and $r+2g$ of $[1]$ in the second. The nonsymmetric invertible $U$ is congruently indecomposable over the algebraic closure in **every** characteristic: a decomposition of a side-two matrix into two one-dimensional forms would be symmetric, and symmetry is invariant under congruence. Its cosquare has characteristic polynomial $t^2-t+1$, which also distinguishes it from the scalar block in characteristic two. The formulas give degree precisely $r+2=D_p$ because a discrepant type has smaller multiplicity exactly $r$, and all multiplicity gaps contain the required power of $p$. In the unrestricted construction pad to any larger side by common copies of $[1]$, keeping the zero type at smaller multiplicity $r$. In the nonsingular construction the same padding keeps the smaller multiplicity of $U$ equal to $r$. For the nonsymmetric singular construction it again keeps the zero-type minimum. These facts preserve the *exact* degree under padding.

Pad the single-prime pairs to the maximum side and apply the ordinary Chinese remainder theorem entry by entry. Representatives between zero and $\prod_{p\in S}p-1$ suffice. The reductions are exactly the prescribed matrices in their given coordinates, proving attainment simultaneously. Conversely any simultaneous example must meet each local lower bound. When canonical labels and multiplicities are required to persist across reductions, the gaps must instead absorb several prime powers at once, as in the stable-data threshold. Neither construction needs an analytic prime bound. [Stable-data comparison](NonsingularThresholds.md)
