# Exact degeneration depth of square matrix pencils

**Informal proof.** This answers the exact-depth question posed in the Depth Hierarchy project after the triangular lower bound. The order is strict equivalence of individual complex matrix pencils, with the spectral parameter fixed. Publication priority for the height formula has not been established.

## Theorem

Write \(h(p,q)\) for the largest number of strict orbit-closure steps among \(p\times q\) complex matrix pencils under independent changes of row and column bases. Then

\[
h(n,n)=\binom{n+1}{2},\qquad
h(n,n+1)=h(n+1,n)=\binom{n+1}{2}+n .
\]

The square formula allows any number of distinct eigenvalues. It continues to hold when regular eigenvalues are restricted to any fixed nonempty finite subset of the projective line. For the latter restriction, the strict-equivalence relation has closed-set difference level exactly \(n(n+1)+1\).

## The potential

Let \(r\) denote normal rank. Let \(a=(a_1\ge a_2\ge\cdots\ge 0)\) and \(b=(b_1\ge b_2\ge\cdots\ge 0)\) list the right and left minimal indices, including zero indices. At each eigenvalue \(\lambda\), write \(c_\lambda=(c_{\lambda,1}\ge c_{\lambda,2}\ge\cdots)\) for the descending sizes of the Jordan blocks. Put

\[
A=|a|+|b|,\quad B=\sum_\lambda |c_\lambda|,\quad
W(d)=\sum_{i\ge1}i d_i,\quad V(d)=\sum_{i\ge1}(i-1)d_i .
\]

Here \(|d|\) is the sum of the entries. Each singular block contributes its minimal index to the normal rank. Each regular block contributes its size. Thus \(A+B=r\). Define

\[
\Phi=\binom{r+1}{2}+W(a)+W(b)-\sum_\lambda V(c_\lambda).
\]

We use the four orbit covering moves of Edelman, Elmroth and Kågström, Theorem 3.2. A strict degeneration can be refined to covers because a strict step lowers orbit dimension. Their orbit moves concern fixed eigenvalues, and their separate bundle moves allow eigenvalues to coalesce. The latter are outside the order here. [Covering theorem](https://math.mit.edu/~edelman/publications/geometric_approach.pdf)

1. **Spread two singular indices.** A rightward coin move in the conjugate partition moves one unit from a smaller index to a larger one. The descending row partition increases in dominance at fixed mass. Since \(W(d)=\sum_{j\ge0}\sum_{i>j}d_i\), \(W\) decreases by at least one.
2. **Transfer a unit from a singular index to the regular part.** The largest singular index loses one unit, so its \(W\) decreases. The unit adds a new rightmost Weyr column to one regular partition, extending a longest block there or creating a new block at an unused eigenvalue. This does not change that partition's \(V\).
3. **Balance Jordan blocks at one eigenvalue.** The leftward move in the Weyr partition moves the row partition strictly down in dominance, so \(V=W-|d|\) increases by at least one.
4. **Drop the normal rank.** Remove a longest Jordan block at each occupied eigenvalue. Let \(k\) be the sum of their sizes. The singular Weyr columns receive one added coin each from column zero through some column \(u\) on the right and through column \(v\) on the left. This inserts a new maximal index \(u\) on the right and \(v\) on the left, with \(u+v=k-1\). The old indices shift down one position in the descending list, so \(W(a)+W(b)\) increases by \(k-1+A\). Removing the first row of each Jordan partition decreases \(\sum_\lambda V(c_\lambda)\) by \(B-k\). The triangular term decreases by \(r\) since the normal rank becomes \(r-1\). The total change is

\[
-r+(k-1+A)+(B-k)=-1.
\]

Thus \(\Phi\) strictly decreases at every proper degeneration. The zero pencil has potential zero and lies in the closure of every pencil orbit. It follows that \(\Phi\) is nonnegative and bounds the number of remaining steps from any pencil.

## Optimal chains

For a square \(n\times n\) pencil there are \(s=n-r\) minimal indices on each side, so \(W(a)+W(b)\le sA\le sr\). Consequently,

\[
\Phi\le \binom{r+1}{2}+sr
=\binom{n+1}{2}-\binom{s+1}{2}.
\]

For the lower bound, fix a single eigenvalue and write \(J_i\) for its regular block. Let \(P_i,I_i\) be singular blocks of sizes \(i\times(i+1)\) and \((i+1)\times i\), respectively. For each \(j\ge1\), begin at \(J_j\) and move one unit at a time to a second Jordan row until reaching \(J_{\lceil j/2\rceil}\oplus J_{\lfloor j/2\rfloor}\). These are \(\lfloor j/2\rfloor\) Jordan dominance steps. Remove the longest regular row by move 4, replacing it by \(P_0\oplus I_{\lceil j/2\rceil-1}\). Now transfer one unit from the positive singular index to the remaining Jordan block at each step by move 2. This takes \(\lceil j/2\rceil-1\) more steps and leaves \(P_0\oplus I_0\oplus J_{j-1}\). A zero-sized regular block is absent. This gives \(j\) steps in all. Continue inductively with the \((j-1)\)-chain padded by \(P_0\oplus I_0\). Direct sums preserve closure inclusions, and Krull–Schmidt cancellation preserves strictness. The total count from \(J_n\) to zero is \(1+\cdots+n\).

For an \(n\times(n+1)\) pencil the two lists have lengths \(s+1,s\). The same potential gives \(\Phi\le\binom{r+1}{2}+(s+1)r\le\binom{n+1}{2}+n\). Start at \(P_n\) and transfer one unit at a time to a regular block using move 2. After \(n\) steps this gives \(P_0\oplus J_n\). Continue with the square chain padded by \(P_0\). Transposition gives the other format.

## Exact difference level on fixed spectral support

If the regular eigenvalues belong to a prescribed finite set, there are finitely many Kronecker types in the format. This set of pencils is invariant, and its relative orbit closures follow the same order. The square upper bound remains valid and the same chain uses just one permitted eigenvalue.

For a finite orbit stratification of depth \(d\), use the product strata \(O\times O'\) in the space of pairs. Give a product stratum the maximum length of a chain of alternating answers ending there and starting on an affirmative stratum, with value zero when no such chain exists. The value is monotone toward the frontier. Its parity determines membership in the relation. Each superlevel set is a finite union of stratum closures, hence closed. In an alternating chain, going from one affirmative stratum to the next via a negative stratum spends a strict step in each coordinate. Therefore the level is at most \(2d+1\). The reverse inequality follows by alternating \(O_i\times O_i\) with \(O_{i+1}\times O_i\) along a longest orbit chain. This proves the precise level \(n(n+1)+1\) for the finite spectral-support restriction, for both the complex Euclidean and Zariski topologies.

The height theorem is for strict equivalence of pencils. A two-slice tensor problem that also allows changes of the spectral parameter uses a larger group and a different degeneration order.

## Determinant-one row and column changes

**Corollary.** The maximum depth for square complex pencils under \(\mathrm{SL}_n\times\mathrm{SL}_n\), with the parameter fixed, is \(\binom{n+1}{2}-1\).

For a singular square pencil there is at least one right and one left singular block. Scale each of those blocks independently in both spaces. These automorphisms have determinant characters with exponent vectors \((i,i+1)\) and \((j+1,j)\), where \(i,j\) are their minimal indices. The exponent matrix has determinant \(-(i+j+1)\ne0\). The character map onto \((\mathbb C^*)^2\) is therefore surjective. For example, use the adjugate of the exponent matrix and take roots in \(\mathbb C^*\). Thus every general-linear equivalence between singular pencils can be adjusted to a determinant-one equivalence. Normal rank cannot increase in a degeneration, so the singular orbit orders agree. The potential gives the upper bound \(\binom{n+1}{2}-1\) for this locus. The pencil \(P_0\oplus I_{n-1}\) attains it by transferring its \(n-1\) singular units to a single regular block and then following the square \((n-1)\)-chain.

In a regular special-linear chain the determinant polynomial is invariant and nonzero, so every pencil in the chain stays regular. Every strict special-linear degeneration is also a strict general-linear degeneration. Indeed, the special-linear subgroup is normal, so its orbits within one general-linear orbit all have the same dimension, whereas a proper boundary orbit has smaller dimension. Appending the degeneration to zero under the general-linear group gives the upper bound \(\binom{n+1}{2}-1\) on regular chains as well.

More precisely, in a fibre with a fixed nonzero determinant polynomial the degeneration order is the product of Jordan dominance orders at the individual eigenvalues, of sizes given by their multiplicities. To see this, choose an invertible linear combination of slices throughout the fibre and call it \(A\), with \(B\) a fixed complementary combination. The determinant of \(A\) is constant. The change \(A\mapsto A_0\) by left multiplication with \(A_0 A^{-1}\) therefore lies in \(\mathrm{SL}_n\) and is regular throughout the fibre. The residual action on \(A_0^{-1}B\) is conjugation by \(\mathrm{SL}_n\), with the same orbits as ordinary conjugation. The regular normalization carries limits to limits and reflects them via inclusion of the fixed-\(A_0\) slice. Classical Jordan degeneration order on a fixed characteristic-polynomial fibre gives the product assertion. Hence the depth of this fibre is the sum of the nilpotent dominance heights at the eigenvalue multiplicities. The zero determinant fibre instead has the triangular-minus-one height above.
