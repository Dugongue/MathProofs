# Algebraic algorithms for four catalogue targets

## GP-0605 · Newton faces of ROABPs preserve width

**Theorem.** Over every field, every nonzero face polynomial of an ROABP output has width at most the original width in the same variable order, including for exposing weights of arbitrary bit length and in the presence of internal cancellation.

At a prefix cut let $C$ be the coefficient flattening. Give each row the weight of its prefix monomial and each column the weight of its suffix monomial. If $M$ is maximum support weight, every nonzero entry has combined weight at most $M$. The face matrix $C'$ keeps only combined weight $M$. In a minor of size $j$, all permutation products have the same combined weight $W$, the sum of the selected row and column weights. If $W\ne jM$, every product for $C'$ is zero. If $W=jM$, every nonzero product for $C$ uses only entries of weight $M$, since $j$ integers each at most $M$ can sum to $jM$ only if all equal $M$. Thus every minor of $C'$ is zero or equal to the corresponding minor of $C$, and rank cannot rise.

At each cut choose a basis of the span of suffix coefficient polynomials obtained by fixing a prefix monomial. Its size is the cut rank. Coefficient extraction in the next variable carries every basis element into the next span and gives the univariate transition matrices. The initial basis is the given polynomial and the final basis is $1$. Composing gives the required ROABP. This proves the width bound without finding the maximizing monomial from the internal paths. [ROABP closure questions](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.9/LIPIcs.ITCS.2026.9.html)

## GP-0640 · Compute the optimal degree of TPP separators

**Theorem.** Given coordinate lists for a finite TPP triple in a matrix group, find the minimum common total degree of ordinary matrix-entry separating polynomials and a shared circuit realizing them in polynomial field-operation time. Over rational coordinates in binary the degree and the shared basis representation are computable in polynomial bit time. Allowing complex coefficients on the rational input gives the same degree.

Let $P=XY^{-1}YZ^{-1}$ as a set of points and $N=|P|$. For nonempty lists the points $xz^{-1}$ belong to $P$ and are all distinct by the TPP. Let $D_\ell$ be the diagonal matrix of entry $\ell$ at $P$. If $E_d$ is the space of evaluation vectors of degree at most $d$, then
$$
E_0=\langle\mathbf1\rangle,\qquad E_{d+1}=E_d+\sum_\ell D_\ell E_d .
$$
Retain an independent subset of the old basis and its coordinate products. Each vector then has an actual monomial representative, stored by a predecessor pointer. At each step test whether all standard vectors for distinguished points belong to $E_d$. The first success is the exact minimum. The procedure stops by $N-1$: a point indicator is the product of one normalized linear coordinate difference for each other point. The shared representation uses the retained monomials and one solved coefficient vector per separator.

The number of coordinates and $N\le |X||Y|^2|Z|$ are polynomial in the coordinate-list input. Rational inversion and multiplication have polynomial bit complexity. At degree $N-1$ the basis evaluations are products of at most $N-1$ coordinates, so their binary lengths are polynomial. Fraction-free elimination or minor bounds give polynomial bit bounds for all rank tests and solutions. Scalar extension preserves the membership tests. [Blasiak–Cohn–Grochow–Pratt–Umans, Definition 2.1](https://arxiv.org/html/2410.14905#S2)

## GP-0542 · Tangent realization for layered ABP varieties

**Theorem.** Fix a layered ABP architecture of depth $L$ over a characteristic-zero field, with each layer matrix in a specified linear space of permitted labels. At a Zariski-generic point of its output variety over the algebraic closure, every embedded tangent vector is realized at depth $L$ and at most twice the original intermediate widths. Each new edge respects the corresponding layer's label restrictions. This covers linear restrictions that enforce degree or allowed variable blocks.

The polynomial parameter map sends $A_1,\ldots,A_L$ to their product, with scalar input and output. It is dominant onto the closure of its image. In characteristic zero the function field extension is separably generated, so the differential has generic rank equal to the image dimension. The smooth locus and the nonvanishing of a full-rank minor give a nonempty open set where the differential surjects onto the tangent space. Its image is dense and constructible and contains an open set of the output variety. For an output there, realize a variation $(B_i)$ of its chosen preimage by multiplying
$$
\begin{pmatrix}A_i&B_i\\0&A_i\end{pmatrix}.
$$
The upper-right output is $\sum_i A_1\cdots A_{i-1}B_iA_{i+1}\cdots A_L$. Select its row and column at the endpoints. Applying a subsequent linear degree-preserving projection gives the same differential argument for the projected image. A finite union of architectures is handled at a generic point of each component by choosing a dense architecture for that component. [ABP complexity background](https://arxiv.org/abs/2003.04834)

## GP-0549 · Intersect two succinct spans by evaluations

**Theorem.** Given lists of circuits for two degree-$d$ polynomial spaces, compute circuits for a basis of their intersection in bounded-error polynomial arithmetic time without multivariate coefficient expansion. Evaluating just the degree-$d$ homogeneous part of each listed circuit is also allowed, using truncated univariate scaling when the parts are not supplied separately.

Let $g_1,\ldots,g_m$ be all listed polynomials and $W$ their joint span. Draw $m$ independent evaluation points from $S^n$ with $|S|\ge md/\epsilon$ over the field or an extension. When the remaining evaluation kernel on $W$ is nonzero, fix a nonzero polynomial in it after extending scalars. The next point cuts the kernel dimension with probability at least $1-d/|S|$. Since $\dim W\le m$, the conditional bounds and union bound give injectivity on $W$ with failure probability at most $\epsilon$. For $d=0$, a single evaluation suffices.

Intersect the two evaluated column spans by Gaussian elimination, keeping coefficient vectors to lift a basis to the original lists. For extension-field evaluations express entries in base-field coordinates, so all output combinations lie over the original field. Injectivity on the entire joint span suffices even when either list has redundancies. For a fixed finite field the extension degree is logarithmic in the arithmetic parameters at fixed error, and one can find a modulus by exhaustively testing monic candidates inside a polynomial-size extension. This is an arithmetic-time claim for arbitrary fields and a bit-time claim for fixed finite fields with ordinary encodings. [Arithmetic PIT background](https://arxiv.org/abs/2306.02184)
