# Deterministic rank-exact probes for marked tensor substitutions

Let $k=\mathbb F_q$, let $m=h+1$, and use the displayed parameter coordinates of the square-zero slice pencils. Their zero-anchor relations encode the matrix spaces $M,M'\subseteq\operatorname{Hom}_k(k^a,k^b)$. A specified matrix $A$ of rank $r>0$ gives an explicit marked membership probe at coefficient size $mr$, or $mr+1$ with symmetric coefficients. We give an algorithm that generates a small family of such probes from one of the spaces and a known bound on the column support of a witness. The family is chosen before the comparison space is known. [Sharp substitution thresholds](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Threshold.md) · [Two-copy isolation](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Algorithms.md)

## Exact-rank extraction from compressed images

Let $L\le k^b$ have dimension $s\ge r$. Define
$$
 U=M\cap \operatorname{Hom}_k(k^a,L),\qquad
 U^{[r]}=\operatorname{span}_k\{A\in U\colon\operatorname{rk}A=r\},
 \qquad d=\dim U .
$$
Use a basis of $L$ to write $U$ as a space of $s\times a$ matrices. If $r>a$, the answer is the empty list.

**Theorem.** Given bases of $M$ and $L$, one can deterministically construct a basis of $U^{[r]}$ consisting of rank-$r$ matrices. Consequently $\dim U^{[r]}$ marked membership probes, constructed independently of $M'$, suffice to detect every rank-$r$ matrix in $U\setminus M'$. If a probe distinguishes, its matrix is a witness in that exact rank layer. Applying the construction to each side gives a test for rank-$r$ discordance in the supplied column envelope.

More precisely, put $D=r(s-r)$. There is an explicit family $\mathcal P$ of linear maps $k^s\to k^r$ with
$$
 |\mathcal P|\le (D+1)\binom{r\ell}{r},
 \qquad
 \ell=\min\{j\ge 1:q^j>\max(\tbinom s2+1,D+1)\}.
$$

Put $d_P=\dim(PU)$. The construction uses polynomial preprocessing in the input dimensions and $\log q$, polynomial work per map in $\mathcal P$, and polynomial work per projective point of $PU$. In particular it examines at most
$$
 \sum_{P\in\mathcal P}\frac{q^{d_P}-1}{q-1}
 \tag{1}
$$
projective points and produces at most
$$
 \sum_{P\in\mathcal P}(1+d-d_P)\frac{q^{d_P}-1}{q-1}
 \tag{2}
$$
rank-$r$ candidates before basis reduction. Every returned substitution uses coefficients in $k$. With a fixed finite field and bounded $r$ and $\max_P d_P$, this is polynomial time in the presentation size. More generally (1) gives an output-sensitive bound in the compressed image dimensions. When $\ell=1$, one may retain any $D+1$ seeds meeting a verified upper bound on $d_P$, from any larger list of distinct nonzero seeds. The row and column roles can be exchanged by transposing the data matrices.

**Proof.** First assume that each $r$-dimensional subspace of $k^s$ has injective restriction under at least one $P\in\mathcal P$. If $A\in U$ has rank $r$, choose such a $P$ on its column space. Then $PA$ has rank $r$. Its row space is contained in $\operatorname{Row}(A)$ and has the same dimension, so they are equal.

For each $P$, enumerate the projective points of $PU$ and take a nonzero representative $B$ for each. Discard $B$ if its rank is less than $r$. Solve the affine linear system
$$
 A\in U,\qquad PA=B,\qquad \operatorname{Row}(A)\subseteq\operatorname{Row}(B).
 \tag{3}
$$
The last equation means that $A$ kills the kernel of $B$. It is linear in the entries of $A$. Every solution has rank at least $r$ by $PA=B$ and rank at most $r$ by the row condition. If the solution set is $A_0+K$, retain $A_0$ and $A_0+C$ for every member $C$ of a basis of $K$. These points have rank $r$, and their linear span contains the entire affine set, because $C=(A_0+C)-A_0$. Also $K\subseteq\ker(A\mapsto PA)$ on $U$, so it has dimension at most $d-d_P$.

For an arbitrary rank-$r$ matrix $A\in U$, the chosen condenser on its image identifies a projective point $[PA]$ in the enumeration. The corresponding solution set of (3) contains a nonzero scalar multiple of $A$. Thus the candidate points span $U^{[r]}$. Retain a linear basis among them by elimination. A linear space $M'$ contains every rank-$r$ matrix in $U$ exactly when it contains this basis. The marked probes test its elements individually. Among tests of this particular form, the basis cardinality is exact: the span of any smaller set of rank-$r$ probes from $U$ itself is a possible comparison space and leaves a rank-$r$ witness undetected.

## The condenser family and its descent

Associate $u=(u_0,\ldots,u_{s-1})\in k^s$ with $f_u(z)=\sum_{j=0}^{s-1}u_jz^j$. Work temporarily over $K=\mathbb F_{q^\ell}$. Choose $\gamma\in K^\times$ of multiplicative order at least $s$, and choose $D+1$ distinct nonzero parameters $\alpha\in K$. For each $\alpha$ evaluate
$$
 \widehat P_\alpha u =
 \big(f_u(\alpha),f_u(\gamma\alpha),\ldots,
         f_u(\gamma^{r-1}\alpha)\big).
$$
Let $W\le k^s$ have dimension $r$ and choose a polynomial basis of $W$ with distinct leading degrees $e_1,\ldots,e_r$. In the determinant of its evaluation matrix, the coefficient at degree $\sum_j e_j$ is the product of the leading coefficients times the Vandermonde determinant on $\gamma^{e_1},\ldots,\gamma^{e_r}$. It is nonzero. By Cauchy–Binet the determinant is divisible by $z^{r(r-1)/2}$, since the monomial indices used in each minor of the evaluation matrix are distinct. The highest possible degree is $\sum_{j=s-r}^{s-1}j$, so the quotient has degree at most $D$. At most $D$ nonzero $\alpha$ fail to preserve this column space. This is the folded Wronskian rank-condenser argument. [Forbes–Guruswami](https://arxiv.org/abs/1411.7455) · [Guruswami–Kopparty](https://www.math.utoronto.ca/swastik/subspace-designs.pdf)

If $\ell=1$, take the resulting maps directly. If $\ell>1$, write each of the $r$ extension outputs in a fixed $k$-basis of $K$. This gives an $r\ell$-row matrix over $k$. Include every choice of $r$ of those rows in $\mathcal P$, discarding rank-deficient choices. At a successful parameter the linearized restriction to $W$ has rank $r$ over $k$. Some $r$ rows stay independent on $W$, so a base-field map in the list has the required injective restriction. This is a descent of the test matrices. The witness and the substitution remain over the original field.

Construction is deterministic in a finite-field representation with polynomial-time arithmetic and standard coefficient enumeration. At most $\sum_{j=1}^{s-1}j=\binom s2$ nonzero elements satisfy $\gamma^j=1$ for some $1\le j<s$. Thus the first $\binom s2+1$ distinct nonzero elements suffice for finding $\gamma$. The bound on $q^\ell$ supplies these elements and the $D+1$ seeds. When an extension is needed, $q$ is at most the threshold in the theorem and $q^\ell$ is at most $q$ times that threshold. One can enumerate monic degree-$\ell$ polynomials and test irreducibility by modular finite-field powering and gcds, in polynomial time in $s$ and $\log q$ here. In particular, the auxiliary extension does not require a general polynomial-time deterministic factoring or primitive-element algorithm.

For example, suppose $U$ is contained in the sum of arbitrary matrices supported on $a_0$ fixed input columns and a specified $c$-dimensional matrix space. Every $d_P$ is at most $ra_0+c$. For fixed $q,r,a_0,c$, there are $O(s(\log(s+2))^r)$ projected points to examine. The theorem therefore runs in polynomial time even when the number of columns, the column envelope and the aggregate span of row spaces all grow. A single extra high-rank matrix in the $c$-dimensional summand can make the aggregate row-space span large.

## An independent bound from support charts

A second procedure is useful if $s-r$ is small and the compressed spaces in (1) are large. Enumerate the $\begin{bmatrix}s\\r\end{bmatrix}_q$ subspaces $H$ of dimension $r$ in $L$ by reduced echelon matrices, and compute
$$
 U_H=\{A\in U\colon\operatorname{im}A\subseteq H\}
$$
by elimination. In a fixed basis of $U_H$, enumerate vectors with at most $r+1$ nonzero coordinates from a fixed set of $\min(q,r+2)$ field elements that contains zero. Retain vectors whose matrices have rank $r$. For a given $H$ this requires at most
$$
 \sum_{j=0}^{r+1}\binom{\dim U_H}{j}\min(q-1,r+1)^j
$$
tests, with the usual zero convention for out-of-range binomial coefficients.

These candidates span the exact-rank part of $U_H$. Otherwise some linear functional $\lambda$ vanishes on their span while $\lambda(A)\ne0$ for a rank-$r$ matrix $A\in U_H$. Choose an $r\times r$ minor $\Delta$ nonzero at $A$. The polynomial $\lambda\Delta$, in the basis coordinates of $U_H$, defines a nonzero function of total degree at most $r+1$. Reduce exponents using $x^q=x$ to individual degrees at most $q-1$. Some nonzero monomial survives, and setting the coordinates outside its support to zero keeps that coefficient. On these at most $r+1$ coordinates, the restricted polynomial has individual degrees less than the selected grid size. A nonzero polynomial of these individual degrees cannot vanish on the full product grid, by induction using the univariate root bound. A grid point with $\lambda\Delta\ne0$ gives a rank-$r$ candidate outside the proposed span, a contradiction. Every rank-$r$ matrix in $U$ belongs to $U_H$ for its own column space $H$. Taking a basis of all the retained candidates therefore gives the same query count.

If rank $r$ is known to be the *first* discordant layer below the column envelope, exact witness extraction becomes simpler on these charts. Compare the two intersection spaces in each $H$, and return a basis vector of one that is outside the other. It has rank at most $r$ by its support and at least $r$ by the first-layer promise. Either support procedure works on each member of any supplied finite list of column envelopes. Their hypothesis only requires a witness covered by the list.

The slack version has a related elementary bound. For $0\le c\le s-r$, project $L$ onto a fixed $(r+c)$-dimensional space and pull back its $r$-dimensional subspaces. Every rank-$\le r$ column support is contained in one of the resulting $(s-c)$-planes. This follows by extending the image of the support to dimension $r$ in the quotient. There are $\begin{bmatrix}r+c\\r\end{bmatrix}_q$ planes in the family. Comparing intersections finds a witness of rank at most $s-c$ whenever a rank-$\le r$ discordance exists and its columns lie in $L$. When $M,M'$ are nested, one can make these comparisons by dimensions alone. For general pairs, use exact spaces. This is the standard covering-design bound applied to the rank budget. [Etzion–Vardy on Grassmannian coverings](https://arxiv.org/abs/0912.1503)

## Finite controls

Over $\mathbb F_2$ take $s=a=3$ and $r=2$, with auxiliary field $\mathbb F_2[\omega]/(\omega^3+\omega+1)$, $\gamma=\omega$, and parameters $1,\omega,\omega+1$. Writing the two outputs in the ordered basis $1,\omega,\omega^2$, the construction gives 14 distinct full-rank ordered row-pair maps after deduplication. Exhaustive enumeration checked that all seven binary planes have an injective restriction under at least six of the maps.

The same control enumerates each source space in the table and its rank-two elements. Here $x,y,z$ are three rows, with coordinates numbered $1,2,3$. For every resulting $B=PA$, keep matrices whose rows belong to the span of $B$, then select a basepoint and basis differences inside each fiber. The span of their retained rank-two points agreed with the span of all rank-two matrices in every case.

| Source rows or equations | Source size | Rank-two elements | Retained span dimension |
|---|---:|---:|---:|
| Arbitrary $(x,y,z)$ | 512 | 294 | 9 |
| $(x,y,0)$ | 64 | 42 | 6 |
| $(x,y,x+y)$ | 64 | 42 | 6 |
| $x_1=y_2,\ z_3=x_3$ | 128 | 76 | 7 |
| $(x,0,0)$ | 8 | 0 | 0 |

## Scope

The one-sided family uses the source matrix space and a supplied envelope. The sharper time bound uses the actual compressed-image dimensions and applies even if lower ranks also have discrepancies. It gives an exact candidate extractor, followed by the prior sharp substitution construction. For finite chain-ring carriers, apply the extraction over the residue field and lift the centered coefficients as in the prior construction. When comparing arbitrary unknown spaces at the first possible coefficient size, neither the supplied source nor a bounded compressed-image dimension is automatic.

The novelty candidate is the use of compressed affine fibers to produce comparison-independent, exact-rank marked query bases. The folded Wronskian and Grassmannian covering are established results. Unrestricted first-layer search contains binary code minimum distance, including on diagonal data spaces. The proof is in prose and the primary-source search did not establish publication priority. [Vardy, minimum distance](https://doi.org/10.1145/258533.258559)
