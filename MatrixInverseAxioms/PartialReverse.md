# Sparse size with a partial reverse inverse

Over a field $F$, take independent matrices $P,Q$ of respective shapes $s$ by $r$ and $r$ by $s$, with $s=r+g$ and $g\ge1$. Fix a subset $T$ of the $r$ small-side indices with $|T|=t$, and write $U$ for its complement, of size $k=r-t$. Let $P_T$ be the column submatrix indexed by $T$ and $Q_T$ the corresponding row submatrix. Give ordinary Polynomial Calculus just the equations
$$
 PQ=I_s,\qquad Q_TP_T=I_t.
$$
For every fixed $C_0>0$ there are constants $c,C>0$ such that, for all sufficiently large $s$ and every $0\le k\le r$ with $g\le C_0(k+1)$, the minimum sparse size is between
$$
 s^{c(k+1)} \quad\text{and}\quad s^{C(k+1)}.
$$
The degree bounds hold for every gap, with no condition on $C_0$. The minimum degree is between $k+2$ and $\min(r+2,2j)$, where $j$ is the first index greater than $k$ with $\binom{s-t}j\ne0$ in $F$. The same bounds hold with $Q=P^T$ and with just the corresponding restricted reverse Gram block. In particular if both sides are proportional and the number of omitted indices is linear in $s$, the size is $s^{\Theta(s)}$ even when the characteristic divides $g$. At unit gap $g=1$ the theorem gives $s^{\Theta(k+1)}$ uniformly in $k$, including bounded $k$. The lower bound counts all monomial occurrences on used lines and allows proofs of arbitrary degree. No field equations are used.

At unit gap and $k=0$ the exact size is $\Theta(s^2\log s)$ and the degree is two. At $k=r$ the degree is exactly $r+2$, and the size is $s^{\Theta(s)}$ when both sides are proportional. [Trace endpoint](https://github.com/Dugongue/MathProofs/blob/55f3f9c1c78a81d4d617f902845a8c94a8455c33/SparseMatrixProofBounds/CriticalMatchings.md) · [One-sided endpoint and expander transfer](OneSidedMatrix.md)

## Upper bound by characteristic coefficients

Write $M=P_UQ_U$ and $W=P_TQ_T$. The forward inverse equation gives $M=I_s-W$. For a square matrix $D$, let $e_i(D)$ be the sum of its size-$i$ principal minors, with $e_0(D)=1$ and $e_i(D)=0$ when $i$ exceeds the side. For every $j>k$ we have the polynomial identities
$$
 e_j(M)=0,\qquad
 e_j(I_s-W)=\sum_{i=0}^j(-1)^i\binom{s-i}{j-i}e_i(W),
 \qquad e_i(W)=e_i(Q_TP_T).
$$
The first and third identities are Cauchy–Binet for a rectangular product. The second follows by expanding $\det(I_s+z(I_s-W))$ in the columns and extracting the coefficient of $z^j$. It holds integrally.

From $M=I_s-W$, derive $e_j(M)-e_j(I_s-W)=0$ term by term using a telescoping difference of products. In the same way replace $e_i(Q_TP_T)$ by $\binom ti$ using the available reverse equations. The scalar sum is $\binom{s-t}j$, since it is the $j$-th coefficient of
$$
 \sum_{i=0}^t\binom ti(-z)^i(1+z)^{s-i}
 =(1+z)^{s-t}.
$$
Choose the indicated first nonzero coefficient, which exists because $\binom{s-t}{s-t}=1$. There is no division by a field integer until rescaling the nonzero constant. Both derivations use degree at most $2j$. For an individual expanded determinant product there are at most $j$ telescoping summands and their factors are polynomials with at most $O(s)$ monomials. Generate products by multiplying by a single variable at each step and sum in binary trees. The total monomial cost for one determinant product is $O(j s^j\log(2s))$. The number of such products per coefficient of order $i\le j$ is at most $s^i$. Accounting for all coefficients and their binary sums gives $s^{2j+O(1)}$ sparse size. Now $j\le s-t=k+g$. The cofactor proof using only $PQ=I_s$ alternatively gives degree $r+2$. Substituting $Q=P^T$ gives the same upper estimates in the symmetric case.

## Lower bound by random pinning and expander sparsification

Choose a uniform injection of the $t$ constrained-column indices into the $s$ target rows. Set each chosen edge to one in both matrices and every other edge incident with a pinned endpoint to zero. After this substitution all reverse axioms vanish. The forward axioms become zero or the one-sided inverse equations on $k$ fixed free columns and $k+g$ uniformly chosen target rows. In the symmetric case the same substitution leaves the one-sided symmetric Gram equations. Thus the exact-degree lower bound for the one-sided Rank Principle gives degree at least $k+2$ for $k>0$, regardless of which injection was chosen. At $k=0$ every original usable axiom is quadratic and the lower bound is two.

For large $k$, apply the bounded-degree bipartite boundary expander from the one-sided construction to the residual $(k+g)$-by-$k$ rectangle, independently permuting its $k$ columns. The sizes are proportional by $g\le C_0(k+1)$. Label the residual target rows in increasing order for this construction. Let $\Delta$ be its row-degree bound. Substitute its edge variables on the allowed positions of the residual matrices, using the same variable for transposed positions, and zero elsewhere. The degree lower bound for its functional pigeonhole formula implies that some original monomial survives normalization with $d=\lfloor c_0 k\rfloor$ or more distinct live matching edges, for a fixed $c_0>0$ small enough that $d\le k/2$. Otherwise immediate normalization yields a PC refutation of that formula of degree at most $\max(\Delta,d,2)$. This holds for every choice of the random pinning and residual column permutation. [Normalization and source lower bound](OneSidedMatrix.md) · [Mikša–Nordström, Theorem 5.8](https://jakobnordstrom.se/docs/publications/GeneralizedMethodPCdegreeJournal.pdf)

To bound the probability for a fixed original monomial, only its positions incident with the $k$ free columns matter. These free-column positions are determined before sampling. If any of those positions has a nonlive target endpoint, the monomial vanishes. If any two distinct positions conflict, either it vanishes under substitution or the product has zero matching normal form. If there are fewer than $d$ positions it cannot witness the claimed degree. Otherwise choose any fixed $d$ of its positions. All their target rows must survive the uniform pinning and then their columns must align with allowed edges of the expander after the independent permutation. The probability is at most
$$
 \frac{(k+g)_d}{(s)_d}\frac{\Delta^d}{(k)_d}
 \le \left(\frac{4(1+2C_0)\Delta}{s}\right)^d ,
$$
where $(v)_d=v(v-1)\cdots(v-d+1)$. Here $d\le k/2$, and the two ratios estimate sampling without replacement on the two sides. The calculation ignores the additional possibility that some other factor of the monomial is killed by pinning. Since some occurrence witnesses degree $d$ for every outcome, the union bound gives $s^{\Omega(k)}$ size for all sufficiently large $k$. For bounded $k$, the gap hypothesis bounds $g$, and every original nonzero axiom has at least $r$ monomials, giving $\Omega(s)$ size. Combining these estimates and decreasing the exponent constant gives $s^{\Omega(k+1)}$ uniformly, with constants depending on $C_0$. The sharper trace lower bound at unit gap and $k=0$ applies to the symmetric version as well, because it evaluates both variables of a transposed pair at the same Boolean matching entry.

## Literal matrix conjugacy

Take complementary diagonal projections of ranks $r,s$ on $n=r+s$ coordinates. Keep $XA=BX$, all entries of $XY=I$, and the principal $T$ block of $YX=I$ within the rank-active source label of size $r$. The exact same interpolation holds, with sparse size $n^{\Theta(k+1)}$ under the stated gap condition and the same degree bounds.

Indeed $XA=BX$ gives the crossing entries of $X$ as zeros, so each desired restricted inverse entry is extracted in degree two by eliminating crossing products. This costs only polynomial sparse size. For the reverse direction specialize both variables in their eigenvalue blocks. Use $P,Q$ on the target-enlarging block, a fixed coordinate inclusion and projection on the other block, and zero on crossings. Every original input becomes zero or a literal partial inverse input. Thus the sparse and degree lower bounds survive. At $k=0$ and unit gap the diagonal trace proof needs only the relevant entries of both products, giving the same sharp $\Theta(n^2\log n)$ as when all reverse equations are given. These arguments establish the comparison for the displayed principal-block pattern of reverse axioms.
