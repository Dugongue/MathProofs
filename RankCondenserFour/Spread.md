# Exact probe complexity at the sharp substitution threshold

Let $k=\mathbb F_q$, $n\ge2$, and $m=h+1$ with $h\ge2$. There is an explicit same-format family of marked square-zero pencils indexed by a zero case and by the $N=(q^n-1)/(q-1)$ lines of $k^n$. Queries return the rational canonical form of an evaluated pencil. The question is whether the unknown instance is zero or indexed by a line. This is a black-box model in which the query algorithm knows the full family and its coordinate conventions. It receives the probe responses from the unknown instance.

**Theorem.**
1. Through coefficient size $m$, the exact deterministic query complexity is $N$, even allowing arbitrary coefficient matrices and adapting to their full rational canonical forms. Each query at size $m$ can reveal at most one hidden line. The minimum worst-case query count for two-sided error $\epsilon\in[0,1/2)$ is
$$
\left\lceil \frac{1-2\epsilon}{1-\epsilon}\,N\right\rceil .
$$
2. For the marked pure-data first-row probes of maximum size $mt$, with $1\le t\le n$, the exact deterministic count is
$$
B=\left\lceil\frac{q^n-1}{q^t-1}\right\rceil.
$$
An explicit $q$-cover attains it. When $t\mid n$, a field-reduction spread attains the same randomized formula with $B$ in place of $N$. For arbitrary $t$, the randomized upper and lower bounds are within one query.

In both clauses the ordinary and normalized last-two-mode symmetric pencils have the same bounds. Clause 2 uses the stated marked first-row family. It compares exact finite families of wider probes with the unrestricted sharp-size result of Clause 1.

## The family

In the [sharp substitution construction](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md) choose data format $n$ by $n$ with one slice. The data space for a line $kx$ is $M_x=k(xx^{\mathsf T})$, and the zero case is $M_0=0$. Write $Z=E\oplus F$ for the two $n$-dimensional data spaces. The augmented rectangular block is $[aI+\widetilde A,bI]$ with $A:E\to F$, and its replicated quadratic space $H_x$ has the same two anchor quadrics as $H_0$. It has one additional quadratic $Q_x$. This has polar rank $2m$. Its support is
$$
\mathcal S_x=X_x\oplus Y_x,
$$
where $X_x$ is the span of the $m$ copies of the data column line in the $F$-slots on the first half, and $Y_x$ the span of the $m$ copies of the data row line on the other half. Distinct projective lines $kx$ give disjoint supports, since in each independent copy their corresponding factor lines intersect in zero. Any relation with a nonzero anchor has polar rank $4mn>2m$, because $aI+\widetilde A$ is invertible for $a\ne0$ and the other block is invertible for $b\ne0$.

The usual padded quotient is $W=(\operatorname{Sym}^2 V/H_x)\oplus W_{\rm in}$ with uniform dimension. For a coefficient array $U=(u_{ij})\in M_b(V)$, its centered map $C_x(U):V^b\to W^b$ sends a tuple $(v_j)$ to the row products $\sum_j[u_{ij}v_j]_{H_x}$. Before taking the quotients, all those row products have the same formula in the zero and line cases. As $H_0\subset H_x$, their kernels satisfy $\ker C_0(U)\subseteq\ker C_x(U)$. Every difference of kernels is a rank difference.

## Only one line can separate at size m

We use a quadratic support property. If $Q$ has polar rank $2m$, $L$ has dimension at most $m$, and $Q\in LV$, then $\dim L=m$ and $L$ is in the polar image of $Q$. Indeed in a basis adapted to $L$ the polar matrix is
$$
\begin{pmatrix}A&B\\B^{\mathsf T}&0\end{pmatrix}.
$$
Its rank is at most $\dim L+\operatorname{rank}B$. The bound forces $B$ to have full row rank and the polar image then contains $L$. This argument works in characteristic two.

Suppose a centered array of size $m$ gives different ranks in the line and zero cases. Take a tuple $(v_j)$ lying in the larger kernel alone. Each row product lies in $H_x$ and has polar rank at most $2m$. The high-rank anchor terms are therefore absent. At least one row product is a nonzero multiple of $Q_x$. Put $A=\operatorname{span}\{v_1,\ldots,v_m\}$. From that row, the preceding support property shows that the $v_j$ are independent and that $A\subseteq\mathcal S_x$.

In any row with nonzero product, apply the same support property to the span of that row's $u_{ij}$. In a row with zero product, reducing $\sum_j u_{ij}v_j=0$ in $AV/\operatorname{Sym}^2 A\simeq A\otimes(V/A)$ shows all $u_{ij}\in A$. Thus every entry of a separating array belongs to $\mathcal S_x$. Since distinct supports intersect in zero, a nonzero array separates at most one line.

Now consider the scalar coefficient $S=Y_0$ and every irreducible power $f=p^j$ used to determine a rational canonical form. The evaluated matrix is
$$
E_x=\begin{pmatrix}S\otimes I_V&0\\C_x(U)&S\otimes I_W\end{pmatrix}.
$$
Products with two centered factors vanish even when scalar coefficient blocks intervene. Thus $f(E_x)$ has common scalar coefficient $f(S)$ and a centered array $C_x(U_f)$ whose directions are linear functions of $U$ independent of $x$.

If $f(S)\ne0$, row and column reduction of the scalar part leaves the centered map from $\ker f(S)\otimes V$ to $\operatorname{coker}f(S)\otimes W$, plus a common rank contribution. The centered map has fewer than $m$ coefficient columns. Each row uses fewer than $m$ directions, so its products intersect both $H_0$ and $H_x$ in zero by the polar-rank bound. Matching each row's image gives equality of ranks. The same argument works before any polynomial evaluation at all matrix sizes below $m$.

If some irreducible power annihilates $S$, its minimal polynomial is $p^e$ for that unique irreducible $p$. Only $p^e$ itself can detect a difference. In fact with $G_x=p(E_x)^e$ and $B=p(S)^{j-e}$ for $j>e$, the centered block of $p(E_x)^j$ is
$$
(B\otimes I_W)C_x(U_{p^e})=C_x(U_{p^e})(B\otimes I_V)
$$
because $G_x$ commutes with powers of $p(E_x)$. If $B=0$ it vanishes. Otherwise $B$ is nilpotent and has rank below $m$. The map factors on input through the image of $B\otimes I_V$. Restrict the centered array to that image in common coefficient coordinates. Again it has fewer than $m$ coefficient columns, and ranks agree. Consequently any query of size $m$ is governed, for possible differences, by at most one centered array $U_{p^e}$. The centered support argument proves the claim even for the full rational canonical form.

For the normalized symmetric carrier the second summand is the transpose of the ordinary evaluation at $(S^{\mathsf T},U^{\mathsf T})$. Its common scalar coefficient has the same minimal polynomial. For an ordinary polynomial, the new array in this transposed probe is $U_f^{\mathsf T}$: each term with one centered factor transposes into another term with the scalar factors reversed. If either summand can detect a line, the entire common array $U_{p^e}$ has entries in that line's support, by the preceding argument applied to it or its transpose. This again permits at most one line. Possible differences are rank decreases from the zero case on both summands, since the defining relation inclusion enlarges the kernels, so they cannot cancel.

Conversely at size $m$ put a basis of $X_x$ in a single centered row, with all other rows zero. Then $Q_x\in X_xV$. The anchors are absent in this product space, and the row image rank decreases by one exactly on the line case $x$. This yields a test for each projective point. The transpose-side rank is common in the normalized symmetric case: with transposed coefficient array it is a single column of maps, one of which is injective because $H_x$ contains no product of two nonzero linear forms. Hence the same tests work there.

## Exact wider-probe complexity from a spread

In this part use only the marked pure-data first-row probes: the scalar coefficient and all rows but the first are zero, and its directions lie in the first-half data slots $F^{\oplus m}$. Write $L\subseteq F^{\oplus m}$ for their span, with dimension at most the probe size. The row measures $\dim LV-\dim(H_x\cap LV)$. A nonzero anchor cannot occur in $H_x\cap LV$ at any width of this family. Its terms in the first-half $E$ coordinates survive on projection away from $F^{\oplus m}$, and the two anchor terms there are independent.

Because $L$ is in the first half, the independent second-half forms of $Q_x$ force exactly its column forms to vanish modulo $L$ if $Q_x\in LV$. Thus the probe distinguishes precisely
$$
\{kx:X_x\subseteq L\}
= \mathbb P(D_L)(k),\qquad
D_L=\{x\in F:e_j\otimes x\in L\text{ for every repetition }j\}.
$$
Here $D_L$ is a linear subspace, and $k^m\otimes D_L\subseteq L$. A probe of size at most $mt$ therefore covers at most $(q^t-1)/(q-1)$ line cases. Every subspace $D\subset F$ of dimension $t$ is realized by the array consisting of a basis of $k^m\otimes D$ in one row of size $mt$. Since these evaluations are square-zero, their canonical forms are determined by rank. The transpose-side contribution in the normalized symmetric case is again the same in both inputs, by the single-column argument above.

When $t\mid n$, identify $F$ with $\mathbb F_{q^t}^{n/t}$ over $k$. The one-dimensional $\mathbb F_{q^t}$-subspaces give a partition of the nonzero vectors into $k$-subspaces of dimension $t$. Their projectivizations partition the line cases into $B=(q^n-1)/(q^t-1)$ groups of the maximum allowable size. The corresponding probes are an explicit exact cover. Equivalently the spread is a strong subspace design for rank one: each $k$-line intersects exactly one member nontrivially. This connects the query bound to the dual, kernel formulation of subspace designs. The construction works by field reduction with any fixed presentation of $\mathbb F_{q^t}$ and produces the advertised number of probes. [Etzion–Vardy, $q$-covering designs](https://arxiv.org/abs/0912.1503) · [Forbes–Guruswami, rank condensers and subspace designs](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2015.800)


When $t$ need not divide $n$, an explicit covering of the same optimal size follows by recursion. For $n=t$ take the whole space. For $t<n<2t$, take a common subspace of dimension $2t-n$ and pull back a spread of dimension $n-t$ in the quotient of dimension $2(n-t)$. This uses $q^{n-t}+1$ subspaces of dimension $t$. For $n\ge2t$, write the space as $D\oplus\mathbb F_{q^{n-t}}$, where $D$ is a $t$-dimensional $k$-subspace of $\mathbb F_{q^{n-t}}$ in the first coordinate. For every $a$ in the extension field use the subspace $\{(x,ax):x\in D\}$. Each vector with first coordinate nonzero lies in exactly one of these graphs. Recursively cover the vectors with first coordinate zero. The recurrence is
$$
B(n,t)=q^{n-t}+B(n-t,t).
$$
The base cases and the recurrence give $B(n,t)=\lceil(q^n-1)/(q^t-1)\rceil$, which meets the point-counting lower bound. This is the rank-one covering number computed by Etzion and Vardy. In the present application each covering subspace becomes one matrix-substitution query. [Etzion–Vardy, Theorem 4.6](https://arxiv.org/abs/0912.1503)

## Exact adaptive and randomized bounds

For deterministic queries, follow the algorithm on the zero case. Any line not detected by a probe on this path produces the identical transcript, by induction on adaptive queries. Each probe covers at most one line in Clause 1, and at most $(q^t-1)/(q-1)$ lines in Clause 2. Thus the zero path must use at least $N$ or $B$ probes, respectively. Enumerating the individual tests or the explicit covering tests attains the corresponding bound.

For a randomized algorithm fix its internal randomness and couple its zero run to its run on a given line $x$. Until a probe hits $x$, both runs have the same responses and make the same decisions. Write $p_0$ for the probability the zero run answers YES, so $p_0\le\epsilon$. If the line run answers YES then either the zero run answers YES or the zero run answers NO and its path hits $x$. To obtain line success at least $1-\epsilon$ we need
$$
\Pr(\text{zero run answers NO and its path hits }x)
\ge 1-\epsilon-p_0 .
$$
Let $a$ be the maximum number of probes and $C$ the maximum number of lines covered by a single probe in the permitted model. Summing over $x$ gives $N(1-\epsilon-p_0)\le (1-p_0)aC$. Because $p_0\le\epsilon$, this implies $a\ge (N/C)(1-2\epsilon)/(1-\epsilon)$.

For equality in Clause 1 and in Clause 2 when $t\mid n$, let $B_*$ be $N$ or $B$ as appropriate and set $a=\lceil B_*(1-2\epsilon)/(1-\epsilon)\rceil$. With probability $\epsilon$ answer YES immediately. Otherwise choose $a$ distinct blocks uniformly from the corresponding partition, and answer YES exactly when one of their probes detects the line. The zero error is $\epsilon$. A line has success $\epsilon+(1-\epsilon)a/B_*\ge1-\epsilon$. This establishes exactness in these cases.

For $t$ that does not divide $n$, let $\kappa=(1-2\epsilon)/(1-\epsilon)$ and $B_{\rm frac}=(q^n-1)/(q^t-1)$. The same coupling gives the lower bound $\lceil\kappa B_{\rm frac}\rceil$. Sampling uniformly from the explicit cover with $\lceil \kappa B(n,t)\rceil$ queries gives at least the required success probability because each line belongs to at least one member. Thus the upper and lower bounds differ by at most one query.

The results concern only the stated oracle observations. They give optimal adaptive probe families even though the individual pencils are explicit and small. The higher-width tradeoff concerns the marked pure-data first-row family. Publication priority for the exact conclusions remains unconfirmed.

Exact controls checked 68 size-three probe configurations over the binary and ternary fields (including scalar Jordan blocks, scalar shifts, and conflicting rows for different hidden lines) and 21 parameters of the recursive binary cover.
