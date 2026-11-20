# A fifth Fourier moment reads two signs on raw ternary tensors

Work over $\mathbb F_3$. Write $P_j$ for three-tensor isomorphism with determinant one in $j$ designated modes. The main result is a deterministic same-field many-one reduction from $P_3$ to $P_1$ on the raw pencil family below. On an explicit unbounded family the last sign is freely correctable, so the same construction reduces $P_3$ to ordinary TI. The family has all three mode dimensions even, is concise, and has only scalar pair adjoints. [Classical tensor actions and the unrestricted question](https://arxiv.org/html/2306.03135v2#S1.SS5)

## 1. The raw sign test

Write a raw tensor as a square matrix pencil $M(z)$ of size $2n$ on a label space $W$, where $n$ is even. A transporter from $T$ to $S$ satisfies
$$M_S(Cz)=P M_T(z)Q^t.$$
On the source, suppose the linear space of right multipliers $B$ for which every $M_T(z)B$ is alternating is a line containing an invertible matrix. Choose one generator $B_T$ by elimination and put $\widehat M_T=M_TB_T$. Let $p_T=\operatorname{Pf}(\widehat M_T)$ in the raw matrix coordinates. Suppose $p_T$ is nonzero and splits into base-field linear factors, counted with their multiplicities.

Write $\chi(0)=0,\ \chi(1)=1,\ \chi(-1)=-1$ as an integer-valued function. For $F(z)=\chi(p(z))$, define
$$J(F)=\sum_{x_1,x_2,x_3,x_4\in W}
   F(x_1)F(x_2)F(x_3)F(x_4)F(x_1+x_2+x_3+x_4).$$
Assume $J(F_T)\ne0$. For the finite evaluation bound let $t$ be the dimension of the relations among the distinct projective factor lines, counted once per factor. If $t=O(\log L)$ for dense input length $L$, the reduction takes deterministic polynomial time. More generally the maximum relation dimension of one factor-matroid component suffices. The theorem uses a promise on the source pencil. It receives the input arrays without factors, multipliers, or transporters. The second tensor is unrestricted.

Here is the exact calibration. If an ordinary transporter exists, the right multiplier lines correspond and $S$ has an invertible generator $B_S$. The normalized transporter is $(P,\widehat Q,C)$, with $\widehat Q=B_S^t Q B_T^{-t}$. Alternation of $P^{-1}\widehat M_S(Cz)P^{-t}$ forces $\widehat Q^t P^{-t}=sI$ for some $s\ne0$. It follows that
$$p_S(Cz)=s^n\det(P)p_T(z)=\det(P)p_T(z),\qquad
 \det Q=(\det B_T/\det B_S)\det P.$$
The first equality uses even $n$ and the second uses even matrix size $2n$. The fourfold change of variables using $C$, together with its preservation of addition, gives
$$J(F_S)=\det(P)J(F_T).$$
Consequently every ordinary transporter has the same two matrix-side determinants, computed from $J(F_S)/J(F_T)$ and the basis calibration. If the target multiplier or factor extraction fails, the correlation magnitudes disagree, or the forced first two signs are wrong, produce a fixed NO instance. In all other cases retain the original tensor pair and the one physical sign on the label mode. A determinant sign equals its inverse over $\mathbb F_3$, so the dual label convention makes no difference. The recovery and extension assertions concern the actual original transporter in both directions. The multiplier equation alone already links the two matrix signs. The fifth moment determines their common sign without using any isomorphism query.

## 2. Exact evaluation from the Fourier projection

Use the finite form of Alpöge–Buckmaster's normalized harmonic projection. The normalized average of a phase is one on zero frequency and zero on every other frequency. Here $\omega$ is a primitive cube root of unity, and the averaging is over the additive group of a relation space. The fifth correlation is the fifth Fourier moment divided by $|W|$ when $F$ is even. Evenness holds here because $p$ has even degree. The fourfold additive expression also gives the covariance directly. [Navier–Stokes torus phase lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126-L151)

Normalize each distinct factor $\ell_i$ by its first nonzero coefficient and write $p=c\prod_{i=1}^{s}\ell_i^{e_i}$. Let $L_W$ send $z$ to $(\ell_i(z))_i$, let $r$ be its rank, and put $D=\ker L_W^t$, with $t=\dim D$. Then $\operatorname{im}L_W=D^\perp$. Encode $a+b\omega$ as an integer pair and use $\omega^2=-1-\omega$. For $e>0$, set $\varphi_e(u)=0$ at zero and $\varphi_e(u)=\chi(u)^e$ elsewhere. Precompute the two small tables
$$H_e(a)=\sum_{x\in\mathbb F_3^4}\omega^{a\cdot x}
     \left(\prod_{j=1}^4\varphi_e(x_j)\right)\varphi_e\left(\sum_{j=1}^4x_j\right),$$
one for each parity of $e$. Each local table has only $3^4$ entries. For $x\in\mathbb F_3^s$,
$$1_{D^\perp}(x)=3^{-t}\sum_{a\in D}\omega^{a\cdot x}.$$
If one pairing is nonzero, translating the summation by a vector with that pairing multiplies the sum by a nontrivial cube root, so it vanishes. Substituting this projector for each of the four label sums and factoring over coordinates gives the exact formula
$$
J=\chi(c)\,3^{4(\dim W-r)-4t}
\sum_{a^1,\ldots,a^4\in D}\prod_i H_{e_i}(a_i^1,\ldots,a_i^4).
$$
The result is an integer, as is already clear from the defining sum. The intermediate integers have polynomial bit length since each local table has absolute sum bounded by a constant and the enumeration has $3^{4t}$ terms.

A factor-matroid component is a set of coordinates connected by minimal relations. To compute these components start with a basis of the factor vectors and merge the supports of the fundamental relations of nonbasis vectors. Those relations span $D$, and their supports are disjoint across the resulting components. Therefore $D$ is a direct sum of component spaces on disjoint coordinates. The product in the formula separates over these components, so the sum is a product of local sums. Enumerating each factor with relation dimension $t_i$ uses $3^{4t_i}$ terms. There is no bound on the number of components.

### Recovering the factors from the raw pencil

Choose an explicit extension $K/\mathbb F_3$ of polynomial cardinality exceeding $n$, $\dim W\binom n2+n\dim W$, and $3$. Its degree is logarithmic, so enumerating monic candidate defining polynomials and testing irreducibility takes polynomial time. Evaluate Pfaffians by alternating elimination. Along the moment curve $(1,a,\ldots,a^{\dim W-1})$, every nonzero linear factor has at most $\dim W-1$ zeros. Thus one direction $u$ on the curve satisfies $p(u)\ne0$. For each candidate $v$ on the curve interpolate $p(v+zu)$ as a degree-$n$ polynomial in $z$. A candidate maximizing the number of distinct roots separates all factors, since failures are the zeros of pairwise differences between the normalized forms $\ell_i/\ell_i(u)$ on the same curve. The root multiplicities give the $e_i$. At the root $z_i$, for each raw coordinate direction $e_j$, test all $b\in K$ for
$$p(v+a e_j+(z_i+ab)u)=0\quad\text{for every }a\in K.$$
On the split input this holds exactly when the factor through $v+z_i u$ vanishes identically on that line. Indeed its univariate degree is at most $n<|K|$, and an identically zero product has an identically zero factor. The root-separation condition identifies the factor, giving $b=-\ell_i(e_j)/\ell_i(u)$. Normalize the recovered coefficients and compute the overall scalar by evaluation at $u$. This produces the claimed factor data in deterministic polynomial time on the promise. The target extraction may fail outside the promised orbit, in which case the ordinary comparison could not have held. Any spurious data on a target outside that orbit cannot create a false positive because the output still retains the original tensor equation.

## 3. The mean can vanish even though the fifth moment reads the sign

On $\mathbb F_3^5$, use these normalized factor rows in the indicated order, with multiplicities $(2,2,2,2,1,2,2,1)$.
$$
\begin{pmatrix}
1&0&0&2&2\\1&2&1&1&0\\1&2&1&0&1\\1&1&0&2&0\\
1&2&1&1&1\\1&1&1&0&1\\1&0&1&2&0\\1&0&2&0&1
\end{pmatrix}.
$$
The row rank is five. For the normalized product, $F$ is even and its Fourier transform is real and integral. Compute each coefficient by
$$\widehat F(a)=\frac12\sum_x F(x)(3\,1_{a\cdot x=0}-1).$$
The complete frequency table is
| Value | $-9$ | $-6$ | $-3$ | $0$ | $3$ | $6$ | $9$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Count | 4 | 14 | 68 | 75 | 58 | 22 | 2 |

The mean is zero, as direct summation also shows. The sum of cubes of the Fourier coefficients is zero, whereas the sum of fifth powers is $-58\,320$, so $J=-240$. The exact control recomputes the table and compares a separate relation-space computation of $J$.

In fact, for a split product over $\mathbb F_3$ the analogous third correlation always equals $3^{\dim W-r}$ times the unnormalized mean. For each factor, all three of $\ell_i(x),\ell_i(y),\ell_i(x+y)$ must be nonzero. Over $\mathbb F_3$ this forces $\ell_i(x)=\ell_i(y)$. In the essential quotient, $x=y$, and the summand is $F(2x)=F(x)$ wherever nonzero. This explains why the fifth test is useful here.

For any even $k\ge0$, append $k$ independent variables and give each its own linear factor of multiplicity two. The relation dimension stays three. The mean remains zero. Each new variable has local factor function $1_{\{1,-1\}}$, whose fifth correlation is $10$ because, out of $16$ four-tuples of signs, exactly six have sum zero. Thus the new fifth correlation is $-240\cdot10^k$ before adding unused directions or the Pfaffian normalization.

## 4. Realization as concise all-even tensors with scalar pair adjoints

Repeat the linear forms according to their multiplicities in the extended product to make a list of length $n=14+2k$. Arrange the two unique odd-multiplicity forms at the first and last positions, respectively. Let $D(z)$ be the diagonal of this list, $N$ the matrix with ones on the superdiagonal, and put $A=D(z)+wN$. Include two additional labels $b,c$. With $E_{ij}$ the matrix unit, take
$$
M(z,w,b,c)=
\begin{pmatrix}
c(E_{n-1,n}-E_{n,n-1}) & A\\
-A^t & b(E_{1,2}-E_{2,1})
\end{pmatrix}.
$$
The Pfaffian is $(-1)^{n(n-1)/2}\det A$, independent of $w,b,c$. A matching in its expansion that uses one of the two internal pairs must use both. This removes bottom indices $1,2$ and top indices $n-1,n$. Top row $1$ can then reach neither of its only two possible bottom partners, so that matching contributes zero. The all-cross matchings give the asserted Pfaffian. The unused directions multiply $J$ by $3^{12}$ and preserve zero mean.

Choose $z_0$ with every list entry nonzero, which exists by the finite table above and setting new independent coordinates to one. Then $M_0=M(z_0,0,0,0)$ is invertible. To analyze the fixed-label pair adjoints, normalize by $M_0^{-1}$. With $B=C=0$ in the two internal positions, label operators for $z$ are block diagonal, with both blocks equal to $D(z_0)^{-1}D(z)$. The operator for $w$ has two opposite weighted shifts $D(z_0)^{-1}N^t$ and $D(z_0)^{-1}N$. The first and last joint diagonal characters occur at unique indices in each half. Each shift has a cyclic endpoint. An endomorphism commuting with all label operators so far has scalar blocks on the two diagonals. Its upper-right block has the form $\beta E_{nn}$ and its lower-left block $\gamma E_{11}$. Indeed, in each diagonal block the cyclic endpoint must go to a scalar multiple of itself, forcing a scalar intertwiner. In each off-diagonal block the cyclic endpoint must go to the same coordinate in the opposite chain, where it is killed by that shift. This forces the indicated rank-one form.

The extra normalized operators for $b,c$ are respectively upper-right and lower-left. The first is nonzero on the first two indices and the second on the last two. Commutation with them forces $\gamma=0$ and $\beta=0$ respectively, and equality of the diagonal scalars. Thus the pair adjoint between the matrix modes is scalar. If $M(z)B_0$ is alternating for every $z$, then using $M_0$ gives $B_0^tM_0=M_0B_0$ and the other labels give commutation with $M_0^{-1}M(z)$. Hence the right multiplier is scalar. For a matrix/label pair adjoint, the matrix operator on a single side must send the pencil space into itself by one-sided multiplication. Since all slices are alternating, this reduces by transposition if necessary to a right alternating multiplier. It is therefore scalar, and label injectivity forces the same scalar on its associated label map. Conciseness follows from the invertible slice in the matrix modes and label injectivity in the third. The latter uses the rank of the factor list and the three additional independent off-diagonal labels. The three dimensions are $2n,2n,8+k$, all even.

Finally choose $\eta=-1$ and conjugate the alternating form by the diagonal congruence whose first-half entries are $\eta^{j-1}$ and whose second-half entries are their reciprocals. The determinant of this matrix is one. Under the congruence, the diagonal terms stay fixed, and all three extra labels $w,b,c$ change by $\eta$. Their simultaneous change gives label determinant $-1$. Thus the source stabilizer has a sign correction supported just on the label mode, which allows either label determinant once the two matrix signs are set. For an arbitrary rebase of a source in this explicit family, conjugation preserves that correction and the two forced signs are still read by the moment. On this promised family the reduction returns the original ordinary pair when the two signs are right, and a fixed ordinary NO otherwise. It tests all three determinants without retaining a physical sign.

The normalized stabilizer sign image of a source in the explicit family is exactly the two vectors with positive signs in the matrix modes. The nonzero fifth moment forces positivity there, and the constructed label flip supplies the other vector. Thus an ordinary orbit contains exactly four classes under the two matrix-side determinant constraints, and exactly four under all three constraints. Independent negative basis changes in the two matrix modes realize the four classes.

## Verification and scope

The reductions and the explicit family have written proofs. The Lean companion verifies the finite fifth-correlation change of variables. The control script checks the displayed base instance and its relation-space formula. The result establishes a concrete sufficient reduction inside the all-even scalar-adjoint branch of the four-tier chain. The unrestricted comparison remains open.
