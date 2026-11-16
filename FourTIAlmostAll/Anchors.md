# Four-tensor isomorphism from ordinary and reciprocal cuts

## Result

Fix a finite field $F=\mathbb F_q$ and consider ordered $n\times n\times n\times n$ tensors. Let
$$
c(q)=\prod_{j\ge1}(1-q^{-j}).
$$
There is a deterministic polynomial-bit-time recognizer for ordinary four-tensor isomorphism that gives a correct answer against every second tensor on a fraction $1-c(q)^5-o(1)$ of uniformly random first tensors. This replaces the earlier $1-c(q)^3-o(1)$ coverage by testing two extra cuts of one reciprocal tensor. For $q=2$, the limiting coverage is about $99.80\%$. The proof uses the existing deterministic algorithm for singular cuts.

In the notation below, the five candidate cuts are $12\mid34$, $13\mid24$, $14\mid23$ of the original tensor and, whenever its first cut is invertible, $13\mid24$ and $14\mid23$ of its $12\mid34$ reciprocal. All five are invertible with probability $c(q)^5+o(1)$. Among inputs whose three ordinary cuts are all invertible, at least a fraction $1-c(q)^2-o(1)$ is recognized by this construction.

## Reciprocal reduction

View the first cut as a matrix $X:V_3^*\otimes V_4^*\longrightarrow V_1\otimes V_2$, with side length $N=n^2$. When $X$ is invertible, its inverse is the first cut of a tensor in the four ordered dual spaces. Denote this tensor by $J(T)$.

If $T$ is acted on by $g_1,g_2,g_3,g_4$, the matrix $X$ is multiplied on the left by $g_1\otimes g_2$ and on the right by $(g_3\otimes g_4)^{\mathsf T}$. Its inverse is multiplied on the left by $(g_3\otimes g_4)^{-\mathsf T}$ and on the right by $(g_1\otimes g_2)^{-1}$. Thus $J$ intertwines the four actions by the contragredient map. Inversion is an involution, so it preserves and reflects isomorphism. A first-cut rank mismatch already rules out any isomorphism.

The previous singular-cut recognizer decides every comparison for all but an $o(1)$ fraction of uniform first tensors having some singular pair cut. Conditional on its first cut being invertible, $T$ is uniform in $\mathrm{GL}_N(F)$ in that cut, and $J(T)$ has the corresponding uniform distribution on the dual tensor space conditioned on first-cut invertibility. Since the conditioning event has probability at least $c(q)$, the old $o(1)$ exceptional estimate applies to $J(T)$ as well. Inversion and the two uses of the old recognizer have deterministic polynomial bit cost at fixed $q$.

## A Fourier estimate for a uniform matrix and its inverse

Let $X:E\to G$ be a uniform isomorphism between two $N$-dimensional spaces. Let $a:G\to E$, $b:E\to G$, and fix a nontrivial additive character $\psi$ of $F$. Put $r=\max(\operatorname{rank}a,\operatorname{rank}b)$. For $r\ge1$ and $N\ge4$ we prove
$$
\left|\mathbb E_X\psi\big(\operatorname{tr}(aX)+\operatorname{tr}(bX^{-1})\big)\right|
\le C_q q^{-\gamma r N}
$$
for an absolute $\gamma>0$ and a constant $C_q$. Interchange $X$ and $X^{-1}$ if needed so $\operatorname{rank} b=r$. Set $k=\min(r,\lfloor N/4\rfloor)$, choose a $k$-space $I\subseteq E$ on which $b$ is injective, and fix $E=I\oplus H$. Average the phase after replacing $X$ by $X(1+U)$, for $U$ uniform in $\operatorname{Hom}(H,I)$ and extended by zero on $I$. This preserves the uniform law of $X$. Since $U^2=0$, the change in phase is
$$
\operatorname{tr}\big(U(aX-X^{-1}b)\big).
$$
Orthogonality of characters on $\operatorname{Hom}(H,I)$ shows that the average vanishes unless
$$
\pi_HaP=Qb|_I,\qquad P=X|_I,\quad Q=\pi_H X^{-1}.
$$
For each $P$, the induced $Q:G/\operatorname{im}P\to H$ is a uniform isomorphism. Indeed $X$ is uniform among extensions of $P$, and each prescribed quotient isomorphism has the same number of extensions. The image of $P$ is a uniform $k$-space.

Write $t=\lceil k/2\rceil$. The chance that the fixed $k$-space $b(I)$ meets $\operatorname{im}P$ in dimension at least $t$ is bounded by the number of $t$-spaces in $b(I)$ times the chance that one prescribed $t$-space lies in the uniform $k$-space. The standard Gaussian binomial formula bounds this product by
$$
C_q' q^{t(k-t)-t(N-k)}=C_q'q^{-t(N-2k+t)}.
$$
Outside this event, the image of $b(I)$ in $G/\operatorname{im}P$ has dimension $s\ge k/2$. The displayed equality prescribes $Q$ on that $s$-space. Whether those prescriptions are consistent or not, their probability is at most $c(q)^{-1}q^{-s(N-k)}$, by the count of injective ordered $s$-tuples. Both terms are bounded by a constant times $q^{-\gamma rN}$, since $k\le N/4$ and $k\ge r/7$ for $N\ge4$. This proves the estimate.

## Four alternate cut coranks

Condition on first-cut invertibility. Write $K_i$ for the left-kernel dimensions at the two alternate cuts of $T$ and the two alternate cuts of $J(T)$, in that order. For each fixed quadruple $d_1,\ldots,d_4$ of nonnegative integers, put $D=\sum_i d_i$. We prove
$$
\lim_{n\to\infty}\mathbb E\prod_{i=1}^4 {K_i\brack d_i}_q
=\prod_{i=1}^4 \frac{q^{-d_i^2}}{\prod_{j=1}^{d_i}(1-q^{-j})}.
\tag{1}
$$

Choose a $d_i$-space $L_i$ of test left-kernel forms for each of the four cuts. Call a test space good if its nonzero $n\times n$ matrices have rank at least $n/2$. For the two cuts of $T$, the span of the linear constraints, as frequency tensors in original coordinates, consists of arrays
$$
Z_{ijkl}
=\sum_\alpha L_\alpha(i,k)C_\alpha(j,l)
+\sum_\beta M_\beta(i,l)D_\beta(j,k).
$$
Here $L_\alpha$ and $M_\beta$ are bases of the two test spaces, and $C_\alpha,D_\beta$ are arbitrary coefficient matrices. If the first summand is nonzero, fix $j,l$ exhibiting a nonzero $n\times n$ block in $i,k$. In that block it has rank at least $n/2$ and the second summand has rank at most $d_2$, since each term is rank at most one. Thus the $12\mid34$ matrix of $Z$ has rank at least $n/2-d_2$. If the first summand is zero and the second nonzero, fixing $j,k$ similarly yields rank at least $n/2$. In particular each separate map from coefficient matrices is injective, and for sufficiently large $n$ their sum is injective. The same reasoning applies to the two cuts of the reciprocal, with $d_4$ in place of $d_2$ and with the appropriate transpose if the original-cut map lists the paired sides in reverse order.

Consequently, for good test spaces, Fourier expansion of the joint kernel events gives
$$
\Pr[L_i\subseteq\ker_i\text{ for all }i\mid X\in\mathrm{GL}_N(F)]
=q^{-DN}\big(1+O(q^{DN-\Omega(n^3)})\big).
$$
Indeed there are $q^{DN}$ characters, and every nonzero frequency has rank $\Omega(n)$ on at least one side of the joint pair $(X,X^{-1})$, so the preceding estimate applies. The constants can depend on the fixed $q,d_1,\ldots,d_4$.

The fraction of $d_i$-spaces failing goodness tends to zero. The number of low-rank test vectors is $q^{n^2-\Omega(n^2)}$, by the matrix rank count, and a fixed nonzero vector belongs to a uniform $d_i$-space with probability $(q^{d_i}-1)/(q^N-1)$. The contribution from good spaces therefore converges to the right side of (1), using ${N\brack d}_q q^{-Nd}\to q^{-d^2}/\prod_{j=1}^d(1-q^{-j})$.

For the bad-space contribution, let $B$ be the event that one of the four actual kernels contains a nonzero form of rank below $n/2$. In a uniform unconditioned tensor any given left form belongs to the corresponding kernel with probability $q^{-N}$. Consequently $B$ has probability $q^{-\Omega(n^2)}$ by the low-rank count, the union bound, and conditioning on first-cut invertibility. This applies to the inverse marginals because inversion preserves the uniform invertible-first-cut law. For each of the four marginals, another union bound on all $u$-dimensional kernel spaces yields
$$
\Pr[K_i\ge u]\le c(q)^{-1} {N\brack u}_q q^{-Nu}\le c(q)^{-2}q^{-u^2}.
$$
In particular all fixed moments of ${K_i\brack d_i}_q$ are bounded uniformly in $n$. Hölder's inequality shows
$$
\mathbb E\!\left[\mathbb 1_B\prod_{i=1}^4 {K_i\brack d_i}_q\right]
\le \Pr[B]^{1/2}\prod_{i=1}^4\left(\mathbb E{K_i\brack d_i}_q^8\right)^{1/8}
=o(1).
$$
This bounds the total bad-space contribution and proves (1).

## Reading simultaneous invertibility from the moments

For $m\ge0$ define
$$
P_m(K)=\sum_{d=0}^m (-1)^d q^{d(d-1)/2}{K\brack d}_q.
$$
For $K>0$, the Gaussian Pascal recurrence gives $P_m(K)=(-1)^m q^{m(m+1)/2}{K-1\brack m}_q$. For $K=0$, the value is $1$. Hence $P_{2j}$ majorizes $\mathbf 1_{K=0}$ and $P_{2j+1}$ minorizes it. The upper product $\prod_i P_{2j}(K_i)$ differs from the product of the four indicators by at most
$$
\sum_i \big(P_{2j}(K_i)-P_{2j+1}(K_i)\big)
         \prod_{\ell\ne i} P_{2j}(K_\ell).
$$
This follows by telescoping the difference of the products of nonnegative upper bounds and indicators.

For each fixed $j$, (1) gives the limiting expectation of each displayed polynomial, equal to its limit on four independent uniform square-matrix coranks. In the single square-matrix limit the expectation of $P_{2j}$ approaches $c(q)$ as $j\to\infty$. This follows from the same upper and lower bounds, the exact invertibility probability, and the limiting expected difference
$$
q^{d(d-1)/2}\frac{q^{-d^2}}{\prod_{h=1}^d(1-q^{-h})}\longrightarrow 0,\qquad d=2j+1.
$$
The expected four-slot upper product therefore tends to $c(q)^4$ in the iterated limit, and the expected excess bound tends to zero. This proves the probability $c(q)^4+o(1)$ that all four alternate cuts are invertible given first-cut invertibility. The base cut contributes a factor tending to $c(q)$.

This proves the claimed recognition density and the conditional coverage gain on the ordinary all-invertible sector. Iterating reciprocal operations across distinct cuts would require an additional joint law for inverses of different reshuffles or a different recovery argument.

## Scope and sources

- The singular-cut recognizer is from *Ordinary Four-Tensor Isomorphism at Fixed Field Size* in [MathProofs](https://github.com/Dugongue/MathProofs/tree/main/FixedFieldOrdinaryFourTI). Its starting point is the kernel-form analysis of [Li, Li, Qiao, Tao, and Wang](https://arxiv.org/html/2604.00591v2).
- [Erdélyi and Tóth](https://msp.org/ant/2024/18-12/ant-v18-n12-p04-s.pdf) study the full matrix Kloosterman sums that appear in the Fourier calculation. The transvection estimate above is self-contained.
- This is an informal proof of a stronger fixed-field recognition density. The remaining mass $c(q)^5+o(1)$ needs another argument for coverage tending to one.
