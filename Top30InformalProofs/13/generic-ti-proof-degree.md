# Nullstellensatz degree for generic tensor non-isomorphism

This is the generic claim from the 25 November manuscript. No independent audit file was located. The argument applies to arbitrary dimensions once the displayed inequality holds.

Let $T,S$ be tensors in $W=F^{n_1}\otimes F^{n_2}\otimes F^{n_3}$ and write $N=n_1n_2n_3$. The action equations for tensor isomorphism are the coordinates of $gT-S$, for a triple $g$ of variable square matrices. If

$$
\binom{N+k-1}{k}>\prod_{i=1}^3\binom{n_i^2+k-1}{k},
$$

then for every $T$ there is a nonzero homogeneous form $f_T$ of degree $k$ for which $f_T(gT)=0$ as a polynomial. Indeed the substitution map from forms of degree $k$ on $W$ takes values in the polynomials of multidegree $(k,k,k)$ in the three matrices. The two sides of the inequality are exactly the dimensions of the domain and this target, so the kernel is nontrivial.

When $f_T(S)\ne0$, telescope the difference $f_T(gT)-f_T(S)$ monomial by monomial. This expresses $-f_T(S)$ as a combination of the action equations of total degree at most $3k$. Division by the constant $-f_T(S)$ gives a Nullstellensatz certificate of degree $3k$. No field equations or matrix inversion equations are needed.

Over an infinite field this gives a nonempty open set of targets for every $T$. It also gives a nonempty open set of pairs. Write $E_T$ for the substitution matrix, $\rho$ for its generic rank, and append the row $\mathrm{ev}_S$. If the augmented matrix has rank at least $\rho+1$, evaluation at $S$ is nonzero on the kernel. That open condition is realized by a maximal-rank $T$ and a target where one of its nonzero kernel forms does not vanish. If $S$ is instead sampled from $A^N$ for a finite $A\subseteq F$, the probability of a certificate is at least $1-k/|A|$ by Schwartz–Zippel.

In cubic format $n_1=n_2=n_3=n$, take $k=\lceil6n^{3/2}\rceil$. The binomial bounds

$$
\binom{n^3+k-1}{k}\ge\frac{n^{3k}}{k!},
\qquad \binom{n^2+k-1}{k}\le\frac{(n^2+k)^k}{k!}
$$

reduce the required strict inequality to the sufficient condition $n^3 k^2/e^2>(n^2+k)^3$, using $k!\ge(k/e)^k$. After division by $n^6$, the left side tends to $36/e^2$ and the right side tends to $1$. Hence for all sufficiently large $n$ the generic certificate has degree at most $18n^{3/2}+3$. Its monomial size is at most $2^{O(n^{3/2}\log n)}$, by the monomial count for bounded-degree polynomials in the $3n^2$ action variables, multiplied by the polynomial number of equations.

The tensor-isomorphism proof-complexity formulation comes from [Grochow, Galesi, Pitassi and Szeszlér, CCC 2023](https://arxiv.org/abs/2305.19320). The argument here concerns generic pairs and gives no worst-case degree bound.
