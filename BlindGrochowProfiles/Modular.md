# The first collision for modular characteristic polynomials and Frobenius tests

Let $P_a$ be the permutation matrix of a cycle profile $a=(a_d)$, with $a_d$ cycles of length $d$. In a fixed dimension, consider two observations:

- the coefficients of $\det(I-XP_a)$ modulo an integer $m\ge1$;
- the cycle types of $P_a^{s}$ for a finite list of positive integers $s\in M$.

The list may be empty. Assume $m>1$ or $M$ is nonempty. If $1\in M$ the observations recover every profile. Otherwise let $S$ be the primes of $m$, $h=m/\operatorname{rad}(m)$, with $\operatorname{rad}(1)=1$. Let $H$ range over prime sets containing $S$ and meeting the prime divisors of each $s\in M$.

**Theorem.** The least common dimension of two distinct profiles with identical observations is
$$
N(m,M)=\frac h2\min_H\prod_{p\in H}(2p).
$$
The observations classify permutation conjugacy below this dimension, and collisions exist in every dimension from this one onwards. When $M$ is empty the threshold is $2^{|S|-1}m$, and the first pair is unique up to interchange and conjugation. Individual power-cycle observations also model tests after scalar extension of finite étale algebras. The modular polynomial here comes from Frobenius acting on the *integral permutation lattice of geometric points*. Its modular reduction is defined independently of the characteristic of the base finite field.

For $m=6$, the first pair has types $(6,1^6)$ and $(3^2,2^3)$ in dimension 12. For modulus 4 alone, the answer is 4. Adding the two power tests 15 and 21 raises it to 24. The minimizing prime set is $\{2,3\}$.

## Prime-power criterion

Write $z_d=a_d-b_d$ and $D_a=\prod_d(1-X^d)^{a_d}$. Use integral power series with constant term 1 so that negative exponents in $D_a/D_b$ are allowed. For a prime $p$ and $e\ge1$, the polynomials agree modulo $p^e$ precisely when both of the following hold:
$$
\sum_{j\ge0}p^j z_{up^j}=0\quad(p\nmid u),\qquad p^{e-1}\mid z_d\quad\text{for every }d.
$$

Indeed modulo $p$, Frobenius replaces the factors on a line by a single $(1-X^u)$ to the indicated integer exponent. Such factors for $p$-free $u$ are multiplicatively independent. If a product with finite signed exponents is 1, take a divisibility-maximal index $u$ with nonzero exponent. At a primitive $u$-th root in an algebraic closure of $\mathbb F_p$, its order of vanishing as a rational function is exactly that exponent, since every $p$-free factor is separable and no larger multiple is present. This is a contradiction.

On a line with weighted sum zero, there is a unique finitely supported integer vector $y$ satisfying $z_d=p y_d-y_{d/p}$, with the last term zero if $p\nmid d$. Solve downwards from beyond the top of the line. The sum condition gives the equation at its base. This recursion also shows that divisibility of all $z_d$ by $p^{e-1}$ is equivalent to divisibility of all $y_d$ by the same number. Then
$$
 D_a/D_b=\prod_d B_d^{y_d},\qquad B_d=(1-X^d)^p/(1-X^{pd}).
$$
Each $B_d$ is 1 modulo $p$, has no positive term before degree $d$, and has coefficient $-p$ there. Repeated binomial expansion gives $B_d^{p^{e-1}}\equiv1\bmod p^e$. Conversely, choose the smallest $d$ where $p^{e-1}$ fails to divide $y_d$. All earlier factors are 1 modulo $p^e$, and later ones have zero coefficient at degree $d$. The coefficient at degree $d$ of the product is $-p y_d$ modulo $p^e$, which is nonzero. This proves the criterion. The Chinese remainder theorem gives the joint scalar divisibility $h\mid z_d$ and a zero weighted sum on every line in each direction $p\in S$.

## An extremal box proves the mixed lower bound

Define $w_d=d z_d$ and $F(n)=\sum_{d\mid n}w_d$. This is the difference between the numbers of fixed points of the $n$-th powers. Since all fixed-point counts recover a cycle profile by triangular inversion, the power tests say exactly that $F(n)=0$ on the multiples of any $s\in M$.

Take a finite divisor box with exponent ceilings covering the support and the test degrees, including all primes of $m$ with ceiling at least 1. If $z\ne0$, inversion on the box gives a nonzero $F$. Take a divisibility-maximal $v$ in the box with $F(v)\ne0$. Let $H$ be the coordinates where $v$ is below the ceiling. Each test degree has a prime in $H$, since no test divides $v$. Moreover every $p\in S$ is in $H$. A coordinate at its ceiling sums whole $p$-lines in $F(v)$, each of weighted sum zero.

In coordinates $p\in H$ split the support into low and high according as the exponent is at most that of $v$ or greater. For each subset $J\subseteq H$, the sum of $w_d$ over the bucket high *exactly* on $J$ is $(-1)^{|J|}F(v)$. Expand each high indicator as unrestricted minus low. Every term where at least one cutoff was raised to its ceiling has zero sum by maximality. In the all-high bucket, each $d$ is divisible by $\prod_{p\in H}p$ and each $z_d$ by $h$. Thus $|F(v)|\ge h\prod_{p\in H}p$. Summing absolute values over the disjoint buckets gives
$$
2n\ \ge\ \sum_d d|z_d|\ \ge\ 2^{|H|}|F(v)|\ \ge\ h\prod_{p\in H}(2p).
$$
Here $n$ is the common dimension. This lower bound allows arbitrary extraneous primes and higher powers in the unknown profiles.

## A pair achieving the bound

For an optimal $H$, put $Q=\prod_{p\in H}p$. Set $z_d=h(-1)^{|H|-\omega(d)}Q/d$ for $d\mid Q$, and zero elsewhere. Each weighted term has magnitude $hQ$. The positive and negative parts have dimension $h2^{|H|-1}Q$ each. Every prime in $S$ balances opposite terms along its coordinate, and $h$ supplies the required divisibility. Furthermore $F(n)=0$ whenever any prime of $H$ divides $n$, so every required power test agrees. Adding common fixed points proves the assertion for larger dimensions.

For uniqueness with $M$ empty, consider a component with fixed prime-to-$Q$ part, as a grid in the exponents of $S$. The entries with every exponent positive determine the whole component: successively reconstruct entries with zero coordinates by the zero line sums. For any nonzero all-positive cell $w_d$, group each coordinate by agreement with that cell or disagreement. The line sums again force all $2^{|S|}$ bucket sums to have magnitude $|w_d|$. At the minimum this implies $|w_d|\le hQ$. Since $Q\mid d$ and $h\mid z_d$, every such nonzero cell has $d=Q$ and $z_Q=\pm h$. Reconstruction forces precisely the displayed cube. Equality of total mass leaves no common summands.

## Verification scope

The prime-power criterion and extremal box argument are written proofs. The finite-grid mass bound used in the uniqueness proof is kernel-checked in [Modular.lean](Modular.lean). [The direct enumeration](profiles.py) computes polynomial coefficients by multiplication, powers cycles by their gcd formula, and compares these observables to the predicted first pairs. [The cancellation proof](Counting.md) gives a second lower-bound proof for $m=1$.

## Uniqueness and complexity for the joint observations

In fact the minimum-dimensional pair is unique for the mixed problem too. The odd prime factors of the cost recover the odd members of $H$, and adding 2 multiplies the cost by 4, so different sets have different costs. Fix the optimal $H$. Each mandatory prime has zero line sums. For any optional $p\in H$, collapse the $p$-coordinate of the signed masses by $w'_u=\sum_j w_{up^j}$ for $p\nmid u$. Each $w'_u$ is divisible by $hu$, its norm cannot increase, and its remaining mandatory line sums still vanish. For a test $s=p^b t$ with $p\nmid t$, the marks of the collapsed profile at multiples of $t$ are the old marks at the same exponents with the $p$-coordinate raised to at least $b$ and past the support. They therefore vanish. If the collapsed vector were nonzero, the same box bound on this smaller problem would reach at least the cost of the best feasible set *excluding* $p$, strictly above the attained optimum. If a stripped test is 1, the collapsed vector vanishes directly by inversion. Thus every coordinate of $H$ has complete line balance. The all-positive cell argument above, now on $H$ with scalar $h$, forces $d=Q$, $z_Q=\pm h$ and the unique cube. This includes the cases without modular observations and without power tests.

For each fixed $m>1$, deciding whether the joint tests can first collide by a binary dimension bound is also NP-complete, even when every power-test degree is semiprime and coprime to $m$. Use the reduction in [the complexity proof](Degree.md), choosing the vertex primes larger than every factor of $m$. The mandatory primes meet none of the edges, so the new first dimension is $h\prod_{p\in S}(2p)/2$ times the vertex-cover cost. Scale the binary cutoff by that fixed factor. A hitting-set certificate with the required product is verifiable in polynomial time. The inputs here specify tests on a whole family.
