# Bounded-size tests for modular homomorphism dependence

## GP-0824

Suppose $H$ has $h>0$ vertices, the two target graphs each have order at most $N\ge2$, and for each prime in a set $\mathcal P$ an admissible test $F_p$ satisfies $\operatorname{hom}(F_p,X)\equiv\operatorname{hom}(H,X)\pmod p$ for every target $X$. Any finite list of distinct primes from $\mathcal P$ whose product exceeds $N^h$ is enough to imply equality of the count from $H$ on these bounded targets. In particular, if the count from $H$ differs on two such targets, an admissible test in the explicit list distinguishes them.

For all three families of Kristjánsson's shift-lift construction, there is a uniform elementary algorithm producing at most $1+\lfloor h\log_2N\rfloor$ such tests, each with at most $hr(N^h+1)$ vertices, where $r$ is the lift parameter. For fixed $r$ the test count improves to $O_r(h\log N/\log(2+h\log N))$ and the maximum order to $O_r(h^2\log N)$. The latter lists can be constructed in polynomial time in $h$ and $\log N$ for fixed $r$. Their equality tests require no approximation of the homomorphism counts. [Kristjánsson's orbit quotients and counterexample families](https://arxiv.org/html/2610.03550v2#S4)

### Finite modular certificate

For two targets $X,Y$ put $\Delta=\operatorname{hom}(H,X)-\operatorname{hom}(H,Y)$. Both counts belong to $[0,N^h]$, so $|\Delta|\le N^h$. Equality of the indicated counts from $F_p$, or merely equality modulo $p$, implies $p\mid\Delta$. If all tests in the finite list agree then their product divides $\Delta$. The bound on its absolute value forces $\Delta=0$. These same residues determine the signed count difference once the prime product exceeds $2N^h$, by Chinese remaindering.

In Kristjánsson's Theorems 12 and 14, the allowed prime residues are those prime to $r$ and not congruent to $1$ or $-1$ modulo $r$. For $H=D_q^{(r)}$ or $H=B_q^{(r)}$, the test replaces $q$ by $qp$. It has exactly $hp$ vertices. It excludes the respective base graph as a minor, or as an immersion in the stated cubic family. Its quotient under a rotation of prime order is $H$, giving the congruence by the orbit count. This applies to every allowed prime and every $q$ satisfying the original theorem's hypotheses.

### Explicit selection of primes

Choose one residue $a$ coprime to $r$ and outside $\{1,-1\}$, which exists by the family assumption. At any stage let $A$ be the product of the primes already chosen, initially $1$. While $A\le N^h$, use the Chinese remainder theorem to choose a positive integer $M\le rA$ with $M\equiv1\pmod A$ and $M\equiv a\pmod r$. The residue $a$ ensures $M>1$. No prime divisor of $M$ divides $A$ or $r$. If every prime divisor were congruent to $1$ or $-1$ modulo $r$, then $M$ would be too. Thus a prime factor of $M$ is a new allowed prime. Trial division gives an explicit choice. Every chosen prime is at most $r(N^h+1)$, and each choice at least doubles $A$. The asserted uniform number and order bounds follow.

For the stronger fixed-$r$ estimate, enumerate primes in the single progression $p\equiv a\pmod r$ until the product exceeds $N^h$. The prime number theorem for this fixed progression gives
$$
\sum_{\substack{p\le x\\p\equiv a\bmod r}}\log p\sim x/\varphi(r),
\qquad
\#\{p\le x:p\equiv a\bmod r\}=O_r(x/\log(2+x)).
$$
Hence the stopping point is $O_r(h\log N)$, with at most the asserted number of primes. No asymptotic threshold need be found for this algorithm because it stops by testing the exact integer product. Even trial division up to that final prime is polynomial in $h,\log N$ for fixed $r$, and each shift lift is explicit in its number of vertices. The output is a list sufficient for every pair with the same target-order cap. [Explicit prime estimates for arithmetic progressions](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf)

The bounded-target conclusion applies in any family supplied with the modular identities. The stated test-size bounds use the specific vertex growth of Kristjánsson's lifts. The earlier catalogue's general separator proofs instead use unrestricted partition-quotient tests. [Earlier homomorphism size bounds](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GrochowCatalogueProofsII/HomomorphismSeparation.md)
