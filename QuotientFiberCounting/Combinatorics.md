# Counting maps from dimension-two posets to chains

**Status.** The first open question in §4 of Cooper–Kirkpatrick (2016) has an affirmative answer from Dittmer–Pak’s 2018 preprint. The reductions below also give exact and parity hardness for maps that can identify incomparable elements, even with an explicit chain of the same cardinality as the source. The proofs are informal. No priority claim is made for the counting transfers.

## The published question and its resolution

Cooper and Kirkpatrick ask whether counting injective order-preserving occurrences of a dimension-two poset in a chain is #P-hard when preservation of incomparability is optional. They explicitly identify the equivalence with counting linear extensions. Dittmer and Pak establish #P-completeness of counting linear extensions of dimension-two posets in Theorem 1.3 of their 2018 preprint. Their §3.3 uses a polynomial number of nonadaptive residue queries followed by Chinese remaindering. The 2020 journal article under the same title records their height-two and incidence-poset results. The preprint is the source for the dimension-two result. Dittmer gives the exact-count theorem again in Theorem 1.1.1 of his dissertation and gives the parity result in Theorem 1.1.2. [Cooper–Kirkpatrick, §4, p. 164](https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p154.pdf#page=11) · [Dittmer–Pak, Theorem 1.3 and §3.3](https://arxiv.org/pdf/1802.06312v1#page=2) · [Dittmer–Pak, journal article](https://doi.org/10.37236/8552) · [Dittmer, dissertation](https://escholarship.org/uc/item/80k2b78q)

Let $P$ have $n\ge 1$ elements, let $[m]=\{1,\ldots,m\}$ with its usual order, and let $e(P)$ be the number of linear extensions. An injective order-preserving map $P\to[m]$ determines a linear extension by ordering the elements by their images. Above each extension, choosing any strictly increasing list of $n$ colors in $[m]$ determines exactly one map. Consequently the number of labeled occurrences is
$$
I(P,m)=e(P)\binom mn,
$$
with zero for $m<n$. For $m=n$ the count equals $e(P)$, so the question has an affirmative answer even with equal-sized source and target. Membership in #P follows by guessing once per map and checking injectivity and order preservation.

For occurrences modulo source automorphisms, the action on injective maps by precomposition is free. The count becomes $e(P)\binom mn/|\operatorname{Aut}(P)|$. Cooper and Kirkpatrick’s Proposition 2.2 computes $|\operatorname{Aut}(P)|$ in polynomial time for dimension-two posets. Thus the same hardness answer also holds if the question is read in their unlabeled convention. The conclusion concerns the first question in §4. Counting texts that avoid a supplied pattern is a separate question. [Cooper–Kirkpatrick, Proposition 2.2 and §4](https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p154.pdf)

## A common proof for maps that allow ties

Write $W_P(m)$ for the number of maps $f:P\to[m]$ such that $f(x)\le f(y)$ whenever $x<_P y$. Write $S_P(m)$ for the number with $f(x)<f(y)$ for every such pair. Strict maps may still identify incomparable elements. Use $F_P$ for either of these counts.

Ranking the distinct values of a map gives a unique surjective map onto $[k]$, where $k$ is the size of its image, and a unique strictly increasing map $[k]\to[m]$. Ranking and lifting preserve either chosen order convention. Thus if $a_k$ counts surjective maps $P\to[k]$ in that convention, then
$$
F_P(m)=\sum_{k=0}^n a_k\binom mk,\qquad
a_0=0,\qquad a_n=e(P).
$$
The polynomial and leading coefficient are classical facts from order-polynomial theory. The rank factorization proves the binomial basis formula directly. [Stanley, *Two poset polytopes*](https://math.mit.edu/~rstan/pubs/pubfiles/66.pdf)

The formula also has a direct lattice interpretation for weak maps. The inverse images of $[1],[2],\ldots,[m-1]$ are a weakly increasing sequence of order ideals of $P$. Conversely the first index at which an element enters this sequence recovers its value, with value $m$ if it never enters. Thus the weak-map conclusions also apply to counting multichains in the distributive lattice of order ideals, given succinctly by the underlying dimension-two poset.

### Exact counting with explicit equal-sized prime chains

**Theorem.** Computing either $W_P(m)$ or $S_P(m)$ is #P-complete under polynomial-time nonadaptive Turing reductions even when $\dim(P)=2$, $m=|P|$ is prime, and the text chain is supplied explicitly.

Let $P$ be a dimension-two instance with $n$ elements and put $b=\max(4,n)$. Enumerate all primes $p$ in the range $b\le p\le b^2$. Set $P_p=C_{p-n}\oplus P$, meaning that a chain of $p-n$ new points precedes every point of $P$. Two total orders realizing $P$ extend by prepending the same chain, and $P$ remains an induced subposet. Therefore $\dim(P_p)=2$ and $e(P_p)=e(P)$. The latter equality holds because the new points must precede the original points in their one fixed order.

Query $F_{P_p}(p)$. Since $|P_p|=p$, $p$ is prime, and $a_0=0$, the binomial basis formula and $(1+X)^p=1+X^p$ over $\mathbb{F}_p$ give
$$
F_{P_p}(p)\equiv e(P_p)=e(P)\pmod p.
$$
The product of the primes in this range exceeds $n!$, by the prime-product bound quoted from Brightwell–Winkler in Proposition 3.1.1 of Dittmer’s dissertation. Since $0\le e(P)\le n!$, Chinese remaindering recovers it exactly. Every query has at most $b^2$ source elements and $b^2$ target elements. The primality scan, construction, returned bit lengths, and reconstruction are polynomially bounded. Membership in #P follows by guessing one value per source element and checking the specified inequalities. [Dittmer, Theorem 1.1.1 and Proposition 3.1.1](https://www.math.ucla.edu/~pak/papers/Dittmer-thesis.pdf#page=43)

If dimension at most two is used in the definition of the input linear-extension problem, exact dimension two can be ensured before the reduction by adjoining an isolated point to a nonempty poset. Opposite placements of that point in two realizer orders preserve dimension at most two, an incomparable pair forces dimension at least two, and $e(P)$ is multiplied by the known factor $n+1$. One can also provide the two realizer orders if the target representation calls for them, by finding a transitive orientation of the incomparability graph and taking its union and its reversed union with the given order. [McConnell–Spinrad, *Modular decomposition and transitive orientation*](https://doi.org/10.1016/S0012-365X(98)00319-7)

### Parity with explicit equal-sized power-of-two chains

**Theorem.** Testing oddness of either $W_P(m)$ or $S_P(m)$ is $\oplus\mathrm P$-complete under polynomial-time many-one reductions even when $\dim(P)=2$, $m=|P|$ is a power of two, and the text chain is supplied explicitly.

Take an instance of Dittmer’s dimension-two linear-extension parity problem. Put $N=2^{\lceil\log_2 n\rceil}$ and $P'=C_{N-n}\oplus P$. The same argument gives $e(P')=e(P)$, $\dim(P')=2$, and $n\le N<2n$ for $n\ge 2$. Over $\mathbb F_2$, $(1+X)^N=1+X^N$, so every intermediate coefficient $\binom Nk$ is even. The formula gives
$$
F_{P'}(N)\equiv e(P)\pmod 2.
$$
This builds one target instance and preserves the decision bit. The dimension-two parity problem cited in the reduction already uses dimension-two posets. Membership in $\oplus\mathrm P$ follows by accepting one branch per admissible map. The congruence generalizes to every fixed prime $p$ by padding to a power of $p$. It transfers existing linear-extension parity hardness when $p=2$. [Dittmer, Theorem 1.1.2 and Chapter 2](https://www.math.ucla.edu/~pak/papers/Dittmer-thesis.pdf#page=18)

### One exact query when the chain size is in binary

For either order convention and a nonempty $n$-element poset, set $M=2n+2n^{n+2}$. For $k<n$ we have $a_k\le n^n$ and $\binom Mk\le\binom M{n-1}$ since $M\ge 2n$. It follows that
$$
0\le\frac{\sum_{k<n}a_k\binom Mk}{\binom Mn}
\le\frac{n^{n+2}}{M-n+1}<1.
$$
Therefore $e(P)=\lfloor F_P(M)/\binom Mn\rfloor$. The target is specified by the binary integer $M$, with $O(n\log(n+2))$ bits. The answer has $O(n\log M)$ bits, and the binomial coefficient and division take polynomial bit time. This is a one-query polynomial-time metric reduction from counting linear extensions. Its encoding allows an exponentially large chain to be represented by its cardinality.

For comparison, when an explicit chain need not have the same size as the source, $n$ evaluations suffice:
$$
e(P)=\sum_{j=0}^n(-1)^{n-j}\binom nj F_P(j),
$$
where $F_P(0)=0$ is known. This follows by taking $n$ forward differences of the binomial basis formula.

## Counting antichains in dimension three

**Theorem.** Counting antichains or order ideals of an explicitly presented poset of order dimension three is #P-complete under polynomial-time nonadaptive Turing reductions. Testing either count for oddness is $\oplus\mathrm P$-complete under polynomial-time many-one reductions. These hardness results hold for products of a dimension-two poset with a chain, even if a three-coordinate realization is supplied. At dimension at most two both tasks are in FP or P, respectively.

For the hardness proof, consider the product $R=P\times C_{m-1}$ in coordinatewise order. For each weak order-preserving $f:P\to[m]$ put
$$
D_f=\{(x,i): 1\le i\le m-f(x)\}.
$$
This is a down-set because $x\le_P y$ implies $m-f(x)\ge m-f(y)$. In the other direction, a down-set intersects each chain $\{x\}\times C_{m-1}$ in an initial segment of length $\ell_x$. If $x\le_P y$, then $\ell_x\ge\ell_y$. Hence $f(x)=m-\ell_x$ is weakly order-preserving. The formulas are inverse. The maximal elements of a down-set give its antichain, with inverse given by downward closure. These are count-preserving bijections.

If $P$ has realizer ranks $r_1,r_2$, the points $(r_1(x),r_2(x),i)$ with coordinatewise order realize $R$. This yields a realizer by three total orders if desired. Start each order by sorting by its designated coordinate and break ties using any fixed linear extension of $R$. Every comparable pair stays in the proper order, and an incomparable pair has opposed strict comparisons in two coordinates. Thus $\dim R\le 3$.

To force dimension exactly three while retaining the product form, make a small change to the padding in both weak-map reductions. For target size $N\ge n+2$, use $P_N=C_{N-n-1}\oplus P\oplus C_1$. The prepended and appended chains are forced before and after the original elements, so $e(P_N)=e(P)$ and $\dim P_N=2$. Use the same next-power-of-two rule above $n+1$ for parity, or the same prime range with $b=\max(4,n+2)$ for exact counting. The modular identities still apply. Because $P$ has an incomparable pair, that pair together with one prepended and one appended point induces a diamond in $P_N$. Its product with any two distinct points of $C_{N-1}$ is the three-dimensional Boolean lattice. This contains the standard example consisting of three singletons and their complementary two-element subsets. Each singleton is below the other two complementary subsets. No one linear extension can reverse two of the three singleton–complement incomparable pairs, since the cross-relations would contradict the two reversals. Thus three total orders are necessary. It follows that $\dim R=3$ for every query, and the products have polynomial cardinality because all the queried chain lengths are polynomially bounded. The counting and parity memberships follow by guessing one subset and checking whether it is an ideal or antichain.

At dimension at most two, sort by the first realizer order and write the sequence of ranks from the second. An antichain selects a decreasing subsequence of that sequence, and every decreasing subsequence selects one antichain. Count nonempty decreasing subsequences by ending position, adding one for the singleton and summing previous entries with greater rank. Add one for the empty antichain. There are $O(n^2)$ additions of integers with $O(n)$ bits. Recover the two realizer orders from raw poset input as above. The polynomial algorithm for two dimensions was already known. The exact and parity hardness at dimension three follow here by the product reduction. [Kozma, SWAT 2020, §4, p. 12](https://drops.dagstuhl.de/storage/00lipics/lipics-vol162-swat2020/LIPIcs.SWAT.2020.30/LIPIcs.SWAT.2020.30.pdf#page=12)

This gives a sharp dimension threshold for the restricted-poset counting problem discussed by Amarilli. His specific question about the class of distributive lattices has a different input promise. A product in the reduction need not be a lattice. [Amarilli, *Complexity of counting antichains in restricted poset classes*](https://a3nm.net/work/research/questions/#complexity-of-counting-antichains-in-restricted-poset-classes)

## Validation

An exhaustive finite check used 33 permutation presentations on one to four elements. It independently enumerated linear extensions and weak and strict maps. It checked 436 chain-size and order-convention cases for the injective and ranked-image counts, and 66 cases each for the finite-difference, large-binary-chain and equal-size parity formulas. A separate exhaustive check passed 90 prime-padding cases for target sizes 2, 3 and 5. Enumeration of all subsets of the product verified the weak-map, ideal, and antichain counts in 27 additional cases. The arguments above establish the formulas for all finite inputs.
