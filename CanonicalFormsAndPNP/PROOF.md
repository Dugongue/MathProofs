# Polynomial-time canonization of all complete invariants is equivalent to P = NP

**Theorem.** For every oracle $A$, the following are equivalent.

1. $\mathsf P^A=\mathsf{NP}^A$.
2. Every polynomial-time equivalence relation relative to $A$ has a polynomial-time shortlex-first representative relative to $A$.
3. $\mathsf{CF}^A=\mathsf{Ker}^A$ for equivalence relations on all finite binary strings.

Here $\mathsf{Ker}^A$ consists of the relations with a polynomial-time complete invariant. A function $c$ is a canonical form for $R$ if $x\,R\,c(x)$ for every $x$, and $c(x)=c(y)$ whenever $x\,R\,y$. This gives an affirmative answer to the first clause of Fortnow–Grochow Open Question 5.10 and negative answers to both of its oracle questions. These are the unrestricted classes in their Definition 1.1. [Fortnow–Grochow, Definition 1.1 and Open Question 5.10](https://arxiv.org/html/0907.4775v2#S5)

## An equivalence relation for a witness verifier

Fix $A$ and a language $L\in\mathsf{NP}^A$. Let $V^A(x,w)$ be a deterministic polynomial-time witness verifier for $L$, with witnesses of length at most $(|x|+2)^e$ for a fixed integer $e\ge1$. Include the length bound as a condition of acceptance. Let $\gamma(x)=1^{|x|}0x$ be a self-delimiting encoding of $x$. For $n=|x|$ and an arbitrary integer $d\ge1$, use these two kinds of strings:

- The **anchor** for $(x,d)$ is $a(x,d)=0\gamma(x)1^d0\,0^{(n+2)^d}$.
- A **witness string** for $(x,d)$ is $b(x,d,w)=1\gamma(x)1^d0w$ with $V^A(x,w)=1$.

The class indexed by $(x,d)$ consists of its anchor and all its witness strings. Every remaining binary string is a singleton. The initial tag separates the two kinds, and the prefix encodings uniquely determine $x,d$. Hence these classes are well-defined and finite.

Compute a complete invariant by returning $0\gamma(x)1^d0$ on an anchor or witness string of type $(x,d)$ and $1z$ on every other input $z$. The witness check uses $V^A$ and the stated length bound. To check an anchor, parse its header, check that the remaining symbols are zero, and compute $(n+2)^d$ with values capped at $|z|+1$. Both the unary exponent and the capped arithmetic fit a polynomial-time computation in $|z|$. Thus this single relation belongs to $\mathsf{Ker}^A$. In particular, checking whether the anchor is valid does not require deciding $x\in L$.

## Canonization yields a decision algorithm

Assume $\mathsf{CF}^A=\mathsf{Ker}^A$ and let $c^A$ be a canonical form for this relation. There are fixed integers $k\ge1$ and $C\ge1$ such that it writes at most $C(m+1)^k$ output bits on every input of length $m$. In particular this bound holds on each witness string. Choose a fixed integer $d>ek$ large enough that

$$
2^{d-ek}>C(d+10)^k.
$$

This is possible because the left side is exponential and the right side is polynomial in $d$. Whenever $w$ is accepted for $x$, the encoding gives $|b(x,d,w)|+1\le(d+10)(n+2)^e$. Thus

$$
|c^A(b(x,d,w))|
\le C(d+10)^k(n+2)^{ek}
<(n+2)^d
\le |a(x,d)|.
$$

The canonical form of a witness string must be in its class, so it is another valid witness string. It is also the canonical form of the anchor. If $x\notin L$, the anchor is a singleton and its canonical form equals itself. Consequently, on input $x$, construct $a(x,d)$, compute $c^A(a(x,d))$, and accept exactly when the result starts with $1$. The anchor has polynomial length in $n$ because this decision machine uses one fixed $d$. The exponent is chosen *after* the clock of $c^A$ is fixed, which is possible because the relation already includes every $d$. The procedure is polynomial-time relative to $A$. This proves $\mathsf P^A=\mathsf{NP}^A$.

The same argument actually recovers an accepting witness when one exists. Thus a specific choice of verifier, such as the standard Boolean satisfiability verifier in the unrelativized setting, suffices to construct one fixed relation with a polynomial-time complete invariant whose polynomial-time canonization would give a polynomial-time witness search algorithm for that verifier.

## Converse and exact scope

Assume $\mathsf P^A=\mathsf{NP}^A$. For a polynomial-time equivalence relation $R$ relative to $A$, the shortlex-first member of the class of $x$ has length at most $|x|$. The predicate that there is a member of a specified length at most $|x|$ and with a specified prefix is in $\mathsf{NP}^A$, by guessing that member and checking the relation. First find the least feasible length and then choose the bits of the least member from left to right. There are polynomially many deterministic polynomial-time oracle calls under the assumption. This proves the shortlex-first conclusion. A canonical form is always a complete invariant, so the inclusions $\mathsf{CF}^A\subseteq\mathsf{Ker}^A\subseteq\mathsf{PEq}^A$ give the remaining equivalences. In particular $\mathsf{CF}^A=\mathsf{Ker}^A=\mathsf{PEq}^A$ holds exactly when $\mathsf P^A=\mathsf{NP}^A$. Fortnow and Grochow already give the shortlex-first argument for this direction. [Fortnow–Grochow, §3](https://arxiv.org/html/0907.4775v2#S3)

The forward construction uses classes whose relative member lengths have no common polynomial bound. Indeed, fix a yes-input and one witness and increase $d$. Its witness strings have length linear in $d$, whereas the corresponding anchors have length exponential in $d$. This distinction is essential for comparing the theorem with Fortnow–Grochow Theorem 5.5, which permits $\mathsf{CF}_p^A=\mathsf{Ker}_p^A$ with $\mathsf P^A\ne\mathsf{NP}^A$ for the polynomially balanced subclasses. [Fortnow–Grochow, Theorem 5.5 and Lemma 5.9](https://arxiv.org/html/0907.4775v2#S5)


## Randomized per-input variants

The same proof gives exact randomized analogues. Each hypothesis below refers to one algorithm per relation, with the stated guarantee on every input.

- If every relation in $\mathsf{Ker}^A$ has a Las Vegas canonical form, meaning a zero-error algorithm for its fixed canonical form with expected polynomial time on each input, then $\mathsf{NP}^A=\mathsf{ZPP}^A$. The expected-time bound on a witness string bounds the length of its fixed output, since every terminating run writes that output. The same choice of $d$ works. Running this algorithm on the anchor decides $L$ with zero error and expected polynomial time. Conversely, if $\mathsf{NP}^A=\mathsf{ZPP}^A$, use Las Vegas prefix tests in the shortlex construction above. There are polynomially many tests of polynomial input length, so the expected total time is polynomial and the output is always the shortlex representative.
- If every relation in $\mathsf{Ker}^A$ has one worst-case polynomial-time randomized algorithm that computes its fixed canonical form with probability at least $2/3$ on every input, then $\mathsf{NP}^A=\mathsf{RP}^A$. The time bound on a witness string still bounds the length of the correct output. On an anchor, accept only upon verifying a valid witness for the original $x$. This has no false positives and succeeds with probability at least $2/3$ on yes-inputs. Conversely, use amplified $\mathsf{RP}^A$ algorithms as the shortlex prefix tests. Set the error per test below the reciprocal of three times the number of tests. A union bound over the adaptive tests then gives the fixed shortlex representative with probability at least $2/3$ in polynomial time.

In the Las Vegas case $\mathsf{NP}^A=\mathsf{coNP}^A$ because $\mathsf{ZPP}^A$ is closed under complement, so the relative polynomial hierarchy collapses to its first level. In the bounded-error case it collapses to $\mathsf{BPP}^A$. To see the latter, $\mathsf{NP}^A=\mathsf{RP}^A$ implies $\mathsf{BPP}^{\mathsf{NP}^A}=\mathsf{BPP}^A$. Also $\mathsf{NP}^{\mathsf{BPP}^A}\subseteq\mathsf{BPP}^{\mathsf{NP}^A}$: amplify the simulated bounded-error oracle and choose one random tape that is correct with high probability simultaneously on every polynomial-length possible query. For a fixed tape the remaining computation is in $\mathsf{NP}^A$. These facts give containment of all hierarchy levels in $\mathsf{BPP}^A$ by induction. The relativizing Sipser–Lautemann bound gives the reverse containment at the second level. The expected-time result uses a per-input randomized guarantee. Fortnow and Grochow also discuss expected-time canonization in §6.2 and cite Babai–Kučera's average-input graph result. An average over a supplied input distribution is a different hypothesis from the per-input guarantee used here. [Fortnow–Grochow, §6.2](https://arxiv.org/html/0907.4775v2#S6.SS2)
