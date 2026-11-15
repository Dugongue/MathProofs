# Exponential query lower bound for principal-minor reconstruction

Aravind, Chatterjee, Ghosh, Gurjar, Raj and Saha leave open whether an arbitrary matrix can be reconstructed in polynomial time from an oracle that returns one specified principal minor per query. For every field and every size $n\ge 1$, an algorithm that always reconstructs the principal-minor profile must query all $2^n-1$ nonempty subsets in the worst case. A randomized algorithm that succeeds with probability at least $1-\varepsilon$ on every input must make at least $(1-\varepsilon)(2^n-1)-\varepsilon$ distinct queries in expectation on the zero matrix. This gives a negative answer in the stated oracle model. [Learning Read-Once Determinants and the Principal Minor Assignment Problem, §1](https://arxiv.org/html/2603.04255#S1)

## Statement

The oracle for an unknown $n\times n$ matrix $A$ over a field $F$ returns $\det A[T,T]$ on query $\varnothing\ne T\subseteq[n]$. The algorithm is required to output a matrix over $F$ with exactly the same principal minors. Success permits returning any realizing matrix. The empty minor, if exposed, is always 1.

## A matrix with one nonzero principal minor

For each nonempty $S\subseteq[n]$, pick a cyclic permutation $\sigma$ of the elements of $S$. Define $A_S$ by putting a 1 at each entry $(i,\sigma(i))$ for $i\in S$, and zero elsewhere. For a singleton the permutation is the identity. The principal submatrix on $S$ is a cyclic permutation matrix, so its determinant is $(-1)^{|S|-1}\ne0$ in every field. If $T$ contains an index outside $S$, then $A_S[T,T]$ has a zero row. If $T$ is a nonempty proper subset of $S$, then some $i\in T$ has $\sigma(i)\notin T$, because a nonempty subset closed under a single cycle is the whole cycle. Row $i$ of $A_S[T,T]$ is zero in this case as well. Thus the profile of $A_S$ differs from the zero matrix's profile at exactly $S$.

## Deterministic and randomized lower bounds

For a deterministic algorithm, follow the execution on the zero matrix. If it omits any nonempty $S$, its entire query and answer transcript on $A_S$ is identical, including every adaptive query and the final output. One output cannot realize the two distinct profiles. The zero execution must query all $2^n-1$ nonempty subsets.

For a randomized algorithm, couple its executions on the zero matrix and on $A_S$ by using the same random bits. Let $H_S$ be the event that the zero execution queries $S$, and let $G_S$ be the event that the zero execution outputs a matrix realizing the profile of $A_S$. Until the first query to $S$, the two executions have identical transcripts. Therefore success on $A_S$ implies $H_S\cup G_S$, so $1-\varepsilon\le\Pr(H_S)+\Pr(G_S)$ for each $S$. The events $G_S$ are disjoint, and their union is contained in the zero execution's failure event. Hence $\sum_S\Pr(G_S)\le\varepsilon$. Linearity of expectation identifies $\sum_S\Pr(H_S)$ with the expected number of distinct queries on the zero matrix. Summing the inequalities gives the claimed bound.

## Scope and provenance

The question here concerns the oracle for individual principal minors. The cited paper separately defines *Black-box PMAP*, whose oracle evaluates $\det(A+\operatorname{diag}(y))$ at supplied values of $y$. Its Theorem 1.1 addresses that evaluation model. The query lower bound concerns the first oracle. The construction uses only zero and one matrix entries, and the priority search found no prior statement of this lower bound in the sources checked. Informal proof. [Problem 1.2 and Theorem 1.1](https://arxiv.org/html/2603.04255#S1.SS1)
