# Exact antichain counting in explicit distributive lattices

Amarilli asks whether counting the antichains of an explicitly given finite distributive lattice is #P-hard. The question remains open in this investigation. The constructions for height-four lattices and rank-three geometric lattices do not give distributive inputs. [Amarilli’s question](https://a3nm.net/work/research/questions/#complexity-of-counting-antichains-in-restricted-poset-classes)

## Unconditional runtime for all explicit distributive lattices

Let $L$ be an explicit distributive lattice on $N$ elements. For every fixed $\delta\in(0,1/2)$ the exact number of its antichains can be computed deterministically in
$$
2^{O_\delta\left(
N\frac{\log\log\log N}{(\log\log N)^{1/2-\delta}}
\right)}
$$
bit operations as $N$ tends to infinity. This is a direct algorithmic consequence of Kahn and Saks’ width theorem.

Find the width $w$ by a maximum matching in the bipartite split graph of the strict order, using Dilworth’s theorem. Enumerate each subset of size at most $w$ and test incomparability of each pair. The counter has at most $N+1$ bits. Kahn and Saks’ Theorem 7.1 states
$$
\frac{w}{N}=O_\delta\big((\log\log N)^{-(1/2-\delta)}\big).
$$
For $w\le N/2$, the number of tested candidates is at most $(w+1)(eN/w)^w$. The function $x\log(e/x)$ increases for $0<x\le1$, giving the claimed exponent and $2^{o(N)}$ time. The enumeration uses polynomial space and measures size by lattice elements rather than by join-irreducibles. A polynomial-time #SAT reduction producing polynomially many lattices with $O(n)$ elements each would imply deterministic $2^{o(n)}$ time for that #SAT encoding. This runtime consequence does not rule out arbitrary polynomial-size counting reductions. [Kahn–Saks, Theorem 7.1](https://core.ac.uk/download/pdf/82629369.pdf#page=11)

## A distributive closure that preserves the counting oracle

There is a direct polynomial-time Turing reduction from counting linear extensions of explicit distributive lattices to Amarilli’s antichain problem. For each $m=1,\dots,N$, the product $L\times C_{m-1}$, when nonempty, is still distributive and has at most $N^2$ elements. Its order ideals correspond to weak order-preserving maps $f:L\to[m]$, by assigning to each $u$ the initial segment of length $m-f(u)$ in the chain above $u$. For $m=1$ there is one map, so no product query is needed.

Write $F_L(m)$ for that map count, and $F_L(0)=0$ for a nonempty lattice. For each weak map, ranking the distinct values factors it into a surjective map on $k$ colors and a choice of a $k$-subset of $[m]$. Consequently
$$
F_L(m)=\sum_{k=0}^N a_k\binom mk,\qquad a_N=e(L),
$$
and $a_N$ is recovered by the $N$-th finite difference. This gives a concrete sufficient hardness target involving linear extensions and retaining the explicit distributive promise. The dimension-two linear-extension hardness theorem allows nondistributive posets and therefore does not settle this source problem. The degree and the query cardinalities here are polynomial in the explicit input size.

## Audit of two recent construction routes

**Ideal completion from incidence lattices.** The incidence constructions produce a poset with all graph vertices pairwise incomparable. Taking its ideal lattice produces at least $2^v$ elements for $v$ such vertices. More generally, if $L=J(P)$ has $N$ elements from its poset of join-irreducibles, then every antichain of size $w$ in $P$ induces $2^w$ distinct ideals, so $w\le\log_2 N$. A compact encoding of the join-irreducibles of an exponential lattice does not give an explicit-lattice reduction.

**Coordinatewise min/max completion.** For a permutation $\pi$ of $[n]$, let $P_\pi=\{(i,\pi(i))\}$ with the coordinatewise order. Its closure under coordinatewise minimum and maximum is exactly
$$
\{(i,j):\min_{k\ge i}\pi(k)\le j\le\max_{k\le i}\pi(k)\}.
$$
The displayed set is a sublattice containing the input. For the reverse inclusion, for each $i$ coordinatewise minima and maxima give points in row $i$ at the two displayed boundary values. If $j=\pi(k)$ and $k<i$, take the join of $(k,j)$ with the lower boundary point in row $i$. If $k>i$, take the meet of $(k,j)$ with the upper boundary point in row $i$. These operations give $(i,j)$, and the case $k=i$ is already an input point. In particular, if $\pi(1)=n$ and $\pi(n)=1$, the completion is the entire grid regardless of the middle permutation. Thus bare completion forgets the data needed to carry the hard count.

One can preserve distributivity when extending a portion of a lattice along a new chain, but the fiber generally changes the antichain constraints. For example, let $L=J(P)$ and $Q$ be an ideal of $P$. Add a chain of $t$ join-irreducibles below every point of $P\setminus Q$ and incomparable to $Q$. The resulting distributive lattice contains $t+1$ copies of each ideal contained in $Q$ along a chain and just one copy of each other ideal. An antichain in the enlarged lattice can project to comparable old ideals by using reversed heights in these fibers. Accordingly, this operation does not supply independent vertex weights in the antichain partition function. Repeating different such markers in independent directions can also create a product of fiber sizes at the common bottom. No polynomial-size count-preserving compiler for the distributive input class follows from these constructions.
