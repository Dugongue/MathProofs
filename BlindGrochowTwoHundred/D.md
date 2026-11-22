# Robust rank tests and weighted cover certificates

A seed $s$ is successful on a target $t$ when $G(s,t)$ holds. In the rank-test application a target is a subspace $E$ and a seed is a linear map $f$. Success means injectivity of $f$ on $E$. This model separates the exact linear information captured by a test from the problem of choosing a small collection of tests.

## Greedy reduction with a certified stopping time

Let $P$ be a nonempty set of $M$ seeds, with every outstanding target served by at least $q$ seeds. Give each target an arbitrary nonnegative integer weight. Double counting over incidences gives some seed serving at least a fraction $q/M$ of the outstanding weight. After $t$ greedy steps, the remaining weight $W_t$ satisfies
$$
M^t W_t \le (M-q)^t W_0 .
$$
The Lean result constructs the list of choices and proves the integer bound. When the weights are all 1 and the right-hand side is strictly below $M^t$, the list hits every target. This is the classical greedy set-cover mechanism in a form that applies to arbitrary finite families of rank tests.

## Exact erasure cost and coverage

A panel survives arbitrary erasures of at most $k$ seed labels exactly when every target has at least $k+1$ successes. If the panel must retain $r>0$ successes per target, it needs at least $k+r$ to start with. With heterogeneous erasure costs, disabling a selected set of targets costs exactly the weight of the union of their successful fibers. A second bound relates the number of fragile targets to the total number of failures across the panel. When successful fibers are disjoint, the optimum size of a panel hitting every target $q$ times is exactly $q$ times the number of targets.

The treatment also covers conjunction on independent seed collections, disjunction, duplicate demand classes, finding a single seed serving a whole list, and witnesses for inclusion-minimal covers. Cardinalities in these statements count labelled seeds.

## Exact linear information and composition

A seed is lossless on a source subspace if its kernel misses that subspace. Its exact rank loss is the dimension of the intersection. Under serial compression, the total loss is the sum of two terms. The first is the loss in the original subspace. The second is the loss in its transferred image. A map on a direct sum is injective exactly when it is injective on both factors and their images are disjoint. The source also gives concrete recovery on the image of a lossy map, compression by the full ambiguity quotient, and criteria for using one seed on an entire family of subspaces.

These are reusable theorems about rank-test selection and exact finite coverage. They supply guarantees for given seed families. Explicit rank-condenser constructions with asymptotic bounds are a separate mathematical contribution in the literature. [Forbes and Guruswami](https://arxiv.org/abs/1411.7455)

Queue positions 22 and 132 joined kernel comparison and rank bounds across opaque modules, with handles 461852, 436749 and 327410. Position 47 exposed handle 471590 on preserving independence after deletion, and position 52 included 145943 and 230864 on basis and iteration. These structures suggested deleting seed labels, measuring surviving kernels, and iterating a rank-test selection rule. The complete proof statements were developed after seeing the frozen matches. [Proofs](D.lean) · [Frozen queue](queues/worker-4.json)
