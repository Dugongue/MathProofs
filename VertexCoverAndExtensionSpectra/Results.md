# Vertex Cover and extension-field isomorphism

Fix a finite field. For a pair of finite étale algebras (products of finite fields), its extension spectrum consists of the positive integers m for which the two multiplication tensors are isomorphic over the degree-m extension. Assign a distinct prime to each vertex of a graph. One can construct a pair such that a degree works precisely when its prime divisors select a vertex cover. This preserves the whole set of answers over all extensions. Four lines of investigation use different features of this correspondence.

## 1. Reverse compilation, counting, and the classical-group question

An arbitrary pair of dimension-n tables gives at most n−1 covering clauses. Each requires that one of a specified list of prime powers divide the degree. The clauses are computable from the two Frobenius cycle profiles. Conversely, lists of clauses can be compiled into tables with polynomial cost in the numerical clause indices. Inclusion and equality of two entire spectra are decidable in polynomial time. The clause criterion was also checked against direct powering in 501,842 cases, covering every distinct unordered pair of partitions of each dimension from 1 to 12 at every divisor of the common universal period for that dimension.

Over any fixed odd finite field, the two determinant conventions differ sharply in the size needed to express the same predicate over all extensions. For k distinct odd primes, a determinant-one pair of common dimension equal to the sum of the primes can express the disjunction of their divisibility tests. Every ordinary étale pair expressing it needs common dimension at least their product times two to the power k−1. This lower bound is attained. Conversely ordinary spectra transfer to determinant-one pairs by doubling the dimension. For nonempty signed spectra on inputs of dimension at most n, the logarithm of the worst required ordinary dimension is asymptotic to the square root of n log n. This identifies a class of reductions that cannot solve the unrestricted Grochow question by staying within polynomial-sized étale tables and preserving all extensions simultaneously.

Counting successful squarefree divisors is #P-complete on graph-encoded instances. The generating polynomial of their prime supports is the vertex-cover polynomial. Consequently characteristic-different-from-two coefficient fields admit VNP-complete families of such polynomials. Grochow's monotone-projection method also gives a lower bound on a distinct family with high extension-complexity cover polytopes. [Proofs](Spectra.md) · [Classical-group TI question](https://arxiv.org/html/2306.03135v2) · [Vertex-cover polynomials](https://perso.ens-lyon.fr/pascal.koiran/Publis/mfcs09.dichotomy_theorem.pdf)

## 2. Optimization and approximation

Let D be the least successful degree. On the graph-clause class a polynomial-time algorithm finds a degree at most D squared. The objective here is the logarithm of the degree, because the weight of selecting a vertex prime p is log p. On a bipartite graph the exact optimum and an optimality certificate come from a minimum cut, even when the graph has to be recovered from the two input tables. For bounded-width clauses the factor extends to their width. For arbitrary explicit tables, achieving any fixed factor on the logarithmic objective is NP-hard by classical hypergraph-cover hardness.

The sharp lower threshold approaching two on ordinary graph clauses uses the revised OpenAI/community Vertex Cover theorem as an external input. The independent upper bound, bipartite algorithm, unrestricted inapproximability, and polyhedral results have their separate proofs and dependencies in the note. [Proofs](Optimization.md) · [Revised Vertex Cover source](https://mathcommunity.github.io/oai-math-revised/papers/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf)

## 3. Transfer to other isomorphism objects

A scalar-extension-compatible construction realizes exactly the same spectrum for alternating matrix spaces, two-step Lie algebras, certain commutative local algebras, and uncolored cubic forms. For the cubic, send A to the polynomial Tr(xyz) on three copies of A. Over a splitting field it is a sum of products of three independent coordinates per primitive idempotent. The geometric Hessian rank-at-most-three locus recovers those blocks, in every characteristic. Thus every equivalence of cubics at a degree forces an algebra isomorphism there.

Two different encodings give further transfers to abstract class-two groups and uncolored graphs. The unitriangular group over the extended algebra recovers the ring from its commutator structure. Its order can be enormous, so this is a succinct family of groups. Even a family of explicit 2-regular graphs can exhibit the hard degree-selection problem, although isomorphism at a supplied degree is elementary. [Constructions, determinant conventions and recognition algorithms](Structures.md) · [Grochow–Qiao on TI-completeness](https://arxiv.org/abs/1907.00309)

## 4. Reconfiguration

Take two successful degrees and a cap K. Permit one multiplication or division by a prime per move, with every intermediate degree successful and at most K. Reachability is PSPACE-complete, for ordinary and determinant-one transport, even for certain graph encodings of bounded bandwidth. The reduction preserves shortest-path distance on its squarefree endpoints. In the same bounded-width regime the static minimum degree can be computed in polynomial time.

For arbitrary étale profiles, the reverse construction uses threshold choices and clause witnesses. It gives a polynomial reduction to minimum-cardinality vertex-cover reconfiguration with a product-weight cap. Without the cap, going through the least common multiple always realizes the shortest possible path. [Proofs and parameterized algorithms](Reconfiguration.md) · [Wrochna's bounded-bandwidth source](https://arxiv.org/abs/1405.0847)

## Interpretation

The shared resource across these problems is the extension degree. Different claims require preserving additional data: numerical costs for approximation, individual prime choices for counting, and single-prime moves for reconfiguration. The constructions specify when those data survive. They leave ordinary fixed-field TI, unrestricted SL-TI containment in ordinary TI, Cayley-table group isomorphism, and general circuit lower bounds with their existing status. All arguments here are informal. Priority for the transferred results has not been established.
