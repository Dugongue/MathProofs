# Explicit homomorphism fingerprints at bounded adjacency rank

## GP-0925. Constructive fingerprints for bounded nonzero adjacency rank

**Theorem.** Fix $r$ and put $s=2^r$. On simple $n$-vertex graphs whose rational adjacency matrix has rank at most $r$, a fixed family of at most
$$
2^{\binom{s}{2}}(1+n2^s)^{2^s}
$$
ordinary homomorphism counts separates every pair. Each test has at most $s+n2^s$ vertices and treewidth at most $s$. Its count has $O((s+n2^s)\log n)$ bits. The family, its evaluations, and reconstruction from the values are polynomial time for fixed $r$. More generally all three claims hold on the recognized class with at most $s$ distinct open neighborhoods, without requiring the rank bound.

A rank-$r$ Boolean matrix has at most $2^r$ distinct rows. Choose $r$ independent column coordinates, since projection to those coordinates is injective on the row space. Two vertices with equal rows are false twins: there is no edge between them, and each pair of distinct row classes is either completely joined or completely nonadjacent. The row classes and their adjacency ranks are directly recognizable in polynomial time.

Take ordered anchor tuples $a=(a_1,\ldots,a_s)\in V^s$, allowing repetitions. For each subset $J\subseteq[s]$ put
$$
c_J(a)= \bigl|\{v\in V\colon \{i:v\sim a_i\}=J\}\bigr|.
$$
The anchor adjacency pattern $A(a)$ is the simple graph on $[s]$ defined by the images' edges. Consider all the joint moments
$$
M(A,(e_J)_J)=\sum_{a\colon \,A(a)=A}\prod_J c_J(a)^{e_J},
\qquad 0\le e_J\le n.
$$
They count maps of the anchors and auxiliary satellite vertices. Each satellite of kind $J$ must be adjacent to exactly the anchors indexed by $J$. There is no constraint between satellites, and all maps may identify vertices.

Impose the listed positive edges and use inclusion-exclusion over the forbidden edges between anchors and from satellites to anchors. The resulting ordinary homomorphism tests have $s$ anchors with arbitrary adjacency and at most $n2^s$ satellites. Every satellite is adjacent to one chosen subset of the anchors. Its neighborhood subset and multiplicity specify all satellite data. Thus the displayed family size suffices. The expansion coefficients are computable in time polynomial for fixed $s$: first enumerate added anchor edges. For satellites of each prescribed kind $J$, enumerate how its at most $n$ indistinguishable positions are apportioned among final neighborhoods $S\supseteq J$. The multinomial coefficient counts the choices of positions, with sign $(-1)^{\sum_S m_{J,S}|S\setminus J|}$. The number of integer apportionments is polynomial for fixed $s$. Sum the multiplicities for the same resulting satellite counts. Dynamic counting of observed test values just enumerates the $n^s$ possible anchor images and uses the number of common neighbors for each satellite kind. An anchor bag containing all $s$ anchors and one extra bag per satellite bounds the test treewidth.

For each anchor graph $A$, the moments determine the number of anchor tuples of every exact profile $c\in\{0,\ldots,n\}^{2^s}$, by inverting the tensor product of the ordinary Vandermonde matrices on $0,\ldots,n$. All integers and denominators have polynomial bit length for fixed $s$, by minor bounds. In all profiles, the positive bins are the distinct adjacency signatures realized into the ordered anchor tuple. Their count is at most the number $t$ of distinct adjacency rows. A tuple containing a representative of every true row class has exactly $t$ positive bins, because the quotient has distinct rows. For that tuple, each positive bin contains at least one anchor, a property detectable from the rows of $A$ itself. Conversely any realized profile with the largest possible number of bins and this coverage property has one bin for each entire original row class. From its associated $A$, the representative anchors reveal all edges between the bins. The sizes $c_J$ give the multiplicities to blow the quotient back up into the original graph.

This proves a polynomial-sized exact homomorphism fingerprint and reconstruction on the stated bounded-rank class. The construction combines a moment evaluation argument with the homogeneous-class principle used in the [finite-group separator interpolation setting](https://arxiv.org/html/2410.14905#S2) and is related to the homomorphism-count viewpoint of [Neuen and Seppelt](https://arxiv.org/abs/2601.18602).

This is also a bounded-algebra class. The unital rational adjacency algebra has dimension at most $r+1$ by diagonalizability and the rank bound. If there are $t$ false-twin types, the adjacency also belongs to the coherent algebra spanned by the ordered type rectangles and their diagonal refinements, of dimension at most $t^2+t$.
