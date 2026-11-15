# Output-size lower bound for graph separating modules

Informal proof, November 14, 2026. The first part of Grochow and Urisman's Open Question 1.10 asks whether one can find a separating module of degree at most $d$ faster than $n^{O(d)}$. Their Theorem 3.1 defines the output to be an explicit list of integer polynomials, each given by its monomials and nonzero coefficients, spanning a separator. In this output model, the following theorem rules out a uniform $f(d)n^{o(d)}$ runtime for any function $f$. The multiplicity-obstruction part of the question, the decision problem, and algorithms with succinct output are separate. [Grochow and Urisman, *Geometric Complexity Theory and Graph Isomorphism*, Open Question 1.10 and Theorem 3.1](https://arxiv.org/html/2606.26244v2)

## Theorem

For every integer $d\ge 4$ and every sufficiently large $n$, there are two simple undirected $n$-vertex graphs $G_0,G_1$ admitting an $S_n$-invariant separating polynomial of degree at most $d$, such that every explicit integer polynomial list spanning a separating module of degree at most $d$ contains at least
$$
\binom{n}{\lfloor d/2\rfloor+1}
$$
distinct monomials. The module can be required to vanish on either member of the pair and to separate it from the other. In particular, for $n\ge\max\{2^{d-1}+d,(2d)^2\}$ this is at least $n^{d/4}$.

We use the paper's ambient ring with variables $x_{ij}$ for all ordered pairs, modulo $x_{ij}^2=x_{ij}$. The group $S_n$ relabels both indices together. A separating module is a group-stable vector subspace all of whose polynomials vanish on the first adjacency matrix, with some polynomial nonzero on the second. The support of a monomial is the set of vertex indices occurring in it. Each polynomial in the Boolean quotient has a unique multilinear representative, and reducing an explicitly listed polynomial to this representative can only decrease its number of monomials.

## Proof

**Two graphs with matching small probe counts.** Start with bipartite incidence graphs $G_0$ and $G_1$. The first part of each graph consists of the $d$ coordinates $[d]$. The second part consists of the even subsets of $[d]$ for $G_0$ and the odd subsets for $G_1$. There is one edge from coordinate $i$ to subset $S$ precisely if $i\in S$. Pad both graphs to $n\ge 2^{d-1}+d$ vertices using isolated vertices.

Consider a connected simple probe $P$ with an edge and maximum degree at most $d-1$. If $P$ is nonbipartite, its homomorphism counts into the two targets are both zero. For bipartite $P$, fix one of the two orientations sending the color classes of $P$ to the coordinate and subset parts. Choose the images of the coordinate-side vertices arbitrarily. Each subset-side vertex must contain the set of distinct images required by its neighbors. If this set has size $s$, then $s\le d-1$. Toggling any one unrestricted coordinate gives a parity-reversing bijection of the allowed supersets. Choices for different subset-side vertices are independent, so summing their equal counts over assignments and orientations gives equal homomorphism counts. No vertex in an edge of $P$ can map to a padded isolated vertex. Single-vertex probes have count $n$ in both targets, and general counts multiply over connected components. In particular, the targets agree on homomorphism counts from every simple graph with at most $d$ vertices.

**A degree-$d$ separator exists.** The invariant
$$
s(X)=\sum_{i=1}^n\Bigl(\sum_{j\ne i}x_{ij}\Bigr)^d
$$
counts homomorphisms from the $d$-leaf star when evaluated on a simple graph $X$. Every coordinate vertex has degree $2^{d-2}$ in either target, and every subset vertex has degree its subset size. Thus
$$
s(G_0)-s(G_1)=\sum_{k=0}^d(-1)^k\binom dk k^d=(-1)^d d!\ne0 .
$$
The last identity follows from inclusion-exclusion counting surjections from a $d$-element set onto a $d$-element set. Subtracting $s(G_i)$ produces the required polynomial for either orientation. Reducing its powers modulo $x_{ij}^2=x_{ij}$ preserves the degree upper bound.

**Small-support invariants give the same value.** An invariant whose monomials all have support at most $d$ is a linear combination of orbit sums of such monomials. A representative of an orbit uses a set of $t\le d$ vertex indices and specifies a directed graph pattern $Q$ on them by its variables $x_{ij}$. Evaluate its orbit sum on a simple undirected target. A loop makes the evaluation identically zero. Otherwise, after forgetting orientation and merging repeated undirected edges, evaluation is a fixed multiple of the number of injective homomorphisms from the resulting simple pattern. To see the multiple is fixed, sum first over all $n!$ relabelings with repetition. Each injection of the $t$ used vertex indices occurs $(n-t)!$ times, and each distinct orbit monomial occurs the same number of times. For a simple pattern on $t$ vertices, injective homomorphism counts are determined by ordinary homomorphism counts of its vertex quotients. Indeed, inclusion-exclusion over collisions of pairs of vertices gives these quotients by identifying the pairs along which collisions are imposed. Quotients with loops have zero count, parallel edges may be merged, and the resulting simple patterns have at most $d$ vertices. Hence all these orbit sums, and all the stated invariants, take equal values on $G_0,G_1$. This is the subgraph-count method in Grochow and Urisman's Observation 3.9. [Source](https://arxiv.org/html/2606.26244v2)

**A separating module must use a large support.** Suppose a list spanning a separating module uses only monomials with support at most $\lfloor d/2\rfloor$. There is a list polynomial $p$ nonzero on the second graph, since evaluation is linear. The stability of the span forces $p$ to vanish on every relabeling of the first graph. Therefore
$$
J(X)=\sum_{\pi\in S_n} p(\pi X)^2
$$
is invariant, vanishes on the first graph, and is strictly positive on the second. The paper's integer output format ensures every summand is the square of a real value. Each monomial of $J$ has support at most $2\lfloor d/2\rfloor\le d$ by expanding the square. Boolean reduction preserves this support upper bound. This contradicts the preceding step. This use of sums of squares is the argument of Grochow and Urisman's Proposition 3.8 applied to support size. [Source](https://arxiv.org/html/2606.26244v2)

**Relabeling forces a large list.** Let $M$ be a list monomial with support size $t\ge\lfloor d/2\rfloor+1$. Degree at most $d$ in the quotient gives $t\le 2d$. For each $\pi\in S_n$, the relabeled polynomial containing $\pi M$ is a linear combination of the output list. As relabeling permutes the multilinear monomials bijectively, the coefficient of $\pi M$ in that relabeled polynomial is nonzero. So $\pi M$ occurs in at least one list polynomial. Relabeling the support over all $t$-subsets of $[n]$ produces at least $\binom nt$ distinct output monomials. For $n\ge 4d$, monotonicity of binomial coefficients up to $n/2$ gives the theorem's claimed binomial bound. Moreover, if $n\ge(2d)^2$, then
$$
\binom nt\ge(n/t)^t\ge n^{t/2}\ge n^{d/4}.
$$
The first inequality follows by writing $\binom nt=\prod_{i=0}^{t-1}(n-i)/(t-i)$. The bound for the multilinear quotient also applies to expanded lists in the ordinary polynomial ring, because reducing such lists to quotient representatives creates no new output monomials.

Every correct explicit-output run must spend time at least its output length. If the bound $f(d)n^{o(d)}$ held, one could fix a sufficiently large $d$ at which its exponent is less than $d/4$, then let $n$ grow arbitrarily with this $d$ fixed to contradict the lower bound. The conclusion concerns output length: on the very same pairs, the star polynomial above has an arithmetic circuit with $O(n^2+d n)$ operations.
