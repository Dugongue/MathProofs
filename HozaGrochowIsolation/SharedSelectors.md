# Shared selectors for routed matrix multiplication

A balanced tensor contraction can have exponentially many nonzero contributions to a coefficient. Their sum can vanish in every characteristic. A single short seed gives one distinguished contribution to every reachable coefficient in a polynomial-size list of sections. For three independently routed operand pairs, this yields a restriction with Laurent coefficients whose initial tensor is an explicitly masked matrix multiplication tensor. The required finite extension for an exact shared-selector restriction can grow logarithmically with the number of sections, and that dependence is sharp.

## Isolation on a binary tree

A **routing system** is a rooted binary tree with a finite set of boundary states at each node. For a fixed node and incoming boundary state, the local alternatives have distinct labels in $[W]$. An alternative specifies the incoming state for each child. An assignment recursively chooses one alternative at every node, beginning with a specified root state. A node with no available alternative in the given state is infeasible. Each alternative can carry an integer primary cost and a nonzero coefficient in a field. The score of an assignment before perturbation is the sum of its costs.

Take a finite list of systems, each with at most $n$ nodes and height at most $h$, where depth is measured from zero at the root. Let $M$ be the sum over all nodes and states in this list of the numbers of unordered distinct pairs of alternatives. Use an explicit binary code $C:[W]\to\{0,1\}^{\ell}$ of minimum distance $d>\log_2\max(1,M)$. One can take $\ell=O(\log(2WM+2W))$, for example with an explicit constant-relative-distance code as used by Hoza. For a seed $x\in\{0,1\}^{\ell}$, put
$$
\rho_x(v,a)=\sum_{j=1}^{\ell}6^{h-\operatorname{depth}(v)+\ell-j} C(a)_j x_j.
\tag{1}
$$
A seed works simultaneously for every feasible incoming state at every node of every system with probability at least $1-M2^{-d}$. Here a working seed means that the lexicographic objective (total primary cost, total perturbation) has a unique minimizer. The weights in (1) depend on depth and alternative labels. The same seed is used for the whole list.

### Proof

Set $U=n6^{h+\ell}$. Multiply each primary cost by $U+1$ and add the corresponding perturbation. As the sum of perturbations within any subtree is between zero and $U$, this single integer objective realizes the desired lexicographic order.

At a node $v$ with a fixed incoming state, let $D_a(x)$ be the minimum objective among the assignments using a feasible alternative $a$ at $v$. Put
$$
B_j=6^{h-\operatorname{depth}(v)+\ell-j}.
$$
For one such assignment, changing bit $j$ from zero to one raises the objective by $B_j C(a)_j$ at $v$. At descendant depth difference $s$ there are at most $2^s$ nodes, each contributing at most $6^{-s}B_j$. The sum of their increases is at most $B_j\sum_{s\ge1}(2/6)^s=B_j/2$. This gives the interval
$$
\partial_jD_a(x)\in B_j[C(a)_j,C(a)_j+1/2]
\tag{2}
$$
also for the minimum: the optimizer at bit zero gives the upper bound by evaluating it at bit one, and the optimizer at bit one gives the lower bound by evaluating it at bit zero.

For $a\ne b$, fix the seed bits at all positions where $C(a)$ and $C(b)$ agree. There is at most one seed with these fixed bits at which $D_a=D_b$. Indeed, if two such seeds tie, change one to the other from left to right. The first changed bit $j$ lies at a code disagreement, so (2) changes $D_a-D_b$ by at least $B_j/2$ in absolute value. At a later bit $j+s$, both derivatives have the same sign under that flip and have absolute value at most $(3/2)6^{-s}B_j$. The change to their difference is at most this bound. The sum of all later bounds is at most $3B_j/10<B_j/2$. Thus the second seed cannot tie. There are at least $d$ disagreement positions, so a tie has probability at most $2^{-d}$.

A union bound excludes every considered tie. At a feasible node and incoming state, the minimum then uses a unique local alternative. Conditional on that alternative its child states are fixed, and costs add independently in the child subtrees. Induction on subtree height gives uniqueness of the full assignment. This proves the simultaneous assertion.

Formula (2) adapts the seed derivative bound from Hoza's proof of Theorem 2.4. His distinguished layer uses the maximum 2-adic valuation and divides a path into two subpaths. Here a fixed binary contraction tree supplies the division, and the tree depth controls the total influence of lower nodes. The extension applies to local transition labels, and an arbitrary additive primary objective can coexist with the perturbation. [Hoza, *NL = UL*, Section 2](https://eccc.weizmann.ac.il/report/2026/323/)

The bound is effective. For a seed, a bottom-up table computes all feasible alternatives' minimum costs by adding child minima, so one can test every possible tie in time polynomial in the explicit list of alternatives and its cost bit lengths. Enumerating the $2^\ell$ seeds is polynomial in $W$ and $M+1$. At height $O(\log n)$, the exponent bound $U=n6^{h+\ell}$ is polynomial in $n,W,M+1$. A balanced binary contraction tree with bond dimension $D$ and at most $b$ exposed bonds per subtree is an example after placing the boundary assignments in the state tables. A pair of child boundary assignments is a local alternative, with label space of size at most $D^{2b}$ at internal nodes. Consistency on shared bonds gives the allowed alternatives. Coefficients from leaf tensors and additional leaf alternatives can be included directly in the tables. Thus cyclic input networks can also use the theorem when a balanced contraction tree with these boundary bounds is supplied. [Dudek, Dueñas-Osorio and Vardi on contraction trees](https://arxiv.org/abs/1908.04381)

## Applying the selectors to matrix multiplication

Give each node its own selector vector space $L_v$ with basis $e_a$ for alternative labels $a\in[W]$. Routing systems for a given set of operand pairs use the same nodes and label spaces. The coefficient tensor $u_{ij}\in\bigotimes_v L_v$ is the sum over all feasible assignments for the boundary pair $(i,j)$, with coefficient the product of the local coefficients and with basis tensor $\bigotimes_v e_{a_v}$. Two distinct assignments for the fixed starting state have different label tuples, since the labels determine all subsequent states. This description applies separately to vectors $v_{jk}$ and $w_{ki}$ in the other two routing trees. A vector is zero when its system is infeasible.

For finite index sets $I,J,K$, consider the fixed tensor
$$
S=\sum_{i\in I,j\in J,k\in K}
 (e_{ij}\otimes u_{ij})\otimes(e_{jk}\otimes v_{jk})\otimes(e_{ki}\otimes w_{ki}).
\tag{3}
$$
The source can be specified by the routing tables even when (3) is large as a dense array. A shared selector on one mode of (3) means a product of scalar linear forms on that mode's selector factors. It is the same product for all boundary pairs of that mode. After contracting the selectors, ordinary linear maps on the three boundary pair spaces are allowed.

Apply (1) with primary costs zero and choose a seed isolating all sections. At each node use the scalar linear form taking $e_a$ to $t^{\rho_x(v,a)}$. Each nonempty section evaluates to a polynomial with a unique lowest-weight contribution. That initial coefficient is nonzero over the starting field, even in positive characteristic, and its exponent is at most $U$. Empty sections evaluate to zero. If the three resulting polynomials are $F_{ij}(t),G_{jk}(t),H_{ki}(t)$, the contracted tensor is
$$
\sum_{i,j,k} F_{ij}(t)G_{jk}(t)H_{ki}(t)
   e_{ij}\otimes e_{jk}\otimes e_{ki}.
\tag{4}
$$
Write a nonzero section as $t^e(c+tP(t))$ with $c\ne0$. On its boundary coordinate apply the diagonal scalar $c^{-1}t^{-e}$. These are modewise Laurent scalars because the sections depend on operand pairs. After normalization, the constant term is the rectangular matrix multiplication tensor with the three missing-pair masks. A triple survives exactly when each of its three pair sections is feasible. Thus (3) gives the masked tensor by an approximative restriction in the shared-selector model.

Let $B$ be the total number of nonempty pair sections across the three modes. There is an exact restriction over any extension field with more than $BU$ nonzero elements. Indeed the product of the nonzero section polynomials has degree at most $BU$. Choose a nonzero evaluation parameter outside its root set, then divide by each surviving factor using diagonal base changes. In particular a finite field $\mathbb F_q$ needs extension degree at most $1+\lfloor\log_q(BU+1)\rfloor$. This follows directly by root counting and works regardless of whether the characteristic is small relative to the number of routings.

### Branching and cancellation in an explicit family

Take a complete binary tree with $L=2^h$ leaves, $h\ge1$. At each node the boundary state is a parity bit. At an internal node whose state is $s$, use the two alternatives $(a,b)\in\{0,1\}^2$ with $a+b=s\bmod2$. They give the child states $a,b$ and local coefficient $(-1)^a$. Every leaf has one alternative with coefficient one for each state. A root parity has $2^{L-1}$ feasible assignments, corresponding to the leaf bit strings of that parity. At the lowest internal level the two alternatives sum to zero under the all-ones selector, for either state. Thus all the unweighted root sections vanish in every field, including characteristic two. The two root parity sections nevertheless have leading coefficients in $\{1,-1\}$ under a working seed.

For any three prescribed operand-pair masks, include one such system in each mode, pin the root parity separately for each allowed pair and make each forbidden pair infeasible. The exponent bound $U$ is polynomial in $L$ and the number of pair sections. The same perturbation within one mode works for both root parities. The family illustrates a genuine cancellation in a single uniform selector assignment and the role of isolation in recovering the full masked tensor.

### A sharp finite-field extension requirement

Let $q$ be a prime power and $k\ge2$. Index rows $i$ by the $(q^k-1)/(q-1)$ points of the projective dual of $\mathbb F_q^k$, and choose a representative nonzero linear form $\lambda_i$ for each. Use one shared $k$-dimensional selector in the first mode, with $u_{ij}$ the coefficient vector of $\lambda_i$ independent of $j$. The second and third modes have no selectors. Take all pair masks full and any positive sizes for the other two multiplication indices.

The formal selector $(1,t,\ldots,t^{k-1})$ makes each $\lambda_i$ a nonzero polynomial with nonzero leading coefficient. Normalizing the row-dependent valuation gives full matrix multiplication by the displayed Laurent restriction. For an exact restriction over $\mathbb F_{q^m}$ with a single shared first-mode selector, every $\lambda_i$ must be nonzero on the selector. If one vanishes, the first flattening rank of (4) loses all pairs in that row. Full matrix multiplication has full first flattening rank, because different pairs $(i,j)$ have disjoint supports in the other two modes. No subsequent linear maps can increase that rank.

For a selector $(z_1,\ldots,z_k)$, having all $\lambda_i(z)\ne0$ is precisely $\mathbb F_q$-linear independence of $z_1,\ldots,z_k$. Such a selector exists exactly when $m\ge k$. When it exists, each row scalar can be divided out, giving an exact restriction. This is a strict gap over the original field and shows logarithmic dependence on the number of pair sections is unavoidable in this shared-selector setting. The gap uses the requirement that a physical selector is shared across row indices. Arbitrary linear maps on a grouped source mode can depend on the boundary pair, which is a different restriction model.

## Relation to previous work and verification

The construction uses local selectors before evaluating the contraction. Our earlier two-scale Lie-group separation results use a polynomial in group entries after evaluating the group product. Group-theoretic separating polynomials likewise separate outputs in a common group-product support. The present construction has a fixed selector-lifted source tensor and a pairwise factorization hypothesis. It avoids cancellation from many internal routes and includes an exact small-field statement. No matrix multiplication exponent estimate follows from the construction alone, since it does not bound the rank of the selector-lifted source. [Blasiak, Cohn, Grochow, Pratt and Umans, Definition 2.5](https://arxiv.org/html/2410.14905#S2.SS2)

Nederlof, Pilipczuk, Swennenhuis and Węgrzycki study isolation for combinatorial problems on decomposable graphs with weights on original graph objects. The weights here act on local transition labels supplied by a contraction tree, which makes conditional subproblems independent. This scope is needed for (2) and for the product-selector interpretation. [Isolation schemes for problems on decomposable graphs](https://arxiv.org/abs/2105.01465)

These are written proofs. The general theorem and its tensor application have not been checked in Lean.
