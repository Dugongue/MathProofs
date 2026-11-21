# Exact white-box identity testing for read ABPs by treewidth

## GP-0746

Consider a rational width-$w$ oblivious algebraic branching program given as a sequence of univariate matrix factors, with coefficients displayed. Let $\delta$ bound their individual degrees, and suppose no variable occurs more than $k$ times. Construct a simple graph on the variables by joining two distinct variables if they occur consecutively in the supplied sequence. Given a tree decomposition of width $t$ of this graph, deterministic identity testing takes
$$
(w+1)^{O(k(t+1))}(\delta+1)^{O(k)}\operatorname{poly}(L)
$$
bit time for input length $L$ and a polynomial-size decomposition. In particular the theorem gives a polynomial-time algorithm for fixed $k,t$, with no restriction on the relative read orders of the different passes. For fixed $t$, a decomposition can also be found in polynomial time. The algorithm works by contracted coefficient inner products and does not rewrite the program in a single read order. [Read-$k$ ABP context](https://arxiv.org/abs/1511.07136) · [Fixed-treewidth recognition](https://doi.org/10.1137/S0097539793251219)

Write the output as $f(x)=u^{\mathsf T}\prod_{a=1}^{\ell} M_a(x_{i_a})v$, where $M_a(x)=\sum_{d=0}^{\delta} M_{a,d}x^d$. The fixed endpoint vectors can be absorbed in the first and last factors. Constant layers can also be multiplied into neighboring factors. Use two copies of this matrix chain. At each occurrence $a$ choose exponents $d_a,d'_a$ for its two copies. For every variable $x_i$, impose the constraint
$$
\sum_{a:i_a=i} d_a=\sum_{a:i_a=i}d'_a .
$$
The sum of all compatible two-chain weights is $\sum_\alpha ([x^\alpha]f)^2$, the sum of squared coefficients of $f$. This follows by expanding the two chains independently and applying the equality constraints to their resulting exponent vectors. The sum is zero precisely when $f=0$, because all coefficients are rational.

Combine all occurrences of each variable into one factor. Its arguments are the two copies of boundary matrix indices for each incident edge of the occurrence chain. Sum product weights locally over its at most $2k$ chosen exponents, requiring the displayed equality. Matrix indices of edges whose endpoints bear the same variable are summed locally as well. Each remaining chain edge carries a paired state of size at most $w^2$. Parallel chain edges between the same pair of variables are kept as separate paired states. Each variable has at most $2k$ incident edges, counting multiplicity. The desired coefficient inner product is the tensor contraction of these local factors.

Convert a bag of the variable decomposition into a bag containing all paired state arguments incident to its vertices. The new bag contains at most $2k(t+1)$ state arguments. For an edge argument, the bags where it occurs are the union of the bags containing its endpoints. This union is connected because the two endpoint subtrees intersect in a bag covering their simple edge. Every factor fits into any bag of its original vertex. Therefore these bags give a tree decomposition of the factor contraction. Eliminate by summing along a rooted decomposition. For each edge of the decomposition table, store the partial contraction as a function of the paired states common to its adjacent bags. Multiply tables and factors in a bag and sum its states missing from the parent. This evaluates the contraction in the displayed time.

For bit complexity, clear one common denominator per input factor, scaling the entire output by a nonzero rational. The local factors and all subsequent partial contractions then use integers. Each term is a product of at most two entries per occurrence. The logarithm of the number of possible choices of states and exponents is polynomial in $L$, so the integers in all tables have polynomial bit length. A zero result is an exact rational identity test.
