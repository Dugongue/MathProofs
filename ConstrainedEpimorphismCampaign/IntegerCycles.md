# Counting optimal integer surface cycles through residual cut posets

Informal research proof. Let S be a closed connected orientable simplicial surface, z an integral 1-cycle, and let the objective be the unweighted integer norm sum of absolute edge coefficients. Write Z for that norm on z. When the coefficients of z are supplied in unary, counting the distinct minimum-norm cycles homologous to z is #P-complete under polynomial-time counting reductions. Its approximation complexity is equivalent, under approximation-preserving reductions, to counting independent sets in bipartite graphs (#BIS). The minimum and one minimizer can be found in polynomial time, even with binary coefficients.

The counting reductions below are polynomial in the number of simplices plus Z. The unary hypothesis is material. The threshold expansion is not a polynomial bit-time reduction for arbitrary binary magnitudes. Optimization over integer coefficients was already established using total unimodularity. The claims here concern the entire set of optima. Publication priority for this classification remains unverified. [Dey–Hirani–Krishnamoorthy](https://arxiv.org/abs/1001.0338)

## 1. An explicit quotient by the kernel

Give all faces compatible orientations. Each homologous representative is y = z minus the boundary of an integer face labeling x. On an edge separating faces f and g its coefficient is z_e minus x_f plus x_g, with the incidence signs fixed by the orientation.

The face-boundary kernel consists exactly of the constant labelings. A chain y therefore has a unique labeling with x at a selected root face equal to zero. This makes the correspondence bijective, including for counting.

A minimum y has norm at most Z. Along a simple path in a spanning tree of the dual graph, integrate x_f minus x_g = z_e minus y_e. Therefore every normalized optimal x has absolute value at most 2Z. If Z=0 the unique minimizer is zero. Otherwise put B=2Z and restrict all variables to the integer interval [-B,B].

## 2. All optima as minimum cuts

Represent x_f by its threshold bits b(f,t) indicating x_f at least t for -B+1 through B. Enforce b(f,t+1) at most b(f,t) using directed arcs of capacity larger than Z, and fix the root bits to their value at zero. Regard a bit below the threshold interval as the constant one and above it as zero.

For each oriented edge, the identity

$$
|x_f-x_g-z_e|
 = sum_t |b(f,t)-b(g,t-z_e)|
$$

uses t ranging from min(-B,-B+z_e)+1 to max(B,B+z_e). Outside this finite range both indicator bits coincide. Each summand is an undirected unit cut edge, possibly incident to a fixed zero or one. Coincident fixed bits give zero, and opposite fixed bits add an explicit constant. The correspondence between monotone threshold assignments and bounded integer labelings is bijective.

There is a feasible labeling of cost Z, so a capacity Z+1 suffices to enforce every monotonicity and root condition. The graph has polynomial size in |S|+Z. A maximum flow and its residual network give a poset of optional strongly connected components. Components reachable from the source are forced in, those reaching the sink are forced out, and the remaining residual implications define an order. Minimum cuts correspond exactly to order ideals, with no multiplicative factor. Optional components of size one and free isolated components are included.

Consequently the surface count equals the ideal count of an explicit polynomial-size poset. This also gives a bijection for sampling. The residual-cut representation is classical. [Picard–Queyranne](https://publications.polymtl.ca/5993/1/EP-R-79-15_Picard.pdf)

## 3. A converse that retains every optimum

Use the earlier MathProofs chamber construction, which has three terminals per equation incidence and two mutually edge-disjoint dual routes per pair in any terminal matching. It produces a closed connected orientable surface with polynomially many triangles. Use integer coefficients on seams and the integer absolute-value objective.

Fix a chamber. Sort its N integer terminal labels. Choose a median m and pair lowest with highest, next-lowest with next-highest. The sum of the pair differences equals D = sum of absolute differences from m. For odd N leave a median terminal unpaired. Each routed pair has two edge-disjoint paths, so the sum of absolute jumps on internal edges is at least 2D. Changing all faces in the chamber to m changes the seam cost by at most D, by the triangle inequality. If D is positive the total objective strictly decreases. If D=0 but some interior face differs, interior connectedness gives positive internal cost and rounding changes no seam. Hence every minimum labeling is uniform in each chamber.

An integer variable labeling then gives cost three times the sum of absolute errors in its translation constraints. Two such labelings give the same chain precisely when they differ by a simultaneous integer translation. Fixing the reference variable to zero removes that ambiguity. This proves a count-preserving compiler for all optimal labelings, including their coefficient values. [Earlier chamber construction](Chambers.md)

Now take a poset P. For each desired ideal bit b_v use an integer variable x_v relative to a reference r=0. For every cover relation u below v penalize x_v greater than x_u. On binary inputs twice this penalty is

$$
|x_v-x_u|+x_v-x_u.
$$

Sum these expressions. Collect the linear coefficient d_v of each variable. Replace a positive d_v x_v by d_v |x_v|. Replace a negative d_v x_v by (-d_v)|x_v-1|, with the corresponding known constant. Add |x_v|+|x_v-1| for every variable. All terms have nonnegative integer weights and are absolute errors of translation constraints. Expand weights as repetitions; their total is polynomial in the poset presentation.

Clipping every integer variable into [0,1] cannot increase any of these unary or pairwise terms. If a variable lies outside that interval its added unary pair strictly decreases. Thus every optimum is binary. On binary inputs the cost is a known constant plus twice the number of violated order implications. The all-zero labeling attains that constant, and the minima are exactly the ideals. Apply the chamber compiler. The image of the all-zero labeling is an explicit minimum homologous cycle, with its length supplied. All seam coefficients are zero or one, so this is a unary input even before encoding.

An ideal of a height-two poset with minimal elements L, maximal elements R and relations from a bipartite graph corresponds to an independent set via I=(L minus S_L) union S_R. Thus the converse is parsimonious from #BIS. Counting ideals is #P-complete under exact counting reductions. [Provan–Ball](https://doi.org/10.1137/0212053)

## 4. Approximation-preserving classification without a black box

For completeness, ideal counting reduces to #BIS by the following explicit filter. Given a poset on n elements, make a bipartite graph with left copy L_v and right copy R_v of every element, and an edge L_u R_v whenever u is at most v. Each diagonal pair is an edge. Independent sets have size at most n, and those of size n choose exactly one member of every pair. Their chosen right elements form an ideal, so their number a_n equals the ideal count.

Replace every vertex by k independent twins with complete bipartite edges corresponding to each original edge. If lambda=2^k-1, the number of independent sets of the twin graph is

$$
W=sum_{j=0}^n a_j lambda^j.
$$

There are at most 4^n independent sets in the original graph, and a_n is at least one. Choose k so lambda exceeds 4^n/epsilon times a fixed constant. The relative contribution of degrees below n is then at most epsilon divided by that constant. A relative approximation of W, divided by lambda^n, gives a relative approximation of a_n, with the desired tolerance after rescaling epsilon. The twin graph size is polynomial in n plus log(1/epsilon). All integer arithmetic has polynomial bit length.

Composing this filter with Sections 1–2 gives the upper approximation reduction. Section 3 applied to a bipartite independent-set instance gives the lower approximation reduction exactly. This proves the equivalence for the whole unary surface class, with arbitrary genus.

For #P membership compute the optimum by the cut construction, guess the signed edge vector within its coefficient bound, and test its norm and homology by integer linear algebra. Use one canonical fixed-length encoding per vector. The number of accepting guesses is the number of distinct cycles. A supplied minimum or minimum representative does not reduce the hardness on the constructed family.

## 5. Relation to the binary-coefficient result

The previous binary construction produces one known optimum and one additional optimum per satisfying circuit input. The integer norm has the residual-poset representation above. Changing the coefficient ring also changes the objective geometry. An argument using support size over a finite field cannot be imported as an integer absolute-value proof without accounting for that change.

The classification uses classical minimum-cut theory and the preceding chamber construction. It answers a precisely stated counting problem. A claim that it resolves a previously posed open question requires a separate identification of such a question.

## 6. Polynomial delay and a tractable uniqueness test over the integers

The counting statement has a stronger algorithmic complement. For arbitrary binary-encoded integral z on a closed orientable surface, all minimum integer norm representatives can be enumerated with polynomial delay and polynomial space. In particular, uniqueness and construction of a second representative are deterministic polynomial-time tasks. This conclusion needs no genus bound and no unary coefficient assumption.

Let K be the optimum, computed by the established integer optimization. It is at most Z. Every edge coefficient of an optimum is between minus K and K. Use a feasibility oracle that asks whether an optimum can satisfy prescribed integer intervals on its edge coefficients. Writing y=z-Dx, those intervals are upper and lower bounds on rows of the dual incidence matrix D. The absolute-value optimization has matrix [D I -I] for nonnegative positive and negative error variables. Adding interval inequalities on Dx appends signed copies of rows of D, with zero entries in the error columns. The stacked incidence matrix is totally unimodular, since it only repeats or negates rows of an incidence matrix. Appending the error columns preserves total unimodularity because each has a single nonzero entry. Fix the root face by a unit row. Convert inequalities to equalities with slack variables. Thus, if the interval-constrained optimization is feasible, it has an integral optimum. Solve it as a rational linear program and check whether its minimum equals K. The coefficient and solution bit lengths are polynomial in the original binary input.

Recursively split each edge interval into two nonempty halves. Keep only subintervals for which the feasibility oracle returns true, and use a fixed edge order. At a leaf every coefficient is fixed, giving one chain. The search tree has depth at most a constant times |E| times log(K+2). Between consecutive outputs a depth-first traversal visits at most twice this depth of feasible or pruned nodes, because every retained subtree contains an output. Initial delay and final exhaustion obey the same bound. The recursion stack and the linear programs require polynomial space. A given optimum can be skipped once if the request is to return another.

It also follows directly that uniqueness is equivalent to every coordinate having identical minimum and maximum over the optimal face. The integral polyhedron above ensures that a nontrivial coordinate interval contains a distinct integral optimum. Positive edge weights make the optimum set finite; the present theorem uses unit weights. The enumeration concerns distinct chains rather than face labelings, so the constant-label kernel introduces no duplicates.

This coefficient distinction is substantive. The finite-field support construction can make finding a second minimum chain NP-complete despite a supplied first minimum. Integer absolute-value optimization admits the polynomial-delay algorithm above, even though counting all optima stays #P-complete. The total-unimodular optimization and the general use of optimization for enumerating integral solutions are classical inputs. Priority for this explicit enumeration consequence has not been established.

## 7. The enumeration theorem extends to every totally unimodular boundary matrix

Let D be any explicit totally unimodular integer matrix. Given an integral chain z and strictly positive rational coordinate weights supplied in binary, one can enumerate every minimum weighted integer absolute-value chain in z plus image(D), with polynomial delay and polynomial space in the input bit length. This includes the higher-dimensional complexes covered by the Dey–Hirani–Krishnamoorthy criterion.

Choose a maximal independent set of columns D'. It has the same integral image as D. To check the integral assertion, take a nonsingular rank-sized row minor of D'. Its determinant is plus or minus one. Every column of D is the same rational linear combination of D' in all rows as it is in the selected rows, by the rank. The inverse minor has integral entries, so those coefficients are integers. Replacing D by D' therefore retains all integer homologous chains and removes the kernel.

Optimize the split nonnegative error variables with the matrix [D' I -I]. For each interval branch on a chain coordinate, append the corresponding signed row of D' with the appropriately translated integral bound. The original TU matrix with repeated signed rows is still TU, and the remaining columns are unit columns. Root normalization is unnecessary after choosing D'. Hence interval-constrained minima exist integrally and are computable in polynomial bit time by linear programming.

If the original chain has weighted norm Z_w and the least coordinate weight is w_min, every optimal coefficient has absolute value at most Z_w/w_min. This ratio can be large, but its binary length is polynomial in the input. The midpoint traversal from Section 6 therefore has polynomial depth in the original input bits. The selected unit-determinant minor also bounds the needed coordinates of a chain preimage, so feasibility certificates have polynomial bit length.

Exact counting is already #P-hard on the unweighted surface subclass and is in #P for this explicit positive-weight TU model: compute the optimum and guess one canonically encoded bounded chain vector. Consequently the general TU model has polynomial-time optimization, uniqueness, second-solution search and polynomial-delay enumeration, together with #P-complete exact counting under counting reductions. The #BIS approximation equivalence proved earlier is asserted only for unary-coefficient surface instances.
