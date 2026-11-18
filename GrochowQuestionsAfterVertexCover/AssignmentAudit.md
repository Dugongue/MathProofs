# An independent proof using assignment duality

This gives a second derivation of the permanent-oracle bound for the formal polynomial model in Grochow's Question 5.6. First pass to Boolean formal supports as justified for the target coefficients in [the main argument](Arithmetic.md). Delete identically zero gate outputs wherever they cannot contribute. At a live permanent gate simply forbid the matrix positions with zero children. Its allowed bipartite graph has a perfect matching.

For a real weight vector w on the input variables and each live gate g, let H_g(w) be the greatest weight of a monomial at g. A variable has its specified weight, and a live constant has weight zero. Union takes a maximum and multiplication takes a sum. At a permanent gate the correct value is a **maximum-weight perfect matching** on its allowed entries, where the weight of each entry is its child's H value. This remains exact for repeated inputs, because different occurrences of a polynomial factor can choose their maximizing monomials independently.

Make one free variable t_g for each live gate. Fix the leaf values as above. At a sum require t_g to be at least each child's t. At a product require it to be at least the sum of its child values, counting repeated slots. At a permanent gate of order m introduce free row and column potentials a_i,b_j, impose

$$
a_i+b_j\ge t_{h(i,j)}\quad\text{on allowed entries},\qquad
t_g\ge\sum_i a_i+\sum_j b_j.
$$

The assignment linear program has an integral optimum, and its dual attains the same value. By induction, every feasible labeling satisfies t_g at least H_g(w) for all g. Conversely set every t_g to H_g(w) and choose optimal dual potentials independently at each permanent gate. This satisfies all constraints at once, including where gates fan out. Hence these inequalities with t_out at most u project to the epigraph of the support function of the output Newton polytope P. There are O(s + sum of the squared query orders) inequalities, where s counts the ordinary circuit description including its queries as nodes.

For completeness, recover an extended formulation for P from this epigraph. Write the homogeneous lifted inequalities as D(w,u,z) at most zero after eliminating equations, or keep equations H(w,u,z)=0. A vector x belongs to P exactly when (x,−1,0) is nonpositive on this cone. The polyhedral Farkas lemma makes this equivalent to

$$
(x,-1,0)=D^T\lambda+H^T\mu,\qquad \lambda\ge0
$$

with free multipliers mu. Thus the same inequality count suffices, also when P lies in a proper affine subspace. If a bounded lift is desired, choose one lift of each of the finitely many vertices and intersect the multiplier system with a single upper bound on the sum of its nonnegative multipliers, after eliminating free variables. The resulting lift in nonnegative multiplier coordinates is bounded and retains all vertices. The extension lower bounds for the three targets now apply directly.

The epigraph method for monotone maxout networks is due to Hertrich and Loho. Here a whole implicit maximum over permutations costs only a polynomial number of inequalities, by assignment duality. Combined with exponential extension complexity of the targets, this explains exactly why even polynomially many nested permanent calls cannot suffice. [Hertrich–Loho, §3](https://arxiv.org/html/2411.03006v4#S3) · [Grochow, Questions 5.1–5.6](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=10)
