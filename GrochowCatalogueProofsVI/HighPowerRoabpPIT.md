# High-power identity tests with ROABP bases

## GP-0703

Let
$$
F(x)=\sum_{i=1}^r c_i f_i(x)^e,\qquad e\ge r^2,
$$
over $\mathbb Q$, with supplied read-once oblivious ABPs for the bases. Deterministic polynomial bit-time identity testing is possible even at variable width and with different variable orders for the bases. The time is polynomial in the displayed base descriptions, the numerical degree bound, $r$, and $e$. In addition, if all bases have fixed bounded width in one known common order, a polynomial-size hitting set works using only evaluations of $F$. This keeps the high-exponent promise of the original sparse-base result.

### Independence after pair separation

The high-power function-field ABC inequality says that any family of at most $r$ pairwise nonproportional, nonzero univariate polynomials in characteristic zero has linearly independent $e$th powers for $e\ge r^2$. For a relation with nonzero constant coefficients, absorb them in the bases by taking $e$th roots over the algebraic closure. A two-term relation would make the bases proportional, and any relation with at least three terms is ruled out by the cited bound. There can be at most one nonzero constant among pairwise nonproportional representatives. [Function-field estimate, Theorem 2.4](https://arxiv.org/html/2602.20832#S2.SS1)

The same assertion holds multivariately. For each pair of nonproportional polynomials $f_i,f_j$, the polynomial $f_i(a)f_j(b)-f_j(a)f_i(b)$ in two independent points $a,b$ is nonzero. The product of the finitely many such polynomials and the evaluations for any singleton is nonzero. Choose $a,b$ where that product is nonzero, using infinitude of the field. The affine line passing through $a,b$ preserves nonzeroness and pairwise nonproportionality, so the univariate statement rules out a relation on the line and hence in the original variables.

### White-box decision at variable width

Test each base for zero by the white-box ROABP test. For each nonzero base find a rational point of nonzero value by fixing one variable at a time. At that variable, test the restrictions at $0,\ldots,\Delta$, where $\Delta$ bounds the individual degree, and take the first nonzero restriction. The degree bound ensures some restriction succeeds whenever the current polynomial is nonzero. Evaluating a variable constant keeps the original order and size bounds.

For testing whether $f_i$ and $f_j$ are proportional, take a point $a$ with $f_j(a)\ne 0$, set $\gamma=f_i(a)/f_j(a)$, and test $f_i-\gamma f_j$ for zero. The deterministic white-box sum-of-two ROABP test applies with separate supplied orders. Its span computations can use actual coefficient rows and dependence solutions of polynomial-sized rational linear systems. The coefficient entries of a ROABP have polynomial bit length by the layer product bound, and the dependence solutions have polynomial bit length by the minor bounds. [White-box equivalence of two ROABPs, Section 2](https://doi.org/10.4230/LIPIcs.CCC.2015.323)

Within each proportionality class choose a representative $g$ and write its terms as $c_i(\gamma_i g)^e$. Compute the class coefficient $\sum_i c_i\gamma_i^e$ in exact rational arithmetic. Its bit length is polynomial in the original bit lengths and numerical $e$. The independence proof shows that $F=0$ exactly when every such class coefficient vanishes. The decision does not construct a branching program for any $f_i^e$.

### Hitting with only the sum oracle

Suppose the bases have width at most a fixed $w$ in one supplied order. Let $H$ be a polynomial-size explicit hitting set for width $2w$ in that order. For any span of two bases its evaluation map on $H$ is injective, since every linear combination is represented by the block-diagonal width-$2w$ program. In particular nonzero bases remain nonzero as evaluation vectors, and nonproportional bases have independent evaluation vectors. [Constant-width ROABP hitting sets](https://arxiv.org/abs/1601.08031)

Enumerate $H$ and interpolate a single univariate polynomial curve $\gamma$ that passes through its points at distinct integer times, of coordinate degrees at most $|H|-1$. Then all pairwise nonproportional nonzero representatives remain nonzero and pairwise nonproportional after composition with $\gamma$. If $F\ne 0$, the sum restricted to this curve is nonzero by the independence result. Its degree is at most $e\Delta_{\rm tot}(|H|-1)$ if $\Delta_{\rm tot}$ bounds the base total degree. Evaluating the original oracle at the curve values on one larger integer grid gives the hitting set. The curve coefficients and query coordinates have polynomial bit length by rational interpolation, using polynomial-bit points in the constant-width hitting construction. This also proves a general lift from any explicit hitting set for linear combinations of two bases to one for high powers, with only the displayed degree factor in the number of queries. [Sparse-base powering context](https://arxiv.org/html/2602.20832#S3)
