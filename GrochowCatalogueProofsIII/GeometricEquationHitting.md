# Quadratic equation-map hitting sets from unsatisfiable CNFs

## GP-0677

Over every infinite field there is a polynomial-time uniform family of unsatisfiable 3-CNFs whose clause-and-Boolean equation maps hit every nonzero polynomial of total degree at most two in the equation variables. In particular, no member has a degree-two geometric IPS certificate. There is also a universal complementary obstruction. The equation map of any such CNF with a three-variable clause fails to hit the class of constant-size polynomials of total degree at most twelve, even when those polynomials use only four equation coordinates.

### Constructing the clauses

Fix a positive integer $c=256$ and choose $m=cn$ independent uniform unordered triples from $[n]$, with independent uniform signs on their three literals. View the result as a bipartite incidence graph with one node per clause instance. For each Boolean assignment the number of falsified sampled clauses is binomial with mean $m/8$. Chernoff's bound gives probability at most $\exp(-m/64)$ that fewer than $m/16$ are falsified. The union bound over $2^n$ assignments goes to zero.

For every fixed $\ell\in\{2,3,4\}$, the expected number of incidence cycles of length $2\ell$ is bounded by a constant depending only on $c$. Count ordered choices of $\ell$ distinct variables and $\ell$ distinct clause instances, at most $n^\ell m^\ell$, and require each chosen triple to contain its two specified variables. The probability for each clause is $6/(n(n-1))$. Hence the expected total number of these cycles is $O_c(1)$. Markov's inequality shows that with probability tending to one there are fewer than $m/32$ such cycles. Delete a clause from every cycle present before deletion. The resulting instance is unsatisfiable and its incidence graph has girth greater than eight. In particular, no two clauses have the same underlying triple.

The generator searches increasing $n$ and then all signed triple collections in a fixed order for the first unsatisfiable incidence-girth-greater-than-eight instance. The existence argument proves that this search terminates after a fixed number of steps independent of the family parameter. The $k$th formula is the disjoint union of $k$ tagged copies of that fixed instance. This gives a deterministic polynomial-time uniform specification, with a constant preprocessing cost. The formula has size linear in $k$.

### Why the image hits quadratic polynomials

Use any graded monomial order in the original variables. The leading exponent of the Boolean equation $x_i^2-x_i$ is $2e_i$. For a clause with underlying triple $E$, the leading exponent of its falsification polynomial is the incidence vector $1_E$, with nonzero coefficient $1$ or $-1$.

Every nonempty set of at most four distinct clause triples has a variable appearing exactly once in that set. Its incidence graph is a forest, and every clause node has degree three. A nontrivial component must have an endpoint on a variable node. Thus no symmetric difference of the corresponding mod-two incidence vectors is zero.

Suppose two monomials of total degree at most two in the equation coordinates gave the same leading exponent under substitution. Modulo two, the preceding fact forces identical sets of odd-multiplicity clause factors. With two such factors the products are already identical. With one such factor the only possible remaining factor is one Boolean equation, determined by its doubled coordinate. With none, the possibilities are the constant, one or two Boolean factors counted with multiplicities, and the square of a single clause. Their total leading degrees are respectively $0,2,4,6$, and at equal degree their exponent vectors identify the factors. The input monomials therefore have pairwise distinct output leading monomials. In a nonzero quadratic polynomial in the equation coordinates the largest such leading monomial cannot cancel. The composite is nonzero and consequently has a nonzero value over the infinite field.

The finite grid $\{0,1,\ldots,6\}^n$ is a hitting set for these composites over characteristic zero, although its full enumeration is unnecessary. For a polynomial of total degree at most six, it suffices to use assignments with at most six nonzero coordinates and nonzero coordinate values among $1,\ldots,6$. A monomial with nonzero coefficient is supported on at most six variables. The restriction to its support remains nonzero and the usual grid induction applies. The same argument over any infinite field uses seven fixed distinct field elements including zero. Thus the restricted image even has an explicit polynomial-size hitting subset.

### Degree-twelve obstruction

For one clause with three distinct variables, let its literal failure indicators be $u_1,u_2,u_3$, each either $x_i$ or $1-x_i$. Set $b_i=u_i^2-u_i$. In $\mathbb Z[b_1,b_2,b_3,Z]$ consider the characteristic polynomial of multiplication by $U_1U_2U_3$ on the free rank-eight algebra
$$
\mathbb Z[b_1,b_2,b_3][U_1,U_2,U_3]/(U_1^2-U_1-b_1,U_2^2-U_2-b_2,U_3^2-U_3-b_3).
$$
In the square-free basis its matrix is the tensor product of three matrices for multiplication by $U_i$ on $\{1,U_i\}$. Each entry is a product of a subset of the $b_i$ and zeros or ones. The characteristic polynomial is monic in $Z$ and vanishes at $Z=u_1u_2u_3$ by Cayley–Hamilton and the substitution $U_i\mapsto u_i$. To bound the total degree, write the coefficient of $Z^{8-j}$ as the signed elementary symmetric polynomial of degree $j$ in the eight products formed by choosing one root from each of the three quadratic pairs. This is symmetric in each pair, and homogeneous of degree $j$ in each pair separately. Expressing it through the elementary symmetric polynomials of each pair and setting the root sums to $1$ and root products to $-b_i$ gives degree at most $\lfloor j/2\rfloor$ in each $b_i$. Thus the total degree is at most $8-j+3\lfloor j/2\rfloor\le 12$. The result remains nonzero in every characteristic by monicity. Arbitrary polynomial-size ROABPs and unrestricted bounded-depth formulas already include such a fixed four-variable relation.

This answers the hitting-set question for bounded quadratic degree and proves a universal obstruction for natural larger classes. The fixed relation can have zero value at the all-zero equation vector, so its existence alone does not yield a geometric IPS certificate. [Grochow–Saxena–Shpilka, Open Question 3](https://arxiv.org/html/1701.01717#S4.SS2)
