# Canonical reweighting of valuated matroids and exact projective transport

A valuated matroid on $E$ assigns a rational weight $w(B)$ to each basis of an ordinary matroid $M$. Use the convention that smaller weights are preferred. Changing the weight by
$$
 w(B)\longmapsto w(B)+u(B)+c,\qquad u(B)=\sum_{i\in B}u_i,
 \tag{1}
$$
defines projective equivalence of valuations. Permutations of $E$ act on the entire presentation. We construct a canonical normalization for (1) which commutes with every permutation of $E$, without selecting a basis canonically. Its inputs are a rank oracle for $M$ and an oracle returning a basis minimizing $w(B)-z(B)$, with its unshifted weight, for any rational price vector $z$. All finite weights are assumed to have a uniform polynomial bit bound. [Dress–Wenzel, valuated matroids](https://www.sciencedirect.com/science/article/pii/000187089290028J)

**Theorem.** In deterministic polynomial oracle and bit complexity one can compute $a\in\mathbb Q^E$ and $b\in\mathbb Q$ such that the normalized function
$$
 \widehat w(B)=w(B)-a(B)-b
 \tag{2}
$$
is nonnegative, attains zero, and depends only on the projective class of $w$. This function is equivariant under relabeling and is complete for projective equivalence on a common labelled matroid. It is represented by the original oracle and two rational shifts. For tropical maximal minors of an explicit rectangular weight matrix, the same construction uses only polynomial-size linear programs and bipartite matching data.

For full row rank matrices over $\mathbb F_2(t)$ whose nonzero maximal minors are supported on a supplied finite list of polynomial primes, the underlying column matroids and simultaneous normalized functions at those primes are complete for exact projective linear equivalence up to a common permutation of the columns. A supplied permutation can be tested in polynomial time, with an exact linear and diagonal transporter reconstructed when it passes. When the normalized data agree, the same construction also gives a leading-coefficient transporter at a single place with residue field $\mathbb F_2$ for general matrices.

## 1. A rational, equivariant interior demand

Write $P$ for the matroid base polytope, and $C$ for a connected component of $M$. Its affine hull has equations $x(C)=r(C)$ for every component. This can be seen from the fundamental exchange graph of an arbitrary basis $B_0$, joining $i\in B_0$ to $j\notin B_0$ whenever $B_0-i+j$ is a basis. The edges are in common circuits. In the reverse direction, each graph component is spanned by its intersection with $B_0$, since every fundamental circuit stays inside one graph component. Their ranks sum to $r(E)$, so these are direct-sum components. Exchange vectors along their edges span all directions whose sums on the components are zero. The graph and the ranks can be recovered by polynomially many rank queries.

Let $n=|E|>0$ and $\delta=1/(2(n+1))$. In the rank inequality description of $P$, tighten $x(S)\le r(S)$ to
$$
 x(S)\le r(S)-\delta
 \tag{3}
$$
for each subset $S$ which splits at least one matroid component. Such inequalities are exactly those whose left side is nonconstant on $P$. The average of an affinely spanning set of at most $n+1$ base vertices satisfies all tightened inequalities: for each nonconstant one some vertex in that set has integral slack at least one. Thus the tightened polytope is nonempty and lies in the relative interior of $P$. It is also bounded by the original rank inequalities. To separate (3), minimize $r(S)-x(S)$ for each pair $i,j$ in a common component, forcing $i\in S$, $j\notin S$. Each constrained problem is ordinary submodular function minimization on the remaining elements. The component equations and coordinate box can be checked directly.

Use the following unique selector for a nonempty compact rational polytope. First maximize the smallest coordinate by a linear program with an extra threshold variable. Retain the optimal face in the extended program, or equivalently restrict all coordinates to be at least the optimal threshold. Among the active coordinates, find those forced to equal the threshold by maximizing each separately on this restricted polytope. At least one is forced, since averaging strictly improving witnesses for every active coordinate otherwise improves the threshold. Freeze all the forced coordinates and repeat with the others. After at most $n$ rounds the surviving vector is unique, and the construction commutes with all coordinate permutations. Apply it to the tightened polytope to obtain $p$. For the empty ground set normalization is immediate. [Edmonds, matroid polyhedra](https://doi.org/10.1007/3-540-36478-1_2) · [Iwata–Fleischer–Fujishige, submodular minimization](https://arxiv.org/abs/math/0004089) · [Fujishige, lexicographically optimal bases](https://doi.org/10.1287/moor.5.2.186)

The exact linear programs here use rational separation and optimization. The selector adds only coordinate bounds and equalities using the new threshold. At each round a basic solution has polynomial determinant bit bound for the constraint normals. Clearing the original right-side denominators for its at most $n+1$ active inequalities and the existing threshold denominators bounds the new denominator by a previous common denominator times an integer of polynomial bit size. Over at most $n$ rounds this gives polynomial bit complexity for the exact thresholds. The same argument applies to the selector below on the price polytope. [Grötschel–Lovász–Schrijver, rational polyhedra](https://doi.org/10.1007/978-3-642-78240-4)

## 2. Canonical prices and completeness

Put $L=\{z:z(C)=0\ \text{for every component }C\}$, and let
$$
 g(p)=\min\Big\{\sum_B \lambda_B w(B):
          \lambda_B\ge0,\ \sum_B\lambda_B=1,\
          \sum_B\lambda_B{\bf 1}_B=p\Big\}.
$$
Compute $g(p)$ by the dual program maximizing $s+z\cdot p$ subject to $z\in L$ and $s+z(B)\le w(B)$ for all bases. Taking $z\in L$ loses no dual solutions modulo the intercept, because $z$ constant on each component has the same pairing with every base vertex and with $p$. Separation is a priced minimum-basis query. The dual is feasible and achieves the finite primal optimum by linear programming duality. In the component-zero space its feasible polyhedron contains no line, since the base differences span $L$. A polynomial bit bound on its vertices follows from the constraint coefficients and the uniform weight bit bound, so a bounding box of polynomial encoding can be imposed when invoking exact optimization.

Consider the polytope of maximizing prices
$$
 Q_w=\{z\in L\colon z\cdot({\bf 1}_B-p)\le w(B)-g(p)\ \text{for every basis }B\}.
 \tag{4}
$$
It is nonempty by the dual description. A recession direction $v\in L$ would satisfy $v\cdot(x-p)\le0$ for every $x\in P$. Since $p$ is relatively interior, this forces $v=0$. Thus $Q_w$ is compact. Its separation oracle again uses a priced minimum-basis query.

For each coordinate take the midpoint of its minimum and maximum on $Q_w$, and project the vector of midpoints to $L$, subtracting the mean within every component. Call this vector $m_w$. Apply the unique selector of Section 1 to $Q_w-m_w$, and add back $m_w$ to obtain $a\in Q_w$. Set $b=g(p)-a\cdot p$. The feasible price condition gives nonnegativity in (2), and an attaining convex combination in the definition of $g(p)$ has average normalized weight zero, so some basis attains zero.

Under the change (1), the value $g(p)$ shifts by $u\cdot p+c$. Since every ${\bf 1}_B-p$ lies in $L$, $Q_w$ translates by the projection $u_L$ of $u$ to $L$. The coordinate midpoint vector translates by that same amount. The centered polytope is unchanged, so $a$ shifts by $u_L$ and $b$ shifts by $(u-u_L)\cdot p+c$. This makes (2) invariant, since $u-u_L$ is constant within each component. Every ingredient is permutation-equivariant. Conversely equality of the normalized functions immediately expresses the original difference in the form (1). This proves the canonical normalization. All steps use polynomially many exact linear programs of polynomial dimension, each with the stated polynomial separation.

## 3. Explicit flow models for tropical determinants

Let a rectangular graph have $r$ left vertices, right set $E$, and rational edge costs $c_{ij}$, with some matching saturating the left vertices. The valuation $w(B)$ on a right set of $r$ vertices is the minimum matching cost between the left and $B$, with weight $+\infty$ for unmatched sets. These are tropical maximal minors. Its priced minimum-basis oracle is a min-cost matching saturating the left side at edge costs $c_{ij}-z_j$. Its underlying rank is maximum matching cardinality into the queried right set. [Fink–Rincón, tropical Stiefel map](https://arxiv.org/abs/1305.6329) · [Fink–Olarte, transversal valuated matroids](https://doi.org/10.1112/jlms.12505)

Every optimization used above then has a compact linear description. To see this for (3), Hall's deficiency formula gives
$$
 r(S)=\min_{T\subseteq S}(|S\setminus T|+|N(T)|)
$$
where $N(T)$ denotes the left neighbors. To minimize $r(S)-x(S)$ with $i\in S,j\notin S$, one can take $S=T\cup\{i\}$, since all optional $S\setminus T$ terms $1-x_e$ are nonnegative. The minimum becomes
$$
 1-x_i+\min_{T\subseteq E\setminus\{j\}}
          \left(|N(T)|-\sum_{e\in T} c_e'\right),\qquad
 c_i'=1,\quad c_e'=x_e\ \ (e\ne i).
$$
The inner expression plus $\sum_{e\ne j}c'_e$ is a minimum cut: put source arcs of capacity $c'_e$ to right vertices other than $j$, capacity $n+r+1$ from each such right vertex to its left neighbors, and unit capacity from each left vertex to the sink. By max-flow min-cut, the required lower bound $\delta$ is exactly the existence of a flow of value at least $x(E\setminus\{j\})+\delta$. Introducing separate flow variables for each ordered pair in a common component gives a polynomial-size linear formulation of the tightened base polytope.

For $g(p)$, minimize flow cost with left sums one and right sums $p$. The polytope with left sums one and right sums at most one is the convex hull of left-saturating matchings by bipartite matching integrality. Constraining its right sums to $p$ therefore gives precisely the convex combinations used to define $g(p)$. For (4), dualize the priced matching problem. Use unrestricted left potentials $\alpha_i$, nonpositive right potentials $\beta_j$, and inequalities
$$
 \alpha_i+\beta_j\le c_{ij}-z_j\quad (ij\text{ an edge}),\qquad
 \sum_i\alpha_i+\sum_j\beta_j=g(p)-z\cdot p.
$$
This gives a polynomial-size extended description of $Q_w$, by matching linear programming duality. The equivariant selectors optimize only the displayed demand or price coordinates, so the auxiliary network variables require no canonical choice.

## 4. Exact transporter from a finite set of valuations

Let $K=\mathbb F_2(t)$, and let $\mathcal S$ be a supplied finite list of monic irreducible polynomials in $\mathbb F_2[t]$. Assume every nonzero full-size minor of both full row rank matrices is in the multiplicative subgroup generated by $\mathcal S$. Negative exponents are allowed. For each $f\in\mathcal S$, apply the theorem to the weight $w_f(B)=\operatorname{ord}_f(\det M_B)$ on the underlying column matroid. Relabel one configuration by the proposed permutation before comparing. Row multiplication by an invertible matrix adds the valuation of its determinant, and diagonal column multiplication adds the sum of the corresponding column valuations. This proves invariance of every $\widehat w_f$.

For the converse, compare normalized values for a common basis $B_0$ and all its single exchanges, including which exchanges are bases. The latter determine the component partition. For each $f$, let $u_i$ be the difference of the two computed prices from (2). Equality of the normalized values, together with integral original weights, makes $u_i-u_j$ integral along every edge of the fundamental exchange graph. Thus subtracting $u_i$ at a chosen reference vertex per component gives an integral vector $v_f$ without changing any of these differences. There is then an integral constant $c_f$ such that
$$
  w'_f(B)-w_f(B)=v_f(B)+c_f
$$
for the tested bases, using $B_0$ to fix the intercept. Multiply column $i$ of the source matrix by $\prod_{f\in\mathcal S}f^{v_{f,i}}$. The resulting matrix and the target now have the same ratios of their $B_0-i+j$ and $B_0$ minors. Indeed the ratios have equal valuations at all listed primes, no valuations elsewhere, and the only nonzero constant in $\mathbb F_2$ is one. Zero exchange minors agree as well. Cramer's rule says their matrices after normalization by their $B_0$ submatrices agree entrywise. Thus the inverse of one basis normalization followed by the other yields the required invertible row map. Testing all basis values is unnecessary for a supplied permutation. Conversely the reconstructed transporter implies equality of the full normalized functions. A missing common basis or any tested discrepancy rejects that permutation.

The min-priced-basis oracle is also available directly on a matrix at any polynomial prime, even when matching costs do not give the actual minor valuations because of cancellation. Select an entry of minimum value after subtracting its column price, use it as a pivot, and perform row elimination below it. Recurse on the remaining rows and columns with their unchanged prices. To prove correctness, regard the priced columns as scaled by powers of a local uniformizer in a valued extension clearing the price denominators. All ratios used to clear the pivot column and row have nonnegative valuation. These row and column operations are invertible over the valuation ring, so they preserve the minimum valuation of maximal minors, by Cauchy–Binet in both directions. After clearing the pivot row, the minimum is the pivot valuation plus that of the residual matrix. A minor using the selected pivot column has the same determinant before and after the pivot-row column operations. Moreover, row elimination on the unscaled entries gives the same residual entries up to their indicated column scales. Thus the algorithm needs only ordinary row elimination and priced valuation comparisons. For explicit dense polynomial numerators and denominators over $\mathbb F_2$, it runs in polynomial bit time. Fraction-free elimination after clearing denominators bounds intermediate degrees by degrees of minors, and divisibility by listed polynomials is tested by Euclidean division. Integer corrections can be chosen by following component exchange paths, so their magnitudes are bounded by $n$ times the largest absolute exchange difference. This also bounds the constructed diagonal degrees polynomially in the dense presentation.

At a single place with residue field $\mathbb F_2$, the same proof through the basis-exchange test gives equality of valuations of the pivot-normalized entries after reweighting, even without the prime-support hypothesis. Their leading coefficients then agree, and each nonzero entry differs from its peer by an error of strictly higher valuation. The full exact equivalence assertion uses the multi-place hypothesis. The search for an unmarked column permutation is a separate isomorphism problem. The normalized functions give a complete invariant *up to that permutation*, rather than canonically numbering its columns.

## 5. Controls and provenance

On the uniform rank-two matroid on four elements, give the pair $14$ weight one and all others zero. This is realized by a two-row assignment with first-row prices zero and second-row prices one at $1,4$, zero at $2,3$. Here $p=(1/2,1/2,1/2,1/2)$ and $g(p)=0$. The price polytope consists of $(x,-x,-x,x)$ for $0\le x\le1/2$, giving $a=(1,-1,-1,1)/4$. The normalized weights are $1/2$ at $14,23$ and zero elsewhere. Adding column prices $(2,-1,3,0)$ and constant $5$ shifts $a$ by $(1,-2,2,-1)$, shifts $g(p)$ to $7$, and preserves these values.

For the arithmetic branch use columns $(1,0),(0,1),(1,1),(1,t^d)$ with $d=1,2$. Every nonzero maximal minor is supported on $\{t,t+1\}$, with exceptional power $t^d$ at $14$ and $(t+1)^d$ at $34$. At $t$ the preceding control scales by $d$, so the configurations have distinct normalized weights under every permutation. Replacing $t$ by $t+t^2$ in the $d=1$ configuration instead preserves all its valuations at $t$, but changes the fourth projective point when the first three are marked. The leading-term result applies and illustrates the extra information needed for exact transport.

An exhaustive finite arithmetic control checked the forced cut identity on all 221 bipartite support graphs on two left and four right vertices admitting a left-saturating matching, all 12 ordered pairs of distinct right indices, and four demand vectors with quarter coordinates, giving 10,608 comparisons. A second control enumerated $2\times3$ matrices with entries $0,1,t,1+t$, retaining full row rank, and compared priced pivot choices to enumeration at both primes $t$ and $t+1$ and three price vectors. All 23,184 queries agreed.

The projective equivalence relation, subdivisions of valuated matroids, and tropical matching presentations have established literatures. The result here is an equivariant exact normalization from optimization oracles and its combination with a multiple-valuation transporter on prime-supported realizations. It provides a fixed-column projective transport step of the kind that appears when generator coordinates have already been extracted, while general tensor isomorphism allows the full independent linear changes in all modes. The proof is in prose and the literature search did not establish publication priority. [Dress–Wenzel](https://www.sciencedirect.com/science/article/pii/000187089290028J) · [Fink–Olarte](https://doi.org/10.1112/jlms.12505) · [Grochow–Qiao, isomorphism reductions](https://arxiv.org/abs/1907.00309)
