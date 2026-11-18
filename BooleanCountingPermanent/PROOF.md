# Monotone permanent projections cannot count general perfect matchings or Hamiltonian cycles

**Theorem.** If a monotone affine projection of the $m\times m$ permanent agrees on every Boolean input with the general perfect-matching count or the directed Hamiltonian-cycle count on $n$ vertices, then $m=2^{\Omega(n)}$. The substitutions may use arbitrary nonnegative real coefficients. This answers both clauses of Grochow's Open Question 5.2. [Original question](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=9)

## Support-polytope theorem

Let $H$ be a bipartite multigraph with $r$ vertices on each side, $s$ edges, and a perfect matching. Label each edge by one element of $\Lambda$ or leave it unlabeled. For a perfect matching $M$ write $S(M)$ for its set of distinct labels. Suppose sets $B\subseteq\Lambda$ cover $\Lambda$, every $S(M)$ meets each $B$ in exactly one label, and at least three possible labels of each $B$ occur as $M$ varies. Then

$$
\operatorname{xc}\bigl(\operatorname{conv}\{\mathbf1_{S(M)}:M\text{ a perfect matching of }H\}\bigr)\le rs.
$$

Here extension complexity counts inequalities, with affine equations free.

### 1. Split into pieces where disjoint edges coexist

Delete all edges outside every perfect matching. The remaining connected components are balanced, and perfect matchings in them can be chosen independently. All occurrences from any one set $B$ lie in one component. If there were occurrences in two components, every pair of their labels would have to agree by independence and the unique-label condition. All labels in $B$ that occur anywhere would then be equal.

In a connected piece with bipartition $(U,V)$ and $|U|=|V|=m$, every nonempty proper $A\subset U$ satisfies $|N(A)|\ge |A|+1$. Hall's theorem gives the weak inequality. Equality $|N(A)|=|A|$ would force all vertices of $N(A)$ to match with $A$, so no edge from $U\setminus A$ to $N(A)$ could belong to a perfect matching. Since each retained edge belongs to one, this would disconnect the piece.

If two disjoint edges cannot occur together, delete their endpoints and apply Hall's theorem. Some nonempty $A$ of the undeleted left vertices has $|N(A)|\le |A|+1$ in the original piece. Hence $|N(A)|=|A|+1$ and $|A|\le m-2$. Every perfect matching crosses the cut at $A\cup N(A)$ exactly once. The vertices of $A$ all match inside the shore, leaving exactly one vertex of $N(A)$ to match outside. Each shore has at least three vertices.

Split the piece by contracting the opposite shore to a distinguished vertex on each side. Retain every crossing edge as a separate edge, with the same identity in both pieces. Both new pieces are connected and bipartite, and each edge still belongs to a perfect matching by restriction of an old matching. The two local perfect matchings glue exactly when they choose the same crossing edge. Recurse until every two disjoint edges in each piece can occur together.

The terminal pieces are nodes of a tree for each connected component. Each split replaces a node with two adjacent nodes. Distinct links incident to a piece have distinct distinguished vertices. Attach each old link to the new piece retaining its vertex and the identities of its incident edges. The new link has one new distinguished vertex at each end. This inductive construction shows that tuples of local matchings glue exactly when common crossing-edge choices agree on every link. In particular, conditional on a link's chosen edge, its two sides can be matched independently. Conditional on a node's local matching, each of its incident branches can be matched independently. All local matchings extend because every crossing edge belongs to a matching on the other side, and the link graph is a tree.

An original edge has at least one copy in the terminal pieces. Assign its original label to just one copy. All other copies are unlabeled. The split gluing condition proves inductively that the assigned copy is selected exactly when the original edge is selected.

### 2. A local readout for each label set

Fix one set $B$ and its component tree. At a node $p$, associate to each edge $e$ a set $S_e\subseteq B$. Include the assigned label of $e$ if it belongs to $B$. At each distinguished endpoint of $e$, also include every $B$-label that can occur in the branch at that endpoint conditional on the common crossing edge being $e$.

For a local matching $J$, the possible values of its global $B$-label are exactly $\bigcup_{e\in J}S_e$, by independent extension on the branches. This union is always nonempty. Over the whole piece the union contains all the possible labels, hence at least three. If disjoint local edges $e,f$ have nonempty sets, every label from $S_e$ must equal every label from $S_f$. A local matching can contain both, and their marked endpoints lead to distinct branches. The two label occurrences can therefore be realized simultaneously.

Group parallel edges into positions, one for each endpoint pair. The label set of a position is the union of the $S_e$ on its parallel edges. Call a position active when its label set is nonempty. Consider the bipartite incidence graph of active positions and labels, with membership as adjacency.

If there is a matching of size three in that incidence graph, take the three positions and their distinct labels. The positions pairwise intersect, by the disjoint-edge argument. Three distinct pairwise intersecting edges in a bipartite simple graph share a vertex $u$. Any position off $u$ is disjoint from at least two of them, whose labels differ. Such a position cannot be active. Thus all active positions are incident to $u$.

Otherwise König's theorem gives a vertex cover of size at most two in the incidence graph. Two labels cannot cover it. If the cover uses only positions, there are at most two active positions, and they must intersect if there are two. Disjointness would force their entire union of labels to be a singleton. Thus again all active positions share a vertex. The remaining case has one position $a$ and one label $\lambda_0$ in the cover. Every other active position carries only $\lambda_0$. The position $a$ carries a different label, so it meets every other active position.

There are therefore two local rules. In the common-vertex case the possible labels are $S_e$ for the edge chosen at that vertex. No other active edge can be chosen. In the one-position case the possible labels are $S_e$ if an edge at $a$ is chosen, and $\{\lambda_0\}$ if no edge at $a$ is chosen. Choosing an edge at $a$ excludes every other active position. Each output set is nonempty by the global unique-label property.

Write $b_\lambda$ for the unit label vector in $\mathbb R^B$. Define $b(S)$ to be $b_\lambda$ if $S=\{\lambda\}$ and zero otherwise. Let $g_p(J)$ be the labeled unit vector when $J$ determines the global label, and zero if variation remains. In the common-vertex case its affine formula is $\sum_{e\ni u} x_e b(S_e)$. In the one-position case it is

$$
\left(1-\sum_{e\text{ at }a}x_e\right)b_{\lambda_0}
+\sum_{e\text{ at }a}x_e b(S_e),
$$

where $x_e$ is the local edge incidence variable.

### 3. Combine the local readouts

For a link $l$ and its crossing-edge state $e$, let $h_l(e)$ be the unit label vector if that state fixes the global $B$-label, or zero otherwise. This is affine in the incident edge variables by summing the vector for each state weighted by the incidence variable of that state.

Fix a compatible tuple of matchings, and call a link fixed when its chosen state fixes the label. For a nonfixed link, exactly one of its two sides can contain any occurrences from $B$, conditional on its chosen state. Indeed, if both sides could contribute, the independent choices on the two sides would force their sets of possible labels to be the same singleton. Every global matching has a label, so the state would fix it. Direct each nonfixed link toward its contributing side.

Each node has at most one outgoing link. Two outgoing links would force all label occurrences in the fixed tuple to lie in two disjoint branches, but there is at least one occurrence. A node determines the label from its local matching exactly when its outdegree is zero. An outgoing link leaves variation in that branch even after the node's matching is fixed. Conversely, if the local matching leaves variation, Step 2 gives a single selected active edge $e$ with $|S_e|\ge2$. A local assigned label is a singleton. If two branches at the endpoints of $e$ could contribute, independent completion would force both to offer only the same label. A local assigned label and a contributing branch likewise cannot offer distinct labels. Thus the variation is in a single branch connected by a nonfixed outgoing link.

The number of nodes with zero outdegree equals one plus the number of fixed links. Indeed, the number of nonfixed links is the sum of all outdegrees, and a tree has one fewer link than nodes. Every nonzero $g_p$ and $h_l$ is the unit vector of the actual global label $c$ in this tuple. Hence

$$
\sum_p g_p(J_p)-\sum_l h_l(e_l)=b_c.
$$

Run this formula for every $B$ in the cover. For each label read its coordinate from any chosen set $B$ containing it. These formulas define a single affine map from the local matching incidence variables to the global set indicators.

### 4. Formulation size

Put the local edge variables of each piece in its bipartite perfect matching polytope, using nonnegativity and degree-one equations. Equate the marginal coordinates of crossing-edge identities at the two ends of each link. This gives exactly the convex hull of compatible matching tuples. For the nontrivial inclusion, take a distribution of local matchings realizing the incidence marginals in each piece. Draw a root matching from its distribution and a child matching from its distribution conditional on the state chosen at the parent. The state marginals at the two ends agree, so the mixture over the possible states gives the child's original distribution. Induction through the tree yields the prescribed point as the marginals of a random compatible tuple. Do this independently for each original connected component.

If a component initially has $m$ left vertices, the recursion preserves the sum of $m_i-1$ over its pieces. Each nontrivial split produces two pieces with at least two left vertices. The number of terminal pieces is at most $m$ including the case $m=1$. Each piece has at most one copy of any edge identity. The total number of local edges is therefore at most $rs$ and each contributes only one nonnegativity inequality. All other constraints are equations. Step 3 gives the stated affine image and proves the support-polytope theorem.

## Applying the theorem to exact counting

Let a monotone affine projection substitute nonnegative affine forms in $K$ variables into the $m\times m$ permanent. Expand each form as its constant and single-variable terms. View each positive constant term as an unlabeled edge and each positive variable term as a labeled edge, assigning its coefficient as the weight. This produces a bipartite multigraph with at most $m^2(K+1)$ edges. The terms of the permanent now correspond to weighted perfect matchings. Its Boolean multilinearization replaces the monomial of a matching by the product on its distinct labels.

Two multilinear real polynomials agreeing on every Boolean input have identical coefficients, by Möbius inversion of subset sums. The coefficient of each label set in the multilinearization is the sum of strictly positive weights of the matchings with that label set. Thus equality of Boolean counts implies that the attainable label sets are exactly the monomial supports of the target.

For general perfect matchings on an even number $n\ge4$ of vertices, use a set $B$ of incident edge labels at each vertex. For the paper's directed Hamiltonian cycles on $n\ge4$ vertices, use the set of outgoing arc labels at each vertex. Every target support chooses exactly one label in each set, and at least three choices occur in each set as the target support varies. Unused variables, such as loop variables, have no occurrence in any perfect matching of the projected graph. The support-polytope theorem therefore gives an extended formulation with at most $m^3(K+1)$ inequalities for the respective general perfect matching or directed Hamiltonian-cycle polytope.

Rothvoß proves $2^{\Omega(n)}$ extension-complexity lower bounds for the general perfect matching and undirected traveling salesperson polytopes. The directed Hamiltonian-cycle polytope maps onto the undirected one by summing the two directions of every edge. Thus it has the same exponential lower bound. As $K=O(n^2)$, the affine projection requires $m=2^{\Omega(n)}$ in either case. This proves both clauses of Open Question 5.2. [Rothvoß, Theorem 1 and Corollary 2](https://arxiv.org/abs/1311.2369)

The proof only requires the full support of the Boolean multilinearization to equal the target support. For the separate Boolean decision question, equality of positive versus zero values fixes the inclusion-minimal supports and permits additional supersets. [Grochow, Questions 5.1 and 5.2](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=9)

As a corollary, every monotone arithmetic formula giving either exact count on Boolean inputs has size $2^{\Omega(n)}$. Grochow's Proposition 4.6 makes the formal polynomial of a size-$s$ monotone formula a monotone projection of $\operatorname{per}_{s+1}$. The projected polynomial still agrees on all Boolean inputs, so the theorem applies even if the formula's polynomial has repeated powers. [Grochow, Proposition 4.6](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=8)
