# Counting optimal transitive stabilizers in compact class-two groups

## GP-0393

For every fixed odd prime $p$, counting conjugacy classes of maximum-order core-free subgroups in a permutation-generator class-two exponent-$p$ group is $\#\mathsf P$-hard under polynomial-time counting reductions. The reduction produces groups with a polynomial-degree faithful permutation presentation and an explicit description of a class on which the optimal faithful **transitive** action degree and a minimum-index core-free stabilizer are computed by a direct polynomial-time formula.

### A bipartite graph with a designated matching

Let $P$ be a finite poset. Counting its order ideals is $\#\mathsf P$-hard even for bipartite height-two posets: for a bipartite graph take the height-two poset with exactly its left-right adjacencies as strict relations. Its antichains are the independent sets, and taking maximal elements is a bijection between ideals and antichains. Exact bipartite independent-set counting is $\#\mathsf P$-complete. [Provan–Ball, counting antichains](https://doi.org/10.1137/0212053)

Replace each element $i$ of $P$ by two labels $i,i'$. Add directed arcs in both directions between twins, and add the arc $i\to j$ for each strict order relation $i<j$ between original labels. For each label $k$ make a matched pair of vertices $L_k,R_k$ and join them by an undirected edge. For each directed arc $k\to l$ add the edge $L_kR_l$. This is a simple bipartite graph $\Gamma$ with a displayed perfect matching. Write $r$ for the number of pairs and $z$ for the number of graph edges.

Let $V=\mathbb F_p^{2r}$ have the graph vertices as basis, let $Z=\mathbb F_p^z$ have the edges as basis, and define an alternating map $b:V\times V\to Z$ by the determinant at the endpoints of each edge. Thus the component for $L_iR_j$ is $v_{L_i}u_{R_j}-v_{R_j}u_{L_i}$. The perfect matching forces the common radical of $b$ to be zero, since each matched coordinate is tested against its partner. The values of $b$ span $Z$ by testing endpoint basis pairs.

### Maximum isotropic subspaces

If $U\le V$ is isotropic for $b$, its projection onto each of the $r$ matched coordinate planes has dimension at most one. Thus $\dim U\le r$. Equality holds exactly when $U$ is a direct sum of one line in every matched plane, with the resulting sum isotropic on all remaining edges. A chosen line either uses only its left coordinate, only its right coordinate, or both. For an arc $i\to j$ with $i\ne j$, the independent summands make the edge condition equivalent to forbidding simultaneous use of the left coordinate at $i$ and the right coordinate at $j$.

The bidirectional arcs between each pair of twins exclude a line using both coordinates, since then the twin would be forbidden to use either one. They also force the two twins to choose the same one-sided type. Every remaining arc $i\to j$ then asserts that choosing left at $i$ forces left at $j$. The left choices are precisely the order filters, whose complements are ideals. Coordinate lines are unique once the type is specified. Therefore the number of maximum isotropic subspaces is the ideal count. One such subspace is explicitly the span of all left vertices. In addition every such $U$ satisfies $U^\perp=U$ for the pairing $b$: the matching edge equations alone force a vector in $U^\perp$ to project to the chosen line in every matched plane, and isotropy gives reverse inclusion.

### Group, faithful input, and exact count

On $G=V\times Z$ use the law
$$
(v,x)(u,y)=(v+u,x+y+\tfrac12 b(v,u)).
$$
It is associative by bilinearity, has exponent $p$, and has commutator map $b$. Its center is $Z$ by the common radical calculation. As every nontrivial normal subgroup of a finite $p$-group meets its center, a subgroup is core-free if and only if it has trivial intersection with $Z$. Its projection to $V$ is an isomorphism to an isotropic subspace, since all its commutators lie in its intersection with the center. Over such a subspace $U$ this group law reduces to direct addition. The possible subgroups projecting onto $U$ are exactly the graphs of linear maps $U\to Z$.

The maximum core-free subgroup order is therefore $p^r$, and the minimum faithful transitive degree is $|G|/p^r=p^{r+z}$, by the coset-action characterization. Both this binary degree and a generating set for a maximum core-free subgroup can be produced in polynomial time by the left-vertex choice. Conjugation fixes the projection $U$ and acts on its maps by adding the restrictions $b(v,-)|_U$, for $v\in V$. The linear map $V\to\operatorname{Hom}(U,Z)$ has kernel $U^\perp=U$, so each orbit has $p^r$ members. Consequently the requested count is
$$
p^{r(z-1)}\cdot\#\{\text{order ideals of }P\}.
$$
The displayed factor is known and has polynomial bit length.

For compact input, project $G$ onto the order-$p^3$ Heisenberg group for each graph edge, using its two endpoint coordinates and its edge central coordinate, in the same half-alternating law. The combined map is injective because every vertex lies on its matching edge and all central coordinates occur. Give each edge component its regular action on $p^3$ points in a separate block. Compute every coordinate-basis group generator on these blocks by the explicit group law. The input permutation degree is $zp^3$ and its construction takes polynomial time for fixed $p$. The reduction can expose the matching and graph certificate along with its action. The formula for the optimum does not require counting maximum subspaces.

This extends the alternating-coordinate class-two constructions in the earlier packets and separates the optimization value from counting optimal conjugacy classes on the same explicit input family. [Earlier alternating coordinates and central gluing](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/GrochowCatalogueProofsIII/MinimalCentralAmalgam.md) · [Earlier faithful permutation encoding](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/GrochowCatalogueProofsIV/FaithfulLinearDimensions.md)
