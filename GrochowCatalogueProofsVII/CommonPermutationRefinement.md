# Minimum common refinements of explicit permutation actions

## GP-0497

Let two nonempty finite $G$-sets be given by the permutations of the same supplied generators. A common refinement is a $G$-set with surjective equivariant maps onto both. When the two actions are jointly faithful, a smallest faithful common refinement and its two maps can be computed in deterministic polynomial time, without expanding $G$. This includes the case where just one input action is faithful. In contrast, the decision version with three jointly faithful inputs is NP-complete even for three actions of an elementary abelian group of rank three, every input orbit having the same prime size.

### Two input actions

Write the orbit sets as $A_1,\ldots,A_s$ and $B_1,\ldots,B_t$. For each pair $(i,j)$ find the smallest orbit size $w_{ij}$ in the diagonal product action on $A_i\times B_j$ and retain that orbit. This is a connected-component computation in the generator action on the product, of total size $|A||B|$.

Every orbit of a common refinement projects onto exactly one orbit on each side. Its image in $A_i\times B_j$ is transitive, so that source orbit has size at least $w_{ij}$. Surjectivity means the selected pairs cover every input orbit index. Conversely for any edge cover in the complete bipartite graph on the orbit indices, take the disjoint union of the retained product orbits and use coordinate projections. It is a common refinement of size exactly the total edge weight. This action is faithful because its kernel is contained in the kernel of each input action, and their intersection is trivial.

The minimum weighted edge cover is computable by an integral minimum-cost circulation. Put an arc from a new source to each left vertex and from each right vertex to a new sink with lower bound one, one capacity-one arc of cost $w_{ij}$ for each pair, and a return arc from sink to source. Give the remaining arcs cost zero and sufficient capacity. The integral feasible flows are the edge covers. The chosen action never has more than $|A||B|$ points, so the witness has polynomial size.

### Three input actions

Reduce from strongly NP-complete Numerical Three-Dimensional Matching. Its three lists have length $h$ and entries $a_i,b_j,c_k$, and a triple is allowed when $a_i+b_j+c_k=T$. On the strongly NP-hard family all numbers are polynomially bounded in the list length. Choose a prime $p$ greater than $T$ plus the sum of the three maximum entries, by Bertrand's postulate and a polynomial search. Use $G=\mathbb F_p^3$ and create one orbit $\mathbb F_p$ for each list entry. The three types of orbits are translations controlled by linear functionals with rows
$$
(1,0,a_i),\qquad (0,1,b_j),\qquad (1,1,T-c_k).
$$
The translation permutations for the three standard generators can be written in polynomial time. Any pair from different lists is independent. A triple of rows has rank two exactly for an allowed numerical triple, by computing the determinant and using the bound on $p$. Otherwise it has rank three. The combined actions are faithful precisely when all displayed rows span $\mathbb F_p^3$. If the rank is only two, every triple is allowed and the original instance is a yes-instance. In that branch output a fixed jointly faithful yes-instance, for example over $\mathbb F_3$ with two rows of each type and third coordinates respectively $(0,1),(0,0),(0,1)$.

The orbit of a point in a triple product has size $p^2$ for an allowed triple and $p^3$ otherwise, since the image of its translation map has that cardinality. As in the two-action argument, any refinement can be replaced by a disjoint union of its image orbits in the triple product. At least $h$ orbits are needed to cover one entire list. The budget $hp^2$ therefore forces exactly $h$ of the cheaper orbits, and each list index must occur exactly once. This is precisely a numerical matching, which conversely realizes the budget. Joint faithfulness again ensures a faithful witness. For three jointly faithful inputs, the triple product and its orbit list have polynomial size, so a chosen cover is a polynomial-size certificate. [Numerical Three-Dimensional Matching, Garey–Johnson SP16](https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf)
