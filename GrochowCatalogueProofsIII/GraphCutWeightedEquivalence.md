# Unweighted and mixed-weight maximum-cut conjectures are equivalent

**GP-0110 and GP-0118, exact relationship.** Over any fixed coefficient field, maximum-cut equality for the asymptotic rank of all noncomplete nonbipartite simple graph tensors with edge dimension two implies the mixed-dimension equality on the same class, and conversely. Here an edge of dimension d carries weight log₂d. The argument concerns the universal conjectures. It gives a sufficient reduction from the weighted question to the unweighted one. This is a written proof.

Use Γ(W) for Zhou's positively homogeneous continuous graph exponent on a nonnegative edge-weight matrix W. At an integer vector of weights w_{ij}, it is log₂ of the asymptotic rank of the graph tensor with edge dimension 2^{w_{ij}}. The weighted flattening bound is MaxCut(W)≤Γ(W). Both facts hold over every field. [Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Bounds](https://arxiv.org/html/2610.34273v3).

Fix any nonbipartite support with n vertices and nonnegative weights W. By homogeneity rescale so its largest weight is one. For each t, replace every vertex i by a class C_i of t vertices and choose each possible edge between C_i and C_j independently with probability w_{ij}. There are no edges inside a class. Let H_t be the resulting unweighted simple graph and let m_{ij}(t) count the edges between these two classes.

Let S be any cut of the expanded graph and put x_i=|S∩C_i|/t. Its expected size is
```
t² Σ_{i<j} w_{ij}(x_i(1−x_j)+(1−x_i)x_j).
```
The summand expression is multi-affine in x. Its maximum on the cube [0,1]^n occurs at a cube vertex, by moving one coordinate to an endpoint at a time without decreasing the value. Its maximum is thus MaxCut(W). By Hoeffding's inequality, the chance that the size of one fixed cut differs from its expectation by more than t^(7/4) is at most 2 exp(−c_n t^(3/2)), since it sums at most n²t² independent zero-one variables. The bound survives a union over at most 2^{nt} cuts with probability tending to one. Concentration of the individual block edge counts also gives m_{ij}(t)/t²→w_{ij}. Further, one odd cycle of positive weights in the support yields t independent chances of an odd cycle in H_t, by using the corresponding numbered vertex of each of its classes. Each chance has fixed positive probability, so H_t is nonbipartite with probability tending to one. It is noncomplete for t≥2. Therefore there is a deterministic sequence of choices with these properties and MaxCut(H_t)/t²≤MaxCut(W)+o(1).

Group the tensor legs in each class C_i into one leg. Every rank-one term across the original legs remains rank one across the grouped legs. The grouped tensor is the weighted graph tensor having dimensions 2^{m_{ij}(t)}, since a product of independent Bell pairs on the edges of a class pair is the Bell pair on the tensor product of their local spaces. Applying the proposed unweighted equality to H_t gives
```
Γ(m(t)/t²) ≤ (log₂ asymptotic-rank(GT₂(H_t)))/t²
              = MaxCut(H_t)/t²
              ≤ MaxCut(W)+o(1).
```
Take the limit by continuity. The flattening bound gives the other inequality. If a convention requires the unweighted inputs to be connected, one may restrict to connected weighted support and add O(nt) edges between classes to connect the realized blowup using an allowable connected support graph. Such changes have vanishing normalized effect on cuts and counts. For bipartite support equality is already known by the flattening bound and the explicit product decomposition on the edges.

For the converse, if the weighted conjecture allows equal dimensions, take every dimension equal to two. If it requires some differing dimensions, use dimensions 2^m on all edges except one edge of dimension 2^m+1. After division of weights by m the weight vectors tend to the all-one support vector. Continuity and positive homogeneity give the unweighted equality.

A complete nonbipartite graph can also be included in the universal unweighted formulation by first taking its independent blowup with all classes of size two. Grouping its legs recovers each original Bell edge with multiplicity four. Its maximum cut is exactly four times the original one by the same multi-affine optimization, so unweighted equality on the noncomplete blowup forces equality on the original graph. In particular the universal statements include the exponent-two conjecture for square matrix multiplication through the triangle.
