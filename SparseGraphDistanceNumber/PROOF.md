# Two bounds for the distance-number of sparse graphs

A drawing sends the vertices of a finite simple graph to distinct points of the plane. The open segment of each edge must contain no vertex. Edge crossings are allowed. The **distance-number** \(\operatorname{dn}(G)\) is the fewest distinct edge lengths among these drawings.

We prove two statements.

1. If \(G\) has a tree-partition of width at most \(w\) whose indexing forest has maximum degree at most \(D\), then
   \[
   \operatorname{dn}(G)\le \binom{w}{2}+Dw^2.
   \]
   In particular, for treewidth at most \(k\) and maximum degree at most \(\Delta\), where \(\Delta\ge 1\), set \(w=(k+1)(8\Delta-3)\). Then
   \[
   \operatorname{dn}(G)\le \binom{w}{2}+(4\Delta-1)w^2
   = O((k+1)^2\Delta^3).
   \]
   This proves [Bakhajian and Feldheim's Conjecture 1](https://arxiv.org/html/1907.13104v2#S6).
2. For every fixed nonnegative integer \(h\), every \(h\)-degenerate graph on \(n\ge 2\) vertices has
   \[
   \operatorname{dn}(G)=O_h(n/\sqrt{\log n}).
   \]
   This answers the question of Carmi, Dujmović, Morin and Wood about sublinear distance-number for graphs of bounded maximum degree. [Distinct Distances in Graph Drawings, Section 7](https://users.monash.edu.au/~davidwo/papers/CDMW-EJC08.pdf#page=19)

## 1. A fixed set of lengths for tree-partitions

A tree-partition is a partition of the vertex set into bags indexed by a forest, with each edge either within a bag or between adjacent bags. Its width is the maximum bag size. First take one component of the indexing forest, root it, and assign different labels from \(1,\ldots,D\) to the children of each node. Each node is identified by its word \(s=s_1\cdots s_m\) of child labels along the path from the root. Assign each vertex in a bag a different slot \(j\) in \(1,\ldots,w\).

Fix a transcendental complex number \(a\) on the unit circle. Let \(b_1,\ldots,b_D,c_1,\ldots,c_w\) be complex parameters. Place slot \(j\) at node \(s\) at the point
\[
Z_{s,j}=\sum_{r=1}^{m}a^{r-1}b_{s_r}+a^mc_j.
\]
Thus the child labelled \(i\) is placed by the isometry \(z\mapsto az+b_i\) in its parent's coordinate frame. The empty word denotes the root and its sum is zero. An edge within a bag has length \(\lvert c_\ell-c_j\rvert\). An edge from parent slot \(j\) to child slot \(\ell\) with child label \(i\) has length \(\lvert b_i+a c_\ell-c_j\rvert\). These are at most \(\binom{w}{2}+Dw^2\) lengths in total.

### Distinct vertices

Consider the positions as complex-linear forms in the parameters. Different slots have different slot coefficients. The same slot at different depths has different coefficients because the nonnegative powers of \(a\) are distinct. For distinct words of the same depth, at the first differing index at least one \(b_i\) has different coefficients as a polynomial in \(a\). Transcendence ensures these coefficients stay different after evaluation. Hence the forms of any two distinct vertices are different.

### No third vertex on an edge line

For distinct endpoint forms \(X,Y\) and third vertex form \(W\), the collinearity condition is the real polynomial equation
\[
\operatorname{Im}\big((W-X)\overline{(Y-X)}\big)=0.
\]
This polynomial is identically zero only if \(W-X=t(Y-X)\) as a linear form for some real \(t\). Indeed, if the two difference forms are independent over \(\mathbb C\), their joint image is \(\mathbb C^2\) and they attain the pair \(i,1\). If they are dependent, evaluate where \(Y-X=1\) to see that the constant of proportionality must be real.

Such a real relation among three distinct vertex forms would have coefficients \(1,-t,-(1-t)\) on \(W,Y,X\), all nonzero since the forms are distinct. If two or three different slots occur, some slot occurs exactly once, and its parameter has a nonzero coefficient in the relation. If all three slots are the same, the edge goes between parent and child. Its endpoint coefficients on that slot's parameter are distinct unit numbers \(a^m,a^{m+1}\). The third coefficient \(a^r\) lies on the same unit circle. The real affine line through \(a^m\) and \(a^{m+1}\) meets that circle in just those two points. Thus \(a^r=(1-t)a^m+ta^{m+1}\) forces \(t=0\) or \(1\), which would make two vertex forms equal. This rules out an identically zero collinearity polynomial.

Choose the real and imaginary parts of all \(b_i,c_j\) algebraically independent over the countable field \(\mathbb Q(\operatorname{Re}a,\operatorname{Im}a)\). Such a tuple exists by successively avoiding the algebraic closure of a countable field. This one choice avoids all collision equations and all edge-line collinearity equations. It works for all finite rooted trees with at most \(D\) children per node and all bags of size at most \(w\). Draw distinct components with the same parameters and translate their finite point sets into disjoint disks. Their edge segments lie inside their disks by convexity. This proves the first inequality and in fact gives one fixed set of lengths for each \(w,D\).

For the treewidth application, Theorem 2 of Distel, Kaul, Kaul and Wood supplies a tree-partition with width at most \((k+1)(8\Delta-3)\) and indexing-tree maximum degree at most \(4\Delta-1\). Applying the inequality gives the stated bound. Edgeless graphs have distance-number zero. The qualitative conclusion also follows from Wood's earlier \(O((k+1)\Delta)\) tree-partition-width bound, because a bag of size \(w\) has at most \(w\Delta\) neighboring bags in the forest of actual interbag adjacencies. [Distel et al., Theorem 2](https://arxiv.org/html/2604.05690v1#Thmtheorem2) · [Wood, On Tree-Partition-Width](https://arxiv.org/abs/math/0602507)

## 2. A square-grid drawing for bounded degeneracy

Let \(v_1,\ldots,v_n\) be an order in which each vertex has at most \(h\) earlier neighbors. Greedily color the vertices in this order with colors \(0,\ldots,h\). For \(h=0\), the graph is edgeless. Otherwise choose a prime \(p>32h+1\) and an integer \(m\ge \max\{\sqrt{2n},8ph\}\).

Assign color \(t\) the residue \(\rho_t=(t,t^2)\) in \(\mathbb F_p^2\). No three of these residues are collinear. A vertical line meets the parabola in at most one point and a nonvertical line meets it in at most two. Inside the grid \(\{0,\ldots,pm-1\}^2\) each color residue has exactly \(m^2\) candidate positions. We place the vertices in the original order, using a fresh candidate and imposing
\[
\gcd(|x_1-y_1|,|x_2-y_2|)<p
\]
for the position \(x\) under consideration and every already placed neighbor \(y\).

To bound the excluded positions for one neighbor, suppose the gcd is at least \(p\) and take \(q\) equal to the gcd. The residues of \(x\) and \(y\) modulo \(p\) are distinct, so \(p\) does not divide \(q\), and \(p\le q<pm\). For fixed such \(q\), in each coordinate the candidate index from \(0\) to \(m-1\) is restricted to one residue class modulo \(q\), because the step \(p\) is invertible modulo \(q\). For \(q\le m\) the total number of choices in two coordinates is at most \((2m/q)^2\). For \(q>m\) there is at most one choice. A union bound excludes at most
\[
4m^2\sum_{q\ge p}q^{-2}+pm \ \le\ \frac{4m^2}{p-1}+pm
\]
positions for one earlier neighbor. Across at most \(h\) earlier neighbors this is at most \(m^2/4\) by the choices of \(p,m\). Occupied candidates account for at most \(n-1<m^2/2\) more. The greedy choice always exists.

If an edge has endpoints \(x,y\) with gcd \(g<p\), every strictly interior lattice point has the form \(x+j(y-x)/g\) with an integer \(0<j<g\). Modulo \(p\), this is \(\overline{x}+jg^{-1}(\overline{y}-\overline{x})\), a point of the line through the endpoint residues distinct from both. It is therefore outside the parabola, so it cannot be any vertex position. This argument includes vertices placed after the edge endpoints. We obtain a drawing in the required sense.

For fixed \(h\), the prime is fixed and we can take \(pm=O_h(\sqrt n)\). Each squared edge length is a positive integer at most \(2(pm-1)^2=O_h(n)\) expressible as a sum of two integer squares. The Landau–Ramanujan estimate gives \(O(X/\sqrt{\log X})\) such integers up to \(X\), which proves the second bound. The grid and arithmetic counting argument is the classical one used by Erdős for the distinct-distances upper bound. The residue and gcd constraints make it apply to the vertex-edge incidence condition. [Erdős, On Sets of Distances of \(n\) Points](https://doi.org/10.2307/2305092)

## Prior work and scope

Carmi, Dujmović, Morin and Wood proved a logarithmic bound for fixed treewidth and maximum degree in Theorem 5 of their 2008 paper and asked for a sublinear bound for bounded maximum degree in Section 7. Bakhajian and Feldheim proved a uniform bound of thirteen for outerplanar graphs and asked for a uniform bound for fixed treewidth and maximum degree in Conjecture 1 of their paper. Searches by the problem statements, paper titles, authors and drawing parameters did not locate prior proofs of the two general bounds above. This is an informal proof and the literature search is provisional. [Carmi et al.](https://www.combinatorics.org/v15i1r107) · [Bakhajian and Feldheim](https://arxiv.org/abs/1907.13104)
