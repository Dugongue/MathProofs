# Six colors for planar unit-distance graphs with at most 245,590 edges

This strengthens the edge bound of O’Neill, Kirkby, Astra and Fable by using a two-defect rounding rule. The numerical estimates used here are their Theorem 3 and Proposition 25. The proof retains the original computation on which those estimates depend. [Release manuscript](https://charlesponeill.com/maths-releases/hadwiger-nelson/hadwiger-nelson.pdf).

Let $G$ be a $K_4$-free graph with no proper $k$-coloring. In any $k$-coloring write $X$ for the number of monochromatic edges and $L$ for the number of locked vertices, meaning that all $k$ colors occur among their neighbors. Then

$$
X+L\ge 3.
$$

For $X=1$, each endpoint of the bad edge must be locked. Otherwise recoloring that endpoint with a color absent from its neighborhood gives a proper coloring. For $X=2$, if the two bad edges meet, their common vertex must be locked by the same argument. If the edges are disjoint and none of their endpoints is locked, some endpoint of one edge is nonadjacent to an endpoint of the other edge. Otherwise their four endpoints span $K_4$. Recolor those two nonadjacent endpoints with colors absent from their respective neighborhoods. These two recolorings fix both defects and cannot interfere. The case $X\ge3$ already satisfies the inequality. The case $X=0$ contradicts the hypothesis.

A planar unit-distance graph is $K_4$-free, since four pairwise equidistant points cannot lie in the Euclidean plane. Let $m$ be its edge count, and place the graph in the preprint’s random translated and rotated six-coloring. Write $C_v$ for the number of neighbors of $v$ sharing its color and $L_v$ for the indicator that $v$ is locked. Then $\sum_v C_v=2X$ and $\sum_v L_v=L$. If the graph were not six-colorable, the inequality above would give

$$
1\le X-\tfrac13\sum_v(C_v-L_v).
$$

The cited estimates give $\mathbb E X\le m p_E$ and $\mathbb E(C_v-L_v)\ge\beta_E \deg(v)$, where $p_E=2038573446989/(5\cdot10^{17})$ and $\beta_E=8\cdot10^{-9}$. Hence

$$
1\le m\left(p_E-\tfrac23\beta_E\right)
=m\frac{6107720340967}{1500000000000000000}.
$$

For $m=245590$ the numerator of the shortfall from $1$ is $4961461914470>0$. This proves the claim. The argument improves the edge threshold by 80. The vertex threshold uses a different estimate.
