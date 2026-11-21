# Exact quantum compactness when walk refinement separates twins

## GP-0968

For a graph on $n$ vertices, begin ordinary vertex refinement with the invariant colors $((A^j)_{vv})_{0\le j<n}$. Suppose its stable cells are exactly the twin classes. On this polynomial-time recognizable class the equality $QP(A)=S(A)$ holds if and only if ordinary vertex refinement begun with a single color also separates the twin classes. In addition the entire quantum automorphism algebra is determined by the twin-class sizes, and its quantum orbital partition can be computed in polynomial time. [Definitions of quantum compactness and quantum fractional automorphisms](https://arxiv.org/html/2606.13928#S3.SS2)

Write $u$ for the fundamental magic unitary. From $uA^j u^{\mathsf T}=A^j$ and row orthogonality, taking a diagonal entry gives
$$
(A^j)_{vv}=\sum_w (A^j)_{ww}u_{vw}.
$$
Multiplying by $u_{vw}$ shows that a nonzero entry connects only equal diagonal-power vectors. Thus the initial color indicators are fixed by $u$. If a cell indicator $\mathbf 1_C$ is fixed by $u$, then $A\mathbf 1_C$ is fixed as well, because $u$ commutes with $A$. Orthogonality again forces its entries to agree at every pair joined by a nonzero $u_{vw}$. This proves inductively that the walk-seeded stable colors are invariant, so $u$ is block diagonal on the twin classes under the hypothesis.

On these classes, each adjacency block is constant, except for the possible identity subtraction in an internal clique. Every block-diagonal tuple of magic unitaries commutes with these blocks by row and column summation. Thus the universal quantum automorphism algebra is exactly the unital free product of the quantum permutation algebras on the respective classes. Its scalar state matrices are block doubly stochastic. Conversely each block doubly stochastic array is a convex combination of permutations obtained independently inside the classes, by the Birkhoff theorem. Those permutations are automorphisms and their states are allowed. Hence $QP(A)=P(A)$ is precisely the product of these Birkhoff polytopes. For two entries of $u$, their product is forced to zero if a class changes or the equality pattern of their two indices changes inside a class. Otherwise some within-class permutations carry both indices as specified, and evaluating at their classical character gives one. This also determines the quantum orbital partition exactly.

For comparison, let $M\in S(A)$ be a doubly stochastic numerical matrix commuting with $A$. If $Mf=f$ for a real column vector $f$, then $M_{vw}>0$ forces $f_v=f_w$. Indeed convexity gives
$$
\sum_v\Big(\sum_w M_{vw}f_w\Big)^2
\le\sum_{v,w}M_{vw}f_w^2
=\sum_w f_w^2.
$$
The left side already equals the right side, and equality in each row's convexity inequality forces its positively weighted values to coincide. Starting with the all-ones vector and applying this to $A\mathbf 1_C$ at each refinement stage shows that $M$ preserves every ordinary stable cell. If these are the twin classes, $S(A)$ is contained in the same product of Birkhoff polytopes and equality follows.

Conversely the orthogonal projector onto vectors constant on the ordinary stable cells is doubly stochastic. It commutes with $A$ because the partition is equitable and $A$ is symmetric, so both the constant-on-cells space and its orthogonal complement are preserved. If a stable cell contains two different twin classes, this projector has strictly positive cross-class entries prohibited in $QP(A)$. This gives the converse and an explicit witness of strict containment on every negative instance of the recognized class.

For a distinction from commutativity, the universal algebra in this class is commutative exactly when at most one twin class has size greater than one and that class has size at most three. Quantum permutations of at most three points are classical, while four points admit two independent $2$ by $2$ magic blocks formed from noncommuting projections. Two different nonsingleton classes allow the same noncommuting projections in separate blocks. For example, the cone over $K_2\sqcup K_3$ is quantum compact by its degree partition and has noncommutative quantum automorphism algebra. [Quantum permutation algebras and free products](https://arxiv.org/abs/math/0503461)

### A strict example with no ordinary refinement distinctions

For a connected cubic example, label the vertices $0,\ldots,11$ and take the edges
$$
04,05,06,\ 12,17,1\,10,\ 28,2\,10,\ 35,38,3\,10,\
47,4\,11,\ 59,\ 67,69,\ 8\,11,9\,11.
$$
The vectors $((A^j)_{vv})_{j=3}^{7}$ in vertex order, computed by multiplying the adjacency matrix repeatedly, are
$$
\begin{array}{c|rrrrr}
v&3&4&5&6&7\\\hline
0&0&19&4&135&66\\
1&2&15&20&97&180\\
2&2&17&20&113&178\\
3&0&17&6&113&96\\
4&0&17&6&117&90\\
5&0&17&4&117&74\\
6&0&19&4&133&70\\
7&0&17&4&115&74\\
8&0&17&6&113&98\\
9&0&17&8&113&114\\
10&2&17&20&111&184\\
11&0&15&8&97&120
\end{array}
$$
Thus walk colors are discrete, whereas ordinary refinement leaves a single cell since the graph is regular. Its quantum fractional automorphism set is $\{I\}$, and $J/12$ is an explicit point in $S(A)$ outside that set.
