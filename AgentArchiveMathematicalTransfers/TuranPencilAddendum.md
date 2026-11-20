# A sharp three-moment certificate for the adjacency–degree pencil

**Corollary.** Fix real numbers \(a,b\) with \(b\ne0\). For a finite simple graph \(G\), put \(M_G=aD_G+bA_G\). Its order and the first three power traces of \(M_G\) distinguish every Turán graph \(T(n,k)\) from every nonisomorphic graph. Three traces are necessary in general.

Write \(t(G)\) for the number of triangles, \(m\) for the number of edges, and \(p(G)\) for the number of induced triples containing exactly one edge. Counting the common neighbors of the endpoints of each edge gives
\[
3t(G)=\sum_v d(v)^2-nm+p(G).
\]
Indeed, for an edge \(uv\), its common-neighbor count equals \(d(u)+d(v)-n\) plus the number of vertices adjacent to neither \(u\) nor \(v\). Each triple with a single edge contributes exactly once to the surplus.

Among integer sequences of length \(n\) with a given sum \(2m\), sequences taking two consecutive degree values (or one value) minimize the sum of squares. Any pair of entries differing by at least two can be moved one unit toward each other to decrease that sum. The Turán graph attains the minimum and has \(p=0\). Therefore, if \(G\) has the same order, number of edges and number of triangles as \(T(n,k)\), then \(G\) has the same degree multiset and \(p(G)=0\). Its complement has no induced path on three vertices, hence is a union of cliques. The multiset of complement degrees recovers the clique sizes. This proves recognition from \(n,m,t\) alone. The degree-square triangle bound and its extremal use belong to the classical Goodman method.

When \(a=0\), the second and third power traces give \(2b^2m\) and \(6b^3t(G)\), proving the corollary. When \(a\ne0\), write \(s_j=\sum_v d(v)^j\). The three traces are
\[
a s_1,\qquad a^2s_2+b^2s_1,\qquad
a^3s_3+3ab^2s_2+6b^3t(G).
\]
The first two recover \(s_1,s_2\). Matching the Turán values forces the minimizing degree multiset, so \(s_3\) also agrees. The third trace recovers the triangle count and the result follows. In fact, whenever the first two traces agree with the Turán graph and \(a\ne 0\),
\[
\operatorname{tr}M_G^3-\operatorname{tr}M_{T(n,k)}^3=2b^3p(G).
\]
For sharpness, \(K_{3,3}=T(6,2)\) and the triangular prism are both 3-regular on six vertices but have zero and two triangles respectively. Their first two traces agree for every choice of \(a,b\).

## The pure-degree boundary

For \(b=0\) and \(a\neq0\), the full spectrum only gives the degree multiset. For \(T(n,k)\), it determines the graph exactly when \(k=1\) or \(n\le 2k\). Indeed, \(k=1\) is edgeless. If \(n\le2k\), the complement is a matching and isolated vertices, so its degrees specify it. In both cases its first trace and order already suffice if the target is edgeless, and its first two traces and order suffice in the matching-complement case because they force the degree multiset as above.

If \(k\ge2\) and \(n>2k\), the complement is a union of at least two nontrivial cliques, one of size at least three. In each of two such cliques take an edge, choosing the first one in a clique of size at least three. Delete the two edges and reconnect their endpoints by two edges across the cliques, preserving every degree. The endpoints of the deleted edge in the larger clique remain connected through another vertex. Hence their common component is no longer complete. Complementing back gives a nonisomorphic graph with the same degree multiset. Finally \(a=b=0\) cannot distinguish graphs of order \(n\ge2\), and there is only one graph of order one.