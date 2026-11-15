# Same-prime markers for finite p-group isomorphism

**Theorem.** Let $G$ and $H$ be finite $p$-groups of the same order $s$, given by Cayley tables, and let $V_G=G/\Phi(G)$ and $V_H=H/\Phi(H)$. Given ordered lists of independent covectors $(\ell_1,\ldots,\ell_k)$ on $V_G$ and $(\ell'_1,\ldots,\ell'_k)$ on $V_H$, there is a deterministic polynomial-time construction of Cayley tables of two $p$-groups $K_G,K_H$ of order $s^{O(1)}$ with the following property. Their isomorphisms induce on the original Frattini quotients exactly the maps of those isomorphisms $f:G\to H$ for which
$$
  \ell'_i\circ\overline f\ \in\ \mathbb F_p^\times\ell_i
  \quad (1\le i\le k).
$$
In particular one ordinary $p$-group isomorphism decision query at the same prime tests these simultaneous constraints. The construction applies to every prime, including $2$, and to every nilpotency class.

The input group side of a query is preserved through an intrinsic subquotient and a surjective restriction, while the constraint is recorded in a mixed commutator pairing. The two ingredients are described below. The reduction uses ordered lines in the dual Frattini quotient. The main search and counting argument can resolve the remaining scales by at most $p^{\dim V_G}\le s$ trials of the prescribed-Frattini-map lifting test.

## A linear-size ordered marker

For $k\ge 7$, take a tree with one vertex of degree three and branches of lengths $1,2,k-4$. Its $k$ vertices form the left part of a bipartite graph. For each tree edge put in a right vertex joined to its two ends. Add a private right vertex adjacent to each left vertex. The tree is identified by the degree-two right vertices, and its three branch lengths are distinct. Thus every part-preserving automorphism fixes every left vertex. The private right vertices ensure that no left neighborhood is contained in another. For $1\le k\le 6$, use a disjoint union of stars with left centers of respective degrees $1,\ldots,k$. In this case the degrees fix each left vertex, and the disjoint nonempty neighborhoods give the same noncontainment property. Both graphs have at most $4k$ right vertices and $4k$ edges, and all vertices meet an edge.

For a labeled right part $J$, let $A=\mathbb F_p^J$ with coordinate covectors $z_j$, let $D=\mathbb F_p^{E(\Gamma)}$ with basis $d_{ij}$, and put
$$
  M(v,a)=\sum_{(i,j)\in E(\Gamma)}\ell_i(v)z_j(a)d_{ij}.
$$
Its values span $D$, since choosing $a$ as a coordinate vector and $v$ dual to one of the independent $\ell_i$ gives each basis vector $d_{ij}$. The image of the dual of $M$ in $V^*\otimes A^*$ is the coordinate subspace spanned by the tensors $\ell_i\otimes z_j$ indexed by edges.

Suppose an isomorphism of such pairings identifies two versions of this subspace. Contracting in the second mode shows that the dual maps carry $\langle\ell'_1,\ldots,\ell'_k\rangle$ onto $\langle\ell_1,\ldots,\ell_k\rangle$. Contracting in the first mode gives the full right covector space. In the indicated labeled bases let $P,Q$ be the respective invertible maps from target covectors to source covectors, so that $P\otimes Q$ maps the target edge subspace onto the source edge subspace. Choose permutations $\sigma,\tau$ such that the determinant terms select nonzero entries $P_{\sigma(i),i}$ and $Q_{\tau(j),j}$. For each edge $(i,j)$ the image of that edge tensor has nonzero coefficient at $(\sigma(i),\tau(j))$, which must also be an edge. Since the product of the permutations is bijective and the graphs are the same, this is a part-preserving graph automorphism. Hence $\sigma$ fixes every left vertex.

Now if $P_{h,i}$ is nonzero, then for every $j$ adjacent to $i$ the coefficient at $(h,\tau(j))$ is nonzero, so $\tau(N(i))\subseteq N(h)$. Because $\tau(N(i))=N(i)$ and the neighborhoods are pairwise incomparable, $h=i$. Thus every covector line is carried to the corresponding labeled line. Conversely, any isomorphism of the first spaces identifying those lines extends to an isomorphism of the pairings by taking the identity on $A$ and scaling each output $d_{ij}$ by the corresponding scalar for $\ell_i$.

## Compiling the marker into a p-group

It suffices to handle $k\ge 1$. Fix $G$, and write $V=G/\Phi(G)$. Use the pairing $M:V\times A\to D$ above, and let $C$ be a copy of $A$ with fixed isomorphism $\iota:A\to C$. Form the group $N=(A\oplus D\oplus C)\rtimes G$, where $g\in G$ acts on the three abelian coordinates by
$$
  (a,d,c)\longmapsto(a,d+M(\overline g,a),c).
$$
Set $e=2+\log_p |N|$, an integer, and let $B=\mathbb Z/p^e\mathbb Z$. The action of $G$ commutes with the action of $B$ where $t\in B$ sends $(a,d,c)$ to $(a,d,c+(t\bmod p)\iota(a))$. Set
$$
  K=(A\oplus D\oplus C)\rtimes(G\times B)
$$
under these commuting actions. Explicitly its multiplication in coordinates is
$$
 (a,d,c,g,t)(a',d',c',g',t')
 =
 (a+a',d+d'+M(\overline g,a'),c+c'+(t\bmod p)\iota(a'),gg',t+t').
$$
The construction uses elementary abelian coordinates and ordinary group multiplication. In particular the formula is valid at $p=2$.

The following groups and pairings can be read intrinsically from $K$. Write $\langle b\rangle$ for the embedded copy of $B$, generated by the coordinate $1\in B$.

1. Define $T=\{x\in K:x^{p^{e-1}}=1\}$. In the construction, an element whose $B$ coordinate is divisible by $p$ lies in the direct product $N\times\langle b^p\rangle$ of exponent at most $p^{e-1}$. An element whose $B$ coordinate is a unit projects to an element of order $p^e$, so is outside $T$. Thus $T=N\times\langle b^p\rangle$. The maximal element order is $p^e$, since no order exceeds $p^e$ by the same argument applied to the $p$-th power of an element with unit $B$ coordinate. Hence $e$ and $T$ are carried to their counterparts by abstract isomorphisms.
2. The characteristic subgroup $[T,T]$ is $[G,G]\times D$. To see the equality, the quotient by this subgroup of the displayed coordinates is abelian, and all of $D$ is generated by the mixed commutators with $A$. Define the characteristic subgroup
$$
  U=\{x\in T:[x,K]\subseteq[T,T]\}.
$$
Here $U$ is the intersection with $T$ of the preimage of the center of $K/[T,T]$. In coordinates the only possible obstruction to this condition is the $C$-component of $[x,b]$, which up to a sign is $\iota(a)$ for the $A$-coordinate $a$ of $x$. This gives
$$
  U=G\times D\times C\times\langle b^p\rangle.
$$
3. In $K$ we have $[K,K]=[G,G]\times D\times C$. The quotient by this derived subgroup is $A\times(G/[G,G])\times B$ as an abelian group. Its $p$-th powers are precisely the zero $A$-coordinate, the $p$-th powers in $G/[G,G]$, and the subgroup $\langle b^p\rangle$ in $B$. The formula $\Phi(K)=K^p[K,K]$ therefore gives
$$
  \Phi(K)=\Phi(G)\times D\times C\times\langle b^p\rangle\ \subseteq\ U.
$$
In particular the inclusion of $G$ followed by the quotient identifies $G/\Phi(G)$ with $U/\Phi(K)$.
4. We have $T/U\cong A$, $[U,U]=[G,G]$, and $[U,T]=[G,G]\times D$. In $K/[U,U]$, the commutator $[u,t]$ for $u\in U,t\in T$ is precisely the indicated mixed pairing $M(\overline g,a)$ with the commutator convention $[u,t]=utu^{-1}t^{-1}$. This expression is independent of all coordinates of $u$ except its class in $U/\Phi(K)$ and of all coordinates of $t$ except its class in $T/U$. Consequently the intrinsic commutator pairing on
$$
  U/\Phi(K)\ \times\ T/U\ \longrightarrow\ [U,T]/[U,U]
$$
is exactly $M$ after the identifications.

Now an isomorphism $K_G\to K_H$ induces an isomorphism of these pairings, so its map on $U_G/\Phi(K_G)$ takes the marked covector lines to the prescribed lines. Its restriction to $G\subseteq U_G$, followed by projection from $U_H=H\times D\times C\times\langle b^p\rangle$ to $H$, is a homomorphism that induces this same invertible map $V_G\to V_H$. Its image generates $H/\Phi(H)$, so its image is all of $H$ by the Frattini property. With the original group orders equal it is an isomorphism. Conversely, a line-respecting isomorphism $G\to H$ gives pairing compatibility by the scaling map on $D$ above. Extending with the identity on $A,C,B$ preserves both semidirect actions and gives the required isomorphism of the compiled groups.

## Cayley-table size and interfaces

For no supplied marks one simply queries the original groups. Otherwise $1\le k\le \dim V\le \log_p s$ and each of $A,C,D$ has dimension at most $4k$. Thus $|N|\le s^{13}$ and
$$
   |K|=|N|p^e=p^2|N|^2\le s^{28}.
$$
The characteristic subgroup $\Phi(G)$ and its quotient can be produced from a Cayley table by closure under commutators and $p$-th powers, followed by elementary abelian coordinates. The multiplication formula then constructs the compiled Cayley table in deterministic polynomial time in the original table size, uniformly in the prime. The same-prime queries may have larger nilpotency and Frattini class than the input groups.

This marking theorem compiles a prescribed partial dual frame. The separate class-two Frattini construction uses a different augmentation when the decision oracle must additionally stay inside Frattini class two. The prescribed-full-map lifting procedure for arbitrary $p$-groups in the accompanying search and counting proof uses characteristic central extensions and can be used after marking here.
