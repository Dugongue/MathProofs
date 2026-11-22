# An ordinary incidence tensor with a constant-degree graph decoder

Let $G,H$ be finite simple undirected graphs with equal numbers $n,m$ of vertices and edges and equal numbers of isolated vertices. Over **every field**, the usual graph-isomorphism equations and the ordinary tensor-isomorphism equations for the diagonal incidence pencils below have mutually bounded-degree Polynomial Calculus substitutions, with polynomial-size derivations. This includes $\mathbb F_3$ without adding field equations. It also proves the comparison at the diagonal matrix Lie conjugacy stage of the Petrank–Roth–Grochow route. Equal isolate counts can be arranged by comparing and removing isolates before both reductions. Every claim about raw graph equations here uses the stated equal-count convention.

Write $M_G=[I_m\ I_m\ I_m\ D_G]$, with $D_G$ the unsigned edge-by-vertex matrix, and write $B_G(z)=\operatorname{diag}(M_G^{\mathsf T}z)$. The ordinary tensor has shape $(3m+n)\times(3m+n)\times m$ and $z$ indexes its slices. Its independent changes of basis admit the equations
$$
P B_G(z) Q'=B_H(Zz)
$$
coefficient by coefficient, where primes denote two-sided inverse variables. These equations and the usual cubic tensor action are interconverted using the third-mode inverse and a transpose convention in constant degree. The linked Lie system additionally sets $P=Q$. The bare pencil treats the two ambient modes independently. General removal of FGS partitions is a separate assertion. [Petrank–Roth code](https://doi.org/10.1109/18.623157) · [Grochow, Theorem 2.1](https://arxiv.org/abs/1112.2012) · [Galesi–Grochow–Pitassi–She, §5 and Question 7.5](https://arxiv.org/html/2305.19320)

## A pair of matrix algebras recovers projective weights

The common image span of the slices is the span of the coordinate vectors of nonzero weight. Each such vector is a column of a basis slice. The common kernel is the span of the zero-weight coordinates, which correspond to isolated vertices. The action equations and their inverse version give $P$ and $P'$ preserving the common image spans between the appropriate spaces, and $Q,Q'$ preserving the common kernels. For example $PB_G(z)=B_H(Zz)Q$ sends every generating image column into the target span. For a source kernel vector $v$, substitute $z=Z'w$ to give $B_H(w)Qv=0$. These are entrywise linear consequences after applying the displayed inverse identities. Restrict $P,P'$ to the image spans and take $Q,Q'$ on the quotients by the common kernels. Their surviving blocks are two-sided inverses by block multiplication. This removes all zero-weight coordinates from both pencils for the rest of the proof.

For a remaining weight $c$ let $E_c$ be the diagonal projector onto the coordinates with that weight. Distinct nonzero weights in this construction are nonproportional, since they are distinct zero-one vectors with distinct supports. Define the algebra of pairs
$$
\mathcal A_G=\{(U,V): U B_G(z)=B_G(z)V\text{ for every }z\}
$$
with componentwise multiplication. Its equation on entry $(a,b)$ is $U_{ab}c_b=V_{ab}c_a$. For unequal weights both entries vanish, and for equal weights they agree. Consequently $\mathcal A_G$ is the product of full matrix algebras on the weight blocks, embedded as $(U,U)$. Its center has basis $(E_c,E_c)$. These descriptions follow by elimination of fixed linear equations. For the center use commutation with the matrix units in each block. All consequent linear identities are constant linear combinations of the defining equations.

Conjugation $(U,V)\mapsto(PUP',QVQ')$ is an isomorphism of these pair algebras in constant PC degree. For each fixed basis element the defining relations in the target follow by inserting the slice equations with $z=Z'w$ and the inverse identities. Applying the reverse calculation to all target basis elements proves transport of the centers, since commutation with a fixed source central element extends linearly to every inverse image. Thus for some degree-two polynomials $q_{dc}$,
$$
 P E_c P'=Q E_c Q'=\sum_d q_{dc}E'_d .
$$
One diagonal coordinate in block $d$ gives $q_{dc}$. The inverse center map has entries $r_{cd}$. The maps preserve units and products in ordinary PC by inserting $P'P,PP'$. Hence both matrices have idempotent entries, row sums one and orthogonal distinct entries in each row. They also satisfy $qr=rq=I$. Multiplying each diagonal inverse equation by its selected row idempotent gives $q_{dc}r_{cd}=q_{dc}=r_{cd}$. The columns of $q$ therefore have the same permutation identities.

## Detecting multiplicities in small characteristic

Let the source and target multiplicities be $a,b$. Every nonzero weight in a simple graph has multiplicity in $\{1,3,4,5\}$. Each edge private weight has its three copies and a further copy for each degree-one endpoint on that edge. Distinct vertices of degree at least two give different weights because two distinct vertices cannot share two edges. Their weights have multiplicity one.

Fix $q=q_{dc}$, with $q^2=q$. Multiplying the conjugated projector identities by inverse variables gives $qPE_c=qE'_dP$ and the corresponding inverse identities. Thus the submatrices $R=qP_{d,c}$ and $S=qP'_{c,d}$ satisfy $RS=qI_b$, $SR=qI_a$. If $a<b$, restrict $RS$ to any $(a+1)$-element principal set of coordinates. Its determinant is identically zero by expansion through the $a$ intermediate indices (or Cauchy–Binet). Substituting $qI$ one entry at a time gives $q^{a+1}=0$, whence $q=0$. If $a>b$ use $SR$ instead. Each determinant has order at most five since the largest multiplicity is five. All products here have a constant number of variable factors even after substituting the quadratic $q$. This removes precisely the spurious congruences in the ordinary trace test, including multiplicities one and four over $\mathbb F_3$.

## Recovering incidence when the two ambient maps differ

Multiplying the action equation by the transported source projector and selecting one fixed diagonal position in target block $d$ gives
$$
 q_{dc}d^{\mathsf T}Z=t_{dc}c^{\mathsf T},
 \qquad t_{dc}=(PE_cQ')_{uu}\quad (u\text{ in block }d).
$$
The opposite action gives $q_{dc}c^{\mathsf T}Z'=t'_{cd}d^{\mathsf T}$. Since $c,d$ have a coordinate equal to one, idempotence first gives $qt=t$ and $qt'=t'$. Applying $Z'$ to the first equation and using the second now gives $tt'=q$. These are polynomial identities, so no scalar division or case split on a variable occurs.

By multiplicity detection, the private edge weights only match private edge weights. Write $s_{fe}=q_{e_f,e_e}$ for their Boolean permutation and $t_{fe}$ for the corresponding parameter. Summing the first identity above over the private weights for fixed $f$ gives $Z_{fe}=t_{fe}$. Distinct entries of $t$ in the same row or column annihilate each other's supporting idempotents. For a pair $c,d$ of nonleaf vertex weights, compare entry $e$ of the same identity after multiplying by $s_{fe}$:
$$
 q_{dc}d_f t_{fe}= t_{dc}c_e s_{fe}.
$$
When $d_f=1,c_e=0$, multiply by $t'_{ef}$ to obtain $q_{dc}s_{fe}=0$. When $d_f=0,c_e=1$, multiply by $t'_{cd}$ for the same conclusion. This enforces incidence in either direction despite the independent row and column transformations of the ordinary tensor.

For a source vertex $i$ and target vertex $u$ of degree at least two, substitute $p_{ui}=q_{d_u,c_i}$. On every edge, fix an order on its degree-one endpoints. For degree-one $u,i$ on edges $f,e$ use $p_{ui}=s_{fe}$ if their endpoint slots coincide, and zero otherwise. Multiplicity detection enforces equal numbers of such slots wherever $s_{fe}$ can be nonzero. Match isolates by a fixed bijection. Set all remaining cross-type variables to zero. Row and column sums, idempotence and collisions now follow from the corresponding equations for $q,s$. For two different leaf slots on the same edge, a common source or target vertex cannot match both slots, so those collision products vanish as well.

For all vertices the substitutions give $p_{ui}s_{fe}=0$ whenever their specified edge incidences differ. On the leaf block this follows by edge row or column collision. Isolates have no incidence. If $ij$ is a source edge and $u,v$ a target nonedge, each target edge $f$ misses at least one endpoint. Multiply the corresponding incidence mismatch by the other vertex variable and sum over $f$, using the column sum of $s$. This yields $p_{ui}p_{vj}=0$. Reversing source and target gives the opposite mismatch. Equal endpoints are already handled by collisions. This completes the substitution into the graph axioms.

Conversely, given graph variables $p$, put $s_{uv,ij}=p_{ui}p_{vj}+p_{vi}p_{uj}$ on edges with unordered pairs of distinct endpoints. Graph collisions and sum axioms make $s$ a Boolean permutation, by expanding products and discarding inconsistent endpoint pairs. Graph adjacency mismatches allow all target endpoint pairs in the sums to be replaced by target edges. Set $P=Q=\operatorname{diag}(s,s,s,p)$, $Z=s$, with transpose inverses. In the private coordinates the slice equation follows from edge collisions and idempotence. In vertex coordinates it reduces to preservation of endpoint incidence, since the surviving images of source edge $ij$ at a vertex $u$ have total $p_{ui}+p_{uj}$. These equations give the bare pencil and simultaneously the linked diagonal Lie system.

Each use of a matrix identity expands to a polynomial number of monomials with a bounded number of variable factors. Multiplying a derived identity by such a polynomial is a bounded-degree PC derivation by linear combination of variable multiples. The largest minor here has bounded order independent of graph size. Neither the coefficient variables nor the matrix entries need finite-field axioms. The zero-edge case with equal vertex counts permits a fixed vertex bijection. The argument is a written proof.

Combining this result with the PC normalization of a unital multiplication tensor and the graph decoder for Grigoriev's algebra gives two actual ordinary three-tensor encodings with mutually constant-degree equations in characteristic three, using their bare tensors. [Grigoriev multiplication-tensor proof](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/proof-complexity.md)

## Uniform version for graphs with any isolate counts

For a simple graph $G$ with vertices $i$, form $G^+$ by adding two fresh pendant vertices $(i,1),(i,2)$ adjacent only to $i$. The new graph has $3n$ vertices, $m+2n$ edges and no isolates. Even a previously isolated $i$ now has degree two, so the original vertices are precisely the vertices of degree at least two. For every pair with equal $n,m$, the ordinary tensors $B_{G^+}$ and $B_{H^+}$ give a constant-degree PC comparison to the **original** graph equations and therefore to the bare Grigoriev tensors on the original inputs, including when their isolate counts differ. The added vertices and edges are linear in $n$.

In the forward substitution, order the old vertices and the two pendant slots in three separate lists. Lift the original vertex map $p$ as $p\oplus p\oplus p$ on those lists. Sums, idempotence and collisions follow blockwise. A pair of old vertices uses the original adjacency test. Two new vertices are always nonadjacent. Across an old and a new vertex the edge condition is equality of parent labels. If the source parents agree but the target parents differ, the offending product is a collision in one column of $p$. If the target parents agree but the source parents differ, use a row collision. This verifies all graph equations on $G^+,H^+$, so the forward incidence construction applies as proved.

In reverse, the weight-multiplicity construction above gives graph variables with both old-to-new and new-to-old blocks identically zero: old vertices have multiplicity-one weights, while each pendant vertex is assigned its own edge slot. Thus their old-to-old block alone satisfies all permutation and adjacency axioms on $G,H$. This argument uses no equality or matching of isolate counts in the original graphs and preserves the identity of the original edge relation between old vertices.
