# A surface Bockstein controls multiplication-tensor determinants

Let $R$ be a finite commutative local ring and write $U=R^\times$. The incidence algebra of a closed surface map has an exact automorphism determinant formula. The formula contains a contribution from the integral Bockstein of its mod-2 fundamental class. Over characteristic-two local rings this contribution can detect principal units of order two, even though a permutation sign can only contribute 1.

Three consequences are explicit. The triangular torus with periods $n\mathbb Z^2$, $n\ge4$, and its dual hexagonal torus each give automorphism determinant image $U^6$. The antipodal quotient of the icosahedron gives a rank-121 algebra with automorphism determinant image $U^2 U[2]$, where $U[2]=\{u\in U:u^2=1\}$. The dodecahedral sphere gives image $U^2\langle-1\rangle$. Each of these images gives the exact determinant-one orbit count by taking its index in $U$.

## Incidence determinants and an integral chain

For a nonempty poset $P$, let $A_R(P)$ have a basis $e_{xy}$ for $x\le y$, with product $e_{xy}e_{zt}=e_{xt}$ when $y=z$ and zero otherwise. Put $X=\Delta(P)$, its order complex. Orient each simplex by increasing order. Use integral chains and let $M=C_1(X;\mathbb Z)/\operatorname{im}\partial_2$. Let $b\in M$ be the class of the sum of all increasing edges $[x,y]$.

Then
$$
D_{\rm aut}=\{\eta(b):\eta\in\operatorname{Hom}(M,U)\}
              \cdot\{\operatorname{sgn}(\pi_*):\pi\in\operatorname{Aut}(P)\}.
$$
Here $\pi_*$ permutes the entire incidence basis, including the diagonal. The formula uses actual $R$-algebra automorphisms and unit values.

To see this, the radical of the incidence algebra consists of the strictly upper part together with diagonal entries in the maximal ideal of $R$. The strictly upper part is nilpotent, the maximal ideal is nilpotent, and the resulting quotient is a product of residue fields. An automorphism therefore permutes the diagonal idempotents modulo the radical. Align the transported family $(f_x)$ to the target family $(e_{\pi(x)\pi(x)})$ by the unit $\sum_x f_xe_{\pi(x)\pi(x)}$. Its diagonal entries are exactly 1, since diagonal idempotents over $R$ are 0 or 1. Its conjugation has determinant 1 over $R$. Left multiplication by the unit and right multiplication by its inverse are triangular with diagonal ones on free Peirce spaces, by ordering them on their start or end indices. This argument works over rings with nilpotents.

After alignment the ranks of the Peirce spaces recover the order relation, so $\pi$ is a poset automorphism. Remove its literal basis permutation. The remaining map scales each $e_{xy}$ by some $c_{xy}\in U$, with $c_{xx}=1$. Multiplicativity is exactly $c_{xy}c_{yz}=c_{xz}$ for strictly increasing triples. These are the boundary relations defining $\operatorname{Hom}(M,U)$. The determinant of this map is the product of all the $c_{xy}$, namely evaluation on $b$. Conversely all these maps and all literal relabelings exist. This proves the formula. It is the incidence-algebra automorphism decomposition with the determinant retained. [Baclawski on incidence-algebra automorphisms](https://doi.org/10.1090/S0002-9939-1972-0313133-8)

Both left and right multiplication-by-unit determinant images are full. A diagonal unit with arbitrary entry at a maximal element has that entry as its left multiplication determinant. For the right determinant use a minimal element. The determinant ratio of any multiplication isotopy is the determinant of its normalized algebra isomorphism, found by evaluating on the unit. The determinant triples of the stabilizer are $(a\delta,b'\delta,ab'\delta)$ for independent $a,b'\in U$ and $\delta\in D_{\rm aut}$. Quotienting by this image gives $[U:D_{\rm aut}]$ determinant-one orbits inside one ordinary orbit. [Determinant ratio and orbit index](https://github.com/Dugongue/MathProofs/tree/main/MultiplicationTensorDeterminants)

## The Bockstein formula

Let $P$ now be the face poset of a finite connected regular closed surface map. Each face has a simple polygonal boundary. Each edge has two distinct endpoints and two distinct incident faces. Its order complex is the barycentric subdivision of the surface. Put
$$
u=\sum_{v<e}[v,e],\qquad w=\sum_{e<f}[e,f],\qquad
\beta=\sum_{v<f}[v,f],
$$
where $v,e,f$ denote vertices, edges, and faces. The sum $z$ of all positively rank-ordered flags $[v,e,f]$ has boundary
$$
\partial z=2(u+w-\beta).
$$
Each vertex-edge and edge-face incidence appears in two flags. Each vertex-face incidence appears in two flags because the vertex has two boundary edges in the face. The negative term follows from the boundary of $[v,e,f]$. Thus $b=2\beta+\tau$ in $M$, where $\tau$ is the class of $(\partial z)/2$ and lies in $H_1(X;\mathbb Z)\subset M$. The reduction of $z$ is the mod-2 fundamental cycle. By the chain definition of the connecting map for $0\to\mathbb Z\xrightarrow{2}\mathbb Z\to\mathbb Z/2\to0$, the class $\tau$ is its Bockstein.

For an orientable surface, $\tau=0$ because the mod-2 fundamental class lifts. For a nonorientable surface, the integral second homology vanishes and the mod-2 second homology has order two. The exact sequence therefore makes $\tau$ the nonzero element of order two in integral first homology. There is a short exact sequence
$$
0\longrightarrow H_1(X;\mathbb Z)\longrightarrow M
\xrightarrow{\partial_1} \operatorname{im}\partial_1\longrightarrow0.
$$
Its rightmost term is free, so it splits. Consequently $M$ is free for an orientable surface, and has torsion $\mathbb Z/2$ generated by $\tau$ for a nonorientable one. [Hatcher, Algebraic Topology, coefficient exact sequences and surface homology](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)

Let $d$ be the gcd of the coordinates of $\beta$ in any basis of $M/\operatorname{tors}M$, taking gcd zero if the vector vanishes. This is independent of the basis and can be obtained by integer Smith normal form. Since $2\beta$ has trivial torsion coordinate in any splitting, the scalar factor of the determinant group is exactly
$$
D_{\rm scalar}=
\begin{cases}
U^{2d},&\text{orientable},\\
U^{2d}U[2],&\text{nonorientable}.
\end{cases}
$$
Indeed a homomorphism on the free coordinates can take independent values in $U$, and a homomorphism on the order-two coordinate takes any value in $U[2]$. Bézout gives exactly the indicated powers on the free part. The boundary of $\beta$ has coefficients minus the number of incident faces at every vertex and plus the face length at every face. In particular $d$ divides the gcd of these numbers.

The remaining sign also has a topological formula. Permutations of the incidence basis are the combined permutations on $C_0$ and $C_1$, while $C_2$ is the flag space. Ranks are preserved, so no reordering sign occurs within a basis simplex. Taking determinants on boundaries, cycles and homology over $\mathbb Q$ gives
$$
\operatorname{sgn}(\pi_*)=\det(\pi|H_1)\det(\pi|H_2)\det(\pi|C_2).
$$
Here $H_0$ contributes 1 since the surface is connected, and inverses of the signs equal the signs. This formula applies in any residue characteristic because the rational signs map to the units $\pm1$ of $R$.

In particular, over $R=\mathbb F_2[\epsilon]/(\epsilon^2)$ the ordinary multiplication orbit has exactly two determinant-one orbits for an orientable surface and one for a nonorientable surface. The unit group consists of $1$ and $1+\epsilon$, so the free-coordinate powers and permutation signs disappear. Only the nonzero Bockstein supplies $1+\epsilon$. This also gives an explicit supplied-transporter criterion for nonorientability. Scale one strictly upper basis vector by $1+\epsilon$, and use this linear map to transport the whole multiplication law. It fixes the unit vector and is the supplied ordinary algebra isomorphism. A determinant-one replacement exists exactly when the original algebra has an automorphism with determinant $1+\epsilon$, hence exactly when the surface is nonorientable.

## Triangular and hexagonal tori

Take the triangular lattice with vertices $\mathbb Z^2$ and triangles of the following two types, for each $x$:
$$
(x,x+e_1,x+e_2),\qquad
(x+e_1+e_2,x+e_1,x+e_2).
$$
Quotient by the period lattice $n\mathbb Z^2$ for $n\ge4$. The local maps are unchanged and the result is a triangulated torus. Here every vertex has valence six and each triangle has three vertices, so $d$ divides 3.

In the first triangle choose $x$ as its anchor, and in the second choose $x+e_1+e_2$. Subtract from each vertex-to-face incidence the anchor-to-face incidence of the same face. Modulo boundaries, the difference is the subdivided edge path from that vertex to the anchor. Over $\mathbb Z/3$, the three subtracted copies of the anchor-to-face edge vanish. Summing the remaining paths over all $x$ gives zero. The first triangles contribute the negative $e_1$ and $e_2$ directions, and the second contribute their positives, cancelling by translation of the starting indices. Hence $\beta$ is zero in $M/3M$. It follows that $d=3$ and that the scalar determinant group is $U^6$.

All poset relabelings have even incidence sign. To see this, the torus triangulation automorphisms lift to automorphisms of its universal covering tiling. A flag determines a tiling automorphism, since the image of a triangle extends uniquely across each edge. The Euclidean symmetry group of that tiling is the translation lattice with the order-12 dihedral action fixing a vertex. Every such symmetry preserves the given period sublattice. Thus the torus group, of order $12n^2$, acts regularly on the flags. Its elements have order dividing $6n$, since their sixth powers are translations. The 2-part of each order is strictly smaller than the 2-part of $12n^2$. A permutation by an element on the regular flag set has all cycles of the same length, so it has an even number of cycles and positive sign. On the torus the determinant on $H_1$ equals the orientation sign on $H_2$, by the exterior square formula. The two signs cancel and the incidence-basis sign equals the flag sign. Hence $D_{\rm aut}=U^6$.

The dual cellulation has hexagonal faces. Its face poset reverses the order, so its incidence algebra is the opposite algebra. This preserves the automorphism determinant image and exchanges the two full unit images. In either case there are $6n^2$ cells and $18n^2$ strict comparabilities. The two rank-$24n^2$ algebras therefore have the same exact orbit count $[U:U^6]$.

## The hemi-icosahedron and principal units

Identify antipodal faces in the boundary of an icosahedron by taking the quotient of the whole triangulated sphere by its antipodal map. The quotient is the standard six-vertex triangulation of $\mathbb{RP}^2$, with 15 edges and 10 triangles. Its vertex valences are five and its face lengths are three, so $d=1$. Its combinatorial automorphism group is $A_5$. In fact the 60 rotations induce a faithful action. The action is nontrivial on antipodal vertex pairs, so faithfulness follows from simplicity of $A_5$. Conversely the link of each vertex is a 5-cycle containing every other vertex, so its stabilizer injects into the dihedral group of order ten. There are six vertices, giving the matching upper bound of 60. A sign character on $A_5$ is trivial, since it is generated by 3-cycles. Thus the exact full determinant image is $U^2 U[2]$. Its incidence algebra rank is $6+15+10+30+30+30=121$.

For the dodecahedral sphere the corresponding result is $U^2\langle-1\rangle$. Its valences and face lengths also give $d=1$, but the Bockstein vanishes. The antipodal map contributes determinant $-1$ from its 15 edge swaps. The vertex, face and comparable-pair swaps have even counts. [Dodecahedral calculation](C.md)

For $R=\mathbb F_{2^f}[t]/(t^a)$, put $q=2^f$. The dodecahedral tensor has $q^{\lfloor a/2\rfloor}$ determinant-one classes in its ordinary orbit. Indeed the units that are squares have only even powers of $t$ and arbitrary nonzero constant coefficient. For the hemi-icosahedral tensor the count is $q^{\lfloor(a+1)/4\rfloor}$. The involutions are precisely $1+t^{\lceil a/2\rceil}R$. Their contribution modulo squares cancels every odd coefficient position at degree at least $\lceil a/2\rceil$. This follows by computing the sizes of the two subgroups and their intersection, which consists of the even-power involutions. The surviving index is $q$ to the number of positive odd degrees below $\lceil a/2\rceil$. Thus the topological Bockstein changes actual principal-unit orbits. For the dual numbers over $\mathbb F_2$, the two counts are two and one, respectively.

These are written proofs of the exact determinant images and orbit counts. The incidence-algebra automorphism decomposition and the topological Bockstein are classical. Bibliographic priority for their determinant and orbit-count combination remains open. The Lean companion verifies the flag boundary multiplicity identity and the comparable-pair chain decomposition. The finite control constructs the icosahedron and its quotient, checks all 60 hemi-icosahedral automorphisms, and checks the mod-3 chain and incidence signs of four triangular tori. [Lean components](D.lean) · [Finite control](DCheck.py)
