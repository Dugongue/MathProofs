# Minimum faithful degree with one large orbit

Fix a prime $p$. A faithful action of an abstract group may differ from the supplied permutation action. Write $\mu(G)$ for the least degree of such an action. All complexity statements use explicit permutation generators and fixed $p$.

**Theorem.** Deciding $\mu(G)\le m$ is NP-complete for class-two groups with $Z(G)=[G,G]$, even with exactly one supplied orbit of size $p^3$ and every other supplied orbit of size $p^2$. The hard groups have exponent $p$ for odd $p$ and exponent four for $p=2$. Deleting the sole $p^3$-point orbit gives an optimal action of a quotient of $G$ by a central subgroup of order $p$. On these same restricted inputs, deciding whether $G$ admits a faithful action with all orbits of size at most $p^2$ is NP-complete.

By contrast, whenever a permutation $p$-group is already supplied on orbits of size at most $p^2$, a minimum-degree action can be constructed in deterministic polynomial time. This upper bound applies to every class and to $p=2$.

## 1. A matrix space with only one basis element of rank two

Take a bipartite instance of list three-coloring with sides $A,B$, nonempty lists $L(v)\subseteq\{1,2,3\}$, and edges $E\subseteq A\times B$. Precoloring extension with three colors is the special case of lists of cardinality one or three, and is NP-complete on bipartite graphs. Add a new isolated vertex with a full list to each side. This preserves the answer and ensures that both sides are nonempty and each side has a list of size three. [Kratochvíl, Precoloring Extension with Fixed Color Bound](https://www.iam.fmph.uniba.sk/amuc/_vol-62/_no_2/_kratoch/kratochv.html)

Use the row index $0$ and indices $(a,c)$ for $a\in A,c\in L(a)$. Use the column index $0$ and indices $(b,c)$ for $b\in B,c\in L(b)$. Over $\mathbb F_p$, let $\mathcal L$ be the matrix space defined by
$$
 \sum_{c\in L(a)} M_{(a,c),0}=M_{00}\quad(a\in A),\qquad
 \sum_{c\in L(b)} M_{0,(b,c)}=M_{00}\quad(b\in B).
$$
Impose the interior zeros $M_{(a,c),(b,c)}=0$ for $ab\in E$ and $c\in L(a)\cap L(b)$. All other interior entries are free.

Put $\mathcal L_0=\{M\in\mathcal L:M_{00}=0\}$. Its basis consists of the allowed interior matrix units and one zero-sum difference basis on each list on the border. More explicitly, for a chosen color $c_a\in L(a)$, the column-border generators are $E_{(a,c),0}-E_{(a,c_a),0}$ for $c\ne c_a$. The row-border generators use the same construction on each $b$'s list. All these generators have rank one and are independent because their blocks have disjoint entries except for the fixed reference position within a zero-sum list. They span the full border with $M_{00}=0$. Extend this basis by the matrix
$$
 J=\begin{pmatrix}1&v^{\mathsf T}\\ u&0\end{pmatrix},
$$
where $u,v$ put one $1$ at the chosen color of each left and right vertex. This matrix satisfies the constraints and has rank exactly two, since $u$ and $v$ are both nonzero. In particular $\mathcal L_0$ has codimension one in $\mathcal L$.

A rank-one $M=xy^{\mathsf T}$ with $M_{00}\ne0$ has both $x_0,y_0\ne0$. Divide $x$ by $x_0$ and $y$ by $y_0$. Each normalized list now sums to one and has nonempty support. The edge zeros give $x_{(a,c)}y_{(b,c)}=0$ for each shared edge color. Choosing one nonzero color from each list therefore gives a proper list coloring. Conversely a list coloring gives such a rank-one matrix by putting $x_0=y_0=1$ and a single $1$ on each chosen color. Thus, with $d=\dim\mathcal L$ and $r$ the dimension of the span of all rank-one matrices in $\mathcal L$,
$$
 r=\begin{cases}
 d & \text{if the graph is list colorable},\\
 d-1 & \text{otherwise}.
 \end{cases}
$$
The basis of $\mathcal L_0$ also shows that $\mathcal L_0$ has zero common left and right kernels. Each nonzero-index row occurs in an allowed matrix unit in a new isolated right vertex's columns. Every nonzero-index column occurs in an allowed matrix unit in a new isolated left vertex's rows. After all these coordinates vanish, the column-zero and row-zero difference matrices each detect the remaining zero-index coordinate on the relevant side. Hence $\mathcal L$ also has zero common left and right kernels.

## 2. Convert matrix rank to the precise least orbit cost

Let $X,Y$ be the row and column vector-coordinate spaces and $W=\mathcal L^*$. Define a bilinear map $m:X\times Y\to W$ by $m(x,y)(M)=x^{\mathsf T}My$. On $X\oplus Y\oplus W$, use the product
$$
 (x,y,w)(x',y',w')=(x+x',\,y+y',\,w+w'+m(x,y')).
$$
Bilinearity gives associativity and the commutator is $m(x,y')-m(x',y)$. The evaluations on standard basis pairs span $W$, so the derived group is $W$. The common left and right kernels of $\mathcal L$ are zero, so the center is $W$ as well. The $k$-th power has first two coordinates $kx,ky$ and central coordinate $kw+\binom{k}{2}m(x,y)$. It follows that the exponent is $p$ for odd $p$ and divides four for $p=2$. In the binary case a nonzero evaluation gives an element with nonzero square, so the exponent is four.

Fix a nonzero central character $\lambda:W\to\mathbb F_p$, identified with its matrix $M\in\mathcal L$, and write $s=\operatorname{rank}M$. For a point stabilizer $H$ whose intersection with $W$ is $\ker\lambda$, its image $U\subset X\oplus Y$ is isotropic for the scalar alternating commutator
$$
 \beta_\lambda((x,y),(x',y'))=x^{\mathsf T}My'-{x'}^{\mathsf T}My .
$$
This form has rank $2s$. Quotienting by its radical proves $\dim U\le\dim X+\dim Y-s$, so $[G:H]\ge p^{s+1}$. The subgroup given by $X\oplus\ker M\oplus\ker\lambda$ attains this index. For its closure, $x^{\mathsf T}My'=0$ whenever $y'\in\ker M$, so the central cocycle takes values in $\ker\lambda$. This gives the matching upper bound in every characteristic, including when the binary group has exponent four.

The action for the mark can be printed without expanding the full group. Factor $M$ over $\mathbb F_p$ as $x^{\mathsf T}My=f(x)\cdot g(y)$ with $f:X\to\mathbb F_p^s$ and $g:Y\to\mathbb F_p^s$ surjective. The quotient map
$$
 (x,y,w)\longmapsto(f(x),g(y),\lambda(w))
$$
takes values in the group with cocycle $u\cdot v'$ on $\mathbb F_p^s\oplus\mathbb F_p^s\oplus\mathbb F_p$. This group has order $p^{2s+1}$ and one-dimensional center. Its action on the cosets of the first coordinate space is faithful and has $p^{s+1}$ points. Indeed that subgroup meets the center trivially, and every nonidentity normal subgroup of a finite $p$-group meets the center nontrivially. The pullback to $G$ has kernel meeting $W$ exactly in $\ker\lambda$.

For each basis matrix from Section 1, print that pullback action on the coordinate generators of $G$ and take the disjoint union. Because the basis characters span $W^*$, the union is faithful by the same central-intersection property. All the quotient tables involved have at most $p^5$ elements, a constant at fixed $p$. The number of basis matrices and coordinate generators are polynomial in the original graph size. There is exactly one $p^3$-point orbit from $J$, and all other orbits have $p^2$ points.

## 3. Optimize over every possible action

For any finite $p$-group, let $S=Z(G)[p]$. A union of coset actions is faithful precisely when the intersections of its point stabilizers with $S$ meet trivially. One direction holds because $S$ is central. For the other, every nontrivial normal subgroup meets the center by the class equation for conjugation on that subgroup and contains some central element of order $p$.

Among optimal faithful actions choose one with as many orbits as possible. For a stabilizer $H$ with $D=H\cap S$ of codimension at least two in $S$, choose two nonzero complementary subspaces of $S/D$ and lift them to $S_1,S_2$. Replace $H$ by $HS_1,HS_2$, whose intersections with $S$ are respectively $S_1,S_2$ and whose common intersection in $S$ is $D$. Both replacement indices are at most $[G:H]/p$. Thus their combined index is at most the old index, and there are more orbits in case of equality. This rules out the original orbit even for $p=2$. An orbit with $D=S$ can simply be removed. The remaining intersections are hyperplanes, with independent defining marks because a dependent mark's orbit can also be removed. The marks therefore form a basis of $S^*$. This is the central socle argument for minimum actions, including the equality case relevant to central involutions. [Elias, Silberman and Takloo-Bighash, Minimal Permutation Representations of Nilpotent Groups, §3](https://www.math.uic.edu/~rtakloo/papers/group-paper/delta.12.pdf)

For the constructed groups $S=W$. Every basis of marks has at most $r$ rank-one vectors, whose least cost is $p^2$, and each other vector costs at least $p^3$ by Section 2. A basis of the rank-one span can be completed with vectors from the supplied rank-at-most-two basis, attaining this bound. Accordingly,
$$
             \mu(G)=p^2 r+p^3(d-r).
$$
The graph is colorable if and only if $\mu(G)\le p^2d$.

The same equivalence holds for the orbit-bound question. Rank-one marks spanning $W^*$ supply a faithful union of $p^2$-point orbits. Conversely, given any faithful action on orbits of size at most $p^2$, its stabilizer intersections with $W$ have annihilators spanning $W^*$. For each nonzero $\lambda$ killing $H\cap W$, the subgroup $H\ker\lambda$ has mark $\lambda$ and index at most $[G:H]$. The orbit-cost bound implies $\operatorname{rank}M_\lambda=1$. Hence the rank-one marks span $W^*$, which implies the graph is colorable.

For membership in NP, use the published upper bound for the degree decision with permutation generators. A certificate for the orbit-bound variant gives images of the input generators as permutations on at most $p^2\dim S$ points. A faithful action meeting the bound can always be trimmed to that size, by the mark construction in Section 4. Standard permutation group algorithms compute a polynomial-length presentation on a strong generating set, together with straight-line translations between it and the input generators. Verify its relations on the proposed images, verify all orbit sizes, and compare the order of the image with the given group's order to check faithfulness. The input promises themselves can be checked in polynomial time. Test exponent dividing $p$, or four for $p=2$, using the generators and central commutators, and use constructive membership after computing the center to test $Z(G)=[G,G]$. [Kantor and Luks, Computing in Quotient Groups, §13 Problem 1](https://pages.uoregon.edu/kantor/PAPERS/quotient.pdf#page=9) · [Levet, Srivastava and Thakkar on Min-Per-Deg](https://arxiv.org/html/2501.16039v4#S1) · [Seress, Permutation Group Algorithms](https://doi.org/10.1017/CBO9780511546549)

Finally delete the $J$ orbit. The kernel of the surviving action is the common kernel of the basis quotient maps for $\mathcal L_0$. Its tangent part is zero by the common-kernel calculation in Section 1, and its central part is the annihilator of $\mathcal L_0$, which is a line. The quotient therefore again has center equal to derived group of dimension $d-1$ and its surviving action on $p^2(d-1)$ points is optimal by the marked orbit bound. The yes and no costs for the original extension are exactly $p^2d$ and $p^2d+(p^3-p^2)$.

## 4. A polynomial algorithm when all supplied orbits have size at most $p^2$

Let $G$ be any permutation $p$-group whose supplied orbits have at most $p^2$ points. Put $S=Z(G)[p]$, $s=\dim S$, and $a=\dim_{\mathbb F_p}\operatorname{im}(S\to G/\Phi(G))$, where $\Phi(G)=G^p[G,G]$. Then
$$
                            \mu(G)=pa+p^2(s-a).
$$
An index-$p$ subgroup has a normal cyclic quotient, so its mark lies in the image of $(G/\Phi(G))^*\to S^*$. Every nonzero mark in that image is realized by such a subgroup. This gives exactly $a$ independent cheap directions. Every other basis direction costs at least $p^2$, since orbit sizes are powers of $p$. The supplied faithful action shows sufficiency. For each supplied orbit stabilizer $H$, take a basis of the annihilator of $H\cap S$. Every basis mark can be realized by $H\ker\lambda$ at index at most $p^2$. All these annihilators together span $S^*$. Extend a basis of the $a$ index-$p$ marks with marks from these bases and print their coset actions.

The construction is polynomial. Standard permutation-group algorithms compute a base and strong generating set, the center, orbit stabilizers and constructive membership. Since the center has exponent at most $p^2$, abelian coordinates and their $p$-torsion use collection and linear algebra. Compute $\Phi(G)$ by taking the normal closure of the generator $p$-th powers and generator commutators. Closing under generator conjugation and adjoining only elements outside the running group gives at most $\log_2|G|$ strict enlargements, and each uses polynomial-time membership. This gives the elementary abelian quotient and the map from $S$. Each orbit's kernel on the abelian $S$ computes its stabilizer intersection by elementary abelian coordinates, or by evaluating its generators on that orbit, which has constant size. Finally every needed coset action has at most $p^2$ points, so enumerate its cosets using subgroup membership and print the associated permutation generators. [Seress, Permutation Group Algorithms](https://doi.org/10.1017/CBO9780511546549)

The gap in the classification comes from the displayed action itself. At the next $p$-power above $p^2$, allowing just one orbit of that size suffices for NP-completeness. At $p=3$ this is a single 27-point orbit added to 9-point orbits of a faithful quotient action, and at $p=2$ it is a single 8-point orbit added to 4-point orbits. The original overall NP-hardness reduction encoded low-rank directions using nontrivial $p$-th powers at odd $p$. The bipartite list-coloring space makes all but one of the basis directions rank one, allowing the same optimization obstruction to be carried by the commutators of a group of exponent $p$. Focused literature searches located the general central socle method and the published algorithms for Fitting-free groups. Priority for the one-orbit hardness statement remains unverified.
