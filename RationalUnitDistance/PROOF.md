# Unit-Distance Realizability over the Reals and Rationals

**Theorem.** For an input finite simple graph, the problem of deciding whether it has an injective unit-edge realization in $\mathbb Q^{24}$ is polynomial-time many-one equivalent to Hilbert's tenth problem over $\mathbb Q$. The lower bound holds on graphs that have injective realizations over $\mathbb R$ and over every $\mathbb Q_p$, with squared length given by the sum of 24 coordinate squares. It also holds if rational realizations are allowed to identify nonadjacent vertices.

Here an injective unit-edge realization assigns distinct points to the vertices and requires squared length $1$ on each edge. Nonedges have no length constraint. In particular, the theorem uses the edge-preserving convention and does not require an induced subgraph of the ambient unit-distance graph.

Consequently, under [Glazer's claimed Diophantine definition of $\mathbb Z$ in $\mathbb Q$](https://github.com/elliotglazer/diophantine-z-q), both rational realization problems are halting-complete. Under the same premise they remain halting-complete on a family of graphs of bounded pathwidth, with the same simultaneous local realizability promise. The polynomial-time equivalence itself is unconditional.

This addresses the rational-coordinate counterpart of the fixed-length realizability problem studied by [Schaefer](https://ovid.cs.depaul.edu/documents/realizability.pdf). The real-coordinate hardness results concern a different predicate. [Friedman's rational incidence reductions](https://fomarchive.ugent.be/2009-April/013574.html) concern constraint languages with distinguished points and geometric relations. The construction below uses no pins or labels in the output graph. A targeted search did not identify the stated rational unit-edge theorem in those sources. Publication priority is unverified.

Section 5 also resolves two published real-coordinate questions, giving completeness for every fixed dimension at least two. The notion of Euclidean graph dimension dates to [Erdos, Harary and Tutte, 1965](https://users.renyi.hu/~p_erdos/1965-09.pdf).

## 1. Compile to bounded arithmetic on the intended lifts

Let $f$ be an integer polynomial. Multiply it by
$$
H(u)=(u^2-13)(u^2-17)(u^2-221).
$$
This does not change rational feasibility because none of $13,17,221$ is a rational square. It gives a solution over every completion of $\mathbb Q$. At an odd prime other than $13,17$, if both $13$ and $17$ are nonsquare units modulo the prime, their product is square, and a root lifts by Hensel's lemma. At $13$ use $17$, at $17$ use $13$, and at $2$ use $17\equiv1\bmod 8$. Over $\mathbb R$ the factor $u^2-13$ has a root.

Write the new polynomial as $F(\mathbf x)$. Introduce
$$
w=2v^2-1,\qquad b=w^2,\qquad
b^D F(\mathbf y/b)=0,
$$
where $D=\deg F$ and the last expression is expanded by homogenizing. On every rational solution $b\ne0$, so the gate equations imply $F(\mathbf y/b)=0$. Conversely, for any rational zero of $F$ take rational $v\in(-1,1)$ sufficiently close to $1/\sqrt2$ that $\mathbf y=b\mathbf x$ lies in $[-1,1]^n$. The same choice works for a real zero, keeping $b$ nonzero. Over $\mathbb Q_p$ use $v=0,b=1$ and any local zero. No boundedness will be needed at a finite place.

Compile to gates $a+b=c$, $ab=c$, and constants in $\{0,1,-1,1/2\}$. Over $\mathbb Q$ and $\mathbb R$ the lifts just described can be chosen with all wire values of absolute value at most $4$. Indeed, the bounded values of $b$ and $\mathbf y$ can be used to compute each monomial by repeated squaring. Divide the homogenized polynomial by a power of two at least the sum of the absolute values of its coefficients. The resulting dyadic coefficients have absolute values summing to at most $1$. Build each from its binary digits using additions and halving, and then sum its monomial contributions. All partial sums of contributions have absolute value at most $1$. The few extra gates for $b,w$ stay within the stated bound. This construction takes polynomial time in a standard binary monomial-list encoding, including when exponents are given in binary. If a polynomial is identically zero, its equation may be dropped.

## 2. A fixed palette of squared lengths implements the gates

Decompose the 24 coordinates into four two-coordinate blocks $B_0,B_1,B_2,B_3$ and two eight-coordinate blocks $S_L,S_R$. For each of the following types, unused coordinates in the $B$ blocks are zero. Left vertices have free slack in $S_L$ and zero slack in $S_R$. Right vertices have the reverse assignment. Each vertex in the table must have squared norm $100$.

| Type | Side | Core coordinates |
| --- | --- | --- |
| $L(u)$, a wire | Left | $B_0=(u,1)$ |
| $C_j(u)$, a copy checker | Right | $B_0=B_j=(1,-u)$ |
| $A(a_1,a_2,a_3)$, a gate | Left | $B_j=(a_j,1)$ for $j=1,2,3$ |
| $M(u)$, a multiplier | Right | $B_0=(1,-u),\ B_1=(u,0),\ B_3=(-1,0)$ |

Each row describes an affine subspace together with a norm condition. For an addition gate further impose $a_1+a_2=a_3$ by a linear equation. For a pinned wire impose $u$ equal to its required constant. All of these conditions can be imposed by a finite palette of squared-length edges to anchors. Include the origin and the 24 coordinate unit vectors as anchors. For each linear equation $\ell\cdot P=d$ in the finite list of types include the rational vector $\ell$ as an anchor, identifying coincident anchor vectors. Pin the anchors up to isometry by giving the complete graph on them their actual squared lengths. Add the edges of squared length $100$ to the origin to set the norms. Then the squared length $100+\|\ell\|^2-2d$ from $P$ to $\ell$ imposes the linear equation. This squared length is positive for every constraint in the list. The linear forms have at most three nonzero coefficients of absolute value $1$, and $d$ lies between $-1$ and $1$. Duplicate constraints with the same endpoints and length can be merged.

For an input gate, use one $A$ vertex. For each $j$ use a fresh $C_j$ vertex and join it both to $A$ and to the $L$ vertex of the corresponding wire. Use squared length $200$ for these edges. They impose dot product zero. The two dot products are $a_j-u$ and the wire value minus $u$, respectively. They therefore copy the three wire values into the gate. For a multiplication gate use an extra $M$ vertex. Join it by the same squared length to the $L$ vertex for the second wire and to $A$. The first dot product copies the second wire value into $M$ and the second equals $a_1u-a_3$. The separate slack spaces make no contribution to any of these dot products. This implements multiplication exactly. No other edge between variable vertices is needed.

In a realization over any field of characteristic zero, the full anchor distance matrix allows a normalization by an isometry of the quadratic form. The differences of the coordinate-unit anchors from the origin have Gram matrix $I$, and all other anchor positions follow from their distances to these anchors. Thus a rational realization, even one that is not injective, gives rational gate values satisfying every equation.

Conversely, use any bounded rational or real gate assignment from Section 1. Every core squared norm is less than $100$. The remaining positive squared norm can be represented by four rational squares over $\mathbb Q$ by Lagrange's theorem, after clearing a square denominator, and by real squares over $\mathbb R$. The eight-coordinate slack sphere has Zariski-dense points in either field. For instance, a smooth quadric with a point is parametrized on a dense open by projection from a point. Thus one may choose the slack vectors independently outside any prescribed finite union of proper algebraic conditions.

At a finite place $\mathbb Q_p$, the sum of eight squares is isotropic and contains a hyperbolic plane. To see isotropy, for odd $p$ write $-1$ as a sum of two squares modulo $p$, by intersecting the sets of squares and of $-1$ minus squares, then lift using a nonzero coordinate. For $p=2$, use $-7$ square in $\mathbb Q_2$ and $-1=(-7)+1+1+4$. An isotropic vector and a vector paired nontrivially with it can be modified to span a hyperbolic plane. In hyperbolic coordinates the equation for any required slack norm is $2xy+q'(\mathbf z)=r$. The chart $x\ne0$ has a Zariski-dense set of local points by solving for $y$. In particular this holds even if the required slack norm is zero. It follows that the local gate assignments from Section 1 admit weighted realizations with independently varying slack.

## 3. Remove the prescribed lengths and preserve injectivity

### Unit-edge replacement

Use the finite rational Beckman–Quarles theorem in dimension $24=4\cdot2\cdot3$. For two rational points at a specified nonzero squared distance, there is a finite set of rational points containing them whose unit edges force that squared distance in every unit-edge map into $\mathbb Q^{24}$. See [Zaks, *A discrete form of the Beckman–Quarles theorem for rational spaces*](https://doi.org/10.1007/s00022-001-8581-1) and [Tyszka, Remark 4(2)](https://arxiv.org/pdf/math/9906001#page=9). Tyszka's remark reports the real-target version of the finite statement for these dimensions.

For each squared length in the finite palette choose a template graph and a rational placement supplied by that theorem. All the palette entries are positive rationals, so endpoint pairs exist by the rational four-square theorem. A finite template table can be fixed independently of the input. The stronger real-target form also permits a direct, potentially large table-construction algorithm. Enumerate finite rational point sets with the required endpoints and use real quantifier elimination to check whether their unit constraints admit a real counterexample to the prescribed endpoint distance. Replace each weighted edge by a separate copy of its template, identifying its endpoints with those of the weighted edge. Soundness over $\mathbb Q$ holds for all maps preserving edges, by applying the endpoint theorem to each template and then decoding the weighted graph.

For completeness in any of $\mathbb Q,\mathbb R,\mathbb Q_p$, a rationally placed template can be transported to any pair of points with its prescribed squared distance. After translating the first point, it suffices to carry one vector $a$ to another $b$ of the same nonzero norm. If $a-b$ has nonzero norm, the reflection in its orthogonal hyperplane does this. If it has zero norm and $a\ne b$, then $a+b$ has nonzero norm and reflection in its orthogonal hyperplane sends $a$ to $-b$. Compose with negation. All isometries are over the field in question.

### Avoid all unwanted identifications

First process the finite graph of anchors and its templates in the fixed rational placement. Identify any template vertices whose positions coincide there. This fixed quotient introduces no loop because unit neighbors have distinct coordinates. Each anchor template still enforces its designated length.

For every remaining template, mark its internal vertices that lie on the line of its endpoints in the chosen rational placement. Their transported positions are forced affine combinations
$$
(1-\lambda)P+\lambda Q,\qquad
\lambda\in\mathbb Q\setminus\{0,1\}.
$$
Choose the slack coordinates of all variable vertices at once so that these forced points, the variable vertices themselves, and the already placed anchor graph are pairwise distinct. Only finitely many algebraic equality conditions must be avoided. Each equality involving a nonzero net coefficient of a variable vertex is proper, because that vertex's slack sphere is nonconstant and can vary independently. The remaining possible equalities are handled by the endpoint sets. Two different weighted edges with two variable endpoints have different pairs of variables, and a forced point has a nonzero coefficient at each endpoint. For two edges with a single shared variable endpoint and distinct anchors, equal coefficients at the variable leave a nonzero multiple of the difference of the anchors. Two different forced points of a single template have different coefficients. Each variable vertex itself has coefficient $1$ at that vertex, so it cannot coincide identically with a forced internal point. Weighted edges with the same endpoints have already been merged. These observations rule out identical equalities, and Zariski density of the product of slack spheres gives a choice avoiding all the proper ones.

Now move the off-line internal points of each template by an isometry fixing its endpoints, keeping the already chosen on-line points fixed. They can avoid any prescribed finite set. For details, the difference of the endpoints has nonzero norm, so its orthogonal complement is nondegenerate. Each off-line point has nonzero projection to that complement. There is a skew-adjoint linear map $A$ of the complement that moves all these finitely many nonzero projections. For any given nonzero vector $x$, choose $u$ paired nontrivially with $x$ and a nonzero $v$ orthogonal to $x$. The skew-adjoint map $y\mapsto\langle u,y\rangle v-\langle v,y\rangle u$ moves $x$. Therefore the maps that fail to move any specified projection lie in a finite union of proper subspaces, which can be avoided over any of the infinite fields under consideration. The Cayley transform $(I-tA)(I+tA)^{-1}$ is orthogonal when defined and moves each designated projection nonconstantly as a rational function of $t$, as seen from the derivative at zero. Only finitely many $t$ can send any moved point to a given forbidden point. Extend this isometry by the identity on the endpoint direction. Apply it separately to each template, avoiding all preassigned on-line and anchor points and all previously placed off-line points. The resulting realization is injective.

The graph has size polynomial in the input length because every template in the fixed table has constant size. For the reverse reduction, use 24 rational coordinate variables per vertex and polynomial equations for unit edges. In the injective case impose a multiplicative inverse for the sum of squared coordinate differences for every distinct vertex pair. Over $\mathbb Q$ this sum vanishes exactly at coincidence. Combine all equations by summing their squares. This also shows that both decision problems are computably enumerable.

## 4. A single bounded-pathwidth family

Under the assumed Diophantine definition of the integers, MRDP provides one polynomial $U(T,\mathbf w)$ whose rational solvability in $\mathbf w$, for nonnegative integer $T$, is many-one complete for the halting problem. Multiply by the fixed $H(u)$ above. Instead of using a wire pinned to a potentially large $T$, substitute $T=s^{-1}-2$ and clear a fixed power of $s$. All of the resulting polynomial gates, including the bounded-witness construction, are fixed because $U$ and $H$ are fixed. On the intended rational and real witnesses the new parameter satisfies $0<s\le1/2$ and its value is bounded along with the other circuit inputs.

Write $N=T+2$ in binary with $\ell$ bits $b_0,\ldots,b_{\ell-1}$ in order from least significant to most significant. Starting from $p_0=0,q_0=1$, impose
$$
p_{i+1}=(p_i+b_i)/2,\qquad q_{i+1}=q_i/2,
\qquad p_\ell s=q_\ell .
$$
Then $p_\ell=N/2^\ell$, $q_\ell=2^{-\ell}$ and $s=1/N$. All added wire values on these assignments have absolute value at most $2$. The fixed gate graph for the polynomial and the anchors can be put in every bag of a path decomposition. The growing portion is a chain, with a constant number of gate vertices and wires per bit, using only the preceding and current states and the fixed portion. The final equation connects the last state to the fixed portion. This gives a constant width independent of $T$ for the weighted graph. When an edge is replaced by a template, insert at a bag containing both endpoints a copy of the bag enlarged by all the internal template vertices. The width increases by at most the constant size of the largest template. The same halting reduction, real and local realizations, and injectivity proof therefore hold on this bounded-pathwidth family.

## 5. Two published real-coordinate questions in all dimensions

**Theorem.** For each fixed $d\ge2$, all three problems below are $\exists\mathbb R$-complete.

1. Does the input graph admit an injective unit-edge realization in $\mathbb R^d$?
2. Does it admit a strict unit-distance realization in $\mathbb R^d$, with distance $1$ exactly for adjacent vertex pairs?
3. Does it admit a unit-edge realization in $\mathbb R^d$ when distinct nonadjacent vertices may coincide?

The first and third statements answer the open questions in [Schaefer, Cardinal and Miltzow, *The Existential Theory of the Reals as a Complexity Class*, CG64–CG65](https://arxiv.org/pdf/2407.18006#page=67). The second gives the analogous induced result. These statements do not use any Diophantine assumption. The planar base cases are [Schaefer, Corollary 2.6 and Theorem 3.1](https://ovid.cs.depaul.edu/documents/realizability.pdf). The compendium cites [Saxe's weighted dimension lift, Lemma 4.4](https://citeseerx.ist.psu.edu/document?doi=40c783985abafb4ea653373c0ffbfd76f27ab7a5&repid=rep1&type=pdf). The lift below uses only lengths $1,\sqrt2$ before removing the second length.

### A weighted lift that forces one common normal direction

From a graph $G$ make two copies of its vertex set. Use $x,x'$ for the two copies of vertex $x$. Add a unit edge $xx'$ for every vertex. For each original edge $xy$, add unit edges $xy,x'y'$ and prescribe length $\sqrt2$ on the two crossed pairs $xy',x'y$.

Suppose this graph is realized in $\mathbb R^d$. For each original edge let $v=y-x$, $a=x'-x$, and $b=y'-y$, using the same letters for point positions. The squared norms of $a,b,v$ are all $1$. The crossed lengths give
$$
\|v+b\|^2=\|a-v\|^2=2
\quad\Longrightarrow\quad
v\cdot a=v\cdot b=0.
$$
The copied edge has $\|v+b-a\|^2=1$. Expanding using the preceding identities gives $\|b-a\|^2=0$, so $a=b$. Thus on every connected component of $G$ all copy displacements are the same unit vector, and all original positions lie in one affine hyperplane perpendicular to that vector. Restriction to the originals therefore gives a realization in $\mathbb R^{d-1}$ component by component. The hyperplanes can be identified with a common $\mathbb R^{d-1}$ and the finite components translated apart. This preserves the strict version too, since the components can be separated by more than $1$.

Conversely, start with a realization in $\mathbb R^{d-1}$, place it in the height-zero hyperplane of $\mathbb R^d$, and make the primed copy at height one. This gives precisely the prescribed lengths. In the strict case the two layers retain strictness internally. Any crossed pair belonging to distinct original vertices has squared distance $1$ plus a strictly positive squared distance in the original layer, so the only unit edges across the layers are the vertical edges.

### Use unit edges alone

For the version allowing coincidences, replace each $\sqrt2$ edge by a fixed finite real unit-edge distance-forcing graph in dimension $d$. Such a graph exists by [Tyszka's discrete Beckman–Quarles theorem, Theorem 1](https://arxiv.org/pdf/math/9906001), since $\sqrt2$ is constructible. The theorem applies to arbitrary unit-edge maps, which is required here. Each template can be positioned independently by an isometry taking its two endpoints to the crossed pair. This closes the induction step for unit linkages.

For the injective and strict versions, use the complete $d$-partite graph with two vertices in each part, designating the two vertices of one part as endpoints. This is the graph of the cross-polytope. Its standard unit-edge realization has points $\pm e_i/\sqrt2$. In every injective realization in $\mathbb R^d$, all same-part distances are $\sqrt2$. To verify this, write the two points in part $i$ as $m_i\pm v_i$. Each $v_i$ is nonzero. The four squared distances between two different parts are all $1$, so expanding their differences gives
$$
v_i\cdot v_j=0,\qquad (m_i-m_j)\cdot v_i=(m_i-m_j)\cdot v_j=0 .
$$
The vectors $v_1,\ldots,v_d$ are an orthogonal basis. For each $i$, the projections of all the $m_j$ onto $v_i$ equal the projection of $m_i$, hence the midpoints coincide. The distance constraints now say $\|v_i\|^2+\|v_j\|^2=1$ for every $i\ne j$. Since the target dimension of a lift is $d\ge3$, all these norms squared are $1/2$. The designated same-part distance is $\sqrt2$, as required.

When placed on a crossed pair, every internal point of this template lies on the sphere of radius $1/\sqrt2$ about the pair's midpoint in the orthogonal complement of the endpoint line. The internal points are off the line. Rotate each template about that line, keeping the endpoints fixed. Collisions with earlier points are avoidable. For strictness, take any other already placed point. If it is off the line, its squared distance to any chosen mobile point varies under rotation. If it is on the line, that squared distance is $1/2$ plus the square of the axial displacement from the midpoint. It equals $1$ only at an endpoint, where unit edges are prescribed. Thus unwanted unit distances to earlier points are also avoidable. More formally, in the connected group of rotations of the $(d-1)$-dimensional orthogonal complement, each nonconstant distance condition defines a proper real-analytic zero set, and finitely many such sets have empty interior. Within a template the only nonedges are the same-part pairs of distance $\sqrt2$. This proves strict completeness of the replacement. In the reverse direction, the unprimed layer is unchanged as an induced graph, so a strict realization of the replacement decodes to a strict realization of $G$.

Iterate the lift from dimension two. For each fixed target $d$, every replacement uses fixed finite templates, so the total reduction is polynomial-time. The upper bounds are direct existential real formulas in the coordinates. If Euclidean dimension is posed as equality to $d$ instead of at most $d$, adjoin a disjoint $K_{d+1}$ to the output of the reduction. Its dimension is exactly $d$ and disjoint components can be translated apart.
