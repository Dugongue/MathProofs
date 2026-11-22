# Parametric subrepresentation flags compute affine tensor instability

A parametric maximization over the subrepresentation lattice gives the exact normalized affine Hilbert–Mumford margin of a layered quiver representation under the product of the special linear groups at its vertices. It also determines the unique optimal weighted flags when the margin is positive. For a rectangular matrix tuple the answer is a closed formula in one principal filtration. Applied to three-tensors, this formula gives a tensor-isomorphism invariant that can distinguish inputs with the same three flattening ranks, maximum matrix rank, and noncommutative rank.

## Representation and numerical margin

Work first over an algebraically closed field $k$ of arbitrary characteristic. A quiver representation $A$ has nonzero spaces $V_v$ at its vertices, dimensions $d_v$, and an arrow map $A_a:V_s\to V_t$ for each arrow $a:s\to t$. A subrepresentation $U$ is a tuple of subspaces with $A_a U_s\subseteq U_t$ for every arrow. Assume the representation has at least one nonzero arrow map. A grading $h$ consists of rational heights $h_v$ with $h_t-h_s=1$ on every arrow.

The action is $A_a\mapsto g_t A_a g_s^{-1}$, with $g_v\in\operatorname{SL}(V_v)$. A cocharacter has integral weights $w_{v,i}$ in eigenbases, with $\sum_i w_{v,i}=0$ at each vertex. Its norm is $\|w\|=(\sum_{v,i}w_{v,i}^2)^{1/2}$. Write $\mu(A,w)$ for the least $w_{t,j}-w_{s,i}$ over all nonzero entries of all arrow matrices in these bases. The positive normalized margin is the supremum of $\mu(A,w)/\|w\|$ over cocharacters with $\mu(A,w)>0$, with value zero if there are none. This is positive exactly on the affine null cone, by Hilbert–Mumford. [Kempf, Instability in invariant theory](https://annals.math.princeton.edu/1978/108-2/p04)

Set
$$
  D=\sum_v d_v,\qquad
  c_v=D^{-1}\sum_u d_u h_u-h_v,\qquad
  r_v=d_v c_v,\qquad C=\sum_v d_v c_v^2.
$$
For a real price vector $\lambda=(\lambda_v)$, take the principal filtration by slope
$$
             \frac{\sigma_\lambda(U)}{|U|}
       = \frac{\sum_v\lambda_v\dim U_v}{\sum_v\dim U_v}.
$$
The construction and its proof appear below. Write $\beta_\lambda$ for the weight vector that assigns each graded block its slope, repeated according to that block's total dimension. Define
$$
 \Gamma=\inf\{t\ge 0:\ \lambda\cdot r\le t\|\beta_\lambda\|
                             \text{ for all real }\lambda\}.
 \tag{1}
$$
The infimum is infinite if the set is empty. Equivalently, $\Gamma$ is the nonnegative supremum of $\lambda\cdot r/\|\beta_\lambda\|$, with value infinite when a zero denominator has positive numerator.

**Theorem.** If $\Gamma$ is infinite, the margin is zero. Otherwise $\Gamma^2>C$, and the margin is attained and equals
$$
                           \frac{1}{\sqrt{\Gamma^2-C}} .
 \tag{2}
$$
After scaling to least arrow exponent one, all maximizing cocharacters induce the same vertexwise weighted flags. The weights at this normalization are rational, so clearing denominators gives an integral cocharacter. If the input is defined over a perfect subfield of $k$, the optimal flags and a splitting cocharacter can be taken over that subfield.

## Principal filtrations and their support function

For a fixed $\lambda$, among nonzero subrepresentations choose one of maximum slope, then of maximum total dimension among these. Call it $F_1$. It is unique and contains every maximizer, since dimension and $\sigma_\lambda$ are modular under sum and intersection. Specifically, if two nonzero subrepresentations have maximal slope $b$, their sum also does, because the excess of their intersection over slope $b$ is nonpositive. Iterate in the quotient. This gives a canonical chain $0=F_0\subset F_1\subset\cdots\subset F_m=V$ with strictly decreasing slopes $b_i$ on its successive quotients. A next slope at least $b_i$ would give a preimage contradicting either the maximal slope or maximal dimension used to construct $F_i$. By construction, a subrepresentation of $F_i/F_{i-1}$ has $\sigma_\lambda$ at most $b_i$ times its dimension.

A weighted flag at each vertex is equivalently a decreasing family of superlevel subspaces $U_v(x)$ indexed by real $x$, with finitely many distinct real weights. Call such a tuple $q$ admissible if every superlevel tuple is a subrepresentation. In adapted bases, this means $q_{s,i}\le q_{t,j}$ on each nonzero arrow entry. Denote by $m(q)_v=\sum_i q_{v,i}$ the vertex sums. The norm and sums depend only on the weighted flags. Assigning the slope $b_i$ to the quotient $F_i/F_{i-1}$ makes $\beta_\lambda$ admissible. It satisfies
$$
        \lambda\cdot m(\beta_\lambda)=\sum_i b_i^2 |F_i/F_{i-1}|
                                      =\|\beta_\lambda\|^2.
 \tag{3}
$$

For any subrepresentation $U$ of total dimension $s$, its induced filtration embeds the graded pieces into the $F_i/F_{i-1}$. Applying their slope inequalities bounds $\sigma_\lambda(U)$ by the sum of the $s$ largest entries of $\beta_\lambda$. Indeed, if the dimensions of the induced pieces are $e_i$, then $0\le e_i\le |F_i/F_{i-1}|$ and $\sum e_i=s$. The bound $\sum b_i e_i$ is largest when available positions with larger slopes are filled first. The total at $s=D$ equals $\sigma_\lambda(V)$. This also proves the parametric characterization. The largest maximizer of $\sigma_\lambda(U)-\alpha |U|$ is the superlevel subrepresentation of $\beta_\lambda$ containing the grades with slope at least $\alpha$. The upper bound on the objective is attained by that subrepresentation, and any maximizer of the same dimension must fill exactly those grades. Then its intersections with the $F_i$ imply it equals the corresponding $F_i$. [Iwamasa, Oki and Soma, principal partitions and Harder–Narasimhan algorithms](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.99/LIPIcs.ICALP.2025.99.html)

For an arbitrary admissible $q$, sort its weights in decreasing order as $z_1\ge\cdots\ge z_D$. Express $\lambda\cdot m(q)$ as $z_D\sigma_\lambda(V)$ plus the sum of consecutive gaps in the $z_j$ times $\sigma_\lambda$ of the associated superlevel subrepresentations. Each gap is nonnegative. The preceding bound, with equality at dimension $D$, gives
$$
                 \lambda\cdot m(q)
                 \ \le\ \langle\beta_\lambda^\downarrow,z\rangle
                 \ \le\ \|\beta_\lambda\|\|q\|.
 \tag{4}
$$
The second inequality is Cauchy–Schwarz, and the arrow over $\beta_\lambda$ denotes decreasing order. If $\|\beta_\lambda\|>0$, the admissible flag with weights $\beta_\lambda/\|\beta_\lambda\|$ attains equality by (3).

## Proof of the affine margin theorem

Let $K$ be the set of $m(q)$ for admissible $q$ with $\|q\|\le1$. It contains zero. Two flags on one vector space have a simultaneous adapted basis. One construction chooses, for each pair of ascending flag steps, a complement of the sum of the two preceding intersections inside the intersection of the current steps. The chosen vectors span each intersection by induction. The sum of the dimensions of all chosen complements telescopes to the full dimension, so the chosen vectors form a basis. Use such a basis at every vertex for any two admissible tuples. Convex interpolation of their weights retains all arrow inequalities in those bases and retains the unit norm bound. Its vertex sums also interpolate, so $K$ is convex.

For compactness, there are finitely many binary support patterns of all arrow matrices in all possible bases. For each attainable pattern, the unit-ball weight vectors satisfying its weak arrow inequalities form a compact set. The images of these sets under the vertex-sum map cover $K$, hence $K$ is compact. Equations (3)–(4) identify its support function with $\|\beta_\lambda\|$. The separating-hyperplane characterization of $tK$ now gives (1) as the least norm of an admissible weighted flag with vertex sums $r$, interpreted as infinite if no flag reaches $r$.

Normalize a proposed positive cocharacter to least arrow exponent one. In any vertex eigenbases put $q_{v,i}=w_{v,i}+c_v$. The identity $c_t-c_s=-1$ gives
$$
     w_{t,j}-w_{s,i}\ge 1
     \quad\Longleftrightarrow\quad q_{t,j}\ge q_{s,i}.
$$
Tracelessness is equivalent to $m(q)=r$. For such flags,
$$
        \sum_{v,i}(q_{v,i}-c_v)^2=\|q\|^2-C .
$$
Thus a least-norm admissible flag with sums $r$ gives an optimal cocharacter after shifting by $-c$. Its norm squared is strictly positive because setting every shifted weight to zero violates the arrow condition on a nonzero entry. At the optimum the least arrow exponent is one. If all exponents were greater than one, shrinking the shifted weights would improve the norm while retaining the constraints.

Existence when $\Gamma$ is finite follows from compactness, or from minimizing over the finitely many support patterns. In a basis for a minimizing pattern, the admissible affine set is described by rational equalities and inequalities. The least-norm point is rational because it is the orthogonal projection of zero onto the affine hull of the face whose relative interior contains it. That affine hull is defined by the vertex sums and the tight rational arrow inequalities. Clearing denominators gives the promised cocharacter. If two distinct tuples minimized the norm, their coordinate arrays in a common adapted basis would differ, and averaging would strictly decrease squared norm while preserving the vertex sums. This proves uniqueness of the weighted flags. Over a perfect field their unique geometric values are invariant under its absolute Galois group. Each constituent subspace descends, for example by normalizing a nonzero Plücker coordinate to one. Rational weights and bases adapted over the ground field give the descent claim.

The argument also applies to any rational $h$ strictly increasing on all arrows if the least exponent is measured after dividing each arrow's exponents by its positive height difference $h_t-h_s$. The normalization then imposes an arrow-dependent lower bound $h_t-h_s$, and the same shift removes it.

## Rectangular matrix tuples and tensor isomorphism

For parallel arrows from dimension $m$ to dimension $n$, use heights $0,1$, price vector $c=(n,-m)/(m+n)$, and $C=mn/(m+n)$. Let $B=\|\beta_c\|^2$. The total sum of the entries of $\beta_c$ is zero, because $\sigma_c(V)=0$. Equation (3), together with $c_s-c_t=1$, gives $m(\beta_c)=(B,-B)$, while $r=(C,-C)$. If $B=0$, (4) rules out the required vertex sums. If $B>0$, $(C/B)\beta_c$ has those sums and attains the bound from (4). Therefore $\Gamma^2=C^2/B$ and the squared affine margin is
$$
                  \frac{B}{C(C-B)} .
 \tag{5}
$$
Here $0<B<C$ follows from the strict inequality in the theorem. The formula computes the unique optimal weighted flags using a single principal filtration.

A rectangular matrix tuple is a three-tensor with a supplied basis in its slice mode. Changing that basis by an invertible matrix leaves the subrepresentation lattice unchanged, because the old and new slices span the same matrix space. Changes of bases at the endpoint spaces transport the whole lattice and its dimension function. Thus (5) is invariant under ordinary three-tensor isomorphism in the sense studied by Grochow and Qiao. The weights optimize the action on the two endpoint spaces. [Grochow and Qiao, Tensor Isomorphism-Completeness](https://epubs.siam.org/doi/10.1137/21M1441110)

For a separation, take $4\times4$ matrix-unit slices at the pairs below, with each listed pair giving one independent slice. Use row indices for sources and column indices for targets.
$$
\begin{aligned}
 A&=\{(1,1),(1,4),(2,2),(2,3),(3,1),(4,1)\},\\
 A'&=\{(1,2),(1,4),(2,2),(2,3),(3,1),(4,1)\}.
\end{aligned}
$$
Both tensors have flattening ranks $(4,4,6)$. Two sources numbered $3,4$ map into target $1$, so the rank of every matrix in a size-$d$ blow-up is at most $3d$. Each support has a matching of size three, so its maximum matrix rank and its noncommutative rank are both three. In the first tuple the principal filtration has successive sizes and slopes $(3,1/6),(2,0),(3,-1/6)$. The first block contains sources $3,4$ and target $1$. On the quotient, source $1$ and target $4$ give the second block. In the second tuple the same first block leaves a semistable block of size five and slope $-1/10$. For the latter quotient, either single source has two neighbors, and the pair has three. In the first tuple's quotients the same slope comparisons follow from the pair of remaining independent stars. The coordinate computation is exact by the next section. Hence $B=1/6$ and $B'=2/15$ and the squared margins are $1/22$ and $1/28$.

## Parametric minimum cuts on a coordinate class

Suppose each arrow, in given bases, is zero or a scalar multiple of a single matrix unit. The diagonal torus in those bases stabilizes the subrepresentation lattice because it rescales each arrow by a nonzero scalar. By uniqueness, that torus fixes the price filtration and the optimal weighted flags. Every subspace fixed by the full diagonal torus over an algebraically closed field is coordinate. This follows by applying to a vector a diagonal matrix with pairwise distinct coordinate eigenvalues and taking the polynomial spectral projectors. Thus the coordinate calculation is exact for the full product of special linear groups at the vertices.

Make a directed graph on basis coordinates, with an arc for each nonzero matrix entry. A coordinate subrepresentation is a successor-closed set. For fixed $\lambda,\alpha$, give a basis coordinate at vertex $v$ weight $\lambda_v-\alpha$. The principal step maximizes total weight over these closed sets. Add a source arc into each coordinate of positive weight with capacity equal to its weight, an arc to a sink for each negative weight with capacity its absolute value, and a capacity larger than the sum of all absolute weights for every closure arc. Each minimum cut has a closed source side, and its capacity is the sum of positive weights minus the weight of that side. The largest source-side minimum cut is the required maximal optimizer. Sweeping $\alpha$ gives a monotone parametric cut instance, with large closure capacities fixed over a bounded interval containing all slopes. In particular the ordinary rectangular score uses a single such profile. For any number of vertices, one can also compute the attained margin and the cocharacter by solving the rational convex quadratic program in the supplied coordinates. Its constraints are the vertex sums and the weak arrow inequalities, and its objective is squared norm. The diagonal-torus argument establishes correctness for unrestricted flags. The exact convex quadratic programming result gives polynomial bit complexity on this class. [Gallo, Grigoriadis and Tarjan, parametric maximum flow](https://epubs.siam.org/doi/abs/10.1137/0218003) · [Kozlov, Tarasov and Khachiyan, exact convex quadratic programming](https://www.mathnet.ru/eng/zvmmf5189)

A three-layer example illustrates why (1) uses multiple prices. Give each layer dimension two and use arcs from both coordinates of layer zero to the first coordinate of layer one, plus an arc from the second coordinate of layer one to the second coordinate of layer two. Here $c=(1,0,-1)$, $r=(2,0,-2)$, and $C=4$. For price $c$, the slopes on the three-coordinate incoming star are all $2/3$, on the remaining edge both $-1/2$, and on the isolated coordinate $-1$. Thus $\|\beta_c\|^2=17/6$ and its squared lower bound on $\Gamma$ is $96/17<6$. Price $(2,-1,-1)$ gives slope one on the star and minus one on all other coordinates. This flag has sums $r$ and squared norm six, and its price bound attains that norm. Thus the exact squared affine margin is $1/2$.

## Literature and scope

The Harder–Narasimhan filtration and its relation to character instability are classical. Zamora identifies it with a Kempf filtration, Iwamasa, Oki and Soma compute it via principal partitions, and Müller treats admissible filtrations of hyperquiver representations under character-linearized affine GIT. Here all vertex sums are fixed simultaneously by the determinant-one constraints, and the objective is the least arrow exponent toward the affine origin. The support-function identity and the height shift turn these constraints into the exact affine margin. The two-vertex formula supplies a numerical invariant for Grochow and Qiao's tensor equivalence. This is a prose proof with publication priority and Lean verification unestablished. [Zamora, Kempf and Harder–Narasimhan filtrations](https://arxiv.org/abs/1210.5475) · [Iwamasa, Oki and Soma, quiver semistability](https://arxiv.org/abs/2407.06493) · [Müller, hyperquiver Harder–Narasimhan filtrations](https://arxiv.org/abs/2610.28028) · [Hamada and Hirai, modular submodularity and noncommutative rank](https://arxiv.org/abs/2012.13651)

An exact finite control compared the principal-filtration formula with direct optimization over all 36 pairs of bases for each of the 15 nonempty 2 × 2 matrix-unit slice sets over the field with two elements. The maximum for each of the 15 inputs agreed with the formula, for a total of 540 basis-pair evaluations. The same control independently recovered the squared margins 1/22 and 1/28 for the two 4 × 4 × 6 tensors, and the squared principal norms 17/6 and 6 for the two prices in the three-layer example.
