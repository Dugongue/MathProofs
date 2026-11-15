# Determinant characters from radical symbols of anchored pencils

Informal mathematics. Work over a fixed finite field $F=\mathbb F_q$. A pencil is a linear map $M:U\to\operatorname{Hom}_F(X,Y)$. A transporter from $M$ to $M'$ satisfies
$$
 M'(fv)=hM(v)g^{-1}.
$$
Its prescribed determinant character is $(\det f)^{a_U}(\det g)^{a_X}(\det h)^{a_Y}=\eta$, with exponents modulo $q-1$ and $\eta\in F^\times$.

The supplied branch data are a paired ordered basis of $W\subseteq U$ and $W'\subseteq U'$, and a prescribed isomorphism $U/W\to U'/W'$. Every marked transporter must realize this pairing and quotient map. The dimensions of $X,Y$ need not agree. All slices may be singular. All finite fields and their extensions below use explicit linear bases.

We construct an endomorphism algebra $B$ of a list of arrows extracted from the radical filtrations of the marked pencil. A computable character-dependent width $b$ is defined below. The marked character question reduces to one ordinary TI instance over $F$, with deterministic time and output size polynomial in the input length and $2^b$. In particular this is polynomial for $b=O(\log L)$ on input length $L$. The construction accepts arbitrary nonsemisimple anchor algebras and does not drop a diagonal block when the characteristic divides its dimension. On an explicit growing family the initial active width is unbounded and the new width is one.

## 1. Align the marked slices and use their radical filtrations

Use the two-vertex representation with arrows $M(w_i)$ of the marked basis. A constructive module isomorphism algorithm either rejects or gives a reference $(g_0,h_0)$ to the ordered target anchor tuple. Pull the target matrix modes back along this reference. The anchored arrows now agree. Let $A\subseteq\operatorname{End}_F(X)\times\operatorname{End}_F(Y)$ be their common endomorphism algebra:
$$
 A=\{(c_X,c_Y):c_YM(w_i)=M(w_i)c_X\text{ for all }i\}.
$$
Before imposing the other slices, the corrected matrix transporters are exactly the pairs of actions of units of $A$. An endomorphism with invertible actions is a unit of $A$, since its inverse obeys the same arrow equations. The known determinants of $g_0,h_0$ account for the first change of frame. The label determinant is prescribed by $W$ and $U/W$, with the known basis ratios, because the unknown shears contribute one.

Compute the Jacobson radical $J$ and the finite-field Wedderburn factors $A/J=\prod_j\operatorname{Mat}_{d_j}(E_j)$. Put $X_r=J^rX$, $Y_r=J^rY$ for $r\ge0$, and extend constantly to negative indices. These subspaces are defined by the $A$-module actions and are preserved by every unit of $A$. Every associated graded is a direct sum of copies of the natural simple modules $V_j=E_j^{d_j}$. Choose matrix-unit frames over $F$, so the same quotient unit $u_j\in\mathrm{GL}_{d_j}(E_j)$ acts on each copy of $V_j$. Let $m_{X,j}$ and $m_{Y,j}$ be their respective total multiplicities over all grades. Every anchor arrow is an $A$-module map, so its degree-zero graded maps are zero between distinct simple factors, and scalar over $E_j$ between copies of $V_j$.

## 2. Read shear-invariant arrows from all other slices

Choose source lifts of a basis of $U/W$ and target lifts of its prescribed image. In the aligned matrix coordinates write the respective slices as $D,D'$. A marked transporter given by a unit $c$ satisfies $c_YD=D'c_X+S c_X$ for some $S\in M(W)$. Hence $c_Y D c_X^{-1}-D'$ is a linear combination of the anchor arrows. We use this on each paired lift independently and keep the original equations in the final instance.

For integer $s\le0$, set
$$
 \mathcal F^s=\{D:D X_r\subseteq Y_{r+s}\text{ for every }r\ge0\}.
$$
Use the largest $s\le0$ with $D\in\mathcal F^s$ as its degree, so the degree is capped at zero. This is computable by linear algebra in a number of tests bounded by the nilpotence lengths. It is invariant under pre- and postcomposition by the two unit actions. Adding an anchor map preserves every negative degree, since the anchor maps belong to $\mathcal F^0$. If the degrees of $D,D'$ differ, a genuine marked transporter is impossible.

For every such pair of common degree $s$, compute its symbol maps
$$
 X_r/X_{r+1}\longrightarrow Y_{r+s}/Y_{r+s+1}.
$$
The indices with negative target degree give a zero grade and can be ignored. These maps are well-defined because $D$ satisfies the filtration inclusion at both $r$ and $r+1$.

* At negative degree the unknown shear vanishes in every symbol. Keep every block between all simple copies as an arrow on the respective $V_j$'s. The matching maps $u_j$ intertwine these arrows exactly.
* At degree zero, keep all blocks between distinct simple factors. For a block on copies of the same $V_j$, regard its matrix $D$ as an $F$-linear endomorphism of the common model $V_j$. It is compared under $E_j$-linear conjugation only up to addition of a scalar $sI$ with $s\in E_j$.

To handle this last case, take the commutator operators
$$
 \operatorname{End}_F(V_j)\longrightarrow\operatorname{End}_F(V_j),
 \qquad D\longmapsto [aI,D]
$$
for the elements $a$ of an $F$-basis of $E_j$. Their joint kernel is $\operatorname{End}_{E_j}(V_j)$. It is complementary to the sum of their images. To see this, extend scalars to an algebraic closure. Separability splits the $E_j$-action into eigenspaces indexed by its embeddings, and a commutator acts by $\sigma(a)-\tau(a)$ on a block from the $\tau$-space to the $\sigma$-space. The diagonal blocks form the kernel. For $\sigma\ne\tau$ some basis element separates them, so the off-diagonal blocks form the sum of images. The kernel and image calculations commute with extension of scalars and are done over $F$. This decomposition is equivariant for conjugation by every $E_j$-linear map. When $E_j=F$ the image component is zero. Write $D=Z+N$ in the kernel and image spaces. The component $N$ is unaffected by scalar shear, so keep it as an $F$-linear arrow.

On each vertex $V_j$, the remaining matrices $Z_i$ lie in $\operatorname{End}_{E_j}(V_j)$. If the field order of $E_j$ is $Q$, use the arrows
$$
 Z_i^{\,Q}-Z_i,\qquad [Z_i,Z_k].
$$
They transform by exact conjugation under the same unit $u_j$. Indeed an added $sI$ commutes with $Z_i$, the $Q$-th power is a characteristic-power on commuting pairs, and $s^Q-s=0$. Independent scalar shifts leave each commutator unchanged. Compute the powers by repeated squaring in $O(\log Q)$ matrix multiplications, where $\log Q=[E_j:F]\log q$. Optionally close the span of these arrows under commutation by every $Z_i$, simultaneously on source and target. Each commutation remains shear-invariant. A paired word basis on the direct sum of the source and target endomorphism spaces bounds the number of retained arrows by the sum of their dimensions. A trace average is unnecessary even if $\operatorname{char} F\mid d_j$.

## 3. Compute the remaining determinant width

Collect all extracted arrows, and add the scalar actions of a basis of each $E_j$ at its vertex. A genuine marked transporter induces an isomorphism of this finite quiver representation in the two inputs. Apply constructive module isomorphism, with vertex projections as operators on $\bigoplus_j V_j$, to compute one isomorphism $(k_j)_j$, or reject. It is a reference for these arrows. Every actual quotient tuple satisfies $u_j=k_j v_j$, where $(v_j)_j$ is a unit of the source endomorphism algebra $B$ of these arrows. No extension of an arbitrary $B$-unit to a marked tensor transporter is needed.

Compute $B/J(B)=\prod_t\operatorname{Mat}_{e_t}(K_t)$. If $\mu_{j,t}$ is the number of copies of the $t$-th natural simple module in the radical grades of $V_j$ as a $B$-module, put
$$
 \alpha_t=\sum_j(a_Xm_{X,j}+a_Ym_{Y,j})\mu_{j,t}
              \pmod {q-1}.
$$
Set $b=\max\{e_t : \alpha_t\ne0\}$, or zero if this set is empty. The character of every actual marked transporter is the known calibration times
$$
 \prod_t \mathrm N_{K_t/F}(\det_{K_t} v_t)^{\alpha_t},
$$
where $v_t$ is the $t$-th simple quotient matrix of its corrected action. Indeed determinants multiply across both $J$-grades and $J(B)$-grades. In every simple module a matrix over $K_t$ has $F$-determinant equal to the norm of its $K_t$-determinant. The first reference contributes the determinants of $g_0,h_0$, and the second reference contributes $\det_F(k_j)^{a_Xm_{X,j}+a_Ym_{Y,j}}$. The label character is already known in this branch. Both filtrations and all multiplicities are computed by linear algebra on the specified finite modules after radical and semisimple decomposition.

## 4. Enforce the character with the same transporter

Keep the original tensor, the paired marks, and the prescribed label quotient map. Tie all associated graded maps to the actual matrix-mode maps by inclusions and quotient maps. In each simple factor choose one copy of $V_j$ in a grade where it occurs, and identify any other occurrences using their $A/J$-module coordinates. Every allowable unit acts by the same $u_j$ in these coordinates, so these links constrain no original transporter further. In the target, use the first reference to attach the same marked grades and copies and the second reference to calibrate their subsequent $B$-module data. In particular the target subspace corresponding to $Z\subset V_j$ in the secondary filtration is its image under $k_j$ in the first reference frame. Attach just one natural simple copy for each $t$ with $\alpha_t\ne0$, and tie its map to the induced true $v_t$ in the calibrated frames. Grades and simple copies are invariant under the appropriate source units, so their maps exist and are forced for each qualifying original transporter.

The exterior algebra over $K_t$ of the chosen simple copy reads its scalar determinant on its top line. The field, finite-field scalar actions, and multiplication maps are supplied in coordinates over $F$. The norm on a determinant line is expressed by the product of conjugate lines using $q$-Frobenius and multiplication maps. The final product of line scalars to the powers $\alpha_t$ is pinned by the known calibration and $\eta$. Every line scale is thus computed from the actual marked transporter. Conversely a system isomorphism restricts to an original marked transporter, with exactly the recorded determinant character. We never require arbitrary solutions to the auxiliary arrow constraints to lift.

For polynomially many linear or bilinear gadgets use labeled direct sums, with the label idempotents pinned in order by a shift and a cyclic vector. Each occurrence of an argument is a block copy linked to its underlying space by the corresponding linear map. Then one blockwise tensor represents an entire list of equations of any one map type. This gives a fixed number of tensors of order at most three to which the published tensor-system compiler applies. All filtration levels, symbols, closure arrows, and module tables have polynomial size in the input before constructing the exterior algebras. Each active exterior algebra has dimension at most $[K_t:F]2^b$ over $F$, and there are only polynomially many of them. This proves the claimed bound.

## 5. A wide active factor in the characteristic that divides its dimension

Take $q>2$, write $p=\operatorname{char}F$, and choose a large integer $d$ divisible by $p$. On $X=Y=F^p\otimes F^d$, use the two marked slices $I$ and $N=N_p\otimes I_d$, where $N_p$ is a length-$p$ nilpotent shift. The third slice is $D=I_p\otimes C$, where $C$ is multiplication by an element $\alpha$ of $F_{q^d}$ for which $\alpha^q-\alpha$ has degree $d$ over $F$. Fix the quotient map on the third label. All slices and marks are distinct, and $I,N,D$ are linearly independent.

For existence, the map $x\mapsto x^q-x$ on $F_{q^d}$ has image of size $q^{d-1}$. The union of proper subfields has size at most $d q^{d/2}$, so the image contains an element of full degree for every sufficiently large $d$. Its preimage also has full degree. The example can be constructed deterministically at fixed $q$. Compute $V=\operatorname{im}(x\mapsto x^q-x)$ and the maximal proper subfields, the latter as kernels of $x\mapsto x^{q^{d/\ell}}-x$ for the prime divisors $\ell$ of $d$. A uniformly random element of $V$ has expected number of memberships in those proper subfields at most $d q^{d/2}/q^{d-1}<1$. Fix the coordinates in a basis of $V$ one at a time. For each of the $q$ choices of a new coordinate, Gaussian elimination counts the intersections of the remaining affine space with the maximal proper subfields, and hence evaluates the exact conditional expectation. Choose a value attaining at most the current expectation. The final nonnegative integer count is less than one, so this constructs a full-degree element of $V$. Obtain $\alpha$ by a linear solve. All counts have polynomial bit length and all fields used here can be constructed deterministically at fixed characteristic.

The initial endomorphism algebra is $\operatorname{Mat}_d(F[\epsilon]/(\epsilon^p))$. Its unique simple factor is $\operatorname{Mat}_d(F)$, occurring $p$ times in each matrix mode. For the requested character $\det g$, the coefficient $p$ is nonzero modulo $q-1$, and this is a genuinely variable determinant: the maps $g=h=I_p\otimes\gamma$ for $\gamma\in F[C]^\times$ realize every value by surjectivity of the field norm and bijectivity of the $p$-th power on $F^\times$.

At degree zero the third slice induces $C$ on each grade, and the unknown $I,N$ shear contributes only a scalar on the grade. Trace subtraction would require division by $d=0$ in $F$. The additional arrow $C^q-C$ is cyclic because it is multiplication by the full-degree element $\alpha^q-\alpha$. Its centralizer is $F[C^q-C]$, a field. For the self-branch the computed $B$ is this field, so $b=1$, with arbitrarily large $d$. The same bound holds for every paired instance admitting an anchor-respecting transporter because its induced arrow systems are isomorphic. Thus the result handles a nonsemisimple starting algebra and an arbitrarily wide active simple factor in a case where the former trace-normalized arrow was unavailable.

## Sources and scope

The constructive module step and finite-field radical computations use [Chistov–Ivanyos–Karpinski](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf) and [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18). The typed compilation uses [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4). The prior paired-slice argument used a second module algebra on split semisimple anchors, with some scalar shifts removed by trace normalization. The argument here constructs shear-invariant arrows from radical symbols, separates linear from non-linear-over-the-center parts by a separable commutator, and handles scalar ambiguity with a characteristic-power polynomial. It proves a sufficient, computable bound for marked branches. Bounded width for arbitrary marked branches and universal production of the branch data remain open.
