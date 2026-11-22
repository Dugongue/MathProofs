# Toric vector bundles realizing parametric tensor flags

A finite loopless quiver representation can be encoded by a single vector bundle on a smooth projective toric surface. Varying only the ample polarization realizes every rational principal-price filtration of the representation as the ordinary slope Harder–Narasimhan filtration of that bundle. Every step is a subbundle, and the shifted slopes recover the exact parametric instability data of matrix tuples. The surface and the equivariant Chern classes depend only on the quiver and dimension vector.

## Statement

Work over an algebraically closed field $k$ of any characteristic. Fix a loopless quiver $Q$ with $m$ arrows and spaces $V_v$ of positive dimension $d_v$. Write $E=\bigoplus_v V_v$ and $D=\dim E$. A representation $A$ assigns a map $A_a:V_s\to V_t$ to each arrow $a:s\to t$. A subrepresentation $U=(U_v)$ satisfies $A_aU_s\subseteq U_t$ for all arrows.

There are a smooth projective toric surface $X$, a torus-equivariant rank-$D$ vector bundle $\mathcal E_A$ on $X$, and an ample rational divisor class $H_\lambda$ for each rational price vector $\lambda$ in the cube $[-1,1]^{Q_0}$ with the following properties.

1. At $H_\lambda$, the slope Harder–Narasimhan filtration has fiber over the torus identity equal to the direct sums of the quiver principal filtration at price $\lambda$. If a quiver graded piece has price slope $b=\sum_v\lambda_v\dim U_v/\sum_v\dim U_v$, the corresponding bundle graded piece has slope $K+b$ for a constant $K$ depending only on $Q$ and $D$. The bundle and the surface are fixed as $\lambda$ varies, and all the graded pieces are locally free.
2. The construction preserves and reflects equivariant isomorphism over the identity of $X$ for the arrow-labeled representations. It preserves the full vertexwise transporter, through the direct-sum identification on the fiber at the torus identity.
3. The equivariant $K$-class, hence the equivariant Chern classes, are constant for the fixed quiver and dimension vector. The construction uses at most $4\max(2,|Q_0|+2m)$ rays. A positive rescaling of any rational price vector puts it in the cube and preserves its principal filtration.

An ample rational class defines slope by intersecting the first Chern class with that class. Clearing denominators gives an ample line bundle and multiplies all slopes by the same positive integer.

## A toric surface with independently prescribed active intersections

Let $q=|Q_0|+2m$. Start with the four rays of the fan of $\mathbb P^1\times\mathbb P^1$. Add opposite pairs of rays until there are $\max(2,q)$ pairs, by star subdividing opposite smooth cones at the sum of their primitive generators. Smoothness is preserved. Make one more star subdivision in every cone, again using the sum of its two generators. Then every new maximal cone has at most one ray from the previous fan. Mark one ray from each of $q$ previous opposite pairs as active, leaving its antipode and all other rays inactive. Thus the active invariant divisors are pairwise disjoint, since invariant divisors of a smooth toric surface meet exactly when their rays bound a cone. The number of rays is the bound in the statement.

Every prescription of positive rational values $\ell_\rho$ at the active rays is realized by a rational ample class with $H\cdot D_\rho=\ell_\rho$. Give each antipodal pair the same prescribed value, taking value one on the remaining pairs. For one primitive vector $v_\rho$ per pair, let $Jv_\rho$ be its primitive perpendicular vector in the dual lattice, obtained by a quarter-turn in lattice coordinates. Take the Minkowski sum of segments $[0,\ell_\rho Jv_\rho]$ over the opposite pairs. In the two directions normal to a particular segment, that segment gives the full edge of the sum, because every other segment contributes a single endpoint. The edges have the prescribed lattice lengths, and there are no other normal directions with a positive-dimensional maximizing face. The polygon is full-dimensional, and its normal fan is exactly the constructed fan. After scaling to a lattice polygon it gives an ample toric line bundle. The degree on an invariant divisor equals the lattice length of the corresponding edge, by restriction of the polygon description to that invariant curve. Dividing by the scale factor proves the intersection claim and shows projectivity of $X$. [Hering, Nill and Süß, slope stability on toric varieties and the facet-volume formula](https://arxiv.org/abs/1910.08848)

## The bundle and its subbundles

Assign the following labeled subspaces $L_\rho$ of $E$ to the active rays. Assign one ray to every $V_v$, and two rays to each arrow $a:s\to t$, carrying respectively
$$
           G_a=\{x+A_ax:x\in V_s\},\qquad
           C_s=\bigoplus_{v\ne s}V_v .
$$
There is a distinct ray for each occurrence of $C_s$. View the following sum as subsheaves in the rationally trivialized vector space:
$$
       \mathcal E_A
       =(\mathcal O_X\otimes E)
         +\sum_{\rho\ {\rm active}}\mathcal O_X(D_\rho)\otimes L_\rho
          \ \subseteq\ k(X)\otimes E .
          \tag{1}
$$
Near any point at most one active divisor occurs. There a complement to $L_\rho$ identifies (1) with a direct sum of $\dim L_\rho$ copies of $\mathcal O_X(D_\rho)$ and $D-\dim L_\rho$ copies of $\mathcal O_X$. This gives a vector bundle and its natural torus action. Its two-step Klyachko filtrations describe the constant directions allowed a simple pole on each active divisor. Formula (1) directly constructs the bundle. [Klyachko, equivariant bundles on toral varieties](https://www.mathnet.ru/eng/im1285)

For any subspace $W\subseteq E$, intersect (1) with $k(X)\otimes W$. Locally choose a basis simultaneously adapted to $W$ and $L_\rho$, which is possible for two subspaces. Then the intersection is a direct summand in the displayed local model, where the pole directions are $W\cap L_\rho$. Hence it is a saturated subbundle $\mathcal F_W$ with locally free quotient, and
$$
  \operatorname{rk}\mathcal F_W=\dim W,\qquad
  \deg_H(\mathcal F_W)=\sum_{\rho\ {\rm active}}(H\cdot D_\rho)\dim(W\cap L_\rho).
  \tag{2}
$$
The degree formula follows by taking determinants of the displayed local lattice. In the rational trivialization these are exactly the orders along the active prime divisors.

Every equivariant saturated subsheaf arises this way. On the torus it is the translation-invariant bundle of a constant subspace $W$ in the trivialization of (1). Saturation determines the subsheaf uniquely by its rational generic fiber. Moreover, the ordinary slope Harder–Narasimhan filtration for an ample polarization is equivariant, by uniqueness and preservation of the polarization by the torus. Thus its steps are among the $\mathcal F_W$. For nested $W\subseteq W'$ the successive subquotient is locally free, since both $\mathcal E_A/\mathcal F_W$ and $\mathcal E_A/\mathcal F_{W'}$ are locally free. [Devey, polarized stability and intersections of Klyachko filtrations](https://arxiv.org/abs/2212.11020) · [Dasgupta, Dey and Khan, stability of equivariant vector bundles](https://ems.press/journals/dm/articles/8965717)

An equivariant map over the identity of $X$ restricts on the torus to a constant linear map in this trivialization. By examining the possible simple poles along each active divisor, this linear map extends exactly when it sends each labeled $L_\rho$ into its counterpart. For an isomorphism it preserves each labeled subspace bijectively. The $V_v$ then make it block diagonal, say $\bigoplus_v g_v$, and the graph conditions become $g_tA_a=A'_ag_s$ for every arrow. These conditions also suffice, since the complementary summands are then preserved. This proves the transporter assertion.

The quotient of (1) by the trivial bundle is the direct sum of $(\mathcal O_X(D_\rho)/\mathcal O_X)\otimes L_\rho$, since the active divisors are disjoint. Consequently
$$
     [\mathcal E_A]
       = D[\mathcal O_X]
         +\sum_{\rho\ {\rm active}}\dim L_\rho
                       \big([\mathcal O_X(D_\rho)]-[\mathcal O_X]\big)
\quad\text{in equivariant }K\text{-theory}.
$$
All the dimensions are independent of $A$, including $\dim G_a=d_s$ for zero arrow maps. This proves the equivariant Chern assertion.

## Matching the complete parametric profile

Take
$$
        M=2D+1,\qquad N=mM+2,\qquad K=N+mM .
$$
Choose $H_\lambda$ with active intersections $N+\lambda_v$ at the $V_v$ rays and $M$ at each $G_a$ and $C_s$ ray, using the polygon above. These are positive. Define $\sigma_\lambda(U)=\sum_v\lambda_v\dim U_v$ and $|U|=\sum_v\dim U_v$. A subspace split across the vertices has form $W=\bigoplus_v U_v$. For that subspace,
$$
\begin{aligned}
 \dim(W\cap G_a)
      &=\dim U_s-\dim((A_aU_s+U_t)/U_t),\\
 \dim(W\cap C_s)
      &=\dim W-\dim U_s .
\end{aligned}
$$
The first identity takes the kernel of $U_s\to V_t/U_t$. Substituting these identities into (2) gives the exact degree formula for split subspaces,
$$
   \deg_{H_\lambda}(\mathcal F_W)
     = K|U|+\sigma_\lambda(U)
           -M\sum_a\dim((A_aU_s+U_t)/U_t).
           \tag{3}
$$

For a general $W$ let $W^\circ=\bigoplus_v(W\cap V_v)$ and $\delta=\dim W-\dim W^\circ$. The coordinate-ray degrees are unchanged upon passage to $W^\circ$. Each of the $2m$ remaining dimensions in (2) drops by at most $\delta$, because $(W\cap L)/(W^\circ\cap L)$ injects into $W/W^\circ$ for every $L$. Thus for $\alpha\in[-1,1]$, replacing a nonsplit $W$ by $W^\circ$ strictly improves the objective $\deg_{H_\lambda}(\mathcal F_W)-(K+\alpha)\dim W$. The improvement is at least $(K+\alpha-2mM)\delta\ge\delta$. A split $W$ with any arrow defect has objective at most $2D-M<0$ by (3), and zero gives objective zero. Hence every maximizer is a split subrepresentation, and on precisely those candidates the objective is
$$
                          \sigma_\lambda(U)-\alpha|U|.
                          \tag{4}
$$
For $\alpha>1$ both problems have the unique maximizer zero, since at $1$ all the surviving objectives are nonpositive. For $\alpha<-1$ both have the unique full-space maximizer. At $-1$ the full space maximizes (4) because its vertex coefficients are all nonnegative, and decreasing $\alpha$ strictly rewards the rank difference between it and any proper competitor. We have proved agreement of maximizers for every real $\alpha$.

For clarity, these maximizers recover the usual slope Harder–Narasimhan filtration of the bundle. Given a filtration with semistable graded pieces of strictly decreasing slopes, intersect any subsheaf with its steps. The associated graded subsheaves have degree at most their rank times the corresponding slope. For a fixed total rank, their total degree is therefore at most the sum of the largest available slopes counted with rank. At a slope threshold, the unique largest-rank saturated maximizer of degree minus threshold times rank is the filtration step including the grades at or above the threshold. Indeed one must fill the full ranks of those grades to attain the maximum at that rank. The resulting subsheaf is contained in that step, and equality of rank and saturation identify it with the step. This argument applies in the same way to the quiver principal filtration. The ordinary bundle filtration is equivariant, so its saturated maximizers are detected by (2). Comparing (4) with its shifted degree objective proves the filtration and slope assertion, including the cases of coinciding slopes within a semistable grade. [Iwamasa, Oki and Soma, principal partitions for quiver representations](https://arxiv.org/abs/2407.06493)

## Recovering a tensor instability invariant from polarization

When $Q$ is layered, the principal slopes $b_i(\lambda)$ and their ranks $e_i(\lambda)$ give the support-function quantity
$$
                   \|\beta_\lambda\|^2=\sum_i e_i(\lambda)b_i(\lambda)^2
$$
in the affine instability theorem for products of vertex special linear groups. By the construction, it can be read from the ranks and shifted slopes of one bundle under varying ample polarization. Rational prices on the cube suffice for the all-price dual gauge, since the support function is continuous on the cube and positively homogeneous. For a rectangular matrix tuple $A:k^u\to k^v$ with the slice mode fixed for the group action, it suffices to use the single price $c=(v,-u)/(u+v)$. With $C=uv/(u+v)$ and $B=\|\beta_c\|^2$, the exact squared positive margin is $B/(C(C-B))$, interpreted as zero when $B=0$. [Parametric subrepresentation flags and the affine margin theorem](https://github.com/Dugongue/MathProofs/blob/main/ParametricConvexFour/Flags.md)

Changing the slice basis of a three-tensor leaves all quiver subrepresentations unchanged, since the slice span is the same. Endpoint basis changes transport the subrepresentation lattice. Thus the polarized Harder–Narasimhan polygons furnished by this construction are invariants under ordinary three-factor tensor isomorphism. The equivariant bundle transporter above refers to the marked arrow list, with the slice basis held fixed. [Grochow and Qiao, tensor isomorphism-completeness](https://epubs.siam.org/doi/10.1137/21M1441110)

For example, take the two $4\times4\times6$ matrix-unit tensors of the prior affine margin theorem. In source-to-target notation their slice positions are
$$
\begin{aligned}
 A&=\{(1,1),(1,4),(2,2),(2,3),(3,1),(4,1)\},\\
 A'&=\{(1,2),(1,4),(2,2),(2,3),(3,1),(4,1)\}.
\end{aligned}
$$
Both have flattening ranks $(4,4,6)$ and maximum and noncommutative matrix ranks three. At the common ample class $H_{(1/2,-1/2)}$, the bundle rank and shifted slope pairs are $(3,1/6),(2,0),(3,-1/6)$ for the first and $(3,1/6),(5,-1/10)$ for the second. Both quivers first take sources $3,4$ and target $1$. For the first quotient the remaining disjoint stars have source and target counts $(1,1)$ and $(1,2)$. In the second quotient each remaining source has two neighbors and together they have three, giving a single semistable grade. For these matrix-unit tuples, the canonical principal steps are coordinate, because uniqueness makes them invariant under the full coordinate torus, which rescales each arrow. The bundle $K$-classes agree, and the common polarization distinguishes the underlying bundles by slope filtration. The exact squared margins recovered from the two polygons are $1/22$ and $1/28$.

When the arrows are matrix units in supplied bases, the whole polarization sweep in (4) has the mincut algorithm of the affine margin theorem. The feasible coordinate subsets are the successor-closed sets of the arrow support graph. Because the extremal quiver subspaces are coordinate, this recovers the ordinary bundle filtration on the stated family of polarizations. [Gallo, Grigoriadis and Tarjan, parametric maximum flow](https://epubs.siam.org/doi/abs/10.1137/0218003)

## Literature and scope

Payne uses Klyachko filtrations to relate equivariant toric-bundle moduli to subspace incidence and establish general singularity phenomena. Devey studies polarized stability in terms of finite subspace configurations and variation of the curve class. The construction here uses a fixed bundle with disjoint active divisors and an ample family to enforce quiver subrepresentations as the exact optimizer sets, realizing their full principal profile as ordinary bundle filtrations. This is a prose proof. Publication priority and Lean verification are unestablished. [Payne, moduli of toric vector bundles](https://arxiv.org/abs/0705.0410) · [Devey, combinatorial stability of toric vector bundles](https://arxiv.org/abs/2212.11020)

An exact finite control compared the complete maximizer sets over all 67 subspaces of the four-dimensional space over the field with two elements. It used all 256 ordered pairs of two-by-two arrow matrices, nine price vectors, and nine thresholds, including values outside [−1, 1]. All 20,736 optimizer comparisons and 6,400 split-subspace defect identities passed. A separate integer check verified smoothness, antipodal edge directions, and prescribed lattice lengths at all 10,228 rays across 71 tested inputs.
