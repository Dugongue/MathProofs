# Hexagon holonomy and determinant-one tensor orbits

An alternating product around a weighted hexagon classifies its edge weights up to vertex gauge. A multiplication tensor can also record the square class of the product of the three alternating edges. The square-class refinement is exact over every finite commutative local ring, including rings whose nontrivial square classes all reduce to 1.

## The polygon theorem

Let $R$ be a finite commutative local ring and $U=R^\times$. For $n\ge 2$, put unit weights on the edges of a bipartite cycle $C_{2n}$, with $n$ left vertices and $n$ right vertices. Denote its two alternating perfect matchings by $M_0,M_1$, and put
$$
 \alpha=\prod_{e\in M_0}w_e,\qquad
 \beta=\prod_{e\in M_1}w_e,\qquad
 \lambda=\alpha/\beta.
$$
The construction below associates an associative unital algebra $A(w)$ of free rank $3n^2+8n+4$ and its based multiplication tensor to $w$.

**Theorem.** Ordinary tensor equivalence is exactly equality of $\lambda$ up to inversion. If $n$ is even, ordinary and determinant-one tensor equivalence coincide in this family. If $n$ is odd, determinant-one equivalence is exactly equality of
$$
 \bigl(\lambda,[\alpha]\bigr)\in U\times U/U^2
$$
up to the involution $(\lambda,[\alpha])\mapsto(\lambda^{-1},[\alpha/\lambda])$. The automorphism determinant subgroup is $U$ for even $n$. For odd $n$ it is $U^2$ if $\lambda^2\ne 1$, and $U^2\langle\lambda\rangle$ if $\lambda^2=1$. Its index in $U$ is exactly the number of determinant-one orbits within the full ordinary orbit.

For a hexagon the tensor side is 55. Over $\mathbb F_q$ with $q\equiv3\bmod 4$, an ordinary hexagon orbit splits in two, except when $\lambda=-1$, in which case it stays whole. For a concrete pair over $\mathbb F_3$, start with all weights 1 and then change one edge in each matching to $-1$. Both holonomies are 1 and the two tensors are ordinarily equivalent, with different determinant-one orbits. Over $\mathbb Z/8\mathbb Z$, take $\lambda=3$. The determinant image is exactly $\{1,3\}$, since the unit squares are all 1. Thus a reflected hexagon can contribute a principal unit that is invisible to residue-field correction. Here the ordinary orbit splits into two, compared with four when $\lambda=1$.

## The full bipartite construction

The same construction works for any connected bipartite graph $G$ with equally sized parts and a perfect matching. Take the quiver
$$
 s \ \longrightarrow\ \{L_i\}_{i=1}^n
 \ \longrightarrow\ m\
 \longrightarrow\ \{Q_j\}_{j=1}^n
 \ \longrightarrow\ t.
$$
Write its arrows $a_i,d_i,e_j,c_j$, respectively. The algebra keeps the paths of lengths 0 through 3 as separate basis elements. It has a single further basis element $h$ in the corner from $s$ to $t$, with
$$
 a_i d_i e_j c_j=w_{ij}h.
$$
Here $w_{ij}$ is the unit edge weight or 0 off the support. The ring is the path algebra quotient identifying the free module of length-four paths with $Rh$ by this weight map. That map is onto because some $w_{ij}$ is a unit. Its kernel is a two-sided ideal because the length-four paths start at the source and end at the sink. This proves associativity and the asserted basis. There are $2n+3$ vertices, $4n$ arrows, $2n+n^2$ length-two paths, $2n^2$ length-three paths, and one last basis element.

For a second weight matrix $w'$, fix a colored support-graph isomorphism $\pi=(\sigma,\tau)$ from $G$ to the support of $w'$. Fix any perfect matching $M$ of $G$, and write
$$
 b_\pi=\frac{\prod_{e\in M} w_{e}}{\prod_{e\in M}w'_{\pi(e)}}.
$$
The following two tests are complete. First, there is an isomorphism inducing $\pi$ precisely when the alternating products of the weights agree on every cycle after applying $\pi$. Second, if this test succeeds, its possible determinants are precisely
$$
 (\operatorname{sgn}\sigma\operatorname{sgn}\tau)^n
 b_\pi^{n+2}
 \begin{cases}
 U & n\text{ even},\\
 U^2 & n\text{ odd}.
 \end{cases}                                                    \tag{1}
$$
In particular the determinant-one criterion for odd $n$ is that some holonomy-preserving $\pi$ makes $(\operatorname{sgn}\sigma\operatorname{sgn}\tau)b_\pi$ a square. The test is independent of the chosen perfect matching. For a fixed plane embedding, the alternating products on the bounded face boundaries suffice. Indeed, orient every edge from left to right. The oriented boundary of any simple cycle is the sum of the oriented boundaries of the faces it encloses. The edge-weight products on a spanning-tree set of fundamental cycles also suffice and take polynomial time to compute for any prescribed $\pi$.

## Proof of both tests

The positive-length ideal $J$ is nilpotent. Over the residue field $k$, it becomes the radical of $A(w)\otimes_R k$, since the quotient is $k^{2n+3}$. An $R$-algebra isomorphism therefore permutes the vertex idempotents modulo the residue radical. The quotient by $J$ has coordinates in the local ring $R$, whose only idempotents are 0 and 1. Thus the vertex idempotents are permuted modulo $J$ as well. For any two ordered lifts $f_v,e_v$ of these idempotents, $u=\sum_v f_v e_v$ is congruent to 1 modulo $J$, satisfies $u e_v=f_v u$, and is invertible since $J$ is nilpotent. Conjugation by $u$ has determinant 1. Left and right multiplication by $u$ are unitriangular in the path-length filtration, since $u-1\in J$. After this alignment, the quiver is recovered by the first radical layer over $k$. Its source $s$ and sink $t$ are unique, and distance from the source fixes their ordered layers. This leaves only permutations $\sigma,\tau$ of the two vertex parts.

Each arrow corner is free of rank one. After alignment an isomorphism has arrow scalars $p_i,q_i,r_j,s_j$ in the stated order, and a scalar $H$ on $h$, all units. Put $X_i=p_iq_i$ and $Y_j=r_js_j$. Preservation of length-four products is exactly
$$
 X_iY_j w'_{\sigma(i),\tau(j)}=H w_{ij}.                          \tag{2}
$$
Conversely any such scalars give an algebra isomorphism. They determine the images of all proper paths and the defining relations suffice.

On any even cycle, alternating multiplication and division in (2) cancel the $X_i,Y_j,H$ factors. Conversely for prescribed $H$, choose the scale at one vertex and propagate the required products $X_iY_j$ along a spanning tree. The non-tree edges hold exactly when the fundamental cycle products agree. This proves the first test. For a successful matching $M$, multiplying (2) on $M$ yields
$$
 \left(\prod_i X_i\right)\left(\prod_jY_j\right)=H^n b_\pi,
$$
which also proves independence of $b_\pi$ from the matching once $\pi$ succeeds.

The path basis gives exponents $n+2,3n+2,3n+2,n+2$ on $p_i,q_i,r_j,s_j$, respectively. For example an arrow $d_i$ occurs in itself, in $a_i d_i$, in the $n$ paths $d_i e_j$, and in each of the $n$-element path families $a_i d_i e_j$ and $d_i e_j c_j$. The permutation part contributes $(\operatorname{sgn}\sigma\operatorname{sgn}\tau)^n$. Each left or right label occurs in one vertex family, two arrow families, one individual and $n$ grid families of length two, and $2n$ grid families of length three, giving sign exponent $4+3n$. The resulting determinant is
$$
 \begin{aligned}
 \det\phi
 &= (\operatorname{sgn}\sigma\operatorname{sgn}\tau)^n
    H\Bigl(\prod_i X_i\prod_jY_j\Bigr)^{n+2}
     \Bigl(\prod_i q_i\prod_jr_j\Bigr)^{2n}\\
 &= (\operatorname{sgn}\sigma\operatorname{sgn}\tau)^n
    b_\pi^{n+2} H^{(n+1)^2}
     \Bigl(\prod_i q_i\prod_jr_j\Bigr)^{2n}.
 \end{aligned}
$$
The two final bases can vary independently over $U$. We already showed $H$ arbitrary, and for any $X_i,Y_j$ we can vary $q_i,r_j$ and obtain $p_i,s_j$ by division. The gcd of $(n+1)^2$ and $2n$ is 1 for even $n$ and 2 for odd $n$. Bézout gives (1).

For completeness, ordinary equivalence of multiplication tensors of two unital algebras is equivalent to algebra isomorphism. Given an isotopy $\gamma(xy)=\alpha_0(x)\beta_0(y)$, set $a=\alpha_0(1)$, $b=\beta_0(1)$. The left multiplier $L_a$ and the right multiplier $R_b$ are bijective by the equation. Taking the preimage of 1 and using injectivity gives two-sided inverses for both units. Then $\phi(x)=a^{-1}\gamma(x)b^{-1}$ is an algebra isomorphism, and the determinants of the three legs are
$$
 (\ell\,\det\phi,\ r\,\det\phi,\ \ell r\,\det\phi),
 \qquad \ell=\det L_a,\quad r=\det R_b.
$$
Consequently any determinant-one isotopy produces a determinant-one algebra isomorphism, and such an algebra isomorphism itself supplies all three legs. The left and right multiplier determinants are independently surjective onto $U$. For left determinants, scale only the sink idempotent $e_t$ in a diagonal unit. The only basis path starting at the sink is $e_t$ itself. For right determinants use the source idempotent $e_s$. The stabilizer determinants thus have index $[U:D_{\rm aut}]$ in $U^3$, as is seen by the determinant ratio on the three coordinates. The determinant-one subgroup is normal with quotient $U^3$, proving the orbit count.

Finally, the color-preserving symmetries of a cycle either preserve the two matchings or exchange them. They are rotations by an even step and reflections fixing two opposite vertices. Such rotations have even permutation sign on the $2n$ vertices. The reflections have sign $(-1)^{n-1}$, which is 1 for odd $n$. The sign factor in (1) therefore disappears for every $n$. A matching-preserving symmetry passes the holonomy test exactly when $\lambda'=\lambda$, and its matching product ratio is $\alpha/\alpha'$. A matching-exchanging symmetry passes exactly when $\lambda'=\lambda^{-1}$, with ratio $\alpha/\beta'$. Both types of symmetry exist. This proves the classification and all stated determinant subgroups. A square has even $n$ and always has one special orbit inside each ordinary orbit. The hexagon is the shortest simple even polygon for which splitting can occur.

## Prior work and verification

The use of alternating products for planar dimer gauge equivalence is classical. Kenyon's lectures identify them as coordinates for multiplicative local systems on bipartite graphs. Grochow and Qiao use path algebras and simultaneous idempotent alignment in tensor-isomorphism reductions. The additional result here is the exact path-basis determinant and its matching-product refinement over finite local rings. The proof above is written. Bibliographic priority for this refinement remains open. [Kenyon, Lectures on Dimers](https://arxiv.org/abs/0910.3129) · [Grochow–Qiao, Tensor Isomorphism-Completeness](https://arxiv.org/abs/1907.00309) · [Grochow–Qiao–Stange–Sun, Over Commutative Rings](https://arxiv.org/abs/2611.00735)

The finite control builds the path basis, computes its permutation determinants, and checks every basis product for a witness of each determinant it finds. It covers ten polygon and ring cases. [Finite control](BCheck.py)

The Lean companion checks the hexagon determinant expression, its exact square coset, and the square-class criterion for determinant one. The path-algebra construction and recovery use the written proof above. [Lean source](B.lean)
