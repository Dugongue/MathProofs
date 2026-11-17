# A one-sign compiler for bounded-order tensor systems

**Theorem.** Work over $\mathbb F_3$. Given two explicit tensor systems of the same signature, whose tensors have order at most three, designate one of their shared vector-space roles. There is a deterministic polynomial-time reduction to one one-sign three-tensor isomorphism instance. Its answer is yes exactly when there is a simultaneous system isomorphism whose map in the designated role has determinant one. In fact the construction preserves the whole menu of relative signs in that role. It accepts any explicit polynomial list of system data of order at most three, even when the number of spaces and maps grows.

Unequal corresponding role dimensions can be rejected before the construction. This upgrades the ordinary tensor-system compiler's decision property for the specific purpose of retaining one physical determinant. It does not remove that determinant. It permits imposing a proved polynomial ordinary lock for one sign and testing a second sign on the same original transporter.

## 1. Put the system into an odd-dimensional bilinear signature

Write the vector-space roles as $V_1,\dots,V_r$ and include the fixed scalar role $V_0=\mathbb F_3$, on which the maps of both systems must act identically. Reinterpret an order-three tensor as a bilinear map by taking the dual on each of its first two slots. Include dual roles where required, and impose ordinary evaluation pairings $V_i^*\times V_i\to V_0$. These pairings make the transformation on a dual role the inverse transpose of the transformation on the original role. For an order-two tensor use a linear map by dualizing its input as necessary, and then regard a linear map $\ell$ as the bilinear map $(x,t)\mapsto t\ell(x)$ with one scalar role. Encode a marked vector $w$ by $(s,t)\mapsto stw$ on two scalar roles, using a dual role when the vector was specified in a dual. A scalar mark has the same interpretation with scalar output. Thus an isomorphism of all the resulting bilinear maps is exactly a system isomorphism.

Replace each even-dimensional nonscalar role, including any dual role if needed, by its direct sum with one scalar line. Extend all existing maps by zero on the new input coordinates and with zero new output coordinate. Add the linear injection of the new line and projection onto its coordinate, in their bilinear interpretations. Fixing the scalar role forces every isomorphism to preserve the old summand and act as identity on the new line. The determinant of the padded designated role therefore equals its determinant in the original coordinates. This also treats a zero-dimensional role if it occurs. All roles now have odd dimension $n_i$, including $n_0=1$.

The system now consists of bilinear maps $\phi_t:V_{i(t)}\times V_{j(t)}\to V_{k(t)}$. The algebra below allows any repeated role among a map's two inputs and output. It also allows zero maps.

## 2. A unital associative algebra carrying all the maps

Begin with primitive idempotent vertices $O,P$ in disjoint left and right levels. For each map $t$ create a private middle vertex $M_t$ and two arrows
$$
O\longrightarrow M_t\colon\ \mathbb F_3e_t\oplus V_i,\qquad
M_t\longrightarrow P\colon\ \mathbb F_3f_t\oplus V_j.
$$
An arrow $a\to b$ denotes the vector subspace in the corner $e_a\,\mathcal R\,e_b$. The common length-two corner $O\to P$ is the space $W=\bigoplus_{i=0}^r W_i$, with $W_i$ a copy of $V_i$. Write $\ell$ for the basis of $W_0$ and $j_i:V_i\to W_i$ for the fixed identification, with $j_0(1)=\ell$. Define the four components of the product in that corner by
$$
e_tf_t=\ell,\qquad xf_t=j_i(x),\qquad e_ty=j_j(y),\qquad
xy=j_k(\phi_t(x,y)).
$$

For each left data arrow, add two scalar arrows from its middle vertex to two private right vertices. Their products with that left data arrow are the corresponding coordinate projections to $V_i$ and to $\mathbb F_3 e_t$, respectively, with copies of these spaces as length-two corners. Use separate right vertices so the two arrows and the two outputs live in distinct corners. For the right data arrow use two scalar arrows from private left vertices to the middle vertex, multiplying on the other side to get the analogous projections to $V_j$ and $\mathbb F_3f_t$. All these private left and right vertices are distinct. Products of any unlisted composable arrows, including between these marker arrows, are zero.

To distinguish each $W_i$ intrinsically, add a probe through a new private middle vertex with arrow spaces $V_i$ and $\mathbb F_3$, whose product is $(x,s)\mapsto sj_i(x)$ in $W$. Use one such vertex for every nonscalar role other than the designated one and two for the designated role. Include two analogous probes with the scalar role and image $W_0$. Each probe has its own pair of arrows and the same endpoints $O,P$. These probes also ensure all of $W$ is in the square of the radical.

Finally, at every vertex $v$ take the diagonal corner to be $\mathbb F_3[\tau_v]/(\tau_v^{N_v})$, with $N_v$ distinct positive integers congruent to $1$ modulo $4$, fixed by the signature and the chosen vertex order. The radical of a diagonal corner annihilates every cross-corner space on both sides. The local identity acts on its incident corners as their appropriate left or right identity. These rules define all products. They make the algebra unital and associative. Products of two cross arrows land in a length-two space and multiplying a third off-diagonal radical element gives zero on either association. Products wholly within a diagonal corner are associative, and positive diagonal degrees annihilate off-diagonal products and factors. The direct sum of positive diagonal degrees and cross corners is a nilpotent ideal, with quotient the split product of copies of $\mathbb F_3$ indexed by the vertices. Hence it is the algebra radical $J$.

The diagonal dimension tags recover the vertex identities up to conjugation by a radical unit. Indeed any algebra isomorphism permutes the primitive coordinate idempotents in the quotient. Let $u_v$ be their actual images in the target and $e'_{\pi(v)}$ the corresponding standard lifts there. The element $z=\sum_v u_v e'_{\pi(v)}$ is congruent to one modulo the radical and satisfies $u_v z=z e'_{\pi(v)}$. Conjugating by $z^{-1}$ normalizes the isomorphism to send every $e_v$ to $e'_{\pi(v)}$. Conjugation by a radical unit acts as the identity on each radical layer and has determinant one. After normalization, a corner maps to its permuted corner, and the diagonal dimensions $N_v$ force the permutation to be the identity. This argument applies to isomorphisms between different endpoint data, not just to automorphisms of a fixed algebra.

## 3. Recover exactly the system maps

A normalized algebra isomorphism preserves each arrow and length-two corner. For each data arrow, the two projection products characterize its two summands as the kernels of multiplying by the two marker lines. Thus its map is block diagonal for that splitting. For the map indexed by $t$, denote by $\alpha_t,\beta_t$ the scales on $e_t,f_t$. Each probe image $W_i$ is preserved, so write $c_i$ for the resulting linear map on $W_i$ in the $V_i$ coordinates. Write $\lambda$ for the scale on $\ell$. Both $\lambda$ and the arrow scales are nonzero. The anchor product yields $\alpha_t\beta_t=\lambda$.

From the other two anchor products, the maps on the left and right variable summands are $\beta_t^{-1}c_i$ and $\alpha_t^{-1}c_j$. The remaining product is preserved exactly when
$$
c_k\phi_t(x,y)=\lambda^{-1}\phi'_t(c_i x,c_j y).
$$
Thus $g_i=\lambda^{-1}c_i$ for all roles gives a simultaneous system isomorphism. The scalar case is $c_0=\lambda$, as required. Conversely take any system isomorphism $g$. Set $\lambda=\alpha_t=\beta_t=1$, use $c_i=g_i$, fix all scalar marker and probe arrows, and use the indicated $g_i$ maps on variable and projection spaces. The marked probe product determines its own variable map as $g_i$. Fix each local corner. These maps define an algebra isomorphism extending $g$. No transporter, gauge choice or auxiliary map needs to be found by the reduction itself.

## 4. Check the determinant on every corner

Use the same ordered arrangement of corners, scalar lines and variable copies at both endpoints, with local bases attached to the system's given coordinate frames. Normalized corner maps compose block-diagonally, since every vertex is fixed. On a diagonal ring, an automorphism sending $\tau_v$ to $\rho\tau_v$ modulo its square has determinant $\rho^{N_v(N_v-1)/2}$. This is one since $N_v\equiv1\bmod4$ and $\rho=\pm1$.

On a left data arrow, the determinant is $\alpha_t\det(\beta_t^{-1}c_i)$. Let $\gamma$ be the scale on the scalar marker arrow that projects to $V_i$, and let $\delta$ be the scale on the scalar marker arrow that projects to the anchor line. The two projective output maps are $\gamma\beta_t^{-1}c_i$ and scalar $\delta\alpha_t$, respectively. Multiplying the determinants of the data arrow, the two markers, and the two projection outputs gives
$$
\alpha_t\det(\beta_t^{-1}c_i)\,
\gamma\det(\gamma\beta_t^{-1}c_i)\,
\delta(\delta\alpha_t)
=\gamma^{1+n_i}=1.
$$
Here the square of every nonzero ground-field determinant is one and $n_i$ is odd. The right data arrow contributes one by the same computation with $\alpha_t,\beta_t$ interchanged and $n_j$ in place of $n_i$. This covers all four auxiliary scalar arrows and all four associated output corners for each data vertex. There are no other present cross corners at those private vertices.

For a probe with role $i$, if the scale on its right scalar arrow is $\beta$, the map on the left arrow must be $\beta^{-1}c_i$. The product of these two arrow determinants is $\beta^{1-n_i}\det c_i=\det c_i$. This applies also to the scalar probes, which each contribute $\lambda$ and jointly contribute one. The corner $W$, counted only once at its common location, has determinant $\lambda\prod_{i=1}^r\det c_i$. All untested roles appear once more through their probes, and the two probes for the designated role $a$ cancel each other. Therefore the full algebra map has determinant
$$
\lambda\det c_a=\lambda^{1+n_a}\det g_a=\det g_a.
$$
This holds even for extensions with all the allowed independent scalar gauges, and the preliminary conjugation by $z^{-1}$ did not change the determinant.

## 5. Convert to one ordinary tensor plus one live sign

Take the multiplication tensors of the two unital associative algebras. Given an isotopy $a(x)b(y)=c(xy)$, put $u=a(1)$ and $v=b(1)$. Evaluating at either unit identifies $c(x)$ with both $a(x)v$ and $u b(x)$. Surjectivity makes $u,v$ units. The linear map $\Phi=L_{u^{-1}}a=R_{v^{-1}}b$ is then a unital algebra isomorphism by the isotopy equation, and
$$
a=L_u\Phi,\qquad b=R_v\Phi,\qquad c=L_uR_v\Phi.
$$
The product of the determinants of these three maps is $\det\Phi$ over $\mathbb F_3$, because each unit multiplication appears twice and $\det\Phi$ appears three times. Conversely each algebra isomorphism is an isotopy with that total sign. Use the existing exact linear sign projection on explicit three-tensor pairs, mapping the total determinant bit to the first physical bit. This preserves the ordinary failure case and makes the resulting one-sign comparison exact.

All spaces have polynomial dimension in the written system size. The number of vertices and cross corners is linear in the number of roles and bilinear maps after padding, and the local tag dimensions are linear in the number of vertices. There is no use of an exterior space in this compiler. Its dense output and all structure constants are computed in polynomial time. The earlier ordinary tensor-system compiler and the earlier exact sign projection are separate dependencies. The former supplies the approach of synchronized shared roles, while the calculation here gives exact preservation of a single designated determinant under a different explicit algebra construction. See [Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2#S4) and [Grochow and Qiao](https://arxiv.org/abs/1907.00309).

## 6. A shared-transporter consequence

Take one arbitrary raw two-sign comparison in which the tested determinant of one mode admits the small adjoint-width lock proved in the accompanying proof. Include its volume mark and all its auxiliary maps as a system containing the original tensor, and designate the other raw tested mode in the compiler above. A positive output is equivalent to one original transporter satisfying both signs: the first sign is forced by the volume mark of that same map, and the second is the designated live determinant. This gives one one-sign instance for the scoped two-sign problem, including cases where the other tested mode is arbitrarily large. The ordered-group refinement of the adjoint-width construction can be used in the same way. This proof is informal.
