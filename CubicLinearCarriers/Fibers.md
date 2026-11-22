# Recover every pure-cube refinement from one polar computation

Let $k$ be an explicit finite field of characteristic three. On $V=k^n$ write $\mathcal C$ for the space of formal cubics, $\pi$ for unnormalized polarization, and $P=\pi(f)$. Form the linear map
$$
  J_P: \mathrm{End}(V)\longrightarrow\mathcal C,\qquad
  J_P(A)(x)=\tfrac12P(Ax,x,x).
$$
The following two conditions are decidable by deterministic coefficient linear algebra:
$$
 P\in \operatorname{im}(\pi J_P),\qquad
 \ker(\pi J_P)=\ker J_P. \tag{1}
$$
They depend only on the polarization. If they hold, **all cubics with this polarization** reduce to a single ordinary three-tensor of side $O(n)$ per input, with polynomial-time construction and recovery of cubic transporters. No bound on $\dim\ker J_P$ is required. The word “all” here quantifies over the refinements of a polarization passing (1).

## Proof

Solve $\pi J_P(A)=P$. By the second equality in (1) every solution has the same image $u_P=J_P(A)$. Equivalently, $u_P$ is the unique cubic in the intersection of $\pi^{-1}(P)$ and $\operatorname{im} J_P$. This specifies $u_P$ without choosing a basis or a preferred endomorphism. If $P=P'\circ S^{\otimes3}$, then $J_P(A)=J_{P'}(SAS^{-1})\circ S$. Hence $u_P=u_{P'}\circ S$. Since $f-u_P$ has zero polarization, it equals the cube of a uniquely determined linear form $\ell_f$ over $k$. Its coefficients are obtained by inverse Frobenius. We have proved
$$
 f=g\circ S\quad\Longleftrightarrow\quad
 \pi(f)=\pi(g)\circ S^{\otimes3}\quad\text{and}\quad
 \ell_f=\ell_g\circ S.
$$
In the reverse implication, add the cubed mark to the distinguished cubic. This is stronger on these fibers than asking whether the particular input $f$ itself is a derivative. It also applies when $P=0$, where $u_P=0$.

The resulting pair has a single ordinary multiplication tensor of side exactly $n+c+9$, where $c$ is the rank of $v\mapsto P(v,-,-)$. The construction also recovers $S$ from any tensor transporter. [Proof](Compact.md) · [Encoder and decoder](compact.py)

An alternative construction starts from three ordered part lists $(V,V^*,k)$, $(V,V^*,k)$, $(V,k)$. Use arguments $(x,\xi,s),(y,\theta,t),(z,c)$. The partitioned trilinear form is
$$
 P(x,y,z)+stc+c\theta(x)+s\theta(z)+c\xi(y)+t\xi(z)+tc\,\ell_f(x).
$$
The singleton scalars $a_1,a_2,a_3$ of a transporter satisfy $a_1a_2a_3=1$. The four pairings force the transformations on the three primal copies to be $a_1 S,a_2 S,a_3 S$ for one $S$. Thus the polar term gives exact transport of $P$ and the last term gives exact transport of $\ell$. Conversely $S$, its inverse dual, and identity scalars lift any simultaneous transporter. The fixed number of partitions can be removed over the same field with linear side growth and recovery of the original transporter, by the duplicate-rank-marker construction detailed in [Frames.md](Frames.md). The final tensor is ordinary and unpartitioned. [Implementation](fiber.py) · [Grochow–Qiao, Part IV](https://arxiv.org/abs/2306.16317)

The implementation does not require the coefficients of a polar tensor as separate input. It computes the image of the infinitesimal substitutions on monomials, pivots on mixed coefficients, tests for a nonzero pure-cube vector in the image kernel of that projection, and then reduces the input cubic. Mixed-coordinate vanishing is exactly polar vanishing in characteristic three. It supplies the ordinary tensor by shape and exact random entry access, with the identity rectangles described by index intervals. A dense array can be produced by iterating over these indices. The fixed rank-marker constants can be large.

## An infinite family with a one-block polarization

Use the cyclic family from [Euler.md](Euler.md), with $m\ge4$ and subscripts modulo $m$:
$$
 F(x,y)=\sum_{i=1}^m y_i(x_i^2+x_ix_{i+1}),\qquad
 f=F+\ell(x,y)^3 .
$$
For these inputs the canonical representative is $u_P=F$, and the canonical mark is exactly $\ell$. Indeed $F=J_P(A)$ for the projection $A(x,y)=(0,y)$. To prove (1) it suffices to show that a pure output of $J_P$ is zero. In the formal derivative of $F$ produced by an arbitrary linear substitution, every term has at least one $x$ factor, so there is no $y_j^3$. The only terms with three $x$ factors are
$$
   \sum_i (x_i^2+x_ix_{i+1})\sum_b R_{ib}x_b ,
$$
where $Rx$ is the $x$-dependent part of the infinitesimal change in $y$. If this is pure, the coefficient of $x_i^2x_b$ kills $R_{ib}$ for $b\notin\{i-1,i,i+1\}$. The coefficients of $x_i^2x_{i+1}$ and $x_i^2x_{i-1}$ give
$$
 R_{i,i+1}+R_{ii}=0,\qquad R_{i,i-1}+R_{i-1,i}=0.
$$
Finally the coefficient on the three distinct indices $(i-1,i,i+1)$ is $R_{i,i-1}+R_{i-1,i+1}=R_{i,i-1}$, since the predecessor and successor are nonadjacent when $m\ge4$. Thus all three surviving diagonals of $R$ are zero. This rules out every pure $x_i^3$ coefficient as well. The other bihomogeneous terms cannot be pure and already vanish by hypothesis. This proves the claim over every characteristic-three field, and yields the canonical marked presentation over every finite such field.

The polarization in this family is concise and has scalar centroid, as proved in [Euler.md](Euler.md). The form $F+y_1^3$ cannot lie in the image of $J_P$ because that image has no $y_1^3$ terms. Nevertheless it, and every other refinement, receives a linear-side tensor via (1). For instance $F$ and $F+y_1^3$ have identical polarization and are inequivalent, since their marked covectors are zero and nonzero. This remains true after arbitrary changes of coordinates.
