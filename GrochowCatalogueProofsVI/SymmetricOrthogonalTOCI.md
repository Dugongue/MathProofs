# A single symmetric tensor of degree 15 is TOCI-complete

## GP-0263

Orbit-closure intersection for $\mathrm O(Z)$ acting on $\operatorname{Sym}^{15}(Z^*)$ is TOCI-complete under efficient algebraic reductions, with the standard complex bilinear form on $Z$. The inputs are single homogeneous forms of fixed degree over the Gaussian rationals. There is also a complete mixed tuple of symmetric tensors for a general linear group. This gives a positive answer to Question I.14 of Lysikov and Walter. The proof uses [the single mixed quartic reduction](PureMixedQuarticTOCI.md) and its marked-fiber fact. Membership follows from the equivariant inclusion of the symmetric power in the fifteenth tensor power and the reduction from orthogonal tensor OCI to TOCI. [Lysikov–Walter, Section V-B](https://arxiv.org/html/2411.04639v2#S5.SS2)

### Encode the mixed quartic with quadratic anchors

Put $Y=\mathbb C^{2n}$ with its standard symmetric form. Equip it with the real orthogonal complex structure $J$ acting on each coordinate pair by $(x,y)\mapsto(-y,x)$. Its $+i$ and $-i$ eigenspaces $Y^+,Y^-$ are maximally isotropic and are paired nondegenerately by the form. Consequently the orthogonal centralizer of $J$ is precisely $\mathrm{GL}(Y^+)$, acting on $Y^-$ by the contragredient action.

Let $U=Y_1\oplus Y_2\oplus Y_3\oplus Y_4$ be an orthogonal direct sum of four coordinate copies of $Y$. Regard a quadratic form on $U$ as its self-adjoint matrix. Use the following five real trace-zero quadratics $Q_0,\ldots,Q_4$.

- $Q_0$ has blocks $-3I,-I,I,3I$, in order.
- $Q_1,Q_2,Q_3$ have identity blocks between $Y_1$ and $Y_j$ in both directions, for $j=2,3,4$ respectively. All other blocks vanish.
- $Q_4$ has $J$ in the block from $Y_1$ to $Y_2$ and $J^{\mathsf T}$ in the reverse block, with all other blocks zero.

Their common orthogonal stabilizer is diagonal $\mathrm{GL}(Y^+)$. Indeed $Q_0$ preserves the four colors, the identity bridges identify the actions on the copies, and the last bridge imposes commutation with $J$. The tuple of quadratics has closed orbit under $\mathrm O(U)$. To see this using the standard Hermitian inner product, a compact real infinitesimal generator acts by a real skew-adjoint operator on the real quadratic space. Its Hermitian moment pairing on each of the real $Q_j$ is zero. Kempf–Ness then applies to the tuple. Equivalently each real symmetric matrix has zero commutator with its adjoint in the matrix conjugation representation.

The quartic data $T\in\operatorname{End}(X\otimes X)$ for $X=\mathbb C^n$ can now be represented by a polynomial $F_T$ multilinear in the four $Y_j$. Use the projections
$$
Y_1,Y_2\longrightarrow Y^-,\qquad
Y_3,Y_4\longrightarrow Y^+,
$$
with bases identifying the duals of these four projected spaces with $X,X,X^*,X^*$ in order. Evaluation of the fourfold coefficient array defines $F_T$. This is an injective equivariant linear map for the anchor stabilizer. In particular its image is a closed stable subspace. The polynomial is harmonic for the standard Laplacian on $U$ because it has degree one in each of the four mutually orthogonal color blocks. The projected bases and matrices can be chosen over the Gaussian rationals with constant coefficient bit length. For example, in each coordinate pair use $e_1-i e_2$ and $(e_1+i e_2)/2$ as the paired bases.

### Encode the tuple by a single symmetric tensor

Adjoin an orthogonal unit coordinate $t$ and write $\rho(u)=\sum_\ell u_\ell^2$ for the quadratic norm on $U$. Set $Z=\mathbb C\oplus U$ and output the degree-15 form
$$
P_T(t,u)=t^{15}
+\sum_{j=0}^4t^{13-2j}\rho(u)^j Q_j(u)
+t\,\rho(u)^5 F_T(u).
$$
Applying the standard Laplacian on $Z$ seven times gives $15!\,t$. In fact for a harmonic homogeneous form $H$ of positive degree $h\ge2$, the identity
$$
\Delta_U(\rho^j H)=2j(\dim U+2h+2j-2)\rho^{j-1}H
$$
follows from differentiation and the Euler formula. Consequently any term involving one of the harmonic forms $Q_j$ or $F_T$ retains $U$-degree at least two until it vanishes. After seven Laplacians the total degree is one, so all those terms vanish. The normalization of $\Delta_Z^7$ gives an equivariant linear map from the target representation to $Z^*$ with value $t$ on the encoded locus. The orbit of $t$ is the closed unit quadric, and its stabilizer acts by $\mathrm O(U)$. The marked-fiber fact therefore reduces closure intersection for the encoded forms to that action on the fiber above $t$.

Within this fiber, there is an $\mathrm O(U)$-equivariant closed affine subspace of forms
$$
t^{15}+\sum_{j=0}^4t^{13-2j}\rho^j A_j+t\,\rho^5 B,
$$
where $A_j$ vary over harmonic quadratics and $B$ varies over harmonic quartics. Its coordinates are recovered uniquely because all the indicated powers of $t$ are distinct and multiplication by $\rho^j$ is injective in the polynomial ring. The displayed affine isomorphism identifies the fiber problem on our inputs with closure intersection for the tuple $(Q_0,\ldots,Q_4,F_T)$. Projection onto the quadratic tuple is equivariant and the tuple orbit is closed, as above. A second use of the marked-fiber fact identifies closure intersection with the action of its stabilizer on $F_T$, which is precisely the original mixed-quartic instance. This proves the reduction.

The output space dimension is $8n+1$ and the degree is constant. The explicit coefficient array and the rational scalar operations have polynomial bit complexity. The case $n=0$ is trivial.

### A complete mixed symmetric tuple under GL

If one requires the acting group itself to be general linear, append the standard quadratic form $q$ and its inverse tensor $q^{-1}$ to $P_T$. Both markings are symmetric tensors. The orbit of $(q,q^{-1})$ under $\mathrm{GL}(Z)$ is precisely the closed set of pairs of symmetric matrices with product equal to the identity. Every such pair has a nonsingular first form, which is congruent to $q$ over $\mathbb C$, with its inverse then forced. The stabilizer of the pair is $\mathrm O(Z)$. The marked-fiber argument gives the same closure equivalence for the mixed signature
$$
\left(\operatorname{Sym}^{15}(Z^*)\oplus
      \operatorname{Sym}^{2}(Z^*)\oplus
      \operatorname{Sym}^{2}(Z),\ \mathrm{GL}(Z)\right).
$$
Membership in TOCI follows by including each symmetric space into the corresponding tensor power. This proves completeness for a signature built exclusively from symmetric powers under the general linear action. [Lysikov–Walter, Question I.14](https://arxiv.org/html/2411.04639v2#S1.SS4)
