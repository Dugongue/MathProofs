# Tensor isomorphism from the singular scheme of a fixed-Hessian cubic

Fix a positive three-tensor format and a field $k$ with $2\ne 0$. Use the symmetric Frobenius carrier $A_t$ and its fixed unit slice $G$ from the common-Hessian construction, and write $Z_t$ for the affine scheme cut out by the coordinate quadrics of $x^2=0$ in $A_t$. Write $Y_t=\operatorname{Proj} k[Z_t]$. The homogeneous presentation defines $Y_t$, but its isomorphisms below are arbitrary $k$-scheme isomorphisms.

**Theorem.** For inputs $t,t'$ of the same format, the following conditions are equivalent over $k$.

1. The inputs $t$ and $t'$ are equivalent under independent changes of basis.
2. The abstract affine schemes $Z_t$ and $Z_{t'}$ are isomorphic.
3. The abstract projective schemes $Y_t$ and $Y_{t'}$ are isomorphic.
4. The local $k$-algebras of $Y_t$ and $Y_{t'}$ at their unique geometric points of maximal tangent dimension are isomorphic after quotienting by the cubes of their respective maximal ideals. These points are defined over $k$.

If also $3\ne0$, these are the affine critical schemes and projective singular schemes of the cubics $f_t(x)=F_t(x,x,x)$. The cubics all have the same Hessian determinant $6^N\det(G)r^N$, where $N=\dim A_t$ and $r$ is the unit coordinate. The affine criterion also applies over the original finite local coefficient rings with odd residue characteristic, using isomorphisms over that coefficient ring and comparing the input tensors over the residue field. The field criterion in characteristic three uses the same quadratic square map.

The last test gives a finite algebra with a multiplication table of polynomial size in the input dimensions. Its isomorphism problem on the written family is polynomial-time equivalent to ordinary tensor isomorphism over $k$, in the field-arithmetic model and in the explicit finite-field model. Computing its presentation or table does not require an isomorphism of schemes as input. [Common-Hessian construction](https://github.com/Dugongue/MathProofs/blob/main/SymmetricFinalFour/Tensor.md)

## The affine square-zero scheme recovers its algebra

The following assertion works over any commutative base ring $B$ with $2$ invertible. Let $A,A'$ be finite free, unital, associative commutative $B$-algebras of the same rank $N$, and let $Z(A),Z(A')$ be their affine square-zero schemes. Then
$$
 Z(A)\cong_B Z(A') \quad\Longleftrightarrow\quad A\cong_{B\text{-alg}} A'.
$$
Moreover, the natural linearization of any isomorphism on the left has the form $x\mapsto a\psi(x)$, for a unique algebra isomorphism $\psi:A\to A'$ and a unique unit $a\in (A')^\times$.

Indeed, the zero section is intrinsically the unique $B$-section at which the pullback of $\Omega^1_{Z(A)/B}$ is free of rank $N$. For a section $x$ the presentation of relative differentials gives the cokernel of the transpose of $2L_x$, where $L_x(y)=xy$. If this cokernel is free of rank $N$, the quotient map, followed by a chosen isomorphism to $B^N$, is an invertible endomorphism of $B^N$. Thus $L_x=0$, and $x=L_x(1)=0$. At zero the matrix is zero and the asserted freeness holds. This argument also applies after any commutative base change.

Every isomorphism therefore preserves the ideal of the zero section. Its associated graded isomorphism gives an isomorphism of the original homogeneous coordinate rings, since each is generated in degree one and its ideal of the zero section is the positive-degree ideal. This is the linearization, given by an invertible map $g:A\to A'$ carrying the degree-two equation spaces to one another. Each equation space is isomorphic to the dual of the algebra module, via $\ell\mapsto \ell(x^2)$. Indeed polarization identifies this inclusion with the transpose of multiplication, which is split surjective since $1\cdot x=x$. Thus the equation-space transporter is equivalent to an invertible $h:A\to A'$ such that
$$
 h(xy)=g(x)g(y)
$$
for all $x,y$. This follows by first comparing the quadratic maps and then polarizing. Putting $y=1$ gives $h=L_a g$ with $a=g(1)$, so $L_a$ is invertible and $a$ is a unit. With $\psi=L_a^{-1}g$, the transporter identity gives $a^2\psi(xy)=a^2\psi(x)\psi(y)$. Hence $\psi$ is the required algebra isomorphism. Conversely every $L_a\psi$ is a linear scheme isomorphism because it takes each square to $a^2$ times its image under $\psi$.

In particular, linearization splits the automorphism functor of $Z(A)$ onto $A^\times\rtimes\operatorname{Aut}_{B\text{-alg}}(A)$, with kernel the automorphisms acting identically on the cotangent module at zero. Here the splitting uses the linear maps just described, so the assertion is functorial in the commutative base change. This statement permits nonlinear scheme automorphisms.

For the common-Hessian carriers, scalar multiplication is interpreted over $B=k$ or over the given finite local ring $B=R$. The carrier product in its augmentation ideal $I_t$ has fourth power zero. Over a field $I_t$ is the unique maximal ideal. Over the original nonfield $R$, the carrier rank is a unit and $\operatorname{tr}(L_x)=N\alpha(x)$, with $\alpha$ its augmentation, so $I_t$ is intrinsic there as well. The annihilator of $I_t$ inside $I_t$ is $Bz$. Its triple product in this line recovers $C_t$ up to a nonzero scalar after removing the contraction radical, using $sR\simeq k$ and residue coordinates over $R$. This is the algebra recovery step of the symmetric construction. The marked-form recovery below then gives the input equivalence. In the forward direction the lifted input transporter is already an algebra isomorphism. [Frobenius carrier and field transporter](https://github.com/Dugongue/MathProofs/blob/main/SymmetricFinalFour/Tensor.md) · [Final-coordinate transporter](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md)

## The intrinsic projective point and its local algebra

Work now over the field $k$. The common-Hessian field carrier has no extra $Q$ summand, so write
$$
 A_t=k1\oplus V\oplus V^*\oplus kz,\qquad
 u\cdot v=C_t(u,v,-),\qquad
 u\cdot\ell=\ell(u)z .
$$
Here $C_t(u,v,-)$ is placed in $V^*$, the listed products concern $u,v\in V$ and $\ell\in V^*$, and the other products in the augmentation ideal are zero.

At a geometric point of $Y_t$ represented by $x\ne0$, the affine derivative of the defining quadrics is $2L_x$. Its kernel contains $x$, because $x^2=0$. In a projective affine chart the tangent dimension is therefore $N-1-\operatorname{rank}L_x$, obtained by removing the representative's radial line. We have $\operatorname{rank}L_x\ge1$ because $L_x(1)=x$. If this rank is one then $\operatorname{im}L_x=kx$ over the geometric field. For any $y\in I_t$, the map $L_y$ acts on this line and is nilpotent, so $xy=0$. Also $x\in I_t$, since $\alpha(x)^2=0$ in a field. The annihilator assertion now gives $x\in kz$. Conversely $L_z$ has rank one. Hence $[z]$ is intrinsically characterized, including after extension to an algebraic closure.

On the chart where the $z$-coordinate is $1$, write the representative as $r1+u+\ell+z$. The vector of equations is
$$
 r^2=0,\qquad 2r u=0,\qquad 2r\ell+C_t(u,u,-)=0,\qquad
 2r+2\ell(u)=0 .
$$
The last equation eliminates $r$, giving $r=-\ell(u)$. In the remaining equations the only homogeneous terms of degree two are the coordinates of $C_t(u,u,-)$. The eliminated relations have no constant or linear terms, so multiplying them by local coefficients adds no new quadratic terms beyond their constant-coefficient span.

For $W=V\oplus V^*$, put
$$
 U_t=\big\langle (u,\ell)\longmapsto C_t(u,u,v):v\in V\big\rangle
        \ \subseteq\ \operatorname{Sym}^2 W^* .
$$
If $\mathfrak n$ is the maximal ideal at $[z]$, the local algebra modulo $\mathfrak n^3$ is
$$
 k\oplus W^*\oplus (\operatorname{Sym}^2 W^*/U_t).
$$
Here the product of degree-one elements is the symmetric product modulo $U_t$, and all products of positive degrees summing to at least three vanish. In particular $U_t$ is intrinsically the kernel of the multiplication map from $\operatorname{Sym}^2(\mathfrak n/\mathfrak n^2)$ to $\mathfrak n^2$ in this truncated algebra. By polarization its common radical in $W$ is $V^*$, since $C_t$ has zero contraction radical. Quotient by that common radical and recover the space of quadrics $C_t(-,-,v)$ on $V$, up to an arbitrary common basis change on $V$.

## Recovering the tensor from the space of quadrics

Recall the marker form. Put $n=a_1+a_2+a_3$, $h_i=2^i(n+7)$, and $O_i=X_i\oplus X_i^*\oplus H_i$, where $\dim H_i=h_i$. Put $K_0=\bigoplus_i O_i$ and $V=K_0\oplus\bigoplus_i kz_i$. The nonzero types of contractions are $C_t(z_i,x_i,y_i)=\beta_i(x_i,y_i)$ on $O_i$, and the three-role data $t$ on $X_1\times X_2\times X_3$, along with permutations. Each $\beta_i$ is nondegenerate and has rank at least two. This also proves conciseness: a contraction-radical vector has zero $O_i$-projection by testing with $z_i,O_i$, then zero marker coefficients by testing on each $O_i^2$.

Identify two such quadratic spaces by a linear change of variables and call the resulting concise forms $C,D$ on the same space. Both maps $v\mapsto C(-,-,v)$ and $v\mapsto D(-,-,v)$ are injective, with the same image by polarization. Thus $D(x,y,v)=C(x,y,Sv)$ for an invertible $S$. Symmetry of $D$ gives the centroid identities
$$
 C(Sx,y,v)=C(x,Sy,v)=C(x,y,Sv).
$$

For the marker form $C=C_t$, every such $S$ acts by scalars $a_i$ on $O_i\oplus kz_i$. To see this, comparing $C(Sx,z_i,z_j)=0$ with $C(x,Sz_i,z_j)$ shows $Sz_i$ has no $O_j$-component for any $j$. Comparing $C(Sx,y,z_i)$ with $C(x,y,Sz_i)$ for $x,y\in K_0$ now shows that $Sz_i=a_i z_i$ and $(Sx)_{O_i}=a_i x_{O_i}$. Write the possible remaining marker component of $Sx$ as $\sum_j\gamma_j(x)z_j$. Taking $x\in O_i$, $y,v\in O_j$ with $i\ne j$ and comparing the first two slots gives $\gamma_j(x)=0$. For $x,y,v\in O_j$ it gives
$$
 \gamma_j(x)\beta_j(y,v)=\gamma_j(y)\beta_j(x,v).
$$
A nonzero $\gamma_j$ would force the nondegenerate form on $O_j$ to have rank at most one. Therefore $\gamma_j=0$ everywhere. The identity on one nonzero evaluated triple of $t$, when $t\ne0$, forces $a_1=a_2=a_3$. Conversely these indicated scalar endomorphisms satisfy the identities. All $a_i$ are nonzero for an invertible $S$.

The form $D(x,y,v)=C_t(x,y,Sv)$ is equivalent to $C_t$ over the original field. If $t=0$, scale $z_i$ by $a_i$ and fix each $O_i$. If $t\ne0$, apply that marker scaling with the common scalar $a$ and additionally scale $X_1$ by $a$ and $X_1^*$ by $a^{-1}$. The changes preserve each $\beta_i$ on its paired middle summands and produce the desired multiplier on every nonzero contraction type. Thus the quadratic space determines the diagonal equivalence class of the marked form over $k$, including in characteristic three.

For completeness, diagonal or projective equivalence of marked forms recovers ordinary three-mode equivalence of the data as follows. The vectors of slice rank at most $n+6$ are exactly $K_0$. Slices at vectors in $K_0$ use at most the $n$ data directions on $K_0^2$ and at most six extra ranks from the three markers. A nonzero $z_i$-coordinate forces rank at least $h_i$ on $H_i$. For a slice at $v$, the determinant on $K_0^2$ is a nonzero constant times
$$
 \prod_i \alpha_i(v)^{h_i+2a_i^{\mathrm{fmt}}},
$$
where $\alpha_i$ is the coordinate of $z_i$ and $a_i^{\mathrm{fmt}}=\dim X_i$. Indeed the $H_i$ are separate and the remaining matrix has blocks $\left(\begin{smallmatrix}P&A\\ A&0\end{smallmatrix}\right)$, with $A$ block scalar $\alpha_i$; exchanging its two column groups gives the formula. Unique factorization and distinct exponents label the three coordinate lines in $(V/K_0)^*$.

Choose lifts $v_i$ of quotient directions dual to those lines. Write $B_i=C_t(v_i,-,-)|_{K_0^2}$, let $B=\sum_i B_i$, and set $A_i=B^{-1}B_i$. The matrix $B$ is invertible by the determinant formula. Let $E_i$ project onto $O_i$ in the written presentation. Each $A_i$ equals $E_i+N_i$ for a map $N_i$ taking $\bigoplus X_i$ into $\bigoplus X_i^*$ and killing $\bigoplus(X_i^*\oplus H_i)$. Indeed the perturbations of the split blocks are supported on the two data variables, and applying the inverse split pairing puts them in this square-zero space of maps. It is preserved by left and right composition with every $E_i$, so the same assertion holds using $B^{-1}$. The polynomial $P_i=3A_i^2-2A_i^3$ is idempotent because $A_i^2(1-A_i)^2=0$. Also $P_i-E_i$ belongs to the same square-zero space. Therefore its image projects onto exactly $X_i$ in the sum of data spaces, and restriction of the tensor to the three images is ordinary $t$ with unused coordinates. These operations are covariant under a marked-form equivalence, by transporting the choices of lifts and bases. Quotienting each restriction by its contraction radical recovers the supported tensor. Extending bases in the three prescribed original dimensions recovers ordinary equivalence, even if the input is nonconcise.

This proves that the local algebra modulo $\mathfrak n^3$ implies input equivalence. In the other direction, an ordinary input transporter extends to an algebra isomorphism preserving $z$, and thus induces isomorphisms of the cones, their projective schemes and the indicated local algebras. This establishes the projective assertions.

## Cubics, complexity, and prior work

Since $F_t(x,y,v)=\lambda(xyv)$ and $G(y,v)=\lambda(yv)$ is a fixed perfect pairing, differentiation gives $d f_t(x)=3G(x^2,-)$ and Hessian matrix $6G L_x$. When $6$ is invertible, the affine Jacobian ideal is exactly the square-zero ideal, and Euler's identity puts $f_t$ in that Jacobian ideal. This identifies the projective singular schemes with $Y_t$. The centered left multiplications are strictly triangular, so the determinant is the displayed pure power. In characteristic two the field carrier has the same squaring law $x^2=\alpha(x)^2 1$ for every input, so the odd-characteristic restriction on square-map reconstruction is sharp for this family.

The schemes have $O(n)$ coordinates and the second-order local algebra has $O(n^2)$ basis elements. Its presentation follows directly from the contractions of $C_t$. A multiplication table is obtained by linear elimination in the degree-two part. For the reverse complexity reduction, a unital algebra isomorphism is equivalent to an independent-mode isomorphism of multiplication tensors: any isotopy between unital associative algebras can be normalized to an algebra isomorphism by the two preimages of the target identity. Explicitly, if $h(xy)=f(x)g(y)$, put $a=f^{-1}(1)$, $b=g^{-1}(1)$. Then $h(ay)=g(y)$ and $h(xb)=f(x)$, so $a,b$ are units. In source coordinates via $h$ the target product is $x b^{-1}a^{-1}y$, and multiplication by the unit $b^{-1}a^{-1}$ identifies this product with the original. This is the tensor-to-algebra link used in Grochow–Qiao's isomorphism framework. [Grochow and Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Bläser and Lysikov, unital isotope normalization](https://doi.org/10.4230/LIPIcs.MFCS.2016.19)

Hwang's Proposition 2.6 describes the relation between a homogeneous form's entire Jacobian space and its symmetrizers over $\mathbb C$, extending the Jacobian reconstruction perspective of Ueda–Yoshinaga and Wang. The centroid argument above specializes that comparison and computes the entire centroid of the marker family over $k$. The geometric step is to extract the needed quadratic space from one intrinsic point on the abstract projective singular scheme, using only its local algebra through order two. Gharahi–Ottaviani characterize the ambient class of complex persistent cubics by their Hessian determinants. The recovery theorem applies within a single explicit Hessian fiber. [Hwang, Symmetrizer group of a projective hypersurface, Proposition 2.6](https://arxiv.org/html/2501.08633v1) · [Wang, On homogeneous polynomials determined by their Jacobian ideal](https://arxiv.org/abs/1402.3810) · [Gharahi and Ottaviani, Symmetric Persistent Tensors and their Hessian](https://arxiv.org/html/2510.07404v1)

Geometry.py checks 15 centroid calculations, 1,095 projective points, 300 local quadratic coordinates and 8,256 rescaling identities in compact marker carriers over the fields of orders 3, 5 and 7. It also checks all 15 square-zero sections and 4,374 unit-scaling identities in the dual-number algebra over $\mathbb Z/9\mathbb Z$. The proof is in prose. Publication priority and Lean verification are unestablished.
