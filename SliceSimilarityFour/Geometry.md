# Tensor isomorphism of smooth projective varieties with common linear restrictions

There is a deterministic construction from ordinary three-tensors $t$ over any field $k$ to smooth projective rational $k$-varieties $X_t$. For a fixed positive input format and any prescribed $h\ge1$, it has the following properties.

- The abstract $k$-varieties $X_t$ and $X_{t'}$ are isomorphic if and only if the input tensors are equivalent under independent changes of basis.
- Each variety is a projective bundle over the same $\mathbb P(V)$. Over every linear subspace $\mathbb P(U)\subseteq\mathbb P(V)$ with $\dim U\le h$, the restricted projective bundles are isomorphic over that subspace. This holds after arbitrary field extension.
- The varieties have explicit presentations as smooth complete intersections of the same number of bidegree-$(1,1)$ equations in a common product of projective spaces. They have the same Hilbert polynomial for the product polarization. The construction takes polynomial time in the explicit input size and in $h$, and can be written by equations of degree at most two in ordinary projective space.

The input to the proof is the common-slice multiplication construction. Its low-direction simultaneous similarities give the common restrictions. The global variety recovers the tensor because its projective-bundle projection is intrinsic and its vector bundle remembers the quadratic kernel of multiplication. [Common slice-similarity theorem](https://github.com/Dugongue/MathProofs/blob/main/HessianFour/Tensor.md)

## The family and its common restrictions

Use the field version of that theorem. Write the input as a rectangular matrix space $M$ with its supplied slice list. Put $d=a+b$, $m=h+1$ and $D=3md$. The theorem constructs an explicitly given subspace $H=H_M\subseteq C=\operatorname{Sym}^2 V$ for $\dim V=D$, such that
$$
 H\cap (UV)=0\qquad(\dim U\le h)
 \tag{1}
$$
after every field extension. Here $UV\subseteq C$ is the span of products from $U\times V$. The construction writes the quadratic forms as $x^{\mathsf T}B^{\oplus m}y$, using the anchored rectangular space $B=[x_0 I+\widetilde A,\ y_0 I]$ with $A\in M$ and $\widetilde A$ square-zero on a common ambient space. Its nonzero polarization ranks are at least $2m$, whereas any element of $UV$ has polarization rank at most $2\dim U$. This proves (1), including in characteristic two. The rank cut and ordered-arrow cancellation of the common-slice theorem prove that two $H_M$ are linearly equivalent exactly when the input tensors are equivalent, with redundant slices allowed. In particular this established equivalence preserves the base field. [Quadratic-space construction and reflection, §1](https://github.com/Dugongue/MathProofs/blob/main/HessianFour/Tensor.md)

Let $W=(C/H)\oplus S$, where $S$ is the inert padding of dimension $\dim H$, so $w=\dim W=D(D+1)/2$ is fixed. Let $\beta(u,v)\in W$ be the class of $uv$ in the first summand. On the projective space of **lines** in $V$ take the bundle
$$
 0\longrightarrow \mathcal O(-1)\otimes V
   \xrightarrow{b_H}\mathcal O\otimes W
   \longrightarrow \mathcal E_H\longrightarrow0,
 \qquad (b_H)_{\ell}(u\otimes v)=\beta(u,v).
 \tag{2}
$$
The map has rank $D$ on every geometric fiber because $H$ contains no nonzero product and multiplication by $u\ne0$ in the symmetric algebra is injective. Hence its cokernel is a vector bundle of rank $\rho=w-D=D(D-1)/2$, with $\det\mathcal E_H\simeq\mathcal O(D)$. The rank and determinant follow directly from (2). Let $X_H=\mathbf P_{\mathbb P(V)}(\mathcal E_H)$, where this second projectivization parameterizes one-dimensional **quotients**. In particular $\pi_*\mathcal O_{X_H}(1)=\mathcal E_H$ for its projection $\pi$. [Stacks Project, projective bundle conventions and tautological quotient](https://stacks.math.columbia.edu/tag/01OA)

Fix $U\subseteq V$ of dimension $j\le h$ and a complement $T$ to $U$. Over $\mathbb P(U)$, the map in (2) takes values in the fixed subspace $\beta(UV)$, and (1) identifies this image with $UV=\operatorname{Sym}^2 U\oplus(U\otimes T)$. The source decomposes accordingly into $\mathcal O(-1)\otimes U$ and $\mathcal O(-1)\otimes T$. Let $\mathcal Q_U$ be the quotient of $U\otimes\mathcal O$ by its tautological line. The first cokernel is $\operatorname{Sym}^2\mathcal Q_U$, since the degree-two kernel of the symmetric-algebra quotient by a line is its product with $U$. The second cokernel is $\mathcal Q_U\otimes T$. Choose a complement to $\beta(UV)$ in $W$. This proves the common restriction formula
$$
 \mathcal E_H|_{\mathbb P(U)}
 \ \simeq\
 \operatorname{Sym}^2\mathcal Q_U
 \ \oplus\ \mathcal Q_U^{\oplus(D-j)}
 \ \oplus\ \mathcal O^{\oplus(w-jD+j(j-1)/2)}.
 \tag{3}
$$
For $h\ge2$, its restriction to every line is $\mathcal O(2)\oplus\mathcal O(1)^{D-2}\oplus\mathcal O^{w-2D+1}$.

## The bundle recovers the quadratic kernel

On the fixed base $\mathbb P(V)$, the sequence (2) can be recovered from the bundle. The vanishing of $H^0(\mathcal O(-1))$ and $H^1(\mathcal O(-1))$ identifies $H^0(\mathcal E_H)$ with $W$. The evaluation map of these sections gives exactly the displayed quotient of $\mathcal O\otimes W$. Its kernel recovers $\mathcal O(-1)\otimes V$, with the second $V$ initially known only up to an independent basis change. [Stacks Project, cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)

Suppose $\mathcal E_H\simeq\mathcal E_{H'}$ over the identity of the projective base. The isomorphism of (2) gives invertible maps $f:W\to W'$ and $g:V\to V$ with
$$
             f\beta(u,v)=\beta'(u,gv).
 \tag{4}
$$
The map on the kernel has constant coefficients since all endomorphisms of $\mathcal O(-1)$ are scalar. Symmetry in $u,v$ gives $u(gv)-v(gu)\in H'$. Extend scalars to an algebraic closure and choose a nonzero eigenvector $u$ of $g$ of eigenvalue $\lambda$. For every $v$, the product $u(gv-\lambda v)$ lies in $H'$, so it is zero by (1). It follows that $g=\lambda I$, and the scalar is already in $k^\times$ because the matrix is defined over $k$. Now (4) identifies the two kernels $H,H'$ inside $C$. Conversely, if the kernels agree and the padding dimensions match, an isomorphism of the padded quotients gives a bundle isomorphism. Only the absence of nonzero products over an algebraic closure is needed in this argument.

A base automorphism of $\mathbb P(V)$ has a linear lift $P\in\operatorname{GL}(V)$, obtained by its action on the sections of $\mathcal O(1)$ after choosing an isomorphism of that line bundle with its pullback. The pullback of $\mathcal E_{H'}$ by this base map is the bundle of $\operatorname{Sym}^2(P^{-1})H'$, as can be seen by changing both inputs of $\beta'$ by $P$. Applying (4) therefore proves that bundle isomorphism covering a base automorphism is equivalent to linear equivalence of $H,H'$.

## The abstract variety recovers its projection

Here $\rho>D$, since $D\ge12$. Every morphism $\mathbb P^{\rho-1}\to\mathbb P^{D-1}$ is constant over an algebraically closed field. Its pullback of $\mathcal O(1)$ has degree $b\ge0$. If $b>0$, the pullback is ample, so a positive-dimensional fiber is impossible, because its restriction to that fiber is trivial. The dimension inequality rules out this case. When $b=0$, the map is constant by the description of a projective-space morphism by generating sections.

Suppose $X_H\cong_k X_{H'}$ as abstract varieties via $F$. The morphism $\pi'F$ is constant on the geometric fibers of $\pi$. Its pullback of the target $\mathcal O(1)$ therefore has fiber degree zero. The projective bundle Picard formula writes this line bundle as $\pi^*L$ for a base line bundle $L$. The formula follows by tensoring a line bundle with a suitable power of the relative $\mathcal O(1)$, then pushing forward and evaluating the resulting fiberwise trivial bundle. Relative cohomology and base change identify the pushforward in that case as a line bundle and the evaluation as an isomorphism. The generating sections of $\pi^*L$ all come from $L$, since $\pi_*\mathcal O_{X_H}=\mathcal O_{\mathbb P(V)}$. They generate $L$ because $\pi$ is faithfully flat. Thus $\pi'F$ factors through a unique base morphism $\varphi$. The same argument for $F^{-1}$ proves $\varphi$ is an isomorphism. This factorization works over $k$ itself. [Bansal, Sarkar and Vats, Theorem 3.9, large-fiber comparison of projective-bundle structures](https://arxiv.org/html/2311.00999v1)

Now $F^*\mathcal O_{X_{H'}}(1)$ and $\mathcal O_{X_H}(1)$ both have degree one on the $\pi$-fibers, so they differ by $\pi^*\mathcal O(q)$ for some integer $q$. Pushing forward gives
$\varphi^*\mathcal E_{H'}\simeq \mathcal E_H\otimes\mathcal O(q)$. Both determinants have degree $D$ on a base line, hence $q\rho=0$ as an integer and $q=0$. The bundle comparison now gives equivalence of the original input tensors. Conversely an input transporter gives a quadratic-space transporter and hence an isomorphism of the projective varieties by (2). This proves the first assertion for unpolarized abstract varieties.

## Smooth projective equations and deformations

Choose a basis $v_1,\ldots,v_D$ of $V$. Inside $\mathbb P(V)\times\mathbb P(W^*)$, with both factors described by lines, the equations are
$$
 \alpha\big(\beta(u,v_i)\big)=0 \qquad(1\le i\le D).
 \tag{5}
$$
For a line $ku$, these equations say that the quotient of $W$ defined by $[\alpha]$ kills the image of $u\otimes V$. Thus (5) presents $X_H$ scheme-theoretically, including on any local chart where a full-rank minor is inverted. There the equations are independent linear equations in the second factor. They form a regular sequence of length $D$ in the product, and their common solution is the indicated projective bundle. Smoothness and geometric integrality follow from local triviality over $\mathbb P(V)$; it is rational over $k$ by trivializing over a nonempty open subset of the base. The Koszul resolution of (5) exhibits the same Hilbert polynomial in the product polarization for every output. Under the Segre embedding the $D$ equations are linear and the ambient product itself has its usual quadratic rank-one equations. This gives the claimed degree and polynomial-size presentation. In particular (5) is a polynomial-time construction over explicit finite fields. [Grochow and Qiao, Part IV, reduction framework for tensor isomorphism](https://arxiv.org/abs/2306.16317)

There is an explicit smooth projective family with nonisomorphic fibers and these same restrictions. Use input format $(2,2,1)$ with single slice $A(\tau)=\operatorname{diag}(1,\tau)$ over the affine parameter line. The two anchor generators and the nonzero data generator of $H$ are independent in every geometric fiber. Consequently they give a rank-three subbundle of the constant symmetric square. Quotient by it and add a rank-three trivial padding. The full fiber rank in (2) holds over the whole parameter line, so its projectivization gives a smooth projective morphism to that line. The fiber at zero has a rank-one input slice, and every nonzero fiber has a rank-two input slice. They are nonisomorphic by the theorem even after algebraic closure, while (3) and the Koszul resolution give their common small-subspace restrictions and Hilbert polynomial.

## Recognition on infinitesimal families

The argument also recognizes quadratic kernels over nonreduced bases. For a commutative ring $B$, use a fixed free $V_B$ of rank $D\ge2$ and subbundles $H,H'\subseteq\operatorname{Sym}^2 V_B$ whose geometric fibers contain no nonzero products. Form (2) with padding of equal rank when desired. Fiberwise injectivity gives vector bundles, and projective-space cohomology identifies their global sections and evaluation kernels as before. An isomorphism over the identity of the base projective space satisfies (4) over $B$. To prove $g$ is scalar over $B$, use the linear map
$$
 \operatorname{End}_B(V_B)/(B I)\longrightarrow
 \operatorname{Hom}_B(\textstyle\bigwedge^2 V_B,\operatorname{Sym}^2 V_B/H'),
 \quad
 [A]\longmapsto(u\wedge v\mapsto u(Av)-v(Au)\bmod H').
$$
Both sides are finite locally free. The eigenvector argument, which did not use invertibility of the hidden operator, proves injectivity on every geometric fiber. Full-rank minors locally split the injection, giving injectivity over $B$. It follows that even nilpotent entries in a nonscalar part of $g$ are excluded and that $H=H'$. With no padding, the remaining fixed-base bundle automorphisms are exactly the invertible scalars.

In the dimension range above, with the same padding and $B$ Artinian local, the abstract total spaces over $B$ also recognize $H$ up to $\operatorname{GL}(V_B)$. The projection argument applies fiberwise and descends by the same generating-section argument, which also holds over this base. The projective bundle Picard formula applies to the flat projective bundles over the locally Noetherian bases used here. Since $\operatorname{Pic}(B)=0$, all base automorphisms have linear lifts and the equal determinants remove the line-bundle twist exactly as over a field. Thus for $B=k[\epsilon]/(\epsilon^2)$, the first-order kernels with fixed special fiber $H_0$ and fixed base are $\operatorname{Hom}(H_0,C/H_0)$ without any identifications from hidden slice changes. Allowing base changes reducing to the identity projectivity identifies directions precisely modulo the derivatives of $\operatorname{Sym}^2(I+\epsilon A)$, for $A\in\operatorname{End}(V)$. This follows by applying the transporter statement over $B$ and taking the graph of the first-order map to $C/H_0$. The construction uses a locally split quadratic quotient over $B$, as in (2).

## Precedents and verification

Marchesi–Miró-Roig study uniform Steiner bundles via their line splittings. Bissinger gives an equivalence between Steiner bundles and suitable Kronecker representations and describes their restrictions. These are precedents for passing from a pencil to a bundle. In the symmetric quadratic quotient here, the independent hidden basis in (4) becomes a scalar. The small-subspace condition supplies the full formula (3), and the abstract smooth projective variety retains the input's tensor-isomorphism class. [Marchesi and Miró-Roig, Uniform Steiner bundles](https://www.numdam.org/articles/10.5802/aif.3403/) · [Bissinger, Uniform Steiner bundles on projective space and reflection functors](https://arxiv.org/html/2509.02014v1)

Geometry.py checks 184 polarization ranks, 45 small-direction intersections and 10 parameter fibers over the fields of orders 2 and 3. It also checks six exact ranks of the scalar-rigidity map over the fields of orders 2, 3 and 5. This is a prose proof. Publication priority and Lean verification are unestablished.
