# Five invariants for cubic geometry and tensor transporters

The tests below preserve data associated with a particular point, line, subgroup, or transporter. This is the part of the earlier Ley, Ward/Trellis, and Sigil approach that transfers. Incidence preserves which objects participate in a relation, simultaneous restrictions test compatibility, and a residual orbit retains the information lost by an initial projection. The statements and examples below are proved informally. The cited constructions are antecedents, and publication priority for the specific combinations has not been established.

## 1. Joint Galois fixed sets of a polar locus

Suppose a specified rank stratum of the Hessian of a cubic is a finite set $X$ of geometric points. Over a common finite Galois splitting field with group $G$, use
$$
 I_X(S)=\left|\bigcap_{g\in S}\operatorname{Fix}_X(g)\right|
       =|X^{\langle S\rangle}|
$$
as a function of indexed lists $S$ of Galois elements. A projective equivalence over the base field is a $G$-equivariant bijection of the polar points, so it preserves the entire function. On explicit permutation actions the evaluation takes $O(|S||X|)$ tests. Recovering the finite locus and its Galois action from a raw cubic has no general polynomial bound here.

**An unbounded joint-data gap.** For every $r\geq2$, there are two geometrically Fermat trace cubics over $\mathbb Q$ whose rank-one Hessian loci have identical restrictions to every proper subgroup of a common splitting group $G=C_2^r$. The cubics are inequivalent over $\mathbb Q$. All lists of fewer than $r$ Galois elements give identical fixed-set counts. There is a list of $r$ elements on which the counts differ.

For the construction, let $\mu$ be the Möbius function of the subgroup lattice and consider the virtual $G$-set
$$
 \Theta=\sum_{H\leq G}|H|\mu(H,G)[G/H].
$$
Since $G$ is abelian, the mark at $K\leq G$ is $|G|\sum_{H\geq K}\mu(H,G)$. It is zero for $K<G$ and $|G|$ for $K=G$. Separate positive and negative coefficients to obtain actual $G$-sets $X_+,X_-$. Their cardinalities agree since the mark at the trivial subgroup is zero. On restriction to any proper subgroup all their marks agree, so those restrictions are isomorphic. Indeed for an abelian group the counts of points with stabilizer exactly $H$ follow from all fixed-set counts by Möbius inversion, and the number of each orbit type follows by dividing by its size. The full $G$-marks differ, so the original sets are inequivalent.

Realize $G$ by a multiquadratic extension of $\mathbb Q$ using $r$ different odd prime radicals. The finite étale algebras of its two sets give the two trace cubics $x\mapsto\operatorname{Tr}(x^3)$. In split idempotent coordinates the Hessian is diagonal with entries $6x_i$. Thus its rank-one lines recover exactly the original $G$-set and rule out projective equivalence over $\mathbb Q$. Proper subgroup restrictions conversely give exact linear equivalences of the trace cubics over the corresponding fixed fields. The primes may all be chosen $1\bmod8$, each new one $1\bmod p$ for all earlier primes $p$, by Dirichlet's theorem. Reciprocity makes the other prime radicals square at each ramified place, and outside ramification decomposition groups are cyclic. Thus the examples can also be made equivalent at every completion. This extends the two-label obstruction of the smooth fourfold companions to arbitrary list length. The table of marks and the Möbius idempotent are classical. The extra statement is their realization and separation in a smooth cubic polar configuration. [Yoshida on Burnside idempotents and mark homomorphisms](https://www.math.sci.hokudai.ac.jp/hmj/page/19-3/pdf/HMJ_19_3_1990_509-574.pdf)

## 2. Joint kernels of normal contractions

Let $T:A\times B\times C\to F$ be trilinear and put $L_a=T(a,-,-):B\to C^*$. At any marked nonzero direction $a$, define
$$
 N_a(v)=\pi_a L_v\vert_{\ker L_a},\qquad
 \pi_a:C^*\longrightarrow C^*/\operatorname{im}L_a.
$$
Equivalently, $N_a$ is the linear map $A\to\operatorname{Hom}(\ker L_a,\operatorname{coker} L_a)$ that sends $v$ to $\pi_a L_v|_{\ker L_a}$. It is independent of the nonzero representative of the projective mark. For a marked family $S$, retain the indexed dimensions
$$
 J_T(U)=\dim\bigcap_{a\in U}\ker N_a,\qquad U\subseteq S.
$$
Mode changes identify kernels, images, and quotients by invertible linear maps, so they carry each $\ker N_a$ to the matching one in the first mode. For symmetric Hessian slices, $\pi_a L_v|_{\ker L_a}$ is the restricted bilinear form on that kernel under the natural identification of the cokernel with its dual.

A single $\ker N_a$ is the tangent space to the rank-at-most-$\operatorname{rank}(L_a)$ locus at $a$. Put $L_a$ in the block form with one identity and three zero blocks, and linearize the minors of size $\operatorname{rank}(L_a)+1$. The equations are precisely the vanishing of the bottom-right block. The proposed test compares these constraints simultaneously across a selected family. For each supplied sublist, construct kernels and quotient matrices by elimination, stack their linear equations, and compute its dimension. This gives polynomial bit time over $\mathbb Q$ and fixed finite fields for polynomially many supplied marks and sublists. Enumerating all sublists or discovering the marks can be expensive.

**Separation on a smooth cubic.** Use
$$
 f=\sum_{i=1}^4x_i^3+
 \varepsilon(x_1^2x_2+x_1x_2^2+x_3^2x_4+x_3x_4^2),
 \qquad \varepsilon=1/10 .
$$
At each coordinate vector the Hessian has rank two, supported on its binary block, and its two-dimensional kernel is the other block. In that other block the two Hessian matrices at the coordinate vectors are linearly independent, since their large diagonal entries occur in different positions. Hence each $N_{e_i}$ has rank two and its kernel is the block containing $e_i$. The marked pairs $(e_1,e_2)$ and $(e_1,e_3)$ have identical individual ranks of the Hessians and normal maps, but their joint kernel dimensions are respectively $2$ and $0$. The form is geometrically smooth. At a nonzero complex point choose a coordinate of maximum absolute value $M$. Its derivative has the term $3x_i^2$ and additional terms of total absolute value at most $3\varepsilon M^2<3M^2$. This separates marked pairs without assuming any one-point invariant complete. [Bricalli–Favale–Pirola on Hessian rank strata and their local geometry](https://arxiv.org/abs/2406.12024)

## 3. Directional Smith orders along polar lines

For a matrix family of contractions $L$ and a projective line $\ell$ through $[a]$, choose $a,b$ spanning it and compute the Smith orders of the pencil $L_a+tL_b$ over the power-series ring $F[[t]]$. A vanishing diagonal entry has order $\infty$. These orders are independent of coordinates in the target and source matrix modes. They also depend only on $(\ell,[a])$, since rescaling the frame or replacing $b$ by $b+c a$ changes $t$ by an invertible local reparametrization and multiplies the pencil by a unit. Thus one may retain the orders indexed by any equivariantly marked pointed-line family.

There is a direct polynomial computation for each marked pencil of side lengths at most $n$. The sum of its finite orders is the minimum order of a nonzero minor of generic full rank and is at most $n$, since such minors are polynomials of degree at most $n$. For $k=1,\ldots,n+1$, the rank of multiplication by the pencil modulo $t^k$ is $\sum_i \max(0,k-\nu_i)$ over finite orders $\nu_i$. Compute it as the rank of a block bidiagonal matrix over $F$. Successive differences recover the finite orders and the generic rank determines the number of infinite ones. This avoids needing to enumerate all minors. Enumeration of an arbitrary intrinsic pointed-line family is a separate problem.

**Separation beyond first-order rank data along the marked line.** Put
$$
 A_0=\operatorname{diag}(1,-1,0),\quad
 A_1=\begin{pmatrix}0&0&1\\0&1&0\\1&0&0\end{pmatrix},\quad
 A'_1=\begin{pmatrix}0&0&1\\0&1&1\\1&1&0\end{pmatrix}.
$$
For $v=(x,y,z)$, take two cubic forms
$$
 a^3+b^3+x^3+y^3+z^3+\tfrac{\varepsilon}{2}
       (a v^TA_0v+b v^TA_1v)
$$
and its version with $A'_1$, where $\varepsilon=1/100$. The same maximum-coordinate derivative estimate proves smoothness. Each added derivative has absolute value at most $4\varepsilon M^2$. On the marked line spanned by $e_a,e_b$, the Hessian at $e_a+t e_b$ is $\operatorname{diag}(6,6t,\varepsilon(A_0+tA_1))$, or the primed version. In both cases the endpoints have ranks $3,4$, and the first-order restriction at $e_a$ along the line has rank one on its kernel $\langle e_b,e_z\rangle$. But the two $3\times3$ determinants are $t^2-t^3$ and $-t^3$, so the full pencil determinants have orders $3$ and $4$. The local Smith forms therefore differ. The Smith invariant for a pencil is established machinery. The candidate uses it in a covariant system of pointed lines of the original tensor. [Dopico–Noferini, local Smith forms and root polynomials](https://doi.org/10.1016/j.laa.2019.09.006)

## 4. The synchronized norm conditions for weighted étale trace tensors

For a finite étale algebra $A/F$ and $a\in A^\times$, let $T_{A,a}(x,y,z)=\operatorname{Tr}_{A/F}(a xyz)$. For two such tensors and prescribed mode determinants $(\delta_1,\delta_2,\delta_3)\in(F^\times)^3$, test the following condition, in the actual bases of the two inputs. There must be an algebra isomorphism $\sigma:A\to B$ with $d=\det\sigma$ such that
$$
  \delta_i/d\in N_{B/F}(B^\times)\quad(i=1,2,3),\qquad
  \delta_1\delta_2\delta_3=d^3 N_{B/F}(\sigma(a)/b).
$$
The condition is both necessary and sufficient. The first projection of the pair-adjoint space of $T_{A,a}$ is the regular multiplication algebra, as follows from nondegeneracy of the trace pairing and evaluation at the unit. This space consists precisely of pairs $(m_c,m_c)$. Thus any three mode transporters conjugate the regular algebras by the **same** algebra isomorphism $\sigma$, by using all three pair-adjoint spaces. The mode maps must be $m_{u_i}\sigma$, since $g_i(x)=\sigma(x)g_i(1)$. The tensor equation becomes $b u_1u_2u_3=\sigma(a)$. Taking norms gives the conditions. Conversely choose $u_1,u_2$ of the prescribed norms, and set $u_3=\sigma(a)/(b u_1u_2)$. The third norm follows from the product condition. This describes the entire set of transporter determinants and is covariant under independently changed bases by their determinant ratios.

For every fixed finite field, the norm is surjective and the product test is polynomial-time. Decompose the finite étale algebras into their finite field factors and find one algebra isomorphism by finite field isomorphism algorithms. The determinants of the others differ by the image of the automorphism group. Its generating signs are $(-1)^{d-1}$ for Frobenius on an extension factor of degree $d$ and $(-1)^d$ for switching two equal-degree factors. The former follows by a normal basis and the latter by swapping $d$-dimensional coordinate blocks. These signs generate the image because every algebra automorphism permutes isomorphic factors and acts by field automorphisms on them. If only raw tensors on the promised trace locus are supplied, solve the pair-adjoint linear equations to find the regular algebras, take a nonzero vector in each primitive component as the regular module generator on each mode, and compute the weight by inverting the trace pairing. The chosen coordinates can be checked on all basis triples, and their determinant factors are recorded. The claim over general fields is an exact criterion, with no general polynomial norm membership assertion.

**Separation from a product-only test.** Over $\mathbb Q$, take both tensors to be $T_{\mathbb Q(i),1}$ and prescribe $(3,1/3,1)$. The product equation holds for the identity algebra map. But $3$ is not a rational norm from $\mathbb Q(i)$, since the valuation at the inert prime $3$ is even for every nonzero norm. The other algebra automorphism has determinant $-1$ and cannot work either, since the norm is positive on each nonzero element and the three determinants are positive. The synchronized condition therefore rejects, although the product test alone accepts. The previously used centroid and finite-field norm techniques here provide an exact joint criterion beyond the algebra isomorphism test. [Huang–Lu–Ye–Zhang on centers of higher-degree forms](https://arxiv.org/abs/2009.12014) · [Lenstra on finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

## 5. An affine Frobenius correction for cubics in characteristic three

Let $F$ be perfect of characteristic three, and denote by $P_f$ the full third polarization of a cubic $f$, taking the coefficient of $str$ in $f(su+tv+rw)$. Its kernel as a map on cubics consists exactly of $\ell^3$ for linear forms $\ell$. A monomial of type $x_i^2x_j$ contributes a nonzero coefficient $2$ when evaluated on $e_i,e_i,e_j$. A monomial of type $x_ix_jx_k$ with distinct indices contributes coefficient one on the corresponding distinct basis vectors. Pure cubes contribute zero, and perfection allows a unique cube root of each pure-cube coefficient.

For $g$ in the exact linear stabilizer of $P_f$, let $\ell_g$ be the unique root of $f(gx)-f(x)=\ell_g(x)^3$. Then
$$
 \ell_{gh}=\ell_g\circ h+\ell_h.
$$
If the base lift of the polarization changes from $f$ to $f+\eta^3$, its cocycle changes by the coboundary $\eta\circ g-\eta$. More precisely, the cubics with a fixed polarization are parametrized by $f+\eta^3$; substitution by $g$ acts on their parameters by $\eta\mapsto\ell_g+\eta\circ g$. This is a complete residual orbit test **after** the polarizations have been identified. Cubic substitution and coefficient tests compute the offsets on supplied generators in polynomial time over fixed finite fields. This does not give a polynomial algorithm for finding a polarization isomorphism or deciding the residual affine orbit for arbitrary presentations. If just the normal tensor of the polarization is retained, the exact obstruction is the missing Frobenius data.

**Smooth separation on the same polarization.** Over $\mathbb F_3$, let
$$
 f_d=y^2z-x^3-x^2z-dz^3,\qquad d=1,2 .
$$
Their difference is a pure cube, so their polarized tensors agree exactly. The Weierstrass equations $y^2=x^3+x^2+d$ have $c_4=1$ and discriminant $-d$ in characteristic three, so both cubics are geometrically smooth and their $j$-invariants are $-1/d$, namely $2$ and $1$. Hence they fail projective equivalence even over the algebraic closure. This example separates the residual cubic information without relying on any degeneracy of the cubic hypersurfaces. The characteristic-three coefficient loss itself is classical. Its explicit affine action describes how to synchronize the leftover data under a single polar transporter. [Fisher, Weierstrass invariant formulas](https://www.dpmms.cam.ac.uk/~taf1000/ell_curves-25-0.pdf)
