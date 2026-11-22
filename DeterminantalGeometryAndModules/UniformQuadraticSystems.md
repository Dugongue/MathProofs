# Exact uniform determinantal size of a linear system of quadrics

Let $k$ be any field, $V=k^n$, and $F\subset k[V]_{\leq 2}$ a linear subspace containing $1$. Choose a basis $f_0=1,f_1,\ldots,f_s$ and independent parameters $a_0,\ldots,a_s$. A uniform representation of $F$ is a square matrix whose entries are affine-linear in the coordinates of $V$ and separately affine-linear in the parameters, with determinant $f=\sum_i a_i f_i$ as a polynomial identity. This definition is independent of the basis. Write $q_g$ for the homogeneous quadratic part of $g\in F$.

**Theorem.** Let $e(F)$ be the maximum dimension of a linear subspace $E\subset V$ such that $q_g|_E=0$ as a polynomial for all $g\in F$. The exact minimum uniform size is $1+n-e(F)$.

For all quadratics, $e(F)=0$, since the squares of the coordinate functions already have no common nonzero vanishing direction. Thus $N^*(n,2)=n+1$ in every characteristic, including $N^*(4,2)=5$, the conjecture following Proposition 5.2 of Boralevi, van Doornmalen, Draisma, Hochstenbach and Plestenjak. The argument also bounds uniform representations with arbitrary polynomial coefficient dependence and affine-linear coordinate dependence. [Uniform determinantal representations, §5](https://doi.org/10.1137/16M1085656)

## A lower bound from the zero member

Suppose $M(a,x)$ is a representation of size $N$. Let $A(x)=M(0,x)$ and let $B_g(x)$ be the derivative in the parameter direction corresponding to $g\in F$, at $a=0$. The coefficient of $t$ in $\det(A(x)+t B_g(x))$ is $g(x)$. For $g=1$ and $x=0$ this implies $\operatorname{rank}A(0)\ge N-1$, since the linear coefficient in the determinant expansion uses only $(N-1)$-minors. Since $\det A=0$, the rank is exactly $N-1$.

If $N=1$, the parameter derivatives are affine-linear, so $e(F)=n$ and the bound holds. Otherwise put $m=N-1$. Use constant invertible row and column changes to normalize $A(0)$ to $\operatorname{diag}(I_m,0)$. The determinant identity and the directional derivative identities are now scaled by the same nonzero scalar $\gamma$. Write the normalized matrix as
$$
A(x)=
\begin{pmatrix}
I_m+L(x)&b(x)\\
c(x)^{\mathsf T}&d(x)
\end{pmatrix},
$$
where the displayed nonconstant parts are homogeneous linear. In the formal series ring at $x=0$, $I_m+L$ is invertible. Its Schur complement vanishes identically, so $d=c^{\mathsf T}(I_m+L)^{-1}b$. Comparison of the degree-one and degree-two parts gives $d=0$ and $c^{\mathsf T}b=0$.

Define $T:V\to k^m\oplus k^m$ by $T(x)=(b(x),c(x))$. Additive polarization of $c^{\mathsf T}b=0$ shows that $\operatorname{im}T$ is isotropic for the nondegenerate bilinear form
$$
\big\langle (u,v),(u',v')\big\rangle=v^{\mathsf T}u'+(v')^{\mathsf T}u .
$$
The Gram matrix has identity off-diagonal blocks in every characteristic. Inclusion of the image in its orthogonal complement gives $\dim(\operatorname{im}T)\le m$.

Set $E=\ker T$. Work in the polynomial coordinate ring $k[E]$, so restriction means a polynomial substitution even over a finite field. On $E$, the normalized zero member is $\operatorname{diag}(I_m+L,0)$. The directional determinant coefficient for any $g\in F$ therefore gives
$$
\gamma g|_E=\det(I_m+L|_E)\,(B_g|_E)_{NN}.
$$
For $g=1$ this product is a nonzero constant. Both factors are units of $k[E]$, so the determinant factor is constant. Consequently every $g|_E$ is affine-linear, and $q_g|_E=0$. Since $\dim E=n-\operatorname{rank}T\ge n-m$, this gives $N\ge 1+n-e(F)$. The coefficient argument only uses first parameter derivatives, so this lower bound allows the stated polynomial parameter dependence.

## Matching matrices and their cokernels

Choose $E$ of dimension $e(F)$ and coordinates $(X,Y)$ in which $E=\{X=0\}$ and $X$ has length $r=n-e(F)$. Each degree-two monomial appearing in the generic member contains some $X_i$. Assign it to one such $i$ in a fixed order. This writes $f=h+\sum_{i=1}^r X_i\ell_i$ with $h$ affine-linear in $(X,Y)$ and each $\ell_i$ homogeneous linear in $(X,Y)$, all linear in the parameters. Then
$$
M=\begin{pmatrix} I_r&X\\ -(\ell_1,\ldots,\ell_r)&h\end{pmatrix}
$$
has determinant $f$. Unipotent block row and column operations give $\operatorname{diag}(I_r,f)$ over the polynomial ring and commute with arbitrary base change.

In fact every such uniform representation of $F$ has cokernel isomorphic to $k[a,x]/(f)$ as a module over $R=k[a,x]$. Write $S=R/(f)$. Differentiating the determinant with respect to $a_0$ expresses $1$ in the ideal of $(N-1)$-minors of $M$. The adjugate shows that $f$ annihilates the cokernel, and local elimination where an $(N-1)$-minor is invertible exhibits the cokernel as locally free of rank one over $S$. Since $f$ is monic linear in $a_0$ with coefficient $1$, $S$ is a polynomial ring over $k$ and has trivial Picard group. This proves the isomorphism. The base change of any chosen isomorphism is again an isomorphism by right exactness of tensor product. This cokernel argument applies also to systems of higher degree containing $1$.

## Exact size with symmetric matrices

**Theorem.** If $\operatorname{char}k\ne2$, the exact minimum size of a symmetric uniform representation of $F$ is $2(n-e(F))+1$.

For the lower bound repeat the zero-member argument using a constant congruence to put its value at the origin in the form $\operatorname{diag}(H,0)$, with $H$ symmetric and invertible of size $m=N-1$. In the formal Schur complement the two off-diagonal parts are $b,b^{\mathsf T}$. The degree-two part gives $b^{\mathsf T}H^{-1}b=0$. Polarizing and dividing by $2$ shows that $\operatorname{im}b$ is totally isotropic for the nondegenerate form with matrix $H^{-1}$, hence $\operatorname{rank}b\le\lfloor m/2\rfloor$. Restricting to $E=\ker b$ again gives a block diagonal zero member. Its leading determinant must be constant by the derivative in the constant direction, so all $q_g|_E=0$. Therefore $n-e(F)\le\operatorname{rank}b\le\lfloor m/2\rfloor$.

For equality use $f=h+LX$ from the previous construction with $r=n-e(F)$, let $s=(-1)^r$, and put
$$
H=\begin{pmatrix}0&I_r\\I_r&0\end{pmatrix},\qquad
z=\begin{pmatrix}X\\-(s/2)L^{\mathsf T}\end{pmatrix},\qquad
M=\begin{pmatrix}H&z\\z^{\mathsf T}&sh\end{pmatrix}.
$$
Here $H^{-1}=H$ and $\det H=s$. The Schur complement is $sh-z^{\mathsf T}H^{-1}z=s(h+LX)$, so $\det M=f$. All entries have the required affine-linear dependence. This includes $r=0$ using the empty leading block. In particular, the full quadratic family has symmetric uniform size exactly $2n+1$.

## Exact complexity of the minimum-size decision problem

Let $G$ be a graph on $n$ vertices. Take $F$ spanned by $1$ and $x_i x_j$ for its edges $ij$. If $E$ is a common vanishing subspace, then for every edge the product $(x_i|_E)(x_j|_E)$ is zero in the domain $k[E]$. At least one coordinate restriction is therefore zero. The coordinates with nonzero restriction form an independent set, and $\dim E$ is at most the size of that set. Conversely the coordinate subspace of an independent set vanishes on every edge monomial. Writing $\alpha(G)$ for the independence number, the minimum is $n-\alpha(G)+1$.

It follows that deciding whether the minimum is at most a given bound is NP-hard over every fixed finite field, even for these monomial systems. For general systems over a fixed finite field, a basis for $E$ of the required dimension is a polynomial-size witness. Row reduction checks its dimension and coefficient comparison checks all quadratic identities in polynomial time. Hence the decision problem is NP-complete over every fixed finite field. [Karp, Reducibility Among Combinatorial Problems](https://doi.org/10.1007/978-1-4684-2001-2_9)

## A counterexample to the matrix-substitution speculation

Section 6 of the same paper defines minimality by the absence of a nonempty constant-determinant-$1$ lower-right block after constant determinant-preserving left and right changes. It speculates that all representations minimal in this sense lift to matrix polynomials by replacing coefficients with equally sized matrices and the unit with the identity. The following representation of the full one-variable affine family $p=a+bx$ is a counterexample over every field:
$$
U(a,b,x)=
\begin{pmatrix}
1&a-1&0&x\\
b&1&a-1&bx\\
0&-b&1&0\\
0&x&0&a+bx
\end{pmatrix}.
$$
Write the leading $3\times3$ block as $N$. Its determinant is $1$ by expansion in commuting coefficients, the top-right column is $x N e_1$, and the bottom-left row is $x e_2^{\mathsf T}$. Its Schur complement is $p-x^2 e_2^{\mathsf T}e_1=p$, so $\det U=p$. [Uniform determinantal representations, Definition 6.3](https://doi.org/10.1137/16M1085656)

For minimality, $U(1,0,0)=I_4$. If constant invertible $P,Z$ made $PUZ$ block upper triangular, the leading coordinate subspace would be invariant under $P U P^{-1}=(PUZ)(PZ)^{-1}$, because $PZ$ is invertible and block upper triangular. Equivalently there would be a fixed invariant subspace for $U$, with the proposed lower diagonal block having determinant equal to that of the induced quotient times a nonzero constant. Invariance under the polynomial family implies invariance under the coefficient matrices in $U(1+u,b,x)$.

Let $W=\langle e_1,e_2,e_3\rangle$. The coefficients of $u$ and $b$ are $C=A+E_{44}$ and $B$, with $A=E_{12}+E_{23}$ and $B=E_{21}-E_{32}$. Their restrictions to $W$ act irreducibly: applying a suitable power of $A$ to a nonzero vector produces a nonzero multiple of $e_1$, and $B e_1=e_2,\ B e_2=-e_3$. The coefficient $T=E_{14}+E_{42}$ of $x$ sends $e_2$ outside $W$. Thus any common invariant subspace meeting $W$ nontrivially is the whole space.

For a nonzero vector $v$ in a common invariant subspace, $Bv\in W$, so this proves the claim when $Bv\ne0$. If $Bv=0$, write $v=s e_3+t e_4$. When $s\ne0$, $(C-I)v=s(e_2-e_3)$ is nonzero in $W$. When $s=0$, $Tv=t e_1$ is nonzero in $W$. Hence $U$ has no proper nonzero common invariant subspace at all, and no nontrivial constant block triangularization in either orientation. A lower-right block of size $4$ would have determinant proportional to the nonconstant polynomial $p$, so it cannot have determinant $1$.

For the matrix-substitution failure, set $x=0$, replace $a$ by $I_2+H$ with $H=E_{12}$, and replace $b$ by $J=E_{21}$. The desired matrix polynomial is $I_2+H$ of determinant $1$. Eliminating the first and third identity blocks of the inflated $3\times3$ corner leaves the middle block $I_2-JH+HJ$, which has diagonal $(2,0)$ and is singular in every characteristic. Hence the inflated determinant is zero.

This counterexample concerns minimality as defined in Section 6. The smallest feasible scalar size for the affine family is $1$, and its size-$1$ representation does lift.

The speculation fails even for **globally smallest possible matrices** of the full quadratic family in every number $n\ge 3$ of variables. Write $p=h+L X$ as in the bordered construction, with $h(0)=a$ the constant coefficient and $b$ the coefficient of the first linear monomial. Take
$$
N_n=\begin{pmatrix}
1&a-1&0\\
b&1&a-1\\
0&-b&1
\end{pmatrix}\oplus I_{n-3},
\qquad
M=\begin{pmatrix}
N_n&N_n X\\
-L&h
\end{pmatrix}.
$$
All entries satisfy the two separate affine-linearity conditions. Since $\det N_n=1$ in the scalar coefficient ring, the Schur complement gives $\det M=h+L X=p$. Its size $n+1$ is optimal by the theorem. In particular, a decomposition as in Definition 6.3 would give a smaller representation by retaining the leading block, so $M$ meets that definition as well.

At $X=0$, substitute $a=I_2+E_{12}$ and $b=E_{21}$; set the other coefficient matrices to zero. The inflated $M$ is block diagonal because $N_n X$ and $L$ vanish at the origin. Its leading block is singular by the $I_2-E_{21}E_{12}+E_{12}E_{21}$ calculation above, while the value of the matrix polynomial is $I_2+E_{12}$, of determinant $1$. This proves the failure for minimum-size uniform quadratic representations.

The bordered construction with identity leading block always lifts. The same block-elimination proof applies after coefficient substitution because the coordinate entries are scalar multiples of identity blocks. Thus in every $n\ge3$ the same full quadratic family admits minimum-size scalar representations with different behavior under matrix substitution.

## Verification

The size formulas and block-substitution claims have written proofs. An independent written review checked the nonsymmetric formula and the substitution examples, including characteristic two. Lean 4.33.0 checked the scalar $3\times3$ determinant and the inflated $2\times2$ Schur determinant, with the usual Mathlib axioms. [Lean source](UniformCorners.lean)
