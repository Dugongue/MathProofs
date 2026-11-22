# A linear tensor carrier from Euler derivations of cubics

Let $F$ be a field of characteristic three and $V=F^n$. All forms are formal homogeneous polynomials. For a cubic $f$, write $P_f$ for its unnormalized complete polarization. Define the linear map

$$
\Psi_{P_f}\colon\operatorname{End}(V)\longrightarrow \operatorname{Sym}^3(V^*),
\qquad
\Psi_{P_f}(A)(x)=\tfrac12 P_f(Ax,x,x).
$$

It is the derivative of $f(x+tAx)$ at $t=0$. This follows by expanding any cubic monomial and holds for every characteristic-three field. In particular $\Psi_{P_f}$ depends only on the polarization, including when derivatives erase pure cubes.

**Theorem.** For a nonzero cubic $f$ in the image of $\Psi_{P_f}$, put $K_f=\ker\Psi_{P_f}$. On this class, exact cubic equivalence reduces to one ordinary tensor isomorphism instance over $F$ with side lengths $O(n+\dim K_f)$. The construction and transporter recovery use a polynomial number of field operations. In particular the sides are linear on the promise $\dim K_f=O(n)$. Both promises can be tested by coefficient linear algebra. The zero cubic can be compared directly.

## The affine matrix coset

Choose any solution $A_f$ of $\Psi_{P_f}(A_f)=f$. Its choice defines the presentation of the intrinsic affine coset $A_f+K_f$. Let $E_f=K_f\oplus F$ and define

$$
G_f(B,s)=B+sA_f,\qquad \pi_f(B,s)=s .
$$

The map $G_f$ is injective since $f\ne0$. The slice $\pi_f=1$ maps onto the affine coset. If $h:V\to V$ obeys $P_f(x,y,z)=P_g(hx,hy,hz)$, covariance gives

$$
\Psi_{P_f}(A)(x)=\Psi_{P_g}(hAh^{-1})(hx).
$$

Therefore $f=g\circ h$ holds precisely when $h$ carries the affine coset of $f$ to that of $g$ by conjugation. Indeed a polarization isometry already conjugates the two kernels, and the coset assertion is equivalent to $hA_fh^{-1}-A_g\in K_g$. This uses the affine fiber at $\pi=1$, so its conclusion is literal polynomial equivalence over $F$.

## One linked tensor and its decoder

Use three marked direct-sum legs

$$
(V_1\oplus A_1\oplus R_1),\qquad
(V_2\oplus B_2\oplus R_2),\qquad
(V_3\oplus R_3\oplus E_f).
$$

The $V_i$ are copies of $V$, $A_1,B_2$ are copies of $V^*$, and $R_i$ are copies of $F$. Displayed summands are the parts for partitioned tensor isomorphism. Write $x,y,z$ for arguments in the $V_i$, $\xi,\theta$ for arguments in $A_1,B_2$, $s,t,c$ for arguments in $R_1,R_2,R_3$, and $k$ for an argument in $E_f$. The only nonzero blocks allowed are

| Parts | Entry |
| --- | --- |
| $V_1,V_2,V_3$ | $P_f(x,y,z)$ |
| $V_1,B_2,R_3$ | $c\,\theta(x)$ |
| $R_1,B_2,V_3$ | $s\,\theta(z)$ |
| $A_1,V_2,R_3$ | $c\,\xi(y)$ |
| $A_1,R_2,V_3$ | $t\,\xi(z)$ |
| $R_1,R_2,R_3$ | $stc$ |
| $V_1,B_2,E_f$ | $\theta(G_f(k)x)$ |
| $R_1,R_2,E_f$ | $st\,\pi_f(k)$ |

Suppose substitution by an invertible partitioned witness carries the tensor for $g$ to that for $f$. Write $S$ for its map on $V_3$, $S_1,S_2$ for its first two $V_i$ maps, $L$ for its map $E_f\to E_g$, and $\alpha_i$ for its nonzero scalar on $R_i$. The scalar anchor gives $\alpha_1\alpha_2\alpha_3=1$. The evaluation blocks imply

$$
S_1=(\alpha_1/\alpha_3)S,\qquad S_2=(\alpha_2/\alpha_3)S,\qquad
B'_2=(1/\alpha_1)S^{-*}.
$$

For example, the two equations involving $B_2$ are $\alpha_3(B'_2\theta)(S_1x)=\theta(x)$ and $\alpha_1(B'_2\theta)(Sz)=\theta(z)$. Evaluation on all dual vectors gives the stated formulas. Put $h=S/\alpha_3$ and $L'=L/\alpha_3$. The polarization block gives $P_f(x,y,z)=P_g(hx,hy,hz)$. The graph and functional blocks give

$$
G_f(k)=S^{-1}G_g(L'k)S,\qquad \pi_f(k)=\pi_g(L'k).
$$

Indeed the $V_1,B_2,E_f$ block contributes a factor $1/\alpha_3$ from its first two argument maps, and the $R_1,R_2,E_f$ block contributes $\alpha_1\alpha_2=1/\alpha_3$. Conjugation by $S$ and by $h$ agree. It follows that $h$ transports the $\pi=1$ affine fibers and decodes to an actual cubic equivalence.

Conversely, from $f=g\circ h$, use $h$ in each $V_i$, its inverse dual in $A_1,B_2$, and the identity in $R_1,R_2,R_3$. On $E_f$ use

$$
(B,s)\longmapsto
\bigl(hBh^{-1}+s(hA_fh^{-1}-A_g),s\bigr).
$$

Covariance makes this an invertible map $E_f\to E_g$, and all eight blocks are preserved. The resulting partitioned tensor has side lengths $2n+1,2n+1,n+\dim K_f+2$. There are three parts in each mode, so the existing constant-part decoloring carries it to one ordinary tensor while preserving linear dependence on the input sides and providing witness recovery. Unequal kernel dimensions certify inequivalence before construction and can be mapped to a fixed negative ordinary instance. [Grochow–Qiao, Part IV, Theorem 5.1](https://arxiv.org/html/2306.16317#S5) · [Pure-cube tensor carrier and linked evaluation blocks](https://github.com/Dugongue/MathProofs/blob/main/GrochowPureCube/Tensor.md).

## A family with scalar centroid and one-dimensional Euler kernel

For $m\ge4$ with cyclic subscripts, put $n=2m$ and

$$
f_m(x,y)=\sum_{j=1}^m y_j q_j(x),\qquad q_j=x_j^2+x_jx_{j+1}.
$$

Projection onto the $Y$-variables is an Euler solution $A_f$. The polarized $X,X,Y_j$ block is a symmetric form $H_j$ on $X$, supported on indices $\{j,j+1\}$ with matrix $\begin{pmatrix}2&1\\1&0\end{pmatrix}$ there. The $H_j$ are independent, as seen at diagonal entries, and their radicals intersect in zero. Pairing a polarization-radical vector first with an $X$ and a $Y$ input and then with two $X$ inputs proves that $P_f$ has zero radical.

Write a centroid operator as $\begin{pmatrix}A&B\\ C&D\end{pmatrix}$ on $X\oplus Y$. For two $Y$ inputs and one $X$ input, moving the operator to the $X$ input gives zero. Moving it to a $Y$ input and using the common radical condition forces $B=0$. On two $X$ inputs and $Y_j$, the centroid identities say $A$ is self-adjoint for every $H_j$, hence preserves $\ker H_j$. For a coordinate line $F x_i$, intersect the kernels whose adjacent pair omits $i$. The intersection is $F x_i$, since every other coordinate belongs to an adjacent pair omitting $i$. Thus $A$ is diagonal. The off-diagonal entry in $H_j$ forces equality of its eigenvalues on $x_j,x_{j+1}$. This gives $A=aI$, and the independent $H_j$ then give $D=aI$.

The map $C:X\to Y$ must make $H_{C(x)}(x',x'')$ fully symmetric on three $X$ inputs. Here write $C_{j,i}$ for the coefficient at $y_j$ on input $x_i$. Symmetry on $(i,j,j)$ gives $C_{j,i}=0$ for $i\notin\{j-1,j,j+1\}$, and gives

$$
2C_{j,j+1}=C_{j,j},\qquad 2C_{j,j-1}=C_{j-1,j}.
$$

On $(j-1,j,j+1)$, the pair $(j-1,j+1)$ is nonadjacent, so symmetry gives $C_{j,j-1}=0$. The displayed equations then force $C=0$. Thus the centroid consists of scalars. This provides a family with a single intrinsic polarization block of unbounded dimension. [Huang, Lu, Ye and Zhang, *Centers of Multilinear Forms and Applications*](https://doi.org/10.1016/j.laa.2023.05.012).

To compute the Euler kernel, write an infinitesimal substitution as $\delta x=Jx+Qy,\ \delta y=Rx+Sy$. The $x^3$ portion of the derivative is $\sum_i (Rx)_i q_i(x)$. Pure monomials force $R_{ii}=0$. For $i\ne j$, the coefficient of $x_i^2x_j$ is $R_{ij}$, except that $j=i-1$ also contributes $R_{i-1,i}$ and $j=i+1$ contributes the already vanishing $R_{ii}$. The successor coefficients kill all potentially remaining predecessor coefficients. Thus $R=0$. The $xy^2$ coefficients require $H_i Q_i=0$ and $H_iQ_j+H_jQ_i=0$, with $Q_j$ the $j$-th column. Disjoint adjacent pairs have disjoint supports. For a fixed $j$, pairs disjoint from $\{j,j+1\}$ cover its complement, so these equations and $H_jQ_j=0$ give $Q_j=0$.

The $x^2y$ coefficients require $D_J q_j\in\operatorname{span}\{q_i\}$, and determine $S$ uniquely. The coefficient of $x_{j+1}x_k$ in $D_Jq_j$, for $k\notin\{j,j+1,j+2\}$, is $J_{jk}$ and must vanish as this pair is nonadjacent. Write $a_j,b_j,c_j$ for the remaining entries in row $j$, at columns $j,j+1,j+2$. The coefficient of $x_jx_{j+3}$ is $c_{j+1}$. It vanishes when $m\ge5$ by nonadjacency. At $m=4$ this is the predecessor edge, and its required matching diagonal coefficient of $x_{j+3}^2$ is zero, so it again vanishes. Then the coefficient of $x_jx_{j+2}$ is $b_{j+1}$ and vanishes by nonadjacency. With $J$ diagonal, equality of the $x_j^2$ and $x_jx_{j+1}$ coefficients gives $2a_j=a_j+a_{j+1}$. Hence $J=aI$ and $S=-2aI=aI$ in characteristic three. This proves $K_f=FI$. Direct row reduction over $\mathbb F_3$ gave centroid and Euler kernel dimensions $1,1$ for each $m=4,5,6,7,8$.

## Unrestricted marked elementary abelian matrix subgroups

There is also a different linear-degree carrier for every characteristic-three cubic over an explicit finite field. It has a marked matrix-subgroup conjugacy target. Form the graded unital algebra

$$
B_f=F\oplus V\oplus V^*\oplus Fz
$$

with $xy=P_f(x,y,-)$, $x\lambda=\lambda x=\lambda(x)z$, and all other positive-degree homogeneous products zero. Its associativity follows from the symmetry of $P_f$ on three degree-one arguments. For $x\in V$ put

$$
u_f(x)=1+x+\tfrac12x^2+f(x)z .
$$

The polarization identity in degree three gives
$f(x+y)-f(x)-f(y)=\tfrac12(P_f(x,x,y)+P_f(x,y,y))$.
Expanding in $B_f$ therefore gives $u_f(x)u_f(y)=u_f(x+y)$. The degree-one coordinate makes this an injective homomorphism of additive groups. Hence the left multiplication matrices $L_{u_f(x)}$ form an elementary abelian subgroup of $\mathrm{GL}(2n+2,F)$, generated by the matrices for a prime-field basis of $V$. This avoids listing the group elements.

Mark the four graded spaces and the vectors $1,z$. A grade-preserving marked conjugator $S$ satisfies $S1=1$ and $Sz=z$. From $SL_{u_f(x)}S^{-1}=L_{u_g(y)}$, evaluation on $1$ gives $Su_f(x)=u_g(y)$. Degree one gives $y=hx$ with $h=S|_V$, while degree three gives $f(x)=g(hx)$. This is a formal equality. When $q>3$, all coordinate exponents are below $q$ and polynomial evaluation is injective at those coordinate degrees. When $q=3$, reduce the pure cubes $x_i^3$ to $x_i$. All mixed cubic monomials already have individual exponents below three, and their reductions are distinct from each other and from the linear monomials. Thus evaluation is still injective on formal homogeneous cubics. Conversely, if $f=g\circ h$, covariance of the polarization makes the map $h$ in degree one, its inverse dual in degree two, and the identity on $1,z$ an algebra isomorphism carrying $u_f(x)$ to $u_g(hx)$. It conjugates the marked groups.

This intermediate uses the subgroup as a set of matrices. Its linear span can discard the required information. The identities
$u_f(x)-u_f(-x)=2(x+f(x)z)$ and $u_f(x)+u_f(-x)-2=x^2$
show that the span contains all $x+f(x)z$ and $x^2$, as well as $1$. Conversely these elements span all $u_f(x)$. For a nonadditive $f$, the differences at $x,y,x+y$ give a nonzero multiple of $z$. The span is then $F1\oplus V\oplus\langle x^2:x\in V\rangle\oplus Fz$, which depends only on the polarization. The truncated logarithms also span $V\oplus Fz$, since $x^3=P_f(x,x,x)z=0$ and $\log_2(u_f(x))=x+f(x)z$.

For example, over $\mathbb F_3$ the cubics $x^2y$ and $x^2y+y^3$ have the same polarization and the same matrix span. They have two and one projective zeros, respectively, so the marked subgroups are inequivalent. Logarithm-based reductions for abstract group isomorphism use an algebraic model with different hypotheses and target structure. The exact result here is the marked subgroup construction of degree $2n+2$. [Grochow–Qiao, *On $p$-Group Isomorphism*](https://doi.org/10.4230/LIPIcs.CCC.2021.16) · [Grochow–Qiao, Part IV](https://arxiv.org/abs/2306.16317).

The Euler construction gives ordinary tensor isomorphism on its stated image-and-kernel promise. The unrestricted construction gives marked subgroup conjugacy. The arguments are written proofs with the finite rank checks above. Publication priority for the combined constructions remains unconfirmed.
