# Tensor isomorphism with a common Hessian determinant and isometric unit slices

**Theorem.** Over any field $k$, ordinary three-tensor isomorphism reduces to isomorphism of fully symmetric three-tensors of linear side length, with one fixed hyperbolic Gram matrix $G$ and one fixed linear coordinate $r$ in each format. Over a finite commutative local ring $R$ with residue field $k$ and a supplied nonzero $s$ annihilating the nonzero maximal ideal $\mathfrak m$, all outputs agree entrywise modulo $sR$. The fixed Gram matrix is hyperbolic in odd residue characteristic and is a hyperbolic sum with one norm-one line in residue characteristic two. In either case the reduction reflects arbitrary independent-mode transporters and lifts input transporters to diagonal determinant-one isometries of $G$ fixing two distinguished vectors. In particular the restricted isometry problem retains the complexity of ordinary tensor isomorphism over $k$.

For an output $F_t$, write $B_t(x)=F_t(x,-,-)$, and put $r=\alpha(x)$ and $a=\lambda(x)$ for two fixed scalar coordinates. The following properties hold in all three modes.

1. Every output has the same formal polynomial $\det B_t(x)=\det(G)r^N$. The centered normalized slices $G^{-1}B_t(x)-rI$ lie in one fixed strictly triangular space, commute, and every product of four centered slices is zero.
2. Every size of matrix substitution has the same determinant polynomial. For matrices $Y_0,\ldots,Y_{N-1}$ of size $q$ with commuting scalar entries, and an output basis with $e_0=1$, one has
$$
\det\!\left(\sum_{i=0}^{N-1}Y_i\otimes G^{-1}B_t(e_i)\right)
  =\det(Y_0)^N .
$$
The matrices $Y_i$ can be noncommuting with one another.
3. On the whole open set $r\in R^\times$, there is a determinant-one congruence, polynomial in the slice coordinates and $r^{-1}$, to a common matrix depending only on $r,a$. It fixes the two distinguished basis vectors and specializes after any commutative base change. On the common affine subspace $r=1,\ a=0$, this gives a congruence to the single fixed Gram matrix $G$ at every point. If $2$ is a unit, all unit slices are congruent to $rG$ by determinant-one maps.
4. In residue characteristic two or three, all outputs have exactly the same formal cubic polynomial $F_t(x,x,x)$. In residue characteristic two, even the formal two-input polynomial $F_t(x,y,y)$ is independent of the input. All scalar laws $\lambda(x^d)$ agree for every $d\ge0$ in residue characteristic two or three. All vector-valued laws $x^d$ agree for every $d\ge0$ in residue characteristic two, and for $d\equiv0,1\pmod 3$ in residue characteristic three.

Here a unit slice means a slice with invertible matrix. All assertions about polynomials hold coefficientwise, including over nonreduced rings. The theorem applies in the usual field-arithmetic model and in polynomial bit time for finite fields and $R=\mathbb Z/p^e\mathbb Z$ with explicit coefficients.

## 1. The Frobenius carrier and the common isometry group

Use the rank-marked trilinear form $C_t$ of Section 1 of the preceding construction. There $L$ is the direct sum of the three input spaces, their three duals, three split even-dimensional spaces and their marker lines. The form is supported on the three different input spaces or on a marker and two different paired basis vectors in its block; its array entries with two equal basis indices are all zero. Every field input transporter extends to an exact diagonal isometry $P$ of $C_t$, and every projective equivalence of the $C_t$ yields an input transporter. The marked support proof works over every field. [Fully symmetric final-digit construction, Section 1](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md).

For a field take $R=k$ and $s=1$, so $\mathfrak m=0$. Otherwise take $s$ as in the theorem, so $s\in\mathfrak m$. In both cases $\jmath:k\to sR$, $\bar b\mapsto sb$, is an isomorphism of $R$-modules. Use the same carrier, now writing its free middle summands as $V$ and $V^*$, with $V$ lifting $L$:
$$
A_t=R1\oplus V\oplus V^*\oplus Q\oplus Rz .
$$
Write $N_0=32(a_1+a_2+a_3)+204$, with $a_1,a_2,a_3$ the original format. Over fields take $Q=0$. Over nonfields choose $Q$ so that $N=N_0+\operatorname{rank}Q$ is a unit. In odd residue characteristic take $Q=0$ if $N_0$ is a unit and otherwise let $Q$ be a hyperbolic pair. In residue characteristic two use one norm-one line. Write $g_Q$ for this fixed metric on $Q$. The unit is $1$. The nonzero products in the augmentation ideal, apart from transposes, are
$$
uv=\jmath\big(C_t(\bar u,\bar v,-)\big),\qquad
u\ell=\ell(u)z,\qquad qq'=g_Q(q,q')z\quad(q,q'\in Q).
$$
The first product is in $sV^*$. Let $\alpha$ take the unit coefficient and $\lambda$ the $z$-coefficient. The algebra is commutative and associative because the only possible nonzero triple product in the augmentation ideal is on three arguments in $V$, where it is the symmetric $C_t$ applied through $\jmath$ times $z$. The same rules show that the augmentation ideal has fourth power zero. Set $F_t(x,y,v)=\lambda(xyv)$. The matrix $G=B_t(1)$ pairs $1$ with $z$, each basis vector of $V$ with its dual and the $Q$-summand by $g_Q$. Its matrix is a fixed permutation.

The previously proved transporter argument also works for $s=1$ over a field. The perfect pairing identifies the output with multiplication. An arbitrary independent-mode transporter gives an isotopy, normalized by evaluating the two inputs at the unit to give a unital algebra isomorphism. Over a nonfield its augmentation ideal is intrinsic as the trace-zero space for left multiplication, since the trace at $x$ is $N\alpha(x)$ and $N$ is a unit. Over a field it is the unique maximal ideal, because it is nilpotent with quotient $k$. The annihilator of that ideal inside itself is $Rz$, by the perfect middle pairing. The triple product in the augmentation ideal, interpreted through $\jmath$ and the socle generator, induces $C_t$ after taking residues and quotienting the contraction radical. This gives the requisite projective equivalence. The field argument interprets the same triple product with $\jmath$ the identity. [Fully symmetric final-digit construction, Sections 2–3](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md).

Conversely the lifted input transporter acts by
$$
\operatorname{diag}(1,\widetilde P,\widetilde P^{-\mathsf T},I_Q,1).
$$
It has determinant one and preserves $G,1,z,\alpha,\lambda$. It induces the same transporter in all three modes. Thus the output decision also equals diagonal isometry under the literal equations $P_0^{\mathsf T}GP_0=G$, $\det P_0=1$, $P_0(1)=1$, $P_0(z)=z$, including in residue characteristic two. Over fields of characteristic two the fixed hyperbolic form is alternating, so the witnesses lie in the symplectic group fixing $1,z$. For finite fixed nonfield $R$, the known reduction of unrestricted $R$-tensor isomorphism to the prime field puts this restricted family in the same fixed-ring equivalence class. [Fixed finite ring equivalence](https://github.com/Dugongue/MathProofs/blob/main/PrimePowerTensorIsomorphism/PROOF.md).

## 2. Determinants and normalized pencil products

The defining identity for $B_t(x)$ is
$$
B_t(x)(y,v)=G(xy,v),
\qquad B_t(x)=G L_x ,
$$
where $L_x$ denotes left multiplication by $x$ in $A_t$. In the displayed basis order $1,V,V^*,Q,z$, left multiplication by an augmentation-ideal element is strictly triangular. Indeed it sends $1$ into the ideal, sends $V$ into $V^*\oplus Rz$, sends $V^*\oplus Q$ into $Rz$, and kills $z$. Hence $L_x=rI+L_{x-r1}$ is triangular with diagonal $r$. This gives $\det B_t(x)=\det(G)r^N$, and the characteristic polynomial of $G^{-1}B_t(x)$ is $(T-r)^N$. Centered left multiplications commute and their fourfold products vanish, by the commutative multiplication and the augmentation-ideal fourth power. In particular each trace or characteristic polynomial of a word in arbitrary normalized slices is determined by the same scalar coordinates.

For the matrix substitution formula reorder the tensor-product basis to use the carrier basis first. The matrix becomes triangular in blocks of size $q$. Each of its $N$ diagonal blocks is $Y_0$, because $G^{-1}B_t(1)=I$ and all other summands are strictly triangular. Determinants multiply along the diagonal blocks over every commutative scalar ring. The result holds formally before specializing any $Y_i$. Finally $r^N$ is a unit exactly when $r$ is, so the unit chart is the same for the whole hard family.

## 3. One normal matrix for the entire unit chart

The $V\times V$ block of $B_t(x)$ is $D_t=\jmath(C_t(\bar u,-,-))$ where $u$ is the $V$-component of $x$. For the universal polynomial congruence this expression means the contraction of the fixed lifted array with the formal coordinates of $u$, so it is defined after arbitrary commutative base change without a residue map of that extension. The matrix $D_t$ is symmetric and its diagonal entries are zero. Write $D_t=T_t+T_t^{\mathsf T}$ with $T_t$ strictly triangular. On the unit chart, change each basis vector $y\in V$ into $y+d(y)$ with $d:V\to V^*$ given by $-r^{-1}T_t$. Act identically on the other summands. The original $V\times V^*$ pairing is $r$ times evaluation and the $V^*\times V^*$ pairing vanishes. The change therefore subtracts $T_t+T_t^{\mathsf T}$ from $D_t$ and keeps all other pairings **among the middle vectors** unchanged. Its determinant is one.

In this new basis every middle vector $q\in V\oplus V^*\oplus Q$ pairs to zero with $z$. Also $B_t(x)(z,z)=0$ and $B_t(x)(1,z)=r$. Replace each middle basis vector $q$ by
$$
q-r^{-1}B_t(x)(1,q)z
$$
and fix $1,z$. This determinant-one change makes $1$ orthogonal to the whole middle space without changing its form there. The resulting common normal matrix consists of $r$ times the split hyperbolic pairing on $V\oplus V^*$, the form $r g_Q$, and the block
$$
\begin{pmatrix}a&r\\ r&0\end{pmatrix}
\quad\text{on }(1,z).
$$
This proves the claimed formula over the localized coordinate ring and all its specializations. Since $D_t$ vanishes modulo $sR$ in the ring case, the normalizing changes for any two outputs agree modulo $sR$. Their quotient supplies a congruence between the two slices that is the identity modulo $sR$ as well as fixing $1,z$ and preserving $\alpha$. For $a=0$ the common normal matrix is $rG$. When $2$ is a unit, replacing $1$ in the normal matrix by $1-a(2r)^{-1}z$ also puts it into $rG$, still with determinant one. This last normalization can change the distinguished vector $1$.

## 4. Common power maps and the Hessian

The difference of two outputs is supported on the $V^3$ block and on triples of distinct basis vectors. Its coefficients lie in $sR$. Restricting to three equal arguments multiplies each contributing unordered triple by $6$. In residue characteristic two or three, $6s=0$, so the restricted formal cubics coincide. In residue characteristic two, restricting the last two arguments to be equal pairs the coefficient terms with distinct second and third indices, giving a factor of $2$, and the diagonal terms are zero. This proves the two-input assertion. These conclusions also hold for $s=1$ over fields of the indicated characteristics.

For the power laws, write $x=r1+v$ with $v$ in the augmentation ideal. Between two outputs the difference in $v^2$ is in $sV^*$. In residue characteristic two it vanishes, because every changed term pairs two distinct basis indices and has coefficient multiplied by $2$. The difference in $v^3$ lies in $sRz$ and vanishes in residue characteristic two and three by the distinct-index factor of $6$. Higher powers of $v$ are zero. Thus the binomial expansion for $d\ge2$ has possible difference only in $\binom{d}{2}r^{d-2}v^2$, and $\lambda$ kills this difference. In residue characteristic three, $3\mid\binom{d}{2}$ for $d\equiv0,1\pmod3$. The cases $d=0,1$ are fixed as well. In residue characteristic two each element generates the same monogenic subalgebra in the common coordinates, with the same induced multiplication there, since all its powers agree. Over fields of characteristic two our even hyperbolic carrier in fact has $v^2=0$, so the full squaring map is $x\mapsto\alpha(x)^2 1$ throughout the hard family.

Over fields of characteristic different from two and three, the Hessian matrix of the formal cubic $F_t(x,x,x)$ is $6B_t(x)$. Thus the cubic Hessian determinant is $6^N\det(G)r^N$, the same nonzero polynomial for every output of the format. Polarization is invertible in these characteristics, so the same reduction applies to ordinary equivalence of these cubic polynomials. In particular the complex carrier lies in the persistent cubic class characterized by Gharahi and Ottaviani through a pure-power Hessian determinant. Their characterization concerns membership in that class. The resulting isomorphism hardness in one fixed Hessian fiber is the claim here. The normalized triangular Hessian calculations in the related work on Kronecker products are direct precedents for the spectral calculation. The additional statements here give explicit congruences on the unit chart, all matrix-substitution determinants for each format, and a transporter-preserving reduction over fields and finite local rings. [Gharahi–Ottaviani, Theorem 2 and Corollary 4](https://arxiv.org/html/2510.07404v1) · [*Kronecker Products of Symmetric Persistent Tensors*, Proposition 17](https://arxiv.org/html/2608.11182v1) · [Grochow–Qiao IV](https://arxiv.org/html/2306.16317).

The proof is informal. The exact control checks representative slices on two small carriers over three fields and three nonfields. It checks 96 specialized gauges, 192 determinant evaluations and 352 comparisons of power laws. Publication priority for the stated complexity and unit-chart package remains unverified.
