# Polynomial-time dyadic matrix tuple isometry with commutative commutant

Let $R=\mathbb Z/2^\tau\mathbb Z$ with arbitrary compact exponent $\tau$, or a finite field of characteristic two in its usual polynomial-basis encoding. Given two ordered tuples of square matrices $A_i,B_i$, assume that in each position the matrices have the same transpose sign at the two endpoints. A specified common linear combination gives invertible anchors $A_0,B_0$ of the same transpose sign. The first position itself can be the anchor. Put $C_i=B_0^{-1}B_i$ and let $E$ be the commutant of these matrices. If $E$ is commutative, simultaneous congruence $P^TA_iP=B_i$ can be decided, constructed and counted exactly in deterministic polynomial bit time. Compute $E$ by linear congruences and check its commutativity on module generators. The adjoint can act nontrivially on this algebra, and the algebra may contain nilpotents and may be nonfree over the coefficient ring.

Sun separates strict left–right equivalence and congruence over $\mathbb Z/2^\tau\mathbb Z$ and gives a superpolynomial bound for general alternating tuples. Grochow–Qiao–Stange–Sun reduce the odd-characteristic case to an adjoint equation. For a commutative commutant, the last equation is a group homomorphism problem. We solve it on the odd-order quotient and the nilpotent unit filtration in residue characteristic two. [Sun, Appendix A](https://arxiv.org/html/2611.05920v1#A1) · [Part V, §§1.4 and 5.3](https://arxiv.org/html/2611.00735v1#S5.SS3) · [Ivanyos–Qiao](https://arxiv.org/abs/1708.03495)

## A norm equation on the commutant

Let $A'_i=A_0^{-1}A_i$. A congruence is an invertible intertwiner $A'_iP=PC_i$ satisfying the anchor equation $P^TA_0P=B_0$. Find one invertible intertwiner $P_0$ by ordered module equivalence. Over the ring this is the strict equivalence test in the companion proof, with an identity arrow to equate its two basis changes. Over a field it is ordinary constructive module isomorphism. If there is no intertwiner, there is no congruence.

Set $D=P_0^TA_0P_0$, and write $\sigma_0,\sigma_i\in\{1,-1\}$ for the transpose signs at the anchor and position $i$. The equalities
$$
C_i^T D=\sigma_0\sigma_i D C_i,\qquad
C_i^T B_0=\sigma_0\sigma_i B_0 C_i
$$
follow from the symmetry assumptions and $D C_i=P_0^TA_iP_0$. They imply $S=D^{-1}B_0\in E^\times$. The adjoint $U^*=B_0^{-1}U^TB_0$ preserves $E$ because it fixes $C_i$ up to sign. It is an involution on $E$ since $B_0^T=\sigma_0 B_0$, and it fixes $S$ because $D$ and $B_0$ have the same sign. For $U\in E$ use $D=B_0S^{-1}$ and commutativity to get $U^TD=DU^*$. Every candidate is uniquely $P_0U$ for $U\in E^\times$. Its anchor equation becomes
$$
(P_0U)^TA_0(P_0U)=D U^*U=B_0,\qquad\text{or equivalently}\qquad N(U)=S,
\qquad N(U)=U^*U.
$$
This is an equation in the abelian group $E^\times$, and $N$ is a homomorphism. Each solution determines the congruence in every position by intertwining.

## Solving the norm equation

Over the ring compute $J$ as the inverse image of the radical of the actual image of $E$ modulo $2$, using the computation in the companion proof. Over a finite field of characteristic two, view $E$ as an algebra over $\mathbb F_2$ and compute its radical $J$ directly. The coefficient field degree contributes polynomially to the input and the binary algebra dimension, so the deterministic algorithms for fixed base field apply. In both cases $J$ is nilpotent and $E/J$ is a product of finite fields of characteristic two, say of degrees $h_j$ over $\mathbb F_2$. The Jacobson radical is preserved by the involution. The group $H=1+J$ has power-of-two order. The odd integer $m=\prod_j(2^{h_j}-1)$ kills the quotient unit group. Consequently $S^m\in H$.

It suffices to test whether $S^m$ belongs to $N(H)$. If $N(Y)=S^m$ for $Y\in H$, take integers $a,b$ with $am+2b=1$ and return $Y^a S^b$ as a norm preimage of $S$. This uses $S^*=S$. Conversely a norm preimage of $S$ raised to $m$ is in $H$ and has norm $S^m$. The bits of $m$ are bounded by the binary dimension of the quotient algebra.

Generate $H$ with lifts $1+x$ of bases for the layers $J^i/J^{i+1}$. These are $\mathbb F_2$-spaces since $2J^i\subseteq J^{i+1}$ in the ring case, and $2=0$ in the field case. Multiplication of units gives addition on each such layer. Take norms of those generators and retain the original generator as its preimage label. For membership in $N(H)$ project the current generators to $J^i/J^{i+1}$ at layer $i$ and pick independent pivot images. Remove the image of every other generator using the inverse of a product of pivots. The adjusted generators, together with the squares of the pivots, generate the kernel at that layer. Indeed, using commutativity, one can put every word into a product of these elements and pivot factors of exponent zero or one. Independence forces all final pivot exponents to vanish for an element of the kernel. Remove the target’s image by the same pivots, failing when it is outside their span. Iterate down the filtration. Retain the preimage labels under multiplication, inversion and squaring. This gives one $Y$ when membership holds, and the product of the powers of two given by the pivot ranks gives $|N(H)|$.

The number of generators never increases in this computation. With $k$ generators and pivot rank $r$, the next list has at most $k-r$ adjusted generators and $r$ pivot squares. The number of layers is bounded by the dimension of the reduced algebra times $\tau$ in the ring case, and the dimension of the binary algebra in the field case. Ring arithmetic and the subgroup and ideal calculations use polynomial-size matrices and exponents.

For counting, the finite abelian group $E^\times$ is the product of its $2$-part $H$ and its odd-order part. The latter maps isomorphically to $K=(E/J)^\times$. Both parts are invariant under the adjoint. The norm on the $2$-part has kernel of order $|H|/|N(H)|$. The image of the norm on $K$ is exactly the adjoint-fixed units. It is contained there because the factors commute. Conversely, every fixed element has a unique square root in the odd-order group $K$, and this root is fixed by the involution, giving a norm preimage. The number of fixed units is computed from the involution on the field factors. A swapped pair contributes the unit count of either field. A fixed field contributes its fixed subfield size minus one, with that subfield determined by binary linear equations for the fixed elements. Thus, when one solution exists, the exact number is
$$
\frac{|H|}{|N(H)|}\,\frac{|K|}{|K^{*}|},
\qquad K^{*}=\{k\in K:k^*=k\}.
$$
All quantities have polynomial bit length.

## Alternating examples and a nontrivial adjoint

For even $n\ge4$, take the standard alternating symplectic anchor with paired indices $i\leftrightarrow\bar i$, and all elementary alternating forms supported at $(i,j),(j,i)$ for $i<j$. Commuting with their ratios preserves the coordinate kernels omitting $i,j$. Intersecting these kernels shows that a commuting map is diagonal. The ratio for $(i,j)$ takes $e_i$ to a unit multiple of $e_{\bar j}$. Thus the diagonal entries at nonpartner pairs agree, and then all agree. The commutant is $R$ acting by scalars.

For a different example put $B_0=\left(\begin{smallmatrix}0&I_2\\-I_2&0\end{smallmatrix}\right)$ and use $C_i=\operatorname{diag}(L_i,L_i^T)$ for $L_i=E_{11},E_{22},E_{12},E_{21}$. Set $B_i=B_0 C_i$, which are all alternating. Commuting with the diagonal matrix units forces each $2\times2$ block of a commuting matrix to be diagonal. Intertwining $E_{12},E_{21}$ with their transposes forces both cross blocks to vanish, and the two diagonal blocks must be scalar. Here $E\simeq R\times R$ and the adjoint exchanges the factors. This family satisfies the hypotheses in every stated characteristic and exhibits a nonidentity adjoint.

The Lean lemma checks the matrix congruence-to-norm step under its displayed adjoint identity. The full algorithm, counting argument and input promise are proved above in prose.
