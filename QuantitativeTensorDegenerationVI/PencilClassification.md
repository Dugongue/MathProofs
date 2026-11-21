# Exact diagonal degeneration orders for semisimple multiplication pencils

Let $k$ be algebraically closed of characteristic different from two. Consider a standard graded commutative Artinian $k$-algebra with Hilbert function $(1,e,2)$ whose multiplication pencil is regular and semisimple. Let $R$ count its distinct repeated eigen-directions and $S$ count its simple eigen-directions. Its diagonal-source degeneration order is exactly two if $R\le S+3$, and exactly three otherwise. The construction allows arbitrary mixtures of these algebras and gives exact additivity for their tensor products.

## 1. Split conductors and points

For a based $n$-dimensional unital algebra $A$, write $T_A$ for its multiplication tensor, and $U_n$ for coordinatewise multiplication on $k^n$. The diagonal-source order $o_k(A)$ is the smallest $d$ such that polynomial mode matrices send $U_n$ to $t^d T_A+O(t^{d+1})$. Set $V=k[[t]]$, with fraction field $K=k((t))$. A split smoothing lattice is a unital full-rank $V$-subalgebra $L\subseteq V^n$ with $L/tL\simeq A$. Its conductor exponent $c(L)$ is least $c$ with $t^cV^n\subseteq L$. Then $o_k(A)=\min_L c(L)$, with an empty minimum interpreted as infinity.

For completeness, divide one input mode of an arc by $t^d$. It defines an integral law $m(x,y)=C(Ux\odot Wy)$ with the target special fiber. The symbol $\odot$ denotes coordinatewise multiplication. Let $e$ be the target unit, $a=Ue$, $b=We$, $S_1=m(-,e)$ and $S_2=m(e,-)$. The slices $S_1=C\operatorname{diag}(b)U$ and $S_2=C\operatorname{diag}(a)W$ are invertible over $V$. In particular all three modes are invertible over $K$ and $a,b$ have no zero coordinates. Choose $h\in\mathrm{GL}_n(V)$ reducing to the identity and taking $e$ to $m(e,e)$, for instance $I+(m(e,e)-e)\ell$ with $\ell(e)=1$. The integral normalized law $h^{-1}m(S_1^{-1}hx,S_2^{-1}hy)$ is coordinatewise multiplication conjugated by $H=h^{-1}C\operatorname{diag}(a\odot b)$. Its character rows $H^{-1}$ are integral, since the algebra is finite over the integrally closed ring $V$, and are primitive because their value at the unit is one. Thus $H^{-1}V^n$ is a split smoothing lattice. If the original three Laurent maps have entry-pole caps $p_1,p_2,p_3$ with sum at most $d$, then
\[
 US_1^{-1}h=\operatorname{diag}(a)H^{-1},\quad
 WS_2^{-1}h=\operatorname{diag}(b)H^{-1},\quad
 h^{-1}C=H\operatorname{diag}((a\odot b)^{-1})
\]
give $v_t(a_i)\ge-p_1$, $v_t(b_i)\ge-p_2$, and $-c_i-v_t(a_i)-v_t(b_i)\ge-p_3$. Here $c_i$ is least $c$ with $t^c e_i\in L$, so $-c_i$ is the minimum valuation in column $i$ of $H$. Hence $c(L)=\max_i c_i\le d$. Conversely, with $M$ the column matrix of a lattice basis lifting a basis of $A$, use $M$ on both inputs and $t^{c(L)}M^{-1}$ on the output. Truncation through degree $c(L)$ gives the required polynomial maps. This is the quantitative form of the unital tensor-to-algebra normalization. [Bläser–Lysikov, *On degeneration of tensors and algebras*](https://arxiv.org/abs/1606.04253)

For a local algebra with residue $k$ the lattice defines $F^jA=\operatorname{im}(L\cap t^j V^n\to L/tL)$. This is a multiplicative filtration with $F^1A=\mathfrak m$, $F^{c(L)+1}A=0$, and $\mathfrak m^j\subseteq F^jA$. Thus the order is at least the Loewy degree $s$.

A point presentation of $A$ means that $A$ is the associated graded algebra of $k^P$ under the polynomial degree filtration for a finite set $P$ of distinct affine $k$-points. Such a presentation gives order $s$, because an adapted basis of the point algebra scaled by the powers of $t$ given by its filtration weights gives a split smoothing lattice of conductor $s$.

Conversely, if $A$ is standard graded and level, meaning its socle is concentrated in degree $s$, order $s$ implies a point presentation. In a lattice of conductor $s$ one has $F^j=\mathfrak m^j$. Otherwise a class in $F^j$ of initial degree $i<j$ could be multiplied by a degree-$(s-i)$ class to give a nonzero product in $F^{s+1}$. Such a multiplier exists since any nonzero homogeneous element below the socle can be repeatedly multiplied by degree-one elements until reaching the top. Let $E_j$ be the possible leading coefficient vectors of $t^{-j}(L\cap t^j V^n)$. The map taking this coefficient gives $F^j/F^{j+1}\simeq E_j/E_{j-1}$, where $E_{-1}=0$. Indeed $tL\cap t^jV^n=t(L\cap t^{j-1}V^n)$ for $j\ge1$. This identification respects products, $E_0=k\mathbf1$, and $E_s=k^n$. Because the associated graded is generated in degree one, each $E_j$ consists of polynomials of degree at most $j$ in the coefficient vectors of degree one. The corresponding rows are distinct affine points, since evaluations separate all coordinates at degree $s$. This recovers a point presentation. Such presentations are Artinian reductions of reduced point schemes. [Elias–Rossi, *Inverse system of Gorenstein points in projective space*](https://arxiv.org/abs/2301.07056)

## 2. The corank budget for reduced points

For Hilbert function $(1,e,2)$ the multiplication pencil is the space of bilinear forms obtained from $A_1\times A_1\to A_2$ by composing with $A_2^*$. It is regular if some form is nonsingular. It is semisimple if, relative to a nonsingular member, the linear map associated to an independent member is diagonalizable. Its eigen-directions are the singular projective directions. At each of these the corank equals the root multiplicity of the determinant. All these multiplicities sum to $e$.

In a point presentation the $e+3$ points affinely span $k^e$. Normalize an affine basis to $0,e_1,\ldots,e_e$ and denote the other points by $p,q$. Subtracting the affine interpolant on the basis identifies the degree-two quotient with the two evaluations left at $p,q$. Since the interpolant of $x_i^2$ is $x_i$ and that of $x_i x_j$ is zero for $i\ne j$, the pencil is
\[
 M(u,v)=u pp^{\mathsf T}+v qq^{\mathsf T}-D(u,v),
 \qquad
 D(u,v)=\operatorname{diag}(up+vq).
\]
Write $P=\sum_i p_i$, $Q=\sum_i q_i$, $a=1-P$, $b=1-Q$, and $h(u,v)=a u+b v$. Generic nonsingularity implies that no coordinate pair $(p_i,q_i)$ is zero and that $(a,b)\ne(0,0)$, since otherwise a coordinate vector or the all-ones vector would be in the common kernel. For a direction $[u:v]$, let $m$ be the number of vanishing diagonal entries of $D$. Summed across distinct directions these counts are at most $e$.

When $u v\ne0$ and $m=0$, put $\alpha=p^{\mathsf T}x$, $\beta=q^{\mathsf T}x$ for a kernel vector. The equation $x=D^{-1}(up\alpha+vq\beta)$ implies that corank at least two would realize both $(\alpha,\beta)=(1,0),(0,1)$. These equations, and $D\mathbf1=up+vq$, would give $P=Q=1$. Thus the corank is at most one.

When $u v\ne0$ and $m>0$, the zero diagonal coordinates require $\alpha=\beta=\theta$, and the others give $x_i=\theta$. Taking the scalar product with $up+vq$ gives $h(u,v)\theta=0$. If $h\ne0$, the kernel has dimension $m-1$, because its only constraint on the zero diagonal group is the nonzero linear equation $p^{\mathsf T}x=0$. If $h=0$, the dimension is $m$. Indeed any $\theta$ can be realized by setting the outside coordinates to $\theta$ and solving the one linear equation $p^{\mathsf T}x=\theta$ on the group. Then the equality with $up+vq$ gives $q^{\mathsf T}x=\theta$ as well since $v\ne0$. At the axis $v=0$ the corank is $m+1$ if $P=1$, and $m$ otherwise. At $u=0$ it is $m+1$ if $Q=1$, and $m$ otherwise. For example at $v=0$, the support coordinates of a kernel vector must all equal $\alpha$, so $a\alpha=0$, whereas the other coordinates are free.

Over the repeated eigen-directions, the sum of coranks is $e-S$. At least $R-2$ of these directions are non-axis, and they all have $m>0$. If $a,b\ne0$, at most one such direction is exceptional, and there are no axis gains. If $a b=0$, the exceptional direction is an axis, and there is at most one axis gain. Either way the sum is at most $e-R+3$. Thus a point presentation implies $R\le S+3$.

## 3. Constructing every pencil at the threshold

Over an algebraically closed field of characteristic different from two, the singular directions and their multiplicities determine a regular semisimple symmetric pencil up to simultaneous congruence and an invertible change of its two parameters. To see this, choose a nonsingular form $B_0$ and diagonalize the relative map of the other form. It is self-adjoint for $B_0$, so its distinct eigenspaces are mutually orthogonal. The restriction of $B_0$ to each is nonsingular and is determined up to isometry by its dimension over this field. A regular pencil with corank equal to determinant multiplicity at all roots is semisimple, since the corresponding eigenspaces then span.

We now construct $p,q$ for the prescribed directions. For a non-axis direction write its defining form as $L_j(u,v)=b_j u+v$ with $b_j\ne0$. A group attached to this direction consists of coordinates $p_i=b_jq_i$ with $q_i\ne0$, so the group contributes
\[
 \sum_{i\text{ in group }j}\frac{p_iq_i}{up_i+vq_i}
   =\frac{r_j}{L_j(u,v)},\qquad r_j=b_j\sum_{i\text{ in group }j}q_i.
\]
A group at $v=0$ has $p_i=0$ and $q_i\ne0$. A group at $u=0$ has $q_i=0$ and $p_i\ne0$. Both axis groups contribute zero to this rational sum. Over an infinite field a group of size at least two can have any prescribed sum of nonzero entries. For group size one the prescribed sum must be nonzero.

The determinant identity used in both cases is
\[
 \det M=(-1)^e\det D
 \left[ a b+h(u,v)\sum_i\frac{p_iq_i}{up_i+vq_i}\right].
 \tag{1}
\]
Indeed, let $A_0=p^{\mathsf T}D^{-1}p$, $B_0=q^{\mathsf T}D^{-1}q$, and $C_0=p^{\mathsf T}D^{-1}q$. The bracket from the rank-two determinant lemma is $(1-u A_0)(1-v B_0)-u v C_0^2$. Using $u A_0+v C_0=P$ and $u C_0+v B_0=Q$ gives (1).

**Case $R\le S+2$.** Take a repeated direction as $v=0$ if one exists, otherwise a simple direction. Choose $u=0$ away from the spectrum. Let $\mu$ be the multiplicity of the anchor direction $v=0$, $R_0$ the number of remaining repeated directions, and $S_0$ the number of remaining simple directions. Assign a group of size $\mu-1$ at $v=0$. At each remaining repeated direction of multiplicity $m_j$, assign a group of size $m_j+1$. Add $S_0+1-R_0$ groups of size one at distinct dummy directions, avoiding both axes and all target directions. The number of coordinates is $e$, and the number of non-axis groups is $S_0+1$.

Let $G$ be the binary form with the remaining simple directions as its roots, normalized to satisfy $G(0,1)=1$. There are unique coefficients $r_j$ with
\[
 G=\sum_j r_j\prod_{l\ne j} L_l.
\]
The displayed products form a basis, as is seen by evaluating at each distinct group direction. All $r_j$ are nonzero because no group direction is a root of $G$. Choose entries in each group to have $\sum_i q_i=r_j/b_j$ there, and set $p_i=b_jq_i$. Then $P=\sum_j r_j=1$. Choose $Q\ne1$. If the axis group has positive size, varying one of its nonzero entries achieves this. Otherwise the anchor is simple and there are no repeated directions, so all non-axis groups are dummy groups. The formula $Q=G(1,0)/\prod_j b_j$ then allows us to choose the dummy directions so that $Q\ne1$.

We now have $a=0$, $b\ne0$, and $h=bv$. Formula (1) shows that the determinant is a nonzero scalar times $v^\mu G$ times the product of the remaining repeated forms to their prescribed multiplicities. From the corank formulas in Section 2, the corank at the anchor is $\mu$, at each non-axis repeated direction it is its multiplicity, and at each remaining simple direction it is one.

**Case $R=S+3$.** Choose three repeated directions as the two axes and the exceptional direction, with the latter written $L_*=b_*u+v$ where $b_*\ne0$. Assign these three groups exactly their target multiplicities. For the other $S$ repeated directions assign groups of size $m_j+1$. There are again $e$ coordinates. Fix nonzero $a,b$ so that $h=a u+b v=b L_*$. Prescribe $P=1-a$, $Q=1-b$.

Choose a binary form $G$ whose roots are the $S$ simple directions. The following expansion is unique:
\[
 G=C\prod_j L_j+h\sum_j r_j\prod_{l\ne j}L_l ,
\]
where the indices run over the other repeated directions. Evaluating at the exceptional direction determines $C$, and evaluating at each remaining group direction determines $r_j$. These evaluations show that all displayed coefficients are nonzero. Rescale $G$ to ensure $C\ne a b$, and choose $r_*=(C-a b)/b$. This makes $r_*$ nonzero. Assign each non-axis group entries with sum $r_j/b_j$ as before. The axis groups can now enforce the prescribed $P,Q$ independently, since each has size at least two. In (1) the exceptional term $h r_*/L_*$ is $b r_*$, so the bracket is $G/\prod_j L_j$. The determinant has all the prescribed multiplicities. The corank at each axis and at the exceptional direction equals its group size, at every other repeated direction it is one less than its group size, and at the simple directions it is one.

In both cases $M$ is regular semisimple with the desired spectrum and therefore gives an isomorphic multiplication pencil. Its two forms are independent because the given pencil has dimension two and, in the regular semisimple case, has at least two eigen-directions. Consequently $p,q$ are distinct from each other and from the basis points, since equality to a basis point makes its form zero and $p=q$ makes the forms equal. Their evaluation space through degree two has dimension $e+3$, by the independence of the two forms after subtracting affine interpolation. Thus the constructed points give precisely the required graded algebra.

## 4. Order three and tensor-product additivity

A regular semisimple pencil has a simultaneous diagonalization as above. This gives basis $x_1,\ldots,x_e$ in degree one, with $x_i x_j=0$ for $i\ne j$ and $x_i^2=p_i\in A_2$. There is a split smoothing of conductor at most three for **any** algebra of this diagonal type with Loewy degree two, over any field. Use one private coordinate branch per $x_i$ and $\dim A_2+1$ other branches. Let $u_i$ be the indicator of private branch $i$, and choose indicators $Z_j$ for all but one of the other branches to represent a basis of $A_2$. Let $P_i$ be the linear combination of $Z_j$ representing $p_i$. Take the lattice with basis
\[
 \mathbf1,\quad X_i=t u_i-t^2P_i,\quad t^3 Z_j.
\]
On dividing the basis columns by their indicated powers of $t$, the resulting matrix is invertible over $k[[t]]$, because its constant matrix has columns $\mathbf1,u_i,Z_j$. Hence the lattice contains $t^3 k[[t]]^{1+e+\dim A_2}$. The identities
\[
 X_i^2=tX_i+t^3P_i+t^4P_i^2,\qquad X_iX_j=t^4P_iP_j\quad(i\ne j)
\]
prove closure and give the prescribed special products. Products with a top basis vector and a positive-degree basis vector are divisible by $t^4$ in the coordinate algebra and hence vanish in the special fiber.

Regularity gives levelness since a nonzero degree-one element cannot be annihilated by all degree-one elements in a nonsingular pencil. Sections 1–3 therefore prove the order formula two for $R\le S+3$ and three otherwise.

Here is the additivity argument for arbitrary mixtures of these regular semisimple pencils. If $R>S+3$, there are at least four distinct repeated directions, so $e\ge8$ and every $p_i$ belongs to the span of the other $p_j$. The quadratic ideal kills each $x_i x_j$ for $i\ne j$ and contains all linear relations among the $x_i^2$ prescribed by the $p_i$. A relation involving $x_i^2$ with nonzero coefficient then kills $x_i^3$ after multiplication by $x_i$. It follows that the algebra is quadratic. Its quadratic relation space is spanned by products of annihilating pairs, since a relation $\sum \gamma_i x_i^2=0$ is represented by $(\sum x_i)(\sum\gamma_i x_i)$ modulo the cross products.

Let $B$ be the tensor product of $r$ such factors, and let $L$ be any split smoothing lattice of $B$. Fix a factor $A_i$ of order three with degree-one space $W_i$. We show $F^3B\cap (A_i)_2\ne0$. If this were zero, levelness would also give $F^2B\cap W_i=0$. Lift generators of $W_i$ linearly to $L\cap tV^n$, and use their first coordinate jets, after division by $t$, as a projected point set. For $x,y\in W_i$ with $xy=0$, the lift $XY/t$ lies in $L\cap tV^n$. Its residue has degree-one part in $W_i$. Indeed choose $z\in W_i$ annihilated by $y$ and linearly independent of $x$, which is possible since the degree-one annihilator has dimension at least $e-2\ge6$. The identity $(XY/t)Z=X(YZ/t)$ shows that in any different degree-one factor $W_j$ the cross component of the left-hand side is $z\otimes u_j$, whereas the right-hand side lies in $k x\otimes W_j$. This forces $u_j=0$.

Therefore every quadratic relation $f$ of $A_i$ has $f(X)/t$ reducing into $W_i+\mathfrak m_B^2$. Subtract a lift of its degree-one part, and a lift of its remaining part in $t^2V^n$, before taking its first jet. Its evaluation on the projected points is affine-linear in the projected coordinates. Thus $A_i$ surjects onto the degree-associated graded of the projected points. This is an isomorphism. If a homogeneous form $f$ of degree $j=1$ or $2$ evaluates to a polynomial of degree $<j$, write the lower polynomial as $\sum_{h<j}g_h$ with homogeneous $g_h$. Then $f(X)-\sum_{h<j}t^{j-h}g_h(X)$ has the same special class and has coordinate valuation at least $j+1$. The assumed zero intersections force its class to vanish. This gives the isomorphism in both positive degrees and contradicts the absence of a point presentation for $A_i$.

Select one nonzero degree-two class in $F^3B$ from each order-three factor, and any nonzero degree-two class, in $F^2B$, from each order-two factor. Their product is a nonzero pure tensor, so its valuation is at least the sum of the individual orders. Tensoring the constructed lattices attains this bound. Thus the tensor product has exact order $2r$ plus the number of factors with $R>S+3$.

These are informal proofs.
