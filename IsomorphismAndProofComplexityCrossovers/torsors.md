# Algebraic-group torsors as ordinary tensor transporters

**Theorem.** Let $K$ be a field of characteristic zero. For two $K$-algebras $D,D'$ of the same positive dimension $d$ with bilinear multiplication, there is an explicit construction of two cubic tensors of side length $40+16d$. Their ordinary three-factor transporter, as a $K$-variety, is isomorphic to
$$
 \operatorname{Isom}_{K\text{-alg}}(D,D')\times R_d,
$$
where $R_d$ is a product $\mathbb G_m^{26}\times\prod_{j=1}^6\operatorname{GL}_{d+j}\times\mathbb A^{114+54d}$. The first isomorphism variety refers to multiplication-preserving linear isomorphisms; $D,D'$ may be nonassociative and need no unit. The construction copies multiplication coefficients and uses constants zero and one. The identification holds after every field extension. For $D=D'$, projection onto the first factor is a split algebraic-group homomorphism with geometrically connected kernel.

Consequently every torsor $X$ under a linear algebraic $K$-group $H$ occurs, up to an explicit split rational factor as above, as an ordinary three-tensor transporter. If $H$ is geometrically connected, both tensor stabilizers are geometrically connected. In particular, there exist ordinary cubic tensors over $\mathbb Q$ whose stabilizers are geometrically connected and which are isomorphic over every completion of $\mathbb Q$ but are nonisomorphic over $\mathbb Q$.

## An associative algebra with nine idempotents

Let $V$ be the underlying space of $D$, with multiplication $\mu$. Take vertices $s,t,m_0,m_1,\ldots,m_6$ and let $e_v$ be their vertex idempotents. The vertex algebra is $K^9$ with its coordinatewise multiplication. Its identity acts as the identity everywhere.

The off-diagonal space $e_sBe_t$ is
$$
 W=K\oplus V_1\oplus V_2\oplus V_3.
$$
The $V_i$ are labelled copies of $V$. The six designated subspaces $W_j$ of $W$, in order, are its scalar line, the three displayed single copies, the diagonal in $V_1\oplus V_2$, and the diagonal in $V_1\oplus V_3$. For the main vertex, the two spaces $e_sBe_{m_0}, e_{m_0}Be_t$ are both $K\oplus V$. Their product in $W$ is
$$
 (a,v)(b,w)=(ab,\; bv,\; aw,\; \mu(v,w)).
 \tag{1}
$$
For the tag $m_j$, $1\leq j\leq6$, take
$$
 e_sBe_{m_j}=K\oplus K^{d+j},\qquad e_{m_j}Be_t=W_j.
$$
Their product is $(a,\xi)w=aw$ in $W_j\subset W$. All other products of two off-diagonal components vanish, and each idempotent acts by the indicated source and target.

Write $J$ for the direct sum of off-diagonal spaces. The multiplication is associative: products of two radical elements land in $W$, and $WJ=JW=0$. Associativity involving idempotents follows from the source and target of each component, and these checks cover homogeneous triples. Thus $J^3=0$, $J$ is the radical, and $B/J=K^9$, over $K$ and over every extension. The dimensions of $W$, the two main spaces, the six tag left spaces, and the six tag right spaces are respectively $1+3d$, $2+2d$, $27+6d$, and $1+5d$. Including the nine vertices gives $40+16d$.

## Recovering the complete isomorphism variety

For clarity, identify the corresponding vertex sets in $B=B(D)$ and $B'=B(D')$. Each algebra isomorphism $\phi:B\to B'$ induces a permutation $\pi$ on the simple summands of $B/J$. Put $f_v=\phi(e_v)$. The element
$$
 a=\sum_v e_{\pi(v)}f_v
$$
equals $1$ modulo $J'$ and therefore lies in $1+J'$. The relations among the orthogonal idempotents give $af_v=e_{\pi(v)}a$. Conjugating by $a$ normalizes the idempotents. The normalizing element is unique in $1+J'$, since an element centralizing all $e_v$ has no off-diagonal part. This gives a free affine-space factor of dimension $\dim J'$, using $a\leftrightarrow a-1$. The maps and their inverses are regular, with inversion in $1+J'$ given by a truncated geometric series.

The directed graph of nonzero off-diagonal components has $s$ as its unique vertex with no incoming edge, and $t$ as its unique vertex with no outgoing edge. Both are fixed by $\pi$. The seven remaining vertices have distinct dimensions of their components out of $s$, namely $d+1$ and $d+1+j$, $1\leq j\leq6$. Hence $\pi$ is the identity. This argument works over every extension with the same labels.

An isomorphism fixing all idempotents restricts to an invertible $C:W\to W'$. The products through the six tag vertices span their individual $W_j$, so $C$ carries each to its corresponding subspace. Preserving the scalar line and the three individual copies makes $C$ block diagonal. Preserving the two diagonals makes the three $V$-blocks equal. Therefore $C=(\lambda,h,h,h)$, with $\lambda\ne0$ and $h:V\to V'$ invertible.

Let $P,Q$ be the main left and right maps. By comparing the scalar output in (1), their scalar components are $\alpha a,\beta b$, with $\alpha\beta=\lambda$. Indeed they are linear forms in their respective arguments whose tensor product is $\lambda$ times the two scalar-coordinate functions; since $\lambda\ne0$ the individual forms are proportional to those functions. The vector components initially have the form $P_V(a,v)=P_0v+a u$, $Q_V(b,w)=Q_0w+b u'$. The independent $bv$ and $aw$ outputs, evaluated at $a=b=1,\ v=w=0$, force $u=u'=0$. Comparing those outputs in general gives $\beta P_0=h=\alpha Q_0$. Comparing the fourth gives
$$
 h\mu(v,w)=\mu'(\beta^{-1}hv,\alpha^{-1}hw).
$$
Thus $M=(\alpha\beta)^{-1}h$ is exactly a multiplication-preserving linear isomorphism $D\to D'$. Conversely, arbitrary $M$ and $\alpha,\beta\in K^\times$ give $h=\alpha\beta M,\ \lambda=\alpha\beta,\ P=\alpha(1\oplus M),\ Q=\beta(1\oplus M)$. These values determine the main maps.

For tag $j$, the left radical of the tag product is precisely $K^{d+j}$. The left transform is therefore
$$
 (a,\xi)\longmapsto (\gamma_j a,\; a\eta_j+L_j\xi)
$$
with $\gamma_j\ne0,\ L_j$ invertible and $\eta_j$ arbitrary. Then the right map is forced to be $\gamma_j^{-1}C|_{W_j}$. All other products impose only idempotent compatibility and zero equations. In particular the parameter space of the full $B$-isomorphism variety is the product of $\operatorname{Isom}(D,D')$ with split tori, the six $\operatorname{GL}_{d+j}$, and affine spaces. The operations specifying the identification are regular on the relevant invertible loci. In characteristic zero we may use the reduced transporter varieties, for which agreement of these maps on geometric points proves the stated identities.

For automorphisms, the normalized subgroup fixing the displayed idempotents is a subgroup. The inner automorphisms from $1+J$ form a normal subgroup, with trivial intersection with the normalized subgroup. Hence projection to the normalized subgroup is a split group homomorphism. Within the normalized subgroup the recovered $M$ composes as expected, since the two scalar parameters multiply under composition. Setting all free parameters to their identity values defines a group section. The kernel is geometrically connected by the parameter description.

## Passing from algebra isomorphism to three-factor tensor isomorphism

Take $T(D)$ to be the multiplication tensor of $B(D)$ in $B(D)^*\otimes B(D)^*\otimes B(D)$. For the chosen input-dual convention, its ordinary transporter consists of invertible maps $X,Y,Z:B\to B'$ satisfying
$$
 Z(xy)=X(x)Y(y).
$$
This differs from the three primal factor matrices by inverting and transposing the two input matrices, which are regular changes of coordinates on the groups.

Put $u=X(1)$ and $v=Y(1)$. The equations say $Z=L_uY=R_vX$, so both multiplication operators are invertible. In a finite-dimensional unital associative algebra this forces $u,v$ to be units. For example an invertible $L_u$ gives $ub=1$, and $L_u(bu-1)=0$ gives $bu=1$. Put $M(x)=u^{-1}Z(x)v^{-1}$. Then $X(x)=uM(x),Y(x)=M(x)v$, and the isotopy equation gives $M(xy)=M(x)M(y)$. Conversely every algebra isomorphism $B\to B'$ and pair of units $(u,v)$ recover the three maps by these formulas. All are regular maps, since unit inversion can be computed with the inverse multiplication operators.

Finally $B'^\times=(K^\times)^9(1+J')$ uniquely in the chosen coordinates, with first factor the invertible diagonal part. It is, as a variety, a product of a split torus and affine space. This supplies the remaining split rational factors of $R_d$. For automorphisms, the $M$ obtained from a composite isotopy is the composite of the individual $M$'s: in the left component $u$ composes as $u_2 M_2(u_1)$, in the right component as $M_2(v_1)v_2$. So its projection is also a split group homomorphism, and the unit factors in the kernel are connected. This proves the assertion about stabilizers and their geometric components.

## Torsors and the Hasse principle

Milne's realization theorem gives, for any linear algebraic $K$-group $H$, a finite-dimensional bilinear algebra $D/K$ with $\operatorname{Aut}(D)\simeq H$. His construction generalizes Gordeev–Popov's theorem for smooth groups. Choose a finite Galois extension $L/K$ splitting a given right $H$-torsor $X$, and a point $x_0\in X(L)$. The cocycle $c_\sigma$ is defined by $\sigma(x_0)=x_0c_\sigma$. Descend $D_L$ with the semilinear action $c_\sigma\,\sigma$, which preserves multiplication. The descended algebra $D'$ has the same dimension over $K$. After identifying $D'_L$ with $D_L$, the Galois action on its isomorphisms from $D$ is $h\mapsto c_\sigma\sigma(h)$. This is also the action on $X(L)$ in the coordinates determined by $x_0$. Thus $\operatorname{Isom}(D,D')\simeq X$ as $K$-varieties and right $H$-torsors. The automorphism groups of $D$ and $D'$ become isomorphic over $\overline K$, so both resulting stabilizers have the geometric connectedness asserted above. [Milne](https://arxiv.org/abs/2012.05708) · [Gordeev–Popov](https://annals.math.princeton.edu/2003/158-3/p08)

Take $K=\mathbb Q$ and $E=\mathbb Q(\sqrt{-3},\sqrt{13})$. The affine norm equation $N_{E/\mathbb Q}(z)=3$ is Hasse's classical example of an everywhere-local norm that is not a global norm. It is a torsor under the norm-one torus; over $\overline{\mathbb Q}$ this is the connected torus defined by $z_1z_2z_3z_4=1$. The factor $R_d$ has a rational point over the base field, so tensor transporter points over any extension exist exactly when the original norm equation has a solution there. This gives the stated failure over $\mathbb Q$ with geometrically connected stabilizers. [Macedo–Newton on the Hasse norm principle, introduction](https://doi.org/10.1017/S0305004121000268)

## An explicit pair of side length 328

The norm example can be produced without searching for a group realization. In fact the construction works for any quartic field extension $E/K$ in characteristic zero, with $J:U\to U$ multiplication by a primitive element and $U=E$ in its coordinate basis. Fix a nonzero fourth exterior product $\omega$. For $c\in K^\times$, use the $18$-dimensional bilinear algebra
$$
 D_c=K e\oplus K a\oplus K b\oplus
 \bigoplus_{i=1}^4\bigwedge^i U .
$$
On the four exterior powers use the usual positive-degree exterior algebra multiplication, with products in degrees above four zero. Declare $e$ to be a left identity. Right multiplication by $e$ acts by the distinct scalars $1,2,3,4,5,6,7$ on the seven summands displayed in order. Set $a^2=a,\ b^2=b,\ ab=c\omega$ and $a u=J u$ for $u\in U$. All remaining products between $a,b$ and themselves or exterior elements are zero. These tables define an algebra with bilinear multiplication. The two-sided associative requirement is supplied later by the nine-vertex construction.

To see that these algebras have exactly the desired isomorphisms, first $e$ is the unique left identity because right multiplication by $e$ is injective. An isomorphism therefore preserves its right-multiplication eigenspaces. The separate one-dimensional idempotent equations for $a,b$ fix them individually. A map $g$ on $U$ extends uniquely on the exterior summands as the exterior powers, since those summands are generated by products of $U$. The equation for $a u$ requires $gJ=Jg$. The equation for $ab$ requires $\bigwedge^4 g(\omega)=c\omega$ in a map $D_1\to D_c$. Conversely these two identities suffice by checking the displayed products.

The commutant of $J$ is $E$ acting by multiplication. Indeed $1$ has cyclic basis $1,\theta,\theta^2,\theta^3$ for $J$, for any primitive $\theta$, so a commuting map is determined by its value at $1$ and is multiplication by that element. This proof works after all field extensions, even when $E$ becomes a product of fields. Thus $\operatorname{Isom}(D_1,D_c)$ is exactly $N_{E/K}^{-1}(c)$, with determinant of multiplication giving the norm. Isomorphisms here retain the norm torsor as a variety because the forward and reverse formulas on matrix entries are polynomial.

For the example over $\mathbb Q$ take $E=\mathbb Q(\sqrt{-3},\sqrt{13})$, the ordered basis $1,\sqrt{-3},\sqrt{13},\sqrt{-3}\sqrt{13}$, and primitive element $\sqrt{-3}+\sqrt{13}$. Its four conjugates are distinct. Take $\omega$ to be the top wedge of the ordered basis and compare $D_1,D_3$. The structure tables above and the nine-vertex construction completely specify the rational tensors, with no coefficients requiring arithmetic over $\overline{\mathbb Q}$. The side length is $40+16\cdot18=328$. The use of an asymmetric identity to mark eigenspaces follows the same principle as [Milne's Lemma 2](https://jmilne.org/math/articles/AUTO.pdf).

## Attribution and scope

The ordinary isomorphism reductions from algebras to tensors are classical in the general tensor-isomorphism framework. The unit normalization reuses the earlier MathProofs proof of isotopy for unital associative algebras. The new construction inserts one explicit split-basic associative algebra between a bilinear algebra and its tensor reduction and computes the full transporter, with connected factors. This preserves the arithmetic of torsors, beyond preserving an isomorphism decision. The polynomial side bound is measured in the dimension of the supplied algebra representing the group. There is no size bound here in terms of an arbitrary presentation of the group or torsor. The explicit norm example also admits the following small construction. These are informal proofs, and publication priority for the transporter result has not been established. [Grochow–Qiao](https://arxiv.org/abs/1907.00309) · [Earlier MathProofs isotopy normalization](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/proof-complexity.md)
