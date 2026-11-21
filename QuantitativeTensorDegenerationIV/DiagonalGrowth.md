# An unbounded diagonal degeneration gap in characteristic two

For every algebraically closed field $k$ of characteristic two and every positive integer $r$, the explicit algebra below has dimension $11^r$, Loewy degree $2r$, and diagonal tensor degeneration order exactly $3r$. Its multiplication tensor has border rank $11^r$. The lower bound applies to arbitrary, independent maps on the three tensor modes.

## 1. Quantitative algebra normalization

Let $R=k[[t]]$, $K=k((t))$, and let $U_n=\sum_{i=1}^n e_i^*\otimes e_i^*\otimes e_i$ be the multiplication tensor of $k^n$. For a based $n$-dimensional unital algebra $A$, write $o_k(A)$ for the least $d\ge0$ for which polynomial mode matrices give
\[
 (P_1(t)\otimes P_2(t)\otimes P_3(t))U_n=t^dT_A+O(t^{d+1}),
\]
where $T_A$ is the multiplication tensor of $A$. If no formal arc exists put $o_k(A)=\infty$. A split smoothing lattice means a full-rank unital $R$-subalgebra $L\subset R^n$ with $L/tL\simeq A$. Its conductor exponent $c(L)$ is the least $d$ with $t^dR^n\subseteq L$. Then $o_k(A)=\min_L c(L)$.

To verify this equality, divide one input map of a polynomial arc by $t^d$ to obtain an integral law $m(x,y)=C((Ux)\odot(Vy))$ reducing to the multiplication of $A$. Here $\odot$ is the coordinatewise product, and the three entry-pole caps $p_1,p_2,p_3$ of $U,V,C$ sum to at most $d$. For the unit $e$ in the chosen based target, put $S=m(-,e)$, $D=m(e,-)$, $a=Ue$, $b=Ve$. The slices $S=C\operatorname{diag}(b)U$ and $D=C\operatorname{diag}(a)V$ are integrally invertible because their reductions are the identity. This forces all entries of $a,b$ to be nonzero, and gives invertibility of $C,U,V$ over $K$. Choose an integral $h\equiv I\bmod t$ with $he=m(e,e)$, for example $h=I+(m(e,e)-e)\ell$ for $\ell(e)=1$. Set $H=h^{-1}C\operatorname{diag}(a\odot b)$. Substitution gives
\[
 h^{-1}m(S^{-1}hx,D^{-1}hy)=H((H^{-1}x)\odot(H^{-1}y)).
\]
The law on the left is integral, with unit $e$ and with the same special fiber as $m$. Hence $L=H^{-1}R^n$ is a unital lattice inside $R^n$. Indeed its generic coordinate characters take integral values on the finite $R$-algebra, and each row of $H^{-1}$ has minimum valuation zero since it evaluates to one at the unit. Let $c_i$ be the least exponent with $t^{c_i}e_i\in L$. The minimum valuation of column $i$ of $H$ is $-c_i$. The identities
\[
 US^{-1}h=\operatorname{diag}(a)H^{-1},\qquad
 VD^{-1}h=\operatorname{diag}(b)H^{-1},\qquad
 h^{-1}C=H\operatorname{diag}((a\odot b)^{-1})
\]
give $v_t(a_i)\ge-p_1$, $v_t(b_i)\ge-p_2$, and $-c_i-v_t(a_i)-v_t(b_i)\ge-p_3$. Thus $\max_i c_i=c(L)\le d$. Conversely, with $M$ the column matrix of a basis of a lattice lifting the chosen target basis, use $M$ on the two inputs and $t^{c(L)}M^{-1}$ on the output. These maps are integral and truncating all of them through degree $c(L)$ preserves the leading tensor. The normalization uses the unital tensor-to-algebra degeneration of Bläser and Lysikov, with valuations retained on all three modes. [Bläser–Lysikov, *On degeneration of tensors and algebras*](https://arxiv.org/abs/1606.04253)

For a local target with maximal ideal $\mathfrak m$ and residue $k$, use the multiplicative filtration
\[
 F^jA=\operatorname{im}(L\cap t^jR^n\longrightarrow L/tL).
\]
The branch reductions are all the residue character, so $F^1A=\mathfrak m$. Also $\mathfrak m^j\subseteq F^jA$ and $F^{c(L)+1}A=0$. In particular, a nonzero product of factors whose lifts have coordinate valuations at least $j_1,\dots,j_m$ forces $c(L)\ge\sum_i j_i$.

## 2. Frobenius detects generators of valuation at least two

**Lemma.** Let $k$ have characteristic two. Suppose $A$ is a finite standard graded commutative $k$-algebra, presented by degree-two relations, and every element of $\mathfrak m=A_{>0}$ squares to zero. Every split smoothing lattice of $A$ induces a graded, Frobenius-semilinear unital endomorphism $\Phi:A\to A$ with
\[
 \ker(\Phi^n|_{A_1})\subseteq F^2A
 \qquad(n\ge1).
\]

For $x\in\mathfrak m$ choose a lift $X\in L\cap tR^n$. Since $x^2=0$, the quotient $X^2/t$ belongs to $L\cap tR^n$. Its class defines $\psi_1(x)\in\mathfrak m$. Two lifts differ by $tY$ with $Y\in L$, so their squares divided by $t$ differ by $tY^2$ and give the same class. The map is additive and sends a scalar multiple by $a$ to a scalar multiple by $a^2$. It kills $\mathfrak m^2$, since the lift of a product can be chosen as a product, and
\[
 (XY)^2/t=t(X^2/t)(Y^2/t).
\]
It also preserves $F^2A$, since if $X\in t^2R^n$ then $X^2/t\in t^3R^n$.

The induced map on $\mathfrak m/F^2A$ is injective. Indeed, for $X\in L\cap tR^n$ let $v=(X/t)\bmod t\in k^n$. A class is zero in $\mathfrak m/F^2A$ exactly when $v$ is constant across branches. In one direction subtract $t$ times that constant to obtain a lift in $t^2R^n$. In the other direction the difference from such a lift is $tY$ with $Y\in L$, whose reduction is constant. The vector of the new lift $X^2/t$ after dividing by $t$ and reducing is $v^{\odot 2}$. If it is constant, $v$ is constant by injectivity of squaring in a field.

For $z\in\mathfrak m^2$, choose a lift $Z$ which is a sum of products of radical lifts in $tR^n$. Then $Z\in t^2R^n$ and $Z^2/t^2\in L$ by multiplicativity of squaring and the existence of $X^2/t$ on each factor. The class of $Z^2/t^2$ in $A$ gives a map $\psi_2:\mathfrak m^2\to\mathfrak m^2$. If two such lifts differ by $tY$, then $Y\in L\cap tR^n$, so the two outputs differ by $Y^2\in tL$. Thus the map is well-defined, semilinear, and satisfies $\psi_2(xy)=\psi_1(x)\psi_1(y)$. Lifting a product of three radical elements shows that $\psi_2$ kills $\mathfrak m^3$, because $(XYZ)^2/t^2=t(X^2/t)(Y^2/t)(Z^2/t)$.

Using standard grading, these maps induce maps in degrees one and two whose products agree. Therefore the semilinear map induced by $\psi_1$ on $A_1$ preserves all quadratic relations and extends to the graded semilinear unital endomorphism $\Phi$. Since $\mathfrak m^2\subseteq F^2A$, the action of $\Phi$ on $\mathfrak m/(\mathfrak m^2+F^2A)$ identifies with that of $\psi_1$ on $\mathfrak m/F^2A$. More explicitly, the identification $A_1\simeq\mathfrak m/\mathfrak m^2$ takes $A_1\cap F^2A$ to $F^2A/\mathfrak m^2$, and the quotient action is the injective map just proved. The same holds for every positive iterate, giving the kernel inclusion.

## 3. An exact additivity criterion

**Theorem 1.** Work over a perfect field of characteristic two. Let $A_1,\dots,A_r$ be standard graded level algebras with common Hilbert function $(1,e,h)$, where $h\ge1$ and $e-h\ge2$. Level here means that each socle is its degree-two part. Suppose they are quadratic and every degree-one element squares to zero. Suppose also $o_k(A_i)\le3$ for all $i$. Let $I$ be the set of indices $i$ for which some positive Frobenius twist of $A_i$ is graded-isomorphic to none of the factors. Then
\[
 2r+|I|\le o_k\!\left(\bigotimes_{i=1}^r A_i\right)\le3r.
\]
In particular, the order is exactly $3r$ if every factor satisfies the twist condition.

Here the $n$-th Frobenius twist of an algebra has each multiplication structure constant raised to $2^n$ in a corresponding basis. A degree-wise Frobenius-semilinear homomorphism becomes linear from this twist by sending the twisted basis to the images of the original basis. A tensor product of the individual split lattices gives the upper bound, since the tensor product of their ambient coordinate algebras is a coordinate algebra and their conductor containments tensor together. Qualitative preservation of smoothability by tensor products also follows by taking products of smoothings. [Flavi–Jelisiejew–Michałek, *Symmetric Powers: Structure, Smoothability, and Applications*](https://doi.org/10.1093/imrn/rnaf277)

For the lower bound put $B=\bigotimes_i A_i$. It is standard graded, has Loewy degree $2r$, and is quadratic since as a commutative algebra it has the union of the factors' quadratic relations on disjoint generators. Its radical squares elementwise to zero, because each positive-degree monomial has at least one generator which squares to zero, and squaring is additive in characteristic two. Let $V_i$ denote the degree-one part of factor $i$. Write $B_1=\bigoplus_i V_i$. If $x\in B_1$ has nonzero components in at least two summands, its degree-one annihilator in $B$ is exactly $kx$. In fact if $xy=0$, its component in degree one in factors $i$ and $j$ reads
\[
 x_i\otimes y_j+y_i\otimes x_j=0\qquad (i\ne j).
\]
When $x_i\ne0$ and $x_j=0$, this forces $y_j=0$. For two nonzero $x_i,x_j$, quotienting either tensor factor by the line of $x_i$ or $x_j$ shows that the corresponding $y_i,y_j$ are scalar multiples of $x_i,x_j$, and comparison of coefficients gives the same scalar in both factors. Thus $y$ lies on $kx$, and $x^2=0$ gives the reverse inclusion.

Fix any smoothing of $B$ and its endomorphism $\Phi$ from the lemma. Suppose an iterate $\Phi^n$ is injective on $V_i$. Every $x\in V_i$ has an annihilator within $V_i$ of dimension at least $e-h\ge2$, since its degree-two products within that factor lie in an $h$-dimensional space. The images of any two independent annihilators remain independent under the injective semilinear map over the perfect field. Therefore $\Phi^n(x)$ cannot have support in two factor spaces. The image of $V_i$ is a linear subspace over the perfect field, and if vectors supported in two different factor spaces belonged to the image, their sum would have support in both. Hence the image lies in a single $V_j$. It equals $V_j$ because all these spaces have dimension $e$. The restriction now gives a graded isomorphism from the $n$-th Frobenius twist of $A_i$ onto $A_j$, since their degree-one spaces generate and their dimensions agree.

For each $i\in I$, choose an iterate excluding all such isomorphisms. Its kernel in $V_i$ contains a nonzero vector $x_i$, and $x_i\in F^2B$ by the lemma. For $i\notin I$ choose any nonzero $x_i\in V_i\subseteq F^1B$. The level hypothesis gives $y_i\in V_i\subseteq F^1B$ with $x_i y_i\ne0$, since otherwise $x_i$ would be a degree-one socle element. The product of all $x_i y_i$ is their nonzero simple tensor in degree $2r$. Its filtration index is at least $2r+|I|$, proving the lower bound for every split smoothing.

## 4. An explicit family with gap exactly proportional to Loewy degree

**Theorem 2.** Let $k$ be any field of characteristic two, and suppose $\lambda\in k\setminus\{0,1\}$ satisfies
\[
 J(\lambda)=\frac{(\lambda^2+\lambda+1)^3}{\lambda^2(\lambda+1)^2}\notin\mathbb F_2.
\]
There is an explicit quadratic, standard graded level algebra $A_\lambda$ of Hilbert function $(1,8,2)$ for which
\[
 o_k(A_\lambda^{\otimes r})=3r,\qquad
 \operatorname{LoewyDegree}(A_\lambda^{\otimes r})=2r
 \qquad(r\ge1).
\]
In every algebraically closed field of characteristic two one may take any $\lambda\in\mathbb F_{128}\setminus\mathbb F_2$. The gap is $r=\log_{11}(\dim A_\lambda^{\otimes r})$.

Take a basis $1,a_1,b_1,\dots,a_4,b_4,z,w$ with $(a_i,b_i)$ in degree one and $z,w$ in degree two. The following display specifies every nonzero product among positive-degree basis elements.
\[
 a_i b_i=b_i a_i=p_i,\qquad
 (p_1,p_2,p_3,p_4)=(z,w,z+w,z+\lambda w).
\]
Associativity follows because every triple product of radical elements vanishes. For any nonzero degree-one vector, multiply by the partner of a basis vector with a nonzero coefficient to obtain a nonzero degree-two element. Thus the algebra is level. For a quadratic presentation on the eight degree-one generators, set all their squares and all cross-pair products to zero, and impose the two linear relations among the four pair products prescribed by the display. Every degree-three monomial then vanishes, since in three positions there is either a repeated generator or two generators from different pairs. The resulting presentation has the displayed graded basis, so is quadratic.

To construct the smoothing, partition eleven coordinate branches into four pairs and one triple. Let $u_i$ be the indicator of pair $i$, let $r_i$ be the indicator of one of its two branches, and let $Z,W$ be indicators of two distinct branches of the triple. Write $P_i$ for the combination of $Z,W$ corresponding to $p_i$, and set $v_i=r_i-P_i$. The vectors $1,u_i,v_i,Z,W$ are a basis of the split coordinate algebra. Consider the lattice with basis
\[
 1,\qquad t u_i,\qquad t^2 v_i,\qquad t^3Z,\qquad t^3W .
\]
It is closed under products of positive total weight at least three because it contains $t^3R^{11}$. For the remaining products, $u_i u_j=\delta_{ij}u_i$ gives closure. Modulo $tL$, products of total weight greater than three vanish, and products of two $t u_i$ also vanish. The identity $u_i v_j=\delta_{ij}(v_i+P_i)$ gives exactly the specified pair products in the special fiber. This proves the order upper bound three over the original field, and hence $3r$ after tensoring.

For the twist condition, compose degree-one multiplication with a linear functional on the degree-two space with coordinates $(u,v)$ in the basis dual to $(z,w)$. The alternating multiplication matrix has four alternating $2\times2$ blocks with entries off the diagonal $u,v,u+v,u+\lambda v$. Thus the four degenerate directions in the pencil are the projective points with affine coordinates $\infty,0,1,\lambda$. A graded isomorphism preserves this unordered four-point configuration up to projectivity. Its invariant $J(\lambda)$ is unchanged under all reordering of those points, since it is unchanged under $x\mapsto 1+x$ and $x\mapsto1/x$, which generate the cross-ratio changes. The Frobenius twist replaces $J(\lambda)$ by $J(\lambda)^2$. Consequently they can be graded-isomorphic only if $J(\lambda)\in\mathbb F_2$. An element of $\mathbb F_{128}\setminus\mathbb F_2$ has degree seven over $\mathbb F_2$, whereas either of the equations $J(\lambda)=0$ and $J(\lambda)=1$ gives a nonzero polynomial of degree at most six.

Apply Theorem 1 with identical factors over an algebraic closure of $k$. Its lower bound also holds over $k$, since an arc over $k$ gives an arc over that closure of the same degree. The explicit upper construction already works over $k$. Finally, $T_{A_\lambda^{\otimes r}}$ has a flattening of rank $11^r$ since multiplication by the unit is the identity. Together with the diagonal degeneration, this gives the stated border rank. The proofs are informal.
