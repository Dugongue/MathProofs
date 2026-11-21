# Sharp diagonal degeneration orders from filtered split algebras

Let $k$ be a field, $R=k[[t]]$, and $K=k((t))$. For a unital $n$-dimensional algebra $A$ with multiplication tensor $T_A$, let $o_k(A)$ be the least integer $d\ge 0$ such that
\[
 (P_1(t)\otimes P_2(t)\otimes P_3(t))U_n
   =t^d T_A+O(t^{d+1}),\qquad
 U_n=\sum_{i=1}^n e_i^*\otimes e_i^*\otimes e_i,
\]
with polynomial mode matrices over $k$. Use $o_k(A)=\infty$ when there is no such arc. The order allows three independent mode maps. The results below give an exact order strictly above Loewy degree over every algebraically closed field of characteristic two, a strict separation in all its tensor powers, and an exact formula for all finite monomial local algebras over any field.

## 1. Split smoothing and the evaluation filtration

A split smoothing lattice is a unital $R$-subalgebra $L\subseteq R^n$ of full rank with $L/tL\simeq A$. Its conductor exponent is
\[
 c(L)=\min\{d:t^dR^n\subseteq L\}.
\]
The order $o_k(A)$ equals the least $c(L)$ over such lattices. Here is the quantitative argument, including why arbitrary mode maps preserve the lower bound.

Given an arc of order $d$, divide one input mode by $t^d$. The result is an integral law $m(x,y)=C((Ux)\odot(Vy))$ reducing to the target multiplication, with $\odot$ coordinatewise product, and with input and output entry pole caps $p_1,p_2,p_3$ summing to at most $d$. Write $e$ for the target unit, $S(x)=m(x,e)$, $D(y)=m(e,y)$, $a=Ue$, and $b=Ve$. The maps $S,D$ reduce to the identity and are integrally invertible. Choose $h\in\operatorname{GL}_n(R)$ with $h\equiv I\bmod t$ and $he=m(e,e)$, for example $h=I+(m(e,e)-e)\ell$ for a constant functional $\ell(e)=1$. All entries of $a,b$ are nonzero, by invertibility of the slice maps. Direct substitution shows that the normalized law
\[
 (x,y)\longmapsto h^{-1}m(S^{-1}h x,D^{-1}h y)
\]
is multiplication in the generic algebra with split basis matrix $H=h^{-1}C\operatorname{diag}(a\odot b)$, meaning it equals $H((H^{-1}x)\odot(H^{-1}y))$. Its integral algebra has unit $e$ and the same special fiber. The algebra characters $H^{-1}$ are integral on it because $R$ is integrally closed, and each character row is primitive because it takes value one at $e$. Thus $L=H^{-1}R^n\subseteq R^n$ is a split smoothing lattice. If $c_i$ is the least exponent with $t^{c_i}e_i\in L$, the minimum valuation of column $i$ of $H$ is $-c_i$. The identities
\[
 US^{-1}h=\operatorname{diag}(a)H^{-1},\qquad
 VD^{-1}h=\operatorname{diag}(b)H^{-1},\qquad
 h^{-1}C=H\operatorname{diag}((a\odot b)^{-1})
\]
give $v_t(a_i)\ge-p_1$, $v_t(b_i)\ge-p_2$, and $-c_i-v_t(a_i)-v_t(b_i)\ge-p_3$. Hence $c(L)=\max_i c_i\le d$.

Conversely, if $M$ has the lattice basis vectors as columns in $R^n$, the product in that basis uses the two input maps $M$ and the output map $M^{-1}$. Clear the output by $t^{c(L)}$. The three mode matrices are integral, and truncation through degree $c(L)$ gives the required polynomial arc. The unital normalization is the one used by Bläser and Lysikov for the equivalence of tensor and algebra degeneration, with the valuations of the original independent modes tracked here. [Bläser–Lysikov, *On degeneration of tensors and algebras*](https://arxiv.org/abs/1606.04253)

Let $A$ now be local with maximal ideal $\mathfrak m$ and residue $k$, and let $s$ be its Loewy degree, i.e. $\mathfrak m^s\ne 0=\mathfrak m^{s+1}$. For a split smoothing lattice $L$, define
\[
 F^jA=\operatorname{im}(L\cap t^jR^n\longrightarrow L/tL),\qquad
 E_j=\operatorname{im}(t^{-j}(L\cap t^jR^n)\longrightarrow k^n)
 \quad(j\ge0),\qquad E_{-1}=0.
\]
All branch reductions are the residue character, so $F^1A=\mathfrak m$ and $E_0=k\mathbf 1$. The descending filtration $F$ and ascending filtration $E$ are multiplicative, $F^{c(L)+1}A=0$, and $E_{c(L)}=k^n$. In particular, $\mathfrak m^j\subseteq F^jA$ and $c(L)\ge s$. Taking the coefficient at degree $j$ yields a graded algebra isomorphism
\[
 \operatorname{gr}_F A\simeq\bigoplus_{j\ge0} E_j/E_{j-1}.
\]
Indeed $F^j/F^{j+1}$ is the quotient of $L\cap t^jR^n$ by $(L\cap t^{j+1}R^n)+(tL\cap t^jR^n)$. For $j\ge1$ the latter intersection is $t(L\cap t^{j-1}R^n)$, whose image at coefficient $j$ is $E_{j-1}$. For $j=0$ all elements of $tL$ already lie in $tR^n$. Coordinatewise multiplication gives compatibility with products.

**Theorem 1 (level order criterion).** Assume that $\operatorname{gr}_{\mathfrak m}A$ is level, meaning that its socle is concentrated in degree $s$. For every split smoothing lattice of conductor $s+\delta$,
\[
 \mathfrak m^j\subseteq F^jA\subseteq\mathfrak m^{\max(0,j-\delta)}
 \qquad(j\ge0).
\]
In particular, if $o_k(A)=s$, then $\operatorname{gr}_{\mathfrak m}A$ is the degree-associated graded of a set of $n$ distinct $k$-points in $k^e$, where $e=\dim_k\mathfrak m/\mathfrak m^2$. For standard graded level $A$, this point condition is also sufficient for $o_k(A)=s$.

For the upper inclusion take nonzero $a\in F^jA$, with initial $\mathfrak m$-adic degree $r$. In a standard graded level algebra, any nonzero degree-$r$ element can be multiplied to a nonzero degree-$s$ element, by repeatedly multiplying by a degree-one element which acts nontrivially until reaching the socle. Lift such a multiplier to $b\in\mathfrak m^{s-r}$. Then $0\ne ab\in F^{j+s-r}A$, forcing $j+s-r\le s+\delta$ and $r\ge j-\delta$.

At $c(L)=s$ we have $F^j=\mathfrak m^j$. Choose vectors $v_1,\dots,v_e\in E_1$ lifting a basis of $E_1/E_0$. Since $\bigoplus E_j/E_{j-1}$ is now generated in degree one, induction on $j$ gives that $E_j$ is spanned by products of at most $j$ of these vectors and the empty product. Thus $E_j$ is the evaluation space of polynomials of degree at most $j$ at the points $(v_{1,i},\dots,v_{e,i})$ for $i=1,\dots,n$. If two points were equal, their evaluations could never separate the corresponding branches, contrary to $E_s=k^n$. The graded algebra of the point evaluation filtration is $\operatorname{gr}_{\mathfrak m}A$.

Conversely let $E_j$ be the degree filtration of such a point configuration, and assume $A$ is the graded algebra $\bigoplus E_j/E_{j-1}$. Choose a $k$-basis of $k^n$ adapted to $E_j$, giving a basis vector $v$ its first filtration index $w(v)$. The $R$-span of $t^{w(v)}v$ is multiplicatively closed because a product of two basis vectors before scaling is a linear combination of vectors of weight at most the sum of their weights. Its special fiber is therefore the prescribed graded algebra, and its conductor is the last filtration index $s$. The point condition here is an Artinian reduction of a reduced set of points, a condition studied for the Gorenstein case via inverse systems. The criterion above connects it to exact diagonal degeneration order for arbitrary level tangent cones. [Elias–Rossi, *Inverse system of Gorenstein points in projective space*](https://arxiv.org/abs/2301.07056)

## 2. A strict separation over algebraically closed characteristic two

**Theorem 2.** Let $k$ be any field of characteristic two, and let $\lambda\in k\setminus\{0,1\}$. The explicit split smoothable, standard graded level algebra $A_\lambda$ below has Hilbert function $(1,8,2)$, Loewy degree two, and $o_k(A_\lambda)=3$. If $k$ is algebraically closed and $\lambda\in\mathbb F_{128}\setminus\mathbb F_2\subset k$, its tensor powers satisfy
\[
 2r+1\le o_k(A_\lambda^{\otimes r})\le 3r\qquad(r\ge1).
\]
Each tensor power has Loewy degree $2r$.

**Algebra and split smoothing.** Take basis $1,a_1,b_1,\dots,a_4,b_4,z,w$, where the $a_i,b_i$ have degree one and $z,w$ have degree two. Define the only nonzero products of positive-degree basis elements by
\[
 a_i b_i=b_i a_i=p_i,\qquad (p_1,p_2,p_3,p_4)=(z,w,z+w,z+\lambda w).
\]
This is associative since all products of three positive-degree elements are zero. Each $p_i$ is nonzero, so a nonzero degree-one vector has nonzero product with the partner of a basis element with nonzero coefficient. Thus the socle is exactly $\langle z,w\rangle$.

For the eleven branches of $k^{11}$ use four clusters of size two and one cluster of size three. Let $u_i$ be the indicator of the $i$-th size-two cluster and $r_i$ the indicator of one of its branches. Let $Z,W$ be the indicators of two distinct branches of the size-three cluster. Write $P_i$ for the same linear combination of $Z,W$ as $p_i$ is of $z,w$, and put $v_i=r_i-P_i$. The eleven vectors $\mathbf1,u_i,v_i,Z,W$ form a basis. Indeed switching $v_i$ back to $r_i$ gives the coordinate indicators for each size-two cluster and, together with $\mathbf1$, for the size-three cluster. Use the lattice basis
\[
 \mathbf1,\quad t u_i,\quad t^2 v_i,\quad t^3Z,\quad t^3W.
\]
This is multiplicatively closed. Products with total weight at least three lie in the lattice, because its highest basis weight is three. For the remaining positive-weight products, $u_i u_j=\delta_{ij}u_i$. Also $u_i v_j=\delta_{ij}r_i=\delta_{ij}(v_i+P_i)$, so modulo $tL$ the only nonzero products of positive-weight basis elements are $(t u_i)(t^2v_i)=t^3P_i$ there. This identifies the special fiber with $A_\lambda$ and gives order at most three.

**A restriction at Loewy order.** Let $B$ be standard graded level over any field of characteristic two. Suppose $x^2=0$ for every $x\in B_1$ and $o_k(B)$ is its Loewy degree. By Theorem 1, $B$ is the graded algebra of a degree filtration on points in $k^e$, with $e=\dim B_1$. The points affinely span $k^e$ because $\dim(E_1/E_0)=e$. Normalize $e+1$ affinely independent points to $0,e_1,\dots,e_e$ by an affine transformation. For each coordinate $x_i$ its square agrees on the configuration with an affine-linear polynomial, since $x_i^2$ is zero in the degree-two graded piece. This affine-linear polynomial agrees with $x_i$ at the normalized points and hence is $x_i$. Every point thus lies in $\mathbb F_2^e$. Evaluation vectors of monomials have entries in $\mathbb F_2$, and their degree filtration commutes with extending scalars from $\mathbb F_2$ to $k$. Consequently $B$ has a graded $\mathbb F_2$-form.

**Pencil invariant.** The family of alternating bilinear forms on $(A_\lambda)_1$ obtained by composing multiplication with the nonzero functionals on $(A_\lambda)_2$ is intrinsic up to changes of bases. If the functional is $(u,v)$ in the dual basis to $(z,w)$, the matrix has four alternating $2\times2$ blocks with off-diagonal coefficients $u,v,u+v,u+\lambda v$. Thus the four degenerate directions in the projective line have affine coordinates $\infty,0,1,\lambda$.

For a degree filtration on binary points as above with Hilbert function $(1,e,2)$, the configuration consists of $0,e_1,\dots,e_e$ and two other binary points $p,q$. Subtracting the unique affine-linear interpolant on $0,e_1,\dots,e_e$ identifies $E_2/E_1$ with the two evaluations left at $p,q$. In the coordinate basis of $E_1/E_0$, the two alternating multiplication matrices are $\operatorname{diag}(p)+pp^{\mathsf T}$ and $\operatorname{diag}(q)+qq^{\mathsf T}$. The off-diagonal entries are the products of the corresponding binary coordinates, and the diagonal entries vanish. Thus the pencil is
\[
 M(u,v)=D+upp^{\mathsf T}+vqq^{\mathsf T},
 \qquad D=\operatorname{diag}(up+vq).
\]
A coordinate of type $(p_i,q_i)=(0,0)$ gives a common kernel, making the pencil singular everywhere. Otherwise, write $a,b,c$ for the numbers of coordinates of types $(1,0),(0,1),(1,1)$ respectively, and read these numbers as field elements whenever they occur as coefficients. Set $A'=1+a$ and $B'=1+b$. Over $k(u,v)$, the matrix determinant lemma for the rank-two update gives
\[
 \frac{\det M}{\det D}
  =\left(A'+\frac{uc}{u+v}\right)
   \left(B'+\frac{vc}{u+v}\right)+\frac{uv c^2}{(u+v)^2}
  =\frac{(A'B'+B'c)u+(A'B'+A'c)v}{u+v}.
\]
For example, the input Gram entries are $p^{\mathsf T}D^{-1}p=a/u+c/(u+v)$, $q^{\mathsf T}D^{-1}q=b/v+c/(u+v)$, and $p^{\mathsf T}D^{-1}q=c/(u+v)$. The numerator is a binary linear form. If the pencil is generically nonsingular, its only possible degenerate directions even over an algebraic closure are therefore $u=0$, $v=0$, and $u+v=0$. The pencil of $A_\lambda$ is generically nonsingular with four degenerate directions. Together with the upper construction and Theorem 1, this proves $o_k(A_\lambda)=3$.

For the tensor-power claim, the unordered projective invariant of the four degenerate directions of $A_\lambda$ is
\[
 J(\lambda)=\frac{(\lambda^2+\lambda+1)^3}{\lambda^2(\lambda+1)^2}.
\]
Indeed every reordering of four distinct points replaces the cross-ratio by an iterate of $x\mapsto 1+x$ and $x\mapsto 1/x$, under both of which $J$ is unchanged by substitution. This invariant commutes with applying field Frobenius to the pencil. If the algebra has a graded $\mathbb F_2$-form, it is graded-isomorphic to its Frobenius twist, and hence $J(\lambda)^2=J(\lambda)$. The element $\lambda$ has degree seven over $\mathbb F_2$, whereas either equation $J(\lambda)=0$ or $J(\lambda)=1$ would give a nonzero polynomial of degree at most six over $\mathbb F_2$ vanishing at $\lambda$. In particular, for this degree-seven choice of $\lambda$, $A_\lambda$ is not graded-isomorphic to its Frobenius twist.

**Tensor powers.** Put $B=A_\lambda^{\otimes r}$. It has degree-one part $\bigoplus_i V_i$, with $V_i$ the copy of $(A_\lambda)_1$ in factor $i$. To see that the tensor product is level, expand a vector in a basis of the other factors. The kernel of multiplication by all positive-degree elements in a single factor is then the socle of that factor tensored with the other factors. Intersecting over the factors leaves precisely the tensor product of their socles, in degree $2r$. Every degree-one square is zero. The tensor product of the displayed smoothing lattices embeds in the coordinate algebra of $11^r$ branches, gives the tensor product special fiber, and contains $t^{3r}R^{11^r}$. This gives the upper bound.

The factor spaces $V_i$ are intrinsic. For $x\in B_1$, consider the rank of $m_x:B_1\to B_2$. If $x\in V_i$, the cross-factor output of $m_x$ has rank at most $8(r-1)$, and the same-factor output rank is at most two. If $x$ has at least two nonzero components, write $y\in\ker m_x$ and use the cross-factor equations $x_i\otimes y_j+y_i\otimes x_j=0$ in $V_i\otimes V_j$. They force $y_j=0$ whenever $x_j=0$, and proportionality $y_i=\alpha x_i$ with the same scalar on every nonzero component. Indeed on any two nonzero components, quotienting one of the factors by its line spanned by $x_i$ forces the corresponding $y_i$ into that line, and comparison of coefficients gives the common scalar. Since $x^2=0$, the kernel is exactly $kx$ and the rank is $8r-1$. Thus the rank-$\le 8(r-1)+2$ locus is the union of the linear spaces $V_i$, which are its irreducible components. Each generates a copy of $A_\lambda$ as a unital graded subalgebra.

If $o_k(B)=2r$, the restriction at Loewy order gives a graded $\mathbb F_2$-form and therefore a graded isomorphism $B\simeq B^{\mathrm{Fr}}$. The rank locus forces this isomorphism to match factor spaces with factor spaces in the twist, and hence $A_\lambda\simeq A_\lambda^{\mathrm{Fr}}$ as graded algebras. The same pencil contradiction excludes this. The lower bound follows for all $r$.

## 3. Exact finite-field formula for arbitrary monomial algebras

**Theorem 3.** Let $S$ be a finite nonempty lower set in $\mathbb Z_{\ge0}^e$, so $\beta\in S$ whenever $\alpha\in S$ and $0\le\beta_j\le\alpha_j$ for all $j$. Let $A_S$ be the local algebra with monomial basis $\{x^\alpha:\alpha\in S\}$, where monomials outside $S$ are zero. For $k=\mathbb F_q$ put
\[
 w_q(a)=\sum_{h\ge0}\left\lfloor\frac{a}{q^h}\right\rfloor.
\]
Then
\[
 o_{\mathbb F_q}(A_S)=\max_{\alpha\in S}\sum_{j=1}^e w_q(\alpha_j).
\]
For any infinite field the corresponding value is $\max_{\alpha\in S}|\alpha|$, the Loewy degree.

For a finite field, identify the base-$q$ digits with field elements using a bijection taking zero to zero. Write $d_i(t)\in R$ for the polynomial whose coefficients are the digits of the integer $i$ in increasing place order. For $a\ge0$ and $y\in R$, the valuation of $\prod_{i<a}(y-d_i(t))$ is at least $\sum_{h\ge1}\lfloor a/q^h\rfloor$. At each precision $h$ every residue class modulo $t^h$ occurs among $d_0,\dots,d_{a-1}$ at least $\lfloor a/q^h\rfloor$ times. The class of $d_a$ occurs exactly that many times, so equality holds at $y=d_a$. This is the digit $t$-ordering of the discrete valuation ring, a specialization of Bhargava's factorial construction. [Bhargava, *P-orderings and polynomial functions on arbitrary subsets of Dedekind rings*](https://geodesic.mathdoc.fr/item/JRAM_1997__490_153942/)

For the lower bound let $L$ be any split smoothing lattice and lift the $x_j$ to $X_j\in L$. Their coordinates lie in $tR$ because each reduces to zero under the residue character. The lattice element
\[
 N_\alpha(X)=\prod_{j=1}^e\prod_{i<\alpha_j}(X_j-t d_i(t)\mathbf1)
\]
has all coordinate valuations at least $w(\alpha)=\sum_j w_q(\alpha_j)$ by the digit valuation calculation. Its residue in $A_S$ is the nonzero basis monomial $x^\alpha$. If $c(L)<w(\alpha)$, it would lie in $t^{c(L)+1}R^n\subseteq tL$, a contradiction.

For the upper bound evaluate $R[x_1,\dots,x_e]$ at the $|S|$ points indexed by $\gamma\in S$ with coordinate $j$ given by $t d_{\gamma_j}(t)$. Denote the image by $L$. The product Newton polynomials $N_\alpha(x)$ form an $R$-basis of the polynomial module, since their leading monomials are $x^\alpha$ and all other terms have smaller total degree. Those with $\alpha\notin S$ vanish on every branch, since for every $\gamma\in S$ at least one coordinate has $\gamma_j<\alpha_j$. The evaluation matrix for $\alpha\in S$ in any linear extension of the coordinatewise order is triangular after dividing column $\alpha$ by $t^{w(\alpha)}$. The divided matrix has integral entries and unit diagonal by equality of the digit valuation at $d_a$. The unscaled evaluation columns are therefore an $R$-basis of $L$. The polynomial evaluation kernel is spanned over $R$ by the $N_\alpha$ for $\alpha\notin S$, whose reductions are $x^\alpha$. It follows that $L/tL\simeq A_S$. Since the divided evaluation matrix lies in $\operatorname{GL}_{|S|}(R)$, the conductor is exactly $\max_{\alpha\in S}w(\alpha)$.

For infinite $k$ use distinct constant digits $d_i$ to the largest index needed. The same construction has column weight $|\alpha|$. The universal Loewy bound supplies equality.

The finite-field formula is additive on tensor products of monomial local algebras, because the product lower set has independent index blocks and one can maximize in each block separately. For example, over $\mathbb F_q$ take the lower set
\[
 S=\{(i,0):0\le i\le q\}\ \cup\ \{(0,j):0\le j\le q\}.
\]
The algebra is $k[x,y]/(x^{q+1},y^{q+1},xy)$, with dimension $2q+1$ and Loewy degree $q$. Its $r$-th tensor power has dimension $(2q+1)^r$, Loewy degree $rq$, and exact order $r(q+1)$ over $\mathbb F_q$, versus order $rq$ over an infinite extension.

These are mathematical proofs. No new formal proof certification is asserted.
