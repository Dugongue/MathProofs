# An exact growing diagonal degeneration gap in every characteristic

For every field $k$ with at least three elements and every positive integer $r$, there are explicit standard graded algebras of dimension $11^r$ and Loewy degree $2r$ with exact diagonal tensor degeneration order $3r$. In particular, the separation holds over $\mathbb C$ and over every algebraically closed field of positive characteristic. The proof gives an additivity criterion for more general tensor products and allows independent maps on all three tensor modes.

## 1. Diagonal order and split smoothing lattices

Let $R=k[[t]]$, $K=k((t))$, and let $U_n=\sum_{i=1}^n e_i^*\otimes e_i^*\otimes e_i$ be the multiplication tensor of $k^n$. For a based $n$-dimensional unital algebra $A$ with multiplication tensor $T_A$, define $o_k(A)$ as the least $d\ge 0$ for which polynomial mode matrices give
\[
 (P_1(t)\otimes P_2(t)\otimes P_3(t))U_n
   =t^dT_A+O(t^{d+1}).
\]
Use $o_k(A)=\infty$ if no such arc exists. A split smoothing lattice of $A$ is a unital full-rank $R$-subalgebra $L\subseteq R^n$ with $L/tL\simeq A$. Its conductor exponent is $c(L)=\min\{d:t^dR^n\subseteq L\}$. Then $o_k(A)=\min_L c(L)$.

Here is the quantitative normalization. Divide one input map of an arc of order $d$ by $t^d$, obtaining an integral law $m(x,y)=C((Ux)\odot(Vy))$ with target special fiber, where $\odot$ is coordinatewise product. The three entry-pole caps $p_1,p_2,p_3$ on $U,V,C$ sum to at most $d$. For the target unit $e$, put $S=m(-,e)$, $D=m(e,-)$, $a=Ue$, and $b=Ve$. The slices
\[
 S=C\operatorname{diag}(b)U,\qquad D=C\operatorname{diag}(a)V
\]
are invertible over $R$ because they reduce to the identity. This forces invertibility of all three mode maps over $K$ and forces all coordinates of $a,b$ to be nonzero. Choose $h\in\mathrm{GL}_n(R)$ with $h\equiv I\bmod t$ and $he=m(e,e)$, for example $h=I+(m(e,e)-e)\ell$ with $\ell(e)=1$. Substitution with $H=h^{-1}C\operatorname{diag}(a\odot b)$ yields
\[
 h^{-1}m(S^{-1}hx,D^{-1}hy)=H((H^{-1}x)\odot(H^{-1}y)).
\]
The normalized law is integral, has unit $e$, and has the same special fiber. Its coordinate characters $H^{-1}$ are integral on the normalized finite $R$-algebra, since $R$ is integrally closed. Their rows are primitive because they take value one at the unit. Thus $L=H^{-1}R^n$ is a split smoothing lattice. The exponent $c_i$ of the first multiple $t^{c_i}e_i$ in $L$ is the negative minimum valuation of column $i$ of $H$. By
\[
 US^{-1}h=\operatorname{diag}(a)H^{-1},\qquad
 VD^{-1}h=\operatorname{diag}(b)H^{-1},\qquad
 h^{-1}C=H\operatorname{diag}((a\odot b)^{-1}),
\]
we have $v_t(a_i)\ge-p_1$, $v_t(b_i)\ge-p_2$, and $-c_i-v_t(a_i)-v_t(b_i)\ge-p_3$. Hence $c(L)=\max_i c_i\le d$. Conversely, if the columns of $M$ are a lattice basis lifting the chosen target basis, use $M$ on the two inputs and $t^{c(L)}M^{-1}$ on the output. These maps are integral, and truncating them through degree $c(L)$ preserves the leading tensor. This argument tracks the conductor in the unital normalization for tensor degenerations. [Bläser–Lysikov, *On degeneration of tensors and algebras*](https://arxiv.org/abs/1606.04253)

For a local target $B$ with residue $k$ and maximal ideal $\mathfrak m$, the lattice defines a descending multiplicative filtration
\[
 F^jB=\operatorname{im}(L\cap t^jR^n\longrightarrow L/tL).
\]
The reductions of all branch characters are the residue character. Consequently $F^1B=\mathfrak m$, $\mathfrak m^j\subseteq F^jB$, and $F^{c(L)+1}B=0$. If the largest nonzero power of $\mathfrak m$ has index $s$, then $s$ is the Loewy degree and $o_k(B)\ge s$. Tensoring split smoothing lattices uses the product coordinate algebra and adds conductor upper bounds.

## 2. Detecting each factor in the first jets

For a finite point set $P$ in an affine $k$-space, give $k^P$ the increasing filtration by the images of polynomials of total degree at most $j$. By a point presentation of a standard graded algebra we mean a graded isomorphism with the associated graded of this filtration. If $A$ has a point presentation and Loewy degree $s$, it has a split smoothing lattice of conductor $s$. Indeed take a basis of $k^P$ adapted to the filtration and scale each basis vector by $t$ to the power of its filtration degree. The span is a lattice closed under products by multiplicativity of the filtration, and its special fiber is the associated graded. The point condition is also the Artinian reduction by the affine-chart coordinate of the projective closure of $P$, a condition studied for Gorenstein algebras via inverse systems. [Elias–Rossi, *Inverse system of Gorenstein points in projective space*](https://arxiv.org/abs/2301.07056)

**Theorem 1.** Let $B=\bigotimes_{i=1}^r A_i$, where the $A_i$ are finite-dimensional standard graded commutative algebras with $k$ in degree zero and with Loewy degrees $s_i$. Let $I$ be the set of indices satisfying the following hypotheses.

- $A_i$ is level, meaning its socle is concentrated in degree $s_i$.
- For $V_i=(A_i)_1$, the algebra is presented by quadratic relations and the quadratic relation subspace is spanned by products $xy\in\mathrm{Sym}^2 V_i$ whose image in $(A_i)_2$ is zero.
- For every $y\in V_i$ the kernel of multiplication $y(-):V_i\to (A_i)_2$ has dimension at least two.
- $A_i$ has no point presentation over $k$.

Then
\[
 o_k(B)\ge \sum_{i=1}^r s_i+|I|.
\]
In particular, if $o_k(A_i)\le s_i+1$ for $i\in I$ and every other factor has order $s_i$, then $o_k(B)=\sum_i o_k(A_i)=\sum_i s_i+|I|$.

Fix a split smoothing lattice of $B$, if one exists, and identify $V_i$ and $(A_i)_j$ with their subspaces in $B$ via the units of the other factors. Fix an index $i\in I$. Suppose for contradiction that
\[
 F^{s_i+1}B\cap (A_i)_{s_i}=0 .
\]
Then $F^{j+1}B\cap (A_i)_j=0$ for all $1\le j\le s_i$. Indeed, any nonzero homogeneous element in a standard graded level algebra can be multiplied to a nonzero homogeneous element in the top degree, by multiplying successively by degree-one elements until reaching the socle. A multiplier of degree $s_i-j$ lies in $F^{s_i-j}B$, so the product would otherwise lie in the displayed zero intersection.

Choose a $k$-linear lift map $x\mapsto X$ from $V_i$ into $L\cap tR^n$. The first-jet vectors $(X/t)\bmod t$ define a finite set $P_i\subseteq V_i^*$, one functional for each branch, identifying repeated functionals. We will recover $A_i$ as the degree-associated graded of $k^{P_i}$.

We first check the quadratic relations on these projected jets. Take nonzero $x,y\in V_i$ with $xy=0$ in $A_i$. Then $U=XY/t$ lies in $L\cap tR^n$. Its class $u$ belongs to $\mathfrak m$. Write $u_1=\sum_j u_{1,j}$ with $u_{1,j}\in V_j$ for its homogeneous degree-one part in $B$. There is a $z\in V_i$ with $yz=0$ and $z$ linearly independent of $x$, by the hypothesis on the kernel of multiplication by $y$. With $Z$ its lift the identity
\[
 (XY/t)Z=X(YZ/t)
\]
gives $u_1 z=xv_1$ in $B_2$, where $v_1$ is the degree-one part of the class of $YZ/t$. For $j\ne i$, comparing the component in $V_i\otimes V_j$ gives $z\otimes u_{1,j}=x\otimes v_{1,j}$. The independence of $x,z$ forces $u_{1,j}=0$. Thus $u\in V_i+\mathfrak m^2$.

For a quadratic relation $f$ on $V_i$, express it as a linear combination of these products. Evaluation on the chosen lifts is linear in this expression, so $f(X)/t$ belongs to $L\cap tR^n$ and its residue also belongs to $V_i+\mathfrak m^2$. Subtract a lift of that degree-one part and a lift in $L\cap t^2R^n$ of the part in $\mathfrak m^2$. The difference belongs to $tL$. After dividing by $t$ and reducing in the coordinate algebra, the difference is constant across branches because every element of $L$ has constant branch reduction. Thus the values of $f$ at the projected jets are an affine-linear function of those jets. This annihilates the quadratic relation in the degree-associated graded of $k^{P_i}$. Since $A_i$ is quadratic, there is a graded surjection
\[
 A_i\longrightarrow \operatorname{gr} k^{P_i}.
\]
Surjectivity holds because the degree filtration on $k^{P_i}$ comes from evaluating polynomials and is generated in the associated graded by the degree-one segments.

This surjection is injective. If a homogeneous polynomial $f$ of degree $j\ge1$ is zero in the degree-$j$ quotient on the right, then its values on $P_i$ agree with those of a polynomial $g=\sum_{h<j}g_h$ of degree less than $j$, with homogeneous parts $g_h$. Hence
\[
 f(X)-\sum_{h<j}t^{j-h}g_h(X)
\]
belongs to $L\cap t^{j+1}R^n$. It has special class $f(x)\in (A_i)_j$ because all correction terms belong to $tL$. By the vanishing intersection in degree $j$, this class is zero. The degree-zero map is an isomorphism on constants. Thus the graded surjection is an isomorphism, contrary to the choice of $i$.

We have proved that $F^{s_i+1}B\cap(A_i)_{s_i}$ contains a nonzero element for every $i\in I$. Choose such elements, and choose arbitrary nonzero top-degree elements for the other factors. The product is their nonzero simple tensor, and its filtration index is at least $\sum_i s_i+|I|$. Therefore every split smoothing lattice has conductor at least this value. Applying the same lower bound to each single factor in $I$, and tensoring individual lattices for the upper bound, proves the equality claim.

## 3. A pencil bound for two extra points

**Lemma.** Let $A$ have Hilbert function $(1,e,2)$ and a point presentation. The pencil of bilinear forms obtained by composing $A_1\times A_1\to A_2$ with the linear functionals on $A_2$ has the following property. If the pencil is generically nonsingular, then the sum of the coranks at any four distinct directions of corank at least two is at most $e-1$.

The point configuration has $e+3$ points affinely spanning $k^e$. Normalize an affine basis to $0,e_1,\dots,e_e$ and denote the remaining two points by $p,q$. Subtracting the unique affine-linear interpolant on this basis identifies the degree-two quotient with the two remaining evaluations. The resulting matrices of the multiplication pencil are
\[
 M(u,v)=u pp^{\mathsf T}+v qq^{\mathsf T}-\operatorname{diag}(up+vq).
\]
Indeed, $x_ix_j$ for $i\ne j$ has zero affine interpolant on the basis points, and $x_i^2$ has interpolant $x_i$. There is no coordinate with $(p_i,q_i)=(0,0)$, since that would give a common kernel. Put $P=\sum_i p_i$ and $Q=\sum_i q_i$. We cannot have $P=Q=1$, since then the vector of all ones is in the common kernel.

At a direction $[u:v]$, put $d_i=up_i+vq_i$ and let $m$ be the number of $i$ with $d_i=0$. The sum of $m$ over distinct directions is at most $e$, since each nonzero linear form $d_i$ vanishes at just one direction. We bound corank in terms of $m$.

First take a non-axis direction, so $uv\ne0$. If $m=0$, write $D=\operatorname{diag}(d_i)$. A kernel vector $x$ satisfies
\[
 x=D^{-1}(up\alpha+vq\beta),\qquad \alpha=p^{\mathsf T}x,\quad\beta=q^{\mathsf T}x .
\]
Thus its kernel injects into the space of pairs $(\alpha,\beta)$. Corank at least two would make this map onto. Substituting $(1,0)$ and $(0,1)$ gives $u p^{\mathsf T}D^{-1}p=v q^{\mathsf T}D^{-1}q=1$ and $p^{\mathsf T}D^{-1}q=0$. But $D\mathbf1=up+vq$, so these equalities imply $P=Q=1$, a contradiction.

If $m>0$, at each coordinate with $d_i=0$ one has $up_i=-vq_i\ne0$. The kernel equation thus gives $\alpha=\beta=\theta$. Outside those $m$ coordinates it forces $x_j=\theta$. Also
\[
 (u+v)\theta=u\alpha+v\beta=\sum_i d_i x_i=\theta(uP+vQ).
\]
Unless $u(1-P)+v(1-Q)=0$, we get $\theta=0$, and the one nonzero linear constraint from $p^{\mathsf T}x=0$ bounds the corank by $m-1$. At the exceptional direction $u(1-P)+v(1-Q)=0$, allowing $\theta$ adds at most one dimension, so the corank is at most $m$.

At the axis $u=0$, the matrix is a scalar multiple of $qq^{\mathsf T}-\operatorname{diag}q$. Its kernel satisfies $x_j=\beta=q^{\mathsf T}x$ on the support of $q$. Thus the corank is $m$ if $Q\ne1$ and $m+1$ if $Q=1$. At $v=0$ the same description uses $P$ in place of $Q$.

Among four directions, at least two are non-axis. If neither $P$ nor $Q$ equals one, at least one of those non-axis directions lies outside the single exceptional direction, and there is no axis credit. If exactly one equals one, the exceptional direction is on the axis, both non-axis directions lose a dimension, and at most one axis gains a dimension. Since every non-axis direction of corank at least two has $m>0$, summing these bounds gives at most $e-1$, as claimed.

## 4. Explicit tensor powers and mixed parameters

**Theorem 2.** Let $k$ be any field and $\lambda\in k\setminus\{0,1\}$. Define $A_\lambda$ to have basis $1,a_1,b_1,\dots,a_4,b_4,z,w$. The $a_i,b_i$ have degree one, $z,w$ have degree two, and the following display gives every nonzero product among positive-degree basis elements.
\[
 a_i b_i=b_i a_i=p_i,\qquad(p_1,p_2,p_3,p_4)=(z,w,z+w,z+\lambda w).
\]
For any parameters $\lambda_1,\dots,\lambda_r$ in $k\setminus\{0,1\}$,
\[
 o_k\!\left(\bigotimes_{i=1}^r A_{\lambda_i}\right)=3r,
 \qquad
 \operatorname{LoewyDegree}\!\left(\bigotimes_{i=1}^r A_{\lambda_i}\right)=2r.
\]
The multiplication tensor has minimal border rank $11^r$.

This algebra is level because each nonzero degree-one element has nonzero product with the partner of a basis vector with nonzero coefficient. Associativity follows because all triple products of positive-degree elements vanish. The quadratic presentation on the eight degree-one generators kills their squares and all cross-pair products, and imposes the two relations between the four pair products. Every cubic monomial has either a repeated generator or two generators from different pairs, so the quadratic relations already kill every cubic. The relation space is spanned by products which vanish in the algebra. The squares and cross-pair products are already such products. Any remaining relation $\sum_j\gamma_j a_jb_j=0$ equals $(\sum_j a_j)(\sum_j\gamma_j b_j)$ modulo cross-pair products, and this latter product vanishes in the algebra. Every degree-one annihilator has dimension at least $8-2=6$.

The actual pencil of multiplication on degree one has four $2\times2$ blocks with zero diagonal and entries off the diagonal $u,v,u+v,u+\lambda v$, respectively. It is generically nonsingular, with four distinct directions of corank two. Their summed corank is eight, so the lemma excludes a point presentation in every characteristic.

For an explicit split smoothing of conductor at most three, partition eleven coordinate branches into four pairs and one triple. Let $u_i$ be the indicator of pair $i$, $r_i$ the indicator of one branch of that pair, and $Z,W$ the indicators of two branches of the triple. Write $P_i$ for the combination of $Z,W$ corresponding to $p_i$, and set $v_i=r_i-P_i$. The vectors $1,u_i,v_i,Z,W$ are a basis of the coordinate algebra, since replacing $v_i$ by $r_i$ recovers the indicators of the eight paired branches, and together with $1,Z,W$ these span the remaining branches. Use the lattice basis
\[
 1,\qquad tu_i,\qquad t^2v_i,\qquad t^3Z,\qquad t^3W.
\]
The lattice contains $t^3R^{11}$ and is closed under products of total weight at least three. The only smaller positive weights to check come from $u_i u_j=\delta_{ij}u_i$. In the special fiber, products of total weight greater than three and products of two $tu_i$ vanish. Finally $u_i v_j=\delta_{ij}(v_i+P_i)$ gives the required nonzero products of the degree-one generators. Theorem 1 now gives the matching lower bound and the exact tensor-product formula.

In the tensor product, the top degree is $2r$ and the dimension is $11^r$. Multiplication by the unit gives a full-rank flattening of the multiplication tensor. Its border rank is therefore at least $11^r$, which the diagonal arc attains. In particular, the exact order exceeds the Loewy degree by $r=\log_{11}(11^r)$, over every algebraically closed field.

The proofs are informal.
