# Diagonal tensor degeneration order equals a split conductor exponent

Let $k$ be a field, $R=k[[t]]$, $K=k((t))$, and let $U_n=\sum_{i=1}^n e_i^*\otimes e_i^*\otimes e_i$ be the multiplication tensor of the coordinatewise algebra $k^n$. For a based unital $n$-dimensional $k$-algebra $A$, write $T_A$ for its multiplication tensor. The diagonal-source order is the least $d\ge0$ for which polynomial mode matrices satisfy
$$
(P_1(t)\otimes P_2(t)\otimes P_3(t))U_n
  =t^d\bigl(T_A+tQ(t)\bigr)
$$
with $Q(t)$ polynomial. Write $o_k(A)=+\infty$ if no such presentation exists. When it exists, the unit gives full flattening ranks for $T_A$ and therefore its border rank is exactly $n$ under this split interpretation.

The order has an exact algebraic description. It gives sharp values for all curvilinear factors over arbitrary fields and for all local algebras with a complete-intersection tangent cone over an algebraically closed field, in every characteristic. On the latter class an explicit criterion characterizes equality with the Loewy lower bound over the original coefficient field.

## 1. Split lattices and arbitrary three-mode arcs

A split smoothing lattice of $A$ means a unital $R$-subalgebra $L\subseteq R^n$ of full $R$-rank, with $L/tL\simeq A$. Its conductor exponent is
$$
c(L)=\min\{d\ge0:t^d R^n\subseteq L\}.
$$
For the coordinate idempotent $e_i$ of $K^n$, let $c_i$ be the least $d\ge0$ with $t^d e_i\in L$. The conductor ideal is $\bigoplus_i t^{c_i}Re_i$ and $c(L)=\max_i c_i$.

**Theorem 1.** $o_k(A)$ is the minimum of $c(L)$ over all split smoothing lattices of $A$, with the empty minimum interpreted as $+\infty$. More precisely, a formal Laurent degeneration of $U_n$ with given nonnegative entry-pole caps $p_1,p_2,p_3$ exists if and only if a split smoothing lattice exists with $c(L)\le p_1+p_2+p_3$. Whenever a finite order $d$ is attainable, it is attained by polynomial mode matrices of degree at most $d$ apiece.

To see necessity, view an ordinary tensor arc as an integral bilinear law
$$
m(x,y)=C\,(Ax\odot By)
$$
reducing to the multiplication of $A$, where $\odot$ is coordinatewise multiplication in $K^n$. The ordinary input mode matrices are $A^{\mathsf T},B^{\mathsf T}$. Let $e$ be the unit in the fixed target basis, and put $R_e(x)=m(x,e)$, $L_e(y)=m(e,y)$ and $u=m(e,e)$. Both slice maps reduce to the identity and $u$ reduces to $e$. Choose a fixed functional $\ell$ with $\ell(e)=1$, and set $h=I+(u-e)\ell$. This is in $\operatorname{GL}_n(R)$ and takes $e$ to $u$. Normalize the law by
$$
\nu(x,y)=h^{-1}m(R_e^{-1}h x,L_e^{-1}h y).
$$
It has unit $e$ and the same special fiber. Let $a=Ae$ and $b=Be$. The formulas for the two invertible slice maps imply that each coordinate of $a,b$ is nonzero. Substitution shows that
$$
H=h^{-1}C\,\operatorname{diag}(a\odot b)
$$
is an algebra isomorphism from $K^n$ to the generic normalized law. Indeed the law before applying $h^{-1}$ to the output and $h$ to the inputs is the coordinatewise product in the $C^{-1}$ coordinates with the extra coefficient $(a\odot b)^{-1}$. Thus $\nu$ is associative and commutative over $R$ as well. This is the unital normalization for multiplication tensors, applied with the pole caps kept on the three original modes. [Bläser–Lysikov, *On degeneration of tensors and algebras*](https://arxiv.org/abs/1606.04253)

The coordinates of $H^{-1}$ are the ring characters of the generic normalized law. They take values in $R$ on its integral algebra because every element is integral over $R$, and the discrete valuation ring is integrally closed. Each row of $H^{-1}$ is primitive, meaning its minimum entry valuation is zero, because its value at $e$ is one. This gives the lattice $L=H^{-1}R^n\subseteq R^n$. The minimum valuation in column $i$ of $H$ is $-c_i$, since $t^{c_i}H e_i$ is the first integral multiple of that column.

The normalized original matrices satisfy
$$
A R_e^{-1}h=\operatorname{diag}(a)H^{-1},\quad
B L_e^{-1}h=\operatorname{diag}(b)H^{-1},\quad
h^{-1}C=H\operatorname{diag}((a\odot b)^{-1}).
$$
Multiplication by the indicated invertible integral matrices preserves the entry-pole cap. For $\alpha_i=v_t(a_i)$ and $\beta_i=v_t(b_i)$, the primitive input rows and the output column give
$$
\alpha_i\ge-p_1,\qquad \beta_i\ge-p_2,\qquad
-c_i-\alpha_i-\beta_i\ge-p_3 .
$$
Thus $c_i\le p_1+p_2+p_3$ for every $i$. This argument uses arbitrary independent mode maps.

Conversely, choose an $R$-basis of $L$ lifting the supplied basis of $A$ via a special-fiber isomorphism. Let $H^{-1}$ have these basis vectors as columns in the coordinate algebra. The generic law in those coordinates has integral multiplication and specializes to $T_A$. Use $t^{-p_1}H^{-1}$ and $t^{-p_2}H^{-1}$ on the inputs and $t^{p_1+p_2}H$ on the output. The cap on the output follows from $c(L)\le p_1+p_2+p_3$, and the three scalar factors cancel. This proves the exact formal criterion.

A polynomial presentation of order $d$ gives the formal cap sum at most $d$ by dividing the first factor by $t^d$. Its generic factor matrices are invertible by the full flattening ranks of the leading output. Conversely, from $c(L)=d$ choose integral factors $(H^{-1})^{\mathsf T},(H^{-1})^{\mathsf T},t^d H$. Truncate each at degree $d$. Their product on $U_n$ is unchanged modulo $t^{d+1}$, giving polynomial matrices of degree at most $d$ and leading term $t^dT_A$. This proves the claimed equality for polynomial order.

### Finite certificates, direct products and nonsplit residues

For $d\ge1$ the criterion for order at most $d$ is finite over $k$. Put $R_j=k[t]/(t^j)$. Choose an $R_d$-subalgebra $S\subseteq R_d^n$ containing the diagonal copy of $R_d$. Let $\widehat S$ be its inverse image in $R_{d+1}^n$. Then
$$
o_k(A)\le d
\quad\Longleftrightarrow\quad
A\simeq \widehat S/t\widehat S\text{ for some such }S .
$$
Indeed take the inverse image of $S$ in $R^n$ to obtain $L$ with $t^dR^n\subseteq L$, and note that $t^{d+1}R^n\subseteq tL$. Conversely reduce a suitable smoothing lattice modulo $t^d$. Order zero occurs exactly for $A\simeq k^n$.

For two finite unital algebras,
$$
o_k(A_1\times A_2)=\max\{o_k(A_1),o_k(A_2)\}.
$$
The upper bound takes products of lattices. In the other direction any smoothing of the product is commutative, and the complementary central idempotents of its special fiber lift through the complete local base. One can lift by correcting $x$ by $-(2x-1)^{-1}(x^2-x)$, which squares the error, and then taking the limit. A generic coordinate idempotent splits the lattice into two factors, whose generic coordinate counts equal their special dimensions by freeness. The conductor exponent of each factor is at most that of the original lattice.

For any smoothing lattice the reduction map $L/tL\to k^n$ has nilpotent kernel: a product of $c(L)+1$ elements in the kernel lifts to $t^{c(L)+1}R^n\subseteq tL$. Its image is reduced, so the kernel is exactly the nilradical. A finite-dimensional unital $k$-subalgebra of $k^n$ is a product of copies of $k$: it is reduced, and each of its field factors embeds into $k$ under some coordinate projection. In particular a nonsplit residue field precludes a split diagonal arc over $k((t))$. Passing to an algebraic closure can change this existence claim.

## 2. Sharp curvilinear order over any field

Let $A=k[x]/(x^n)$. If $k$ is infinite, then
$$
o_k(A)=n-1.
$$
If $k=\mathbb F_q$, then
$$
o_k(A)=\sum_{j\ge0}\left\lfloor\frac{n-1}{q^j}\right\rfloor.
\tag{1}
$$
Any split monogenic algebra $k[x]/\prod_{\alpha\in k}(x-\alpha)^{n_\alpha}$ has the maximum of these values over its nonempty factors. A monogenic quotient with a residue field other than $k$ has infinite split order.

For the proof, in any smoothing lattice lift the generator $x$ to $z$. The powers $1,z,\ldots,z^{n-1}$ form an $R$-basis by reduction modulo $t$. Its coordinate values $\lambda_1,\ldots,\lambda_n$ are distinct elements of $tR$, since the evaluation matrix in this basis is invertible generically and its special character values are zero. The coefficients of the Lagrange polynomial for the $i$-th idempotent are the coordinates of that idempotent in the power basis. The numerator $\prod_{j\ne i}(X-\lambda_j)$ has integral coefficients with leading coefficient one. Hence
$$
c_i=\sum_{j\ne i}v_t(\lambda_i-\lambda_j).
$$
Conversely any such list of distinct roots gives the smoothing $R[X]/\prod_j(X-\lambda_j)$ and the same conductor formula.

For infinite $k$, all differences have valuation at least one, and $\lambda_i=t a_i$ with distinct constants attains one for each difference. Over $\mathbb F_q$ write $\lambda_i=t\mu_i$ and let $b_j(i)$ count the $\mu$ values in the residue class of $\mu_i$ modulo $t^j$. Thus
$$
c_i=\sum_{j\ge0}(b_j(i)-1).
$$
Recursively follow a largest child at each step of the $q$-ary residue tree. This supplies a single index $i$ for which all $b_j(i)\ge\lceil n/q^j\rceil$. In the other direction represent $0,\ldots,n-1$ in base $q$, use the digits in order from least to most significant as coefficients of $\mu_i$, and identify the digits with the $q$ field elements. Every residue class modulo $t^j$ has at most $\lceil n/q^j\rceil$ chosen elements. This attains the lower bound since $\lceil n/q^j\rceil-1=\lfloor(n-1)/q^j\rfloor$. The roots are polynomial, so the upper bound requires no extension of the finite field.

## 3. The Loewy bound and its equality condition

Let $A$ be local with residue $k$ and maximal ideal $\mathfrak m$. Choose $s$ with $\mathfrak m^s\ne0$ and $\mathfrak m^{s+1}=0$. Every element of $\mathfrak m$ lifts in a split smoothing to a vector in $tR^n$, since the coordinate reductions are characters. A product of $c(L)+1$ such lifts lies in $tL$. Consequently $o_k(A)\ge s$.

A finite set $\Xi$ of $n$ distinct $k$-points in $k^e$ gives the degree filtration $F_j$ on $k^\Xi$: take the image under evaluation of polynomials of total degree at most $j$. Its associated graded is a standard graded local algebra. If $A$ is isomorphic to this algebra and $F_s=k^\Xi$, there is a smoothing of order $s$. Choose a basis $v_j$ adapted to the filtration and let the weight of $v_j$ be its first filtration index. The span of $t^{\mathrm{weight}(v_j)}v_j$ over $R$ is a ring, by multiplicativity of the filtration. Its special fiber is the associated graded and it contains $t^sR^n$. This is a constructive sufficient condition.

There is a converse at equality for local Gorenstein algebras with symmetric $\mathfrak m$-adic Hilbert function. Here “Gorenstein” can equivalently be taken to mean that the socle has dimension one. Suppose $c(L)=s$ for a split smoothing of such an $A$. Pick a $k$-linear functional of $A$ nonzero on its socle. It gives a perfect product pairing because every nonzero ideal meets the socle. For example, for a nonzero element choose a product of it by an element of the maximal ideal's highest power that still acts nontrivially. Lift the functional to an $R$-linear functional of $L$. Its product pairing is perfect over $R$, by reduction of its determinant. Write $u_i$ for the value of its generic extension on $e_i$. All $u_i$ are nonzero, and the coordinate trace-dual lattice is
$$
L^*=\{z\in K^n: \textstyle\sum_i z_i x_i\in R\text{ for all }x\in L\}
    =\operatorname{diag}(u_i)L .
$$
The minimum valuation of the $i$-th coordinate of $L^*$ is $-c_i$, by testing membership of $t^d e_i$ in the double dual $L=(L^*)^*$. Since the coordinate projection of $L$ is $R$, this gives $v_t(u_i)=-c_i$. Comparing determinants of bases of the two expressions for $L^*$ gives
$$
\sum_i c_i=2v_t(\det M),
\tag{2}
$$
where $M$ is any lattice basis matrix in the coordinate algebra.

Choose minimal generators $x_1,\ldots,x_e$ of $\mathfrak m$, and monomials $b_j(x)$ whose leading classes form a homogeneous basis of $\operatorname{gr}_{\mathfrak m}A$. Let $d_j=\deg b_j$. Lift the generators to $L$ and use the same monomials as its basis. All coordinate generator values are divisible by $t$, so the evaluation matrix has the form
$$
M=W(t)\operatorname{diag}(t^{d_j}),\qquad W(t)\in M_n(R).
$$
Symmetry of the Hilbert function gives $\sum_j d_j=ns/2$. Since each $c_i\le s$, (2) forces all $c_i=s$ and $W(0)$ invertible. Write $\rho_i\in k^e$ for the vector of coordinate generator values after dividing them by $t$ and reducing. The rows of $W(0)$ are the monomial evaluations at $\rho_i$, so the $\rho_i$ are distinct and generate the full coordinate algebra under evaluation.

These points have degree-associated graded exactly $\operatorname{gr}_{\mathfrak m}A$. To prove it, let $f$ be the initial homogeneous form of degree $d$ of any relation $g$ on the generators of $A$. The evaluation vector of $g$ on the lifted generators belongs to $tL$, and is divisible by $t^d$ in the coordinate algebra. Express it as $tW(t)\operatorname{diag}(t^{d_j})r(t)$ with $r(t)$ integral. Divide by $t^d$ and multiply by $W(t)^{-1}$, which is integral. This shows that all the coefficients $t^{1+d_j-d}r_j(t)$ are integral. Only the terms with $d_j<d$ can contribute at zero. Hence $f(\rho)$ lies in the degree-$d-1$ evaluation space. The initial relations of $A$ therefore vanish in the degree-associated graded of these points, giving a graded surjection. Both algebras have dimension $n$, so it is an isomorphism.

In particular, for a standard graded local Gorenstein algebra with symmetric Hilbert function, diagonal order equals Loewy degree if and only if it admits such a split point presentation of its grading. Over $\mathbb F_q$ equality requires $n\le q^e$.

## 4. Exact order for complete-intersection tangent cones

**Theorem 2.** Suppose
$$
\operatorname{gr}_{\mathfrak m} A
   \simeq k[x_1,\ldots,x_e]/(f_1,\ldots,f_e)
$$
where $f_i$ are a homogeneous regular sequence of degrees $d_i\ge2$ and $x_i$ are minimal tangent generators. Let $s=\sum_i(d_i-1)$ and $n=\prod_i d_i$. Then $o_k(A)=s$ if and only if there are $n$ distinct points of $k^e$ whose degree-associated graded has the displayed presentation after a linear change of tangent generators. If $k$ is algebraically closed, such points always exist in every characteristic, and $o_k(A)=s$. The embedding dimension zero case is $A=k$, of order zero.

The Hilbert series of the tangent cone is $\prod_i(1+z+\cdots+z^{d_i-1})$, so its Loewy degree is $s$ and its Hilbert function is symmetric. A zero-dimensional complete intersection is Gorenstein. The original algebra also has a one-dimensional socle: the initial class of a nonzero socle element is killed by the degree-one generators of the tangent cone, hence lies in its one-dimensional top degree. The top power $\mathfrak m^s$ itself lies in the socle. This proves the necessity of the point condition by Section 3. [Stacks Project, Gorenstein property of complete intersections](https://stacks.math.columbia.edu/tag/0DWA)

For sufficiency, let $\rho$ be such a point set, choosing its linear coordinates to agree with the presentation. Each $f_i$ evaluates as a polynomial of degree strictly less than $d_i$. Thus there are polynomials $F_i=f_i+\text{lower-degree terms}$ vanishing on the point set. The quotient by the $F_i$ has dimension $n$, with a basis given by the same monomials as for the quotient by the $f_i$. One way to verify this is to homogenize with a variable $u$. The homogenized equations and $u$ form a homogeneous system of parameters, since at $u=0$ they reduce to the regular zero-dimensional system $f_i$. In a polynomial ring this sequence is regular in either order. The homogenized quotient is free over $k[u]$ on the chosen monomial lifts: generate by descending total degree after reduction modulo $u$, and use that $u$ is a nonzerodivisor to test independence modulo $u$. Setting $u=1$ proves the assertion. Therefore the ideal of the $F_i$ is exactly the ideal of the $n$ points. At each point the Jacobian is invertible, since the equations generate its maximal ideal locally and hence generate its cotangent space. [Stacks Project, regular sequences in polynomial local rings](https://stacks.math.columbia.edu/tag/00S8)

It remains to smooth $A$ itself, including its nonhomogeneous relations. Present it as $k[[x_1,\ldots,x_e]]/I$, choose $g_i\in I$ with initial form $f_i$, and choose a finite monomial basis $b_j$ adapted to the tangent cone. The $g_i$ generate $I$: subtract multiples giving the lowest homogeneous degree of any relation, and continue to higher degrees in the complete ring. The coefficients converge, giving the asserted ideal equality. Since $I$ contains all sufficiently high powers of $(x)$, the $g_i$ may be chosen polynomial by truncation.

If $F_i(y)=f_i(y)+\sum_{a<d_i}F_{i,a}(y)$ with its indicated homogeneous pieces, use equations
$$
\widetilde g_i(t,x)
      =g_i(x)+\sum_{a<d_i}t^{d_i-a}F_{i,a}(x).
$$
The quotient $B=k[[t,x_1,\ldots,x_e]]/(\widetilde g_i)$ is finite free over $R$ on the monomial lifts $b_j$. In detail, the equations together with $t$ form a system of parameters, so $t$ is regular on $B$. The special fiber is $A$. Its maximal ideal is nilpotent modulo $t$, so the maximal-ideal and $t$-adic topologies of $B$ are equivalent. Completeness gives generation over $R$ by successively lifting modulo $t$, and independence follows from regularity of $t$ and independence modulo $t$.

On putting $x=ty$, the equations $t^{-d_i}\widetilde g_i(t,ty)$ specialize to $F_i(y)$. Hensel lifting at each of their simple $k$-points gives a tuple $y=\rho_j(t)$ over $R$. This can be computed one coefficient at a time using the invertible residual Jacobian. Evaluate the monomial basis of $B$ at $x=t\rho_j(t)$. The evaluation matrix is $W(t)\operatorname{diag}(t^{\deg b_j})$. Its normalized matrix reduces to the invertible monomial evaluation matrix on the split point set. There is therefore an embedding of $B$ as a split smoothing lattice in $R^n$ containing $t^sR^n$. The Loewy bound proves equality, and Theorem 1 gives a polynomial tensor presentation of precisely this order.

For algebraically closed $k$, choose $F_i(y)=f_i(y)+y_i-\alpha_i$ for suitable $\alpha_i\in k$. The polynomial map $y\mapsto (f_i(y)+y_i)_i$ is finite: degree reduction using the highest forms $f_i$ expresses $k[y]$ as a finite module over the algebra generated by the coordinate functions. It is dominant by dimension, and its Jacobian at zero is the identity. The critical locus is a proper closed set. Its image under the finite map is closed of dimension less than $e$. Choose $\alpha$ outside that image. The resulting fiber is reduced and split over $k$, and the homogenized basis argument gives exactly $n$ points of the required degree filtration. This reasoning is valid in positive characteristic, even if the map given by the $f_i$ alone is inseparable.

For a nonhomogeneous example, take $A=k[x,y]/(x^2-y^3,y^4)$. Reduction replaces $x^2$ by $y^3$, increasing total degree, and gives basis $y^j,xy^j$ for $0\le j<4$. Hence the tangent cone is $k[x,y]/(x^2,y^4)$ and over algebraically closed $k$ the exact diagonal order is four.

For the same algebra the exact order is five over $\mathbb F_2$ and $\mathbb F_3$. To attain order four, Theorem 2 would require eight distinct first-order points in the plane. The plane over $\mathbb F_2$ has only four points. Over $\mathbb F_3$, a polynomial with highest homogeneous part $x^2$ is monic quadratic in $x$ for each fixed $y$, so it has at most six zeros in the plane. Thus order four is impossible over either field.

For the upper bound, take four balanced roots $\lambda_i\in tR$ for the $y$ variable as in Section 2, with maximum $y$-conductor exponent four over either field. Impose $\prod_i(y-\lambda_i)=0$. Over $\mathbb F_3$ also impose $x^2-y^3-t^2=0$, and over $\mathbb F_2$ impose $x^2+tx-y^3=0$. The resulting algebra is free over $R$ on the same eight basis elements and has special fiber $A$. Over each generic $y=\lambda_i$, substitute $x=tz$ and divide the second equation by $t^2$. It reduces to $z^2-1$ in characteristic three and $z^2+z$ in characteristic two. Its two simple roots lift to two $x$ values whose difference has valuation one. For a point with coordinates $(x_{i,\pm},\lambda_i)$, the primitive idempotent is the $i$-th $y$-Lagrange polynomial times $(x-x_{i,\mp})/(x_{i,\pm}-x_{i,\mp})$. Its smallest basis coefficient valuation is minus the $i$-th $y$-conductor exponent minus one, by the monic numerators. The split conductor is therefore five.

## Verification and scope

The tensor–smoothability direction on a unital slice is classical. Here its quantitative content is the equality with the minimal conductor exponent of a split lattice and the exact corner pole calculation. The order concerns a diagonal source of length $n$ and a concise unital target. The proof gives exact new sufficient criteria and values on the described classes, and does not give a universal upper bound on the order for every smoothable algebra. The distinction from the error degree of the resulting tensor arc and from merely reduced nonsplit generic fibers is essential. [Bläser–Lysikov](https://arxiv.org/abs/1606.04253) · [Ganesh–Koiran–Oliveira on degeneration order and error degree](https://arxiv.org/html/2608.10179v1)

These are written proofs. All constructions and pole estimates are over the stated fields.
