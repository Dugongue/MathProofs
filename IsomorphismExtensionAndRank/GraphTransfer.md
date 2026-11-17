# Reconstructing graph isomorphisms from irreducible determinant polynomials

## Theorem

There is an explicit assignment $G\mapsto P_G$ over $\mathbb F_3$ for finite simple graphs with at least one edge and even order $m$. The form $P_G$ is the determinant of an $(m+2)\times(m+2)$ matrix of linear forms in $m+2$ variables. It is homogeneous and absolutely irreducible. The pencil and a division-free polynomial-size arithmetic circuit for its determinant are computable in deterministic polynomial time. Then:

1. Two graphs are isomorphic if and only if their forms are projectively linearly equivalent over $\mathbb F_3$. This is also equivalent to exact linear equivalence of the normalized forms. Ordinary tensor isomorphism of the corresponding pencils has the same answer.
2. Every projective linear symmetry of a normalized form comes from a graph automorphism, a common scalar on all variables, and one common Frobenius power on a two-dimensional quotient. Every such symmetry lifts to an isomorphism of the original pencils, with precisely two scalar choices for the lift.
3. Given only extension-field evaluations of a polynomial promised to be in this family up to a base-field linear substitution and nonzero scalar, a Las Vegas polynomial-time algorithm recovers its graph and a variable change to the normalized form, including the scalar. The algorithm does not need the circuit description or a determinantal presentation.

Thus GI has a deterministic many-one reduction to equivalence of these absolutely irreducible determinant forms under arbitrary linear changes of variables, and a Las Vegas many-one reduction in the other direction even from black-box inputs. The statements concern formal polynomial identities. Evaluation on the three base-field elements alone is not the access model.

The construction starts from the graph pencils of the preceding rank-one-incidence proof, and the pencil formula and needed properties are included below. For context, the classical critical polynomial $\det(\operatorname{diag}(x)-A_G)$ permits graph recovery in its displayed variables. Here the data include an arbitrary linear change mixing the vertex variables with the extra variables, and the algorithm recovers the hidden vertex lines. The older general reductions to cubic form equivalence also apply to arbitrary linear substitutions. The specific homogeneous irreducible determinant realization and black-box reconstruction are the claims proved below. [Lorenzini, The Critical Polynomial of a Graph](https://arxiv.org/abs/2311.06367) · [Grochow and Qiao, Tensor Isomorphism-Completeness](https://arxiv.org/abs/1907.00309)

## The polynomial and its leading coefficients

Put $F=\mathbb F_3$, $E=\mathbb F_9$, $\sigma(z)=z^3$, and write $N,L$ for the norm and trace from $E$ to $F$. Let $A_G$ be the symmetric $0,1$ adjacency matrix with zero diagonal. Set $n=m+2$. The variables are $x=(x_1,\ldots,x_m)$ and $z\in E$, where $z$ denotes two $F$-variables in a fixed basis. Use the pencil
$$
 M_G(x,z)=
 \begin{pmatrix}
   \operatorname{diag}(x)+L(z)A_G
   &{\bf1}\operatorname{Tr}(\sigma(z)\,\cdot)\\
   \sigma(z){\bf1}^{T}&[w\mapsto zw]
 \end{pmatrix},
 \qquad P_G(x,z)=\det M_G(x,z).
$$
The $E$-coordinates of $\sigma(z)$ are linear over $F$. Over a splitting field write $p,q$ for the two linear coordinates of $z$, so $N=pq$, $L=p+q$, and $\sigma$ swaps $p,q$. The bottom Schur complement gives
$$
 P_G=N(z)\det\bigl(\operatorname{diag}(x)+L(z)A_G-s(z){\bf1}{\bf1}^{T}\bigr),
 \qquad
 s(z)=q^2/p+p^2/q .
$$
This equality is in the rational function field. The full expression is a polynomial. For $S\subseteq[m]$, write $x_{\widehat S}=\prod_{i\notin S}x_i$. The needed coefficients are
$$
 [x_{\widehat\varnothing}]P_G=N,\qquad
 [x_{\widehat i}]P_G=-Ns,\qquad
 [x_{\widehat {ij}}]P_G=
 N\left(s^2-(a_{ij}L-s)^2\right).
 \tag{1}
$$
In particular $-Ns=-(p^3+q^3)$. The pair-deletion coefficient at a nonedge is zero. At an edge it is
$$
 2LNs-L^2N=-p^4-q^4+p^3q+pq^3+p^2q^2 .
 \tag{2}
$$

To see absolute irreducibility, work first over the rational function field of $p,q$ over an algebraic closure. The Schur determinant is multiaffine in $x$, with leading term $\prod_i x_i$ and leading coefficient one. In a factorization the variables partition between factors, since degrees in each variable add. Normalize the top coefficients of the factors to one. If $x_i,x_j$ belonged to different factors, the double-deletion coefficient would be the product of the two single-deletion coefficients. By (1) the difference is $-(a_{ij}L-s)^2$, which is nonzero because $s$ has a pole along each of $p=0,q=0$. Thus there is no factorization with both factors using $x$. A pure $p,q$ factor of the full polynomial would divide its leading coefficient $pq$. Its single-deletion coefficient $-(p^3+q^3)$ is divisible by neither $p$ nor $q$. This excludes every pure $p,q$ factor. Standard division-free determinant circuits, for example Berkowitz's, have polynomial size. [Berkowitz](https://doi.org/10.1016/0020-0190(84)90018-8)

## Classification under arbitrary linear changes

A nonzero rational direction $v=(u,w)$ for which $P_G(X+t v)$ has degree at most one in $t$ is exactly one of the $m$ vertex lines. For $w\ne0$, the coefficient of $\prod_i x_i$ is $N(z+t w)$, whose quadratic term is the nonzero $N(w)$. For $w=0$, the terms of degree $m-2$ in $x$ in the quadratic coefficient of the translation are $N(z)\sum_{i<j}u_i u_j x_{\widehat{ij}}$. They vanish precisely when at most one $u_i$ is nonzero. A translation along such a line is linear by multiaffinity.

An invertible linear $F$-map $T$ with $P_H(T(x,z))=\lambda P_G(x,z)$ for $\lambda\in F^\times$ must permute these lines. Write it in the form
$$
 x'_{\pi(i)}=a_i x_i+\ell_i(z),\qquad z'=Cz ,
$$
with $a_i\in F^\times$, linear forms $\ell_i$, and $C$ invertible. The leading coefficient in (1) implies that $N(Cz)$ is a nonzero constant multiple of $N(z)$. Over $E$, the unique two factors give a diagonal map on $p,q$, possibly followed by their interchange. Rationality forces the two diagonal entries to be conjugate. Equivalently $Cz=c\tau(z)$ for $c\in E^\times$ and $\tau\in\{1,\sigma\}$. Comparing each single-deletion coefficient to the leading coefficient gives
$$
 \ell_i(z)=s(Cz)-a_i s(z).
$$
The coefficients of $q^2/p,p^2/q$ in $s(Cz)$ are $c^5,c^7$, in either order. Thus cancellation of both poles implies $a_i=c^5=c^7$ for every $i$. In particular $c^2=1$, so $c\in F^\times$, $a_i=c$, and $\ell_i=0$.

The pair-deletion ratios now identify whether each $a_{ij}$ is zero or one. In fact $L(c\tau z)=cL(z)$ and $s(c\tau z)=cs(z)$. The rational functions $s^2$ and $(L-s)^2$ differ, since their difference is $L(L-2s)$ and $s$ has poles. Hence the pair-deletion comparison forces $a_{ij}=a'_{\pi(i)\pi(j)}$. Conversely each such graph isomorphism, common scalar $c\in F^\times$, and $\tau$ give a polynomial equivalence. The multiplier is $c^n=1$, because $n$ is even. Thus every normalized projective transporter is exact, and the normalized variable automorphism group is $\operatorname{Aut}(G)\times C_2\times C_2$.

For the lift, in the two matrix modes use the same graph permutation and quotient $\tau$, and multiply the two modes by $a,b\in F^\times$ with $ab=c$. These give the required variable map on the parameter space in the convention $M_H(T(x,z))=P M_G(x,z)Q^*$, where $*$ is the adjoint for the coordinate and trace pairings. Any two lifts of one variable map differ by an isomorphism with identity variable map. To compute this kernel, use the rank-one vertex slices, which force diagonal top banks with reciprocal scalar factors on the two modes, and use the invertible bottom multiplication block at $z=1$, which makes the two quotient maps trace-adjoint inverses. Commuting with every multiplication $w\mapsto zw$ then forces those quotient maps to be multiplication by $a,a^{-1}$ for $a\in E^\times$. In the mixed row and column equations the unknown shears contribute terms linear in $z$ as an $E$-variable, while the original mixed equations have coefficient of $z^3$. The two $E$-linearized monomials are independent. Thus both shears vanish and the top scalars are $a,a^{-1}$ in $F^\times$ in every coordinate. These two common-scalar pairs are the entire kernel. Any ordinary tensor isomorphism induces projective polynomial equivalence by taking determinants, so the three equivalence relations in assertion 1 agree.

## Recovering the vertex lines from polynomial evaluations

For a polynomial $P$ in the promise, form the span
$$
 \mathcal Q_P=\operatorname{span}\bigl\{[t^2]P(X+t v): X\in K^n\bigr\}
$$
of quadrics in the formal direction $v$, for an extension $K/F$ containing $E$ and of cardinality greater than $2n$. Its dimension in the displayed coordinates is $\binom{n+1}{2}-m$. To show this, the following computation uses the coefficients in the formal base point $X=(x,z)$. They span the same space as evaluations over $K$, since every individual degree is less than $|K|$ and a nonzero polynomial with those individual degree bounds cannot vanish on all $K^n$.

Write $u_i,w_p,w_q$ for the direction coordinates. By multiaffinity no quadric has a term $u_i^2$. The coefficient at $\prod_i x_i$ gives $w_p w_q$. The coefficient at $x_{\widehat i}$ gives $u_i(pw_q+qw_p)$: the term $-Ns=-(p^3+q^3)$ has zero quadratic Hasse derivative in characteristic three. Taking its $p,q$ coefficients gives all mixed $u_i w_p,u_i w_q$. At a pair $i,j$ forming an edge, the coefficient at $x_{\widehat {ij}}$ gives the sum of $pq\,u_i u_j$ and the quadratic derivative of (2). The $q^2,p^2$ coefficients of the latter are $w_p^2,w_q^2$, respectively. The terms with exponents $4$ or $3,1$ in (2) have zero quadratic Hasse derivative, while the term $p^2q^2$ supplies the two squares. This gives both squares. Finally, for every pair $i,j$, the $pq$ coefficient at $x_{\widehat{ij}}$ gives $u_i u_j$ after subtracting a multiple of $w_p w_q$; this also covers a nonedge. Thus the missing $u_i^2$ monomials are exactly the codimension $m$ deficiency of the computed span. An arbitrary base-field substitution just transports this span, and multiplication of $P$ by a nonzero scalar leaves it unchanged.

Construct $K$ with even degree and $|K|$ polynomial in $n$ by enumerating irreducible polynomials of the required degree. Sample independent uniform $X\in K^n$. For each sample recover the quadric by evaluating $v$ at coordinate vectors and sums of two coordinate vectors, with univariate interpolation in $t$ on at most $n+1$ values. Keep sampling while the current span has smaller dimension than $\binom{n+1}{2}-m$. Whenever it is smaller, there is a linear functional vanishing on the sampled space that is not identically zero on the full span. Its value on the next quadric is a nonzero polynomial in $X$ of total degree at most $n-2$. By the Schwartz–Zippel bound the probability of increasing the rank is at least $1/2$. Thus the rank stopping rule takes expected polynomially many evaluations. On the promise it always returns the exact span.

The annihilator $\mathcal D=\mathcal Q_P^\perp$ in symmetric matrices, with pairing $\langle Q,vv^T\rangle=Q(v)$, is the span of the $m$ squares of the hidden vertex lines. It descends to $F$: the defining coefficient span is over $F$, and the reduced row echelon basis computed over $K$ therefore has entries in $F$. Compute the sum $H$ of the images of the elements of $\mathcal D$. Within $\operatorname{Sym}^2 H$ the left idealizer
$$
 B=\{a\in\operatorname{End}_F(H):a\mathcal D\subseteq\mathcal D\}
$$
is the diagonal algebra in the unknown basis of the $m$ vertex lines. Indeed in that basis $\mathcal D$ is the space of diagonal matrices, so multiplying each diagonal matrix unit detects each off-diagonal entry of $a$. Compute $B$ by linear equations and refine simultaneous eigenspaces of its basis matrices using the three possible eigenvalues. The resulting lines give the desired $F$-rational axes. If a full coefficient list is the input, expanding the quadratic Hasse translation of each monomial directly computes $\mathcal Q_P$ in deterministic time polynomial in the list length and $n$.

## Read the graph in the recovered frame

Choose an arbitrary ordered rational basis $v_i$ of the recovered lines and a complement to $H$ in the raw variable space. Enumerate the constantly many identifications of that complement with $E$, and write $\widetilde P(x,z)$ for the input polynomial in each chart. Extract its leading, single-deletion and pair-deletion coefficients in $x$. This is polynomial-time interpolation using only evaluations: to recover the coefficient of $x_{\widehat S}$ at any $z$, set $x_i=0$ for $i\in S$, and set every other $x_i=t$. The coefficient of $t^{m-|S|}$ is the desired one by multiaffinity. Then interpolate the two $z$-variables in total degree at most four.

In a chart use $A(z)=[x_{\widehat\varnothing}]\widetilde P$ and $R_i(z)=[x_{\widehat i}]\widetilde P/A(z)$. Check first that $A=\gamma N$ for $\gamma\in F^\times$. For each $i$ find $b_i\in F^\times$ such that $b_iR_i+s$ is linear, by checking both possible scalars. There is at most one by the pole test. Call that linear form $L_i(z)$. Compute
$$
 b_i b_j\left(R_i R_j-\frac{[x_{\widehat{ij}}]\widetilde P}{A}\right).
$$
Give the pair an edge exactly when this equals $(L-s)^2$, and a nonedge when it equals $s^2$. Reject the chart on any failed check. These are tests of bounded-degree rational functions, so can be done by cross multiplication. The chart with true quotient coordinates passes. In any other chart passing the tests, express the promised equivalence in true coordinates as $x'_{\pi(i)}=a_i x_i+\ell_i(z)$, $z'=Cz$. The leading check forces $C=c\tau$. The tests $b_iR_i+s$ linear require $s(Cz)-(a_i/b_i)s(z)$ linear. The two poles force $c\in F^\times$ and $a_i/b_i=c$, as in the classification. Hence every passing chart gives the true graph in its recovered vertex ordering.

Substitution $x_i=(y_i-L_i(z))/b_i$ in a passing chart now exhibits the required normalization: in the original graph coordinates it sends $y_i$ to $c\,y_i$ up to the common permutation, and sends $z$ to $c\,\tau(z)$. The scalar multiplier between the raw form in the new chart and the normalized graph form is obtained by dividing the coefficient of $\prod y_i$ by $N(z)$. This calibration also gives the exact-equivalence decision on raw promised forms, since every projective transporter between normalized forms has multiplier one. For projective equivalence, the recovered graph pair is the required ordinary GI instance.

For the forward reduction from unrestricted GI, handle pairs with different orders directly. Adjoin one disjoint copy of $K_2$ to both graphs, and if necessary adjoin one isolated vertex to both to make their order even. Adding the same connected components preserves and reflects isomorphism by uniqueness of the multiset of connected components. The resulting graphs meet the edge assumption used in the rank computation.

The unrestricted equivalence problem for arbitrary irreducible determinant polynomials is outside this theorem. The new feature is a polynomial-time recovery algorithm on the specified raw orbit family without its pencil representation. The proof is informal. Exact finite controls covered the 64 labelled graphs of orders two and four with at least one edge. They checked the determinant coefficient identities and quadratic-span rank before and after bank shears. The exact novelty of the combination remains to be checked beyond the related principal-minor and graph-polynomial literature. [Al Ahmadieh and Vinzant, principal minors through determinantal representations](https://arxiv.org/abs/2105.13444)
