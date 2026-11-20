# Prescribed-determinant tensor equivalence from finite rank loci with projective frames

## Statement

Fix a label dimension $r\ge 2$. Let $F=\mathbf F_q$ be explicitly represented in a polynomial basis, with $q$ varying. Let $A(x)=\sum_{i=1}^r x_i A_i$ and $B(x)=\sum_{i=1}^r x_i B_i$ be $m$ by $n$ matrix spaces given as linear matrix maps in $r$ labeled variables. Assume that for some nonnegative threshold $k$ the geometric rank locus
$$
X_k(A)=\{[x]\in\mathbf P^{r-1}(\overline F):\operatorname{rank} A(x)\le k\}
$$
is finite and contains a projective frame. A projective frame consists of $r+1$ ordered projective points such that every $r$ of their vector representatives are linearly independent. Both the threshold and the geometric points can be computed in the algebraic representations below. The target matrix space $B$ is arbitrary.

Given $c,s,t\in F^\times$, one can decide deterministically in polynomial bit time whether there are $f\in\mathrm{GL}_r(F)$, $g\in\mathrm{GL}_n(F)$, and $h\in\mathrm{GL}_m(F)$ with
$$
B(fx)g=hA(x),\qquad \det f=c,\qquad \det g=s,\qquad \det h=t.
$$
The polynomial degree in the running-time bound may depend on the fixed $r$. The all-ones determinant triple gives a same-field polynomial many-one decision reduction of this family of special-linear tensor isomorphism to ordinary tensor isomorphism, by mapping the verdict to the fixed scalar yes instance $(1,1)$ or no instance $(0,1)$. A covariant tensor action uses the inverse transpose of $f$ on the label mode, inverse transpose of $g$ on the column mode, and $h$ on the row mode. This proof uses the ordered determinant-image lemma in the accompanying paper *Deterministic polynomial-time special-linear equivalence of matrix pencils over finite fields*, in the section “Ordered equivalence with prescribed determinants.” The lemma handles arbitrary ordered lists of slices.

## Equations for rank loci

For $1\le \ell\le d$ define the $\ell$ by $d$ matrix $C_{d,\ell}(U)$ by
$$
(C_{d,\ell}(U))_{ij}=U^{ij}\qquad (1\le i\le \ell,\ 0\le j<d).
$$
Over any field extension $K/F$, its action on a vector of coefficients of $p(z)\in K[z]$ of degree at most $d-1$ is evaluation at $U,U^2,\ldots,U^\ell$. On any $\ell$-dimensional subspace of $K^d$ its restriction becomes invertible over $K(U)$. Indeed, choose a polynomial basis $p_1,\ldots,p_\ell$ with strictly increasing degrees $b_1<\cdots<b_\ell$ by coefficient elimination. In the determinant of $(p_j(U^i))_{i,j}$ the maximum degree $\sum_i i b_i$ occurs only for the identity permutation using all leading terms. Swapping any inversion in the degrees paired to the increasing row indices strictly increases this sum. Taking a non-leading monomial in any entry strictly lowers degree within its permutation. Thus the coefficient of the highest degree is a nonzero product of leading coefficients, in every characteristic.

Put $M=\min(m,n)$ and, for $1\le \ell\le M$, form
$$
D_{A,\ell}(x,U,V)=
\det\!\big(C_{m,\ell}(U)A(x)C_{n,\ell}(V)^{\mathsf T}\big).
$$
For any fixed $x$ over a field extension of $F$, this polynomial in $U,V$ is nonzero exactly when $\operatorname{rank} A(x)\ge \ell$. If the rank is at least $\ell$, restrict the first compression to $\ell$ independent vectors in the column span. This gives rank $\ell$ for $C_{m,\ell}(U)A(x)$ over $K(U)$. Apply the same evaluation argument to the $\ell$-dimensional row space with parameter $V$, which gives an invertible $\ell$ by $\ell$ matrix over $K(U,V)$. If $\operatorname{rank} A(x)<\ell$, the compressed matrix has rank less than $\ell$ over this field.

The polynomial is homogeneous in $x$ of degree $\ell$, and its degrees in $U$ and $V$ are at most
$$
(m-1)\ell(\ell+1)/2,\qquad (n-1)\ell(\ell+1)/2
$$
respectively, by counting the exponents contributed by the rows and columns in each determinant term. For fixed $r$, the number of monomials within these bounds is polynomial in $m+n$. Compute the coefficients in $U,V$ by exact fraction-free determinant arithmetic in $F[x_1,\ldots,x_r,U,V]$. The fraction-free intermediates are signed minors, or intermediate sums and products of two minors, so all degrees are polynomially bounded. The coefficient polynomials in $x$ cut out exactly $X_{\ell-1}(A)$ geometrically. The generic rank is also computable as the largest $\ell$ with $D_{A,\ell}\ne 0$, or zero if none is nonzero. The same equations apply to $B$. [Bareiss, exact fraction-free elimination](https://www.ams.org/mcom/1968-22-103/S0025-5718-1968-0226829-0/S0025-5718-1968-0226829-0.pdf)

## Computing finite chart algebras

For each $k=0,\ldots,M-1$, use the coefficient equations at $\ell=k+1$. In each affine chart $x_i=1$, substitute that value in all equations and work in the other $r-1$ variables. The ideal may be nonreduced. It has a finite geometric zero set exactly when its quotient algebra over $F$ is finite dimensional, including the zero algebra for an empty chart.

One can compute the quotient or detect that it has infinite dimension in polynomial bit time for fixed $r$. Here is the degree-bound approach. Use a degree-compatible monomial order. Dubé's bound on Gröbner basis degrees is polynomial in the input degree for a fixed number of variables. Call such a bound $G$. Hermann's bound guarantees that each element of the ideal of degree at most $G$ has a representation by the supplied generators with multiplying polynomials of bounded degree that is also polynomial for fixed $r$. In a single coefficient linear system solve for such multiplying polynomials and for their sum in the space of degree at most $G$. Project its nullspace onto the coefficients of that sum to find the entire space of ideal elements of degree at most $G$. Row reduce this space in decreasing monomial order. The pivot monomials produce the initial ideal: they all belong to it and include the leading monomials of all elements of degree at most $G$, hence of a Gröbner basis. The resulting row polynomials themselves form a Gröbner basis. The quotient is finite dimensional exactly when the initial ideal contains a power of each variable. The constant leading monomial yields the zero algebra. Otherwise, in the finite case each required pure power has degree at most $G$, and the at most $G^{r-1}$ standard monomials give the quotient basis. Polynomial reduction computes the multiplication tables. Thus the algebra sizes and all operations are polynomial in the explicit instance length. [Dubé, Corollary 8.3](https://cs.uwaterloo.ca/~r5olivei/courses/2025-spring-cs860/D90.pdf), [Hermann's degree bound in Aschenbrenner, Introduction](https://www.math.ucla.edu/~matthias/pdf/ideal2.pdf)

For a chart algebra $H$ of positive finite dimension $D$ choose $j\ge 0$ with $q^j\ge D$. The linear map $a\mapsto a^{q^j}$ has kernel equal to the nilradical. If $a$ is nilpotent, its nilpotence index is at most $D$ by the minimal polynomial of the multiplication operator, whose unit vector gives $a^i$ on its successive iterates. Conversely an element in this kernel is nilpotent by definition. Compute the kernel and quotient it out. The reduced algebra is a product of finite separable fields over $F$ and represents its geometric chart points. Use the direct product of all reduced chart algebras to represent the full projective set. A point may occur in several charts, and each of its chart representatives is a vector with its specified coordinate $1$.

In a finite product of fields given by its multiplication table, one can split according to the vanishing of any element $u$ by computing the kernel and image of multiplication by $u$ as complementary ideals. Project $1$ onto the two ideals to get the two component identities. On the nonvanishing part $u$ is invertible, computed by solving a linear system. This allows simultaneous Gaussian elimination and other field arithmetic with component-dependent branches. If each field computation has polynomial length and the algebra dimension is polynomial, the total work is polynomial, since each nonzero branch represents at least one field component and the component computations partition at every split.

Search all thresholds for a finite $X_k(A)$ whose chart algebra admits a frame. A frame is detected in its tensor power of order $r+1$ by the determinant and coordinate tests described below. If $X_k(A)$ is infinite some chart is infinite. If it is finite, this representation and test give exactly whether a frame exists, even when no frame is rational over $F$. The stated assumption guarantees some threshold is found. Threshold $M$ and higher give the entire projective space, which is infinite over $\overline F$ for $r\ge2$.

## Candidate maps and determinant lift

For a threshold found for $A$, compute the chart algebras of $X_k(B)$. If any chart has infinite dimension, reject, since every transporter carries $X_k(A)$ bijectively onto $X_k(B)$. If the chart algebras are finite, let $H_A,H_B$ denote the two reduced chart products. The algebra
$$
T=H_A^{\otimes_F(r+1)}\otimes_F H_B^{\otimes_F(r+1)}
$$
is finite étale. Its geometric components enumerate ordered tuples of $r+1$ source points and $r+1$ target points with all their chart representations. For a tuple of source representatives $v_1,\ldots,v_{r+1}$, test that $W=(v_1,\ldots,v_r)$ is invertible and that all coordinates $\alpha_i$ of $\alpha=W^{-1}v_{r+1}$ are nonzero. This is precisely the frame test, since replacing $v_i$ by $v_{r+1}$ multiplies the determinant by $\alpha_i$ up to sign. Apply the same test for the target. The tests apply to the source tensor power alone during threshold search.

On every surviving component form $Q_A=W\operatorname{diag}(\alpha_1,\ldots,\alpha_r)$ and its target counterpart $Q_B$. The map $Q_A$ carries the standard ordered frame $[e_1],\ldots,[e_r],[\sum_i e_i]$ to the source frame. The unique projective map between these frames is represented by $Q_BQ_A^{-1}$. For uniqueness, the only projective map stabilizing the standard ordered frame is the identity, because a representative is diagonal and the last point forces all its diagonal entries to agree. Changes of chart representatives therefore leave the projective map unchanged.

Normalize this candidate matrix $U$ on each component by its first nonzero entry. Retain the components where all normalized entries satisfy $z^q=z$. A projective map over an extension is rational precisely when its normalized entries are rational. This test also handles frame tuples for which none of the points are rational. Compute the $q$-Frobenius-fixed algebra of the surviving components as the kernel of $a\mapsto a^q-a$. It is a product of copies of $F$, and $U$ belongs to the matrix algebra over this split algebra.

Every lift of $U$ with determinant $c$ has the form $f=\lambda U$ with $\lambda^r=c/\det U$. In each split component put $b=c/\det U$. Compute
$$
P(Y)=\gcd\big(Y^r-b,Y^q-Y\big)
$$
by first reducing $Y^q-Y$ modulo $Y^r-b$ using modular powering. This works when the characteristic divides $r$: $Y^q-Y$ is squarefree and has exactly the elements of $F$ as its roots, so the gcd is the product of the distinct rational scalar lifts. Discard constant gcd components and adjoin a root of $P(Y)$ in each remaining component. The enlarged algebra is again split over $F$. All arithmetic in it can therefore be interpreted componentwise over the original field.

For each retained $f$, apply the ordered determinant-image lemma to the slices of $A(x)$ and $B(fx)$, with determinant targets $s,t$. Accept if any component passes. Every passing component gives a rational label map of determinant $c$ with a valid ordered transporter of the required determinants. Conversely, a prescribed-determinant transporter maps any source frame in the chosen rank locus to a target frame in that same rank locus. Those two frames occur in the algebra, their unique projective map is the class of the given $f$, and the original $f$ survives the determinant lift and ordered test.

There are at most $M$ threshold checks. All chart algebra dimensions are polynomial in the input for fixed $r$. The largest candidate tensor powers have exponent $2(r+1)$ and therefore have polynomial dimension for fixed $r$. Normalization and determinant arithmetic use polynomially many operations in these algebras. Frobenius and modular powering use polynomially many operations in $\log q$ and the algebra dimensions. The ordered test is polynomial bit time even for variable $q$, with no factorization step. The method produces a deterministic decision.

## Example families

For every $r\ge3$ one rectangular family has $r+1$ column blocks of width one, each in its own disjoint $(r-1)$-row block. Given a fixed rational projective frame, choose its $i$th block to be a linear map $F^r\to F^{r-1}$ with kernel the line of frame point $i$. The block rank drops exactly at that point, hence the generic rank-drop locus is exactly the entire frame. The matrix has $(r-1)(r+1)$ rows and $r+1$ columns.

The finite threshold may be strictly below the generic rank-drop threshold, even for square matrices. Given an arbitrary data matrix map $A_{\rm data}(x)$ of size $a$ by $b$, choose a positive integer $N>\min(a,b)$ and set
$$
A(x)=\operatorname{diag}\big(A_{\rm data}(x),L_1(x)I_N,\ldots,L_{r+1}(x)I_N\big),
$$
where $L_i=x_i$ for $i\le r$ and $L_{r+1}=-\sum_{i=1}^r x_i$. This is square when $a=b$. Its map $x\mapsto (L_1(x),\ldots,L_{r+1}(x))$ identifies the label space with the sum-zero hyperplane in $F^{r+1}$. Every nonzero projective point has at least two nonzero $L_i$. Exactly two nonzero coordinates give total rank at most $k=2N+\min(a,b)$, while at least three give rank at least $3N>k$. Thus $X_k(A)$ is exactly the finite set of points spanned by the vectors $e_u-e_v$ in this hyperplane. The $r+1$ cyclic differences $e_i-e_{i+1}$, with cyclic subscripts, form a projective frame in every characteristic: any relation on all differences forces equal coefficients at each index, so the only relations are multiples of the relation with all coefficients $1$. In particular every $r$ of them are linearly independent. For $r\ge3$, each hyperplane $L_i=0$ lies in the generic rank-drop locus. Indeed, the generic rank is $(r+1)N$ plus the generic rank of the data block, whereas at least $N$ scalar-block rank is lost on each such hyperplane and the data rank cannot exceed its generic rank. Consequently the generic rank-drop locus is positive dimensional, while the chosen deeper rank locus still gives the frame and the decision theorem.

This is a paper proof for the fixed-label-dimension family with a finite frame-bearing geometric rank locus. It depends on no Riemann hypothesis. It has no Lean certificate. The unrestricted special-linear reverse reduction remains open here. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
