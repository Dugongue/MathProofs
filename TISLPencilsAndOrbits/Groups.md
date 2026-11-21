# Determinant characters split generic three-slice tensor orbits

Let $G=\operatorname{GL}_a(F)\times\operatorname{GL}_b(F)\times\operatorname{GL}_c(F)$ act on $F^a\otimes F^b\otimes F^c$, and let $H$ be the product of the three special linear groups. The following is a same-field result about exact orbits. A generic condition below is given by explicit polynomial nonvanishing tests.

**Theorem.** On an explicit nonempty Zariski-open subset of the $3\times n\times n$ tensor space over every algebraically closed field of characteristic zero, $n\geq2$, one polynomial-time computable scalar $\Omega$ classifies the $H$-orbits inside each $G$-orbit. In particular, on this subset, there is a polynomial-time many-one reduction from special-linear tensor isomorphism to ordinary tensor isomorphism over the same field in the arithmetic model. It takes the input pair unchanged when their $\Omega$-values agree, and emits a fixed non-isomorphic pair otherwise.

For $F=\mathbb F_q$ and $\gcd(n,q-1)=1$, the analogous theorem holds over $F$ on the nonzero locus of the Strassen determinant, with deterministic bit complexity polynomial in $n$ and $\log q$. This locus has a rational point for every finite field and every $n\geq2$. In characteristic zero the proof does not require $\gcd(3,n)=1$.

## Scalar corrections and the field of definition

Put $L=\operatorname{lcm}(a,b,c)$ and define the primitive determinant character
$$
 \chi(u,v,w)=u^{L/a}v^{L/b}w^{L/c}\qquad((u,v,w)\in(F^\times)^3).
$$
The three exponents have greatest common divisor one, so $\chi$ is surjective. Every tensor is fixed by the scalar subgroup
$$
 Z_0=\{(\lambda I_a,\mu I_b,(\lambda\mu)^{-1}I_c):\lambda,\mu\in F^\times\}.
$$
Its determinant image $D_0$ lies in $\ker\chi$. The exponent columns of this determinant map are $(a,0,-c)$ and $(0,b,-c)$. Write $s_1,s_2$ for their nonzero integer Smith diagonals. The gcd of the entries and the gcd of the maximal minors give
$$
 s_1=\gcd(a,b,c),\qquad s_1s_2=\gcd(ab,ac,bc).
$$
Because the character is primitive, an integer coordinate change makes $\ker\chi$ the first two coordinates. Integer unimodular transformations are isomorphisms of powers of $F^\times$, using only multiplication and inversion. Smith form on those two coordinates therefore gives
$$
 (\ker\chi)/D_0
 \cong
 F^\times/(F^\times)^{s_1}\ \times\ F^\times/(F^\times)^{s_2}.
$$
In particular $D_0=\ker\chi$ over an algebraically closed field. For a finite field, equality holds exactly when $\gcd(q-1,\gcd(ab,ac,bc))=1$.

Suppose $D_0=\ker\chi$ and a scalar function $P$ on a $G$-stable subset satisfies
$$
 P(gT)=\chi(\det g_1,\det g_2,\det g_3)^kP(T)
$$
with no zero values there, and the $k$-th power map is injective on $F^\times$. For a $G$-transporter between tensors with equal values, its determinant triple lies in $\ker\chi$. Right-multiply the transporter by a scalar stabilizer element with the inverse determinant triple to obtain an $H$-transporter. The converse follows from the transformation rule. This shows that the determinant image of each stabilizer on this subset is exactly $D_0$. When $k=1$, every nonzero scalar value occurs within each $G$-orbit, by surjectivity of the character. Thus each such ordinary orbit splits into special-linear orbits indexed by $F^\times$. The same surjectivity of values holds when the $k$-th power is bijective.

There is also a scheme version when the function itself has primitive weight $k=1$, given by polynomial expressions and invertible denominators on the subset. Regard $Z_0$ as a split torus scheme. In the same Smith coordinates, its determinant map onto $\ker\chi$ is the product of the $s_1$-th and $s_2$-th power maps, which is finite flat with kernel $\mu_{s_1}\times\mu_{s_2}$. For two tensors with equal values of the primitive function, the scheme-theoretic determinant of any ordinary transporter lies in $\ker\chi$. Then
$$
 \operatorname{Isom}_{H}(T,T')\times Z_0
 \ \cong\
 \operatorname{Isom}_{G}(T,T')\times_{\ker\chi} Z_0,
 \qquad (h,z)\longmapsto(hz,z).
$$
The inverse sends $(g,z)$ to $(gz^{-1},z)$. Thus adjoining a scalar correction over the ordinary transporter is a finite flat torsor under the indicated group scheme. This statement records possible purely inseparable corrections without presuming they are rational over every field.

## The Strassen determinant and its weight

Let $A=F^3$, $B=C=F^n$. A tensor with slices $M_1,M_2,M_3:B^*\to C$ defines
$$
 K_T:A\otimes B^*\longrightarrow \bigwedge^2A\otimes C,\qquad
 v\otimes t\longmapsto\sum_{i=1}^3(e_i\wedge v)\otimes M_i(t).
$$
Write $P(T)=\det K_T$. For $g=(g_A,g_B,g_C)$, the matrix changes by left multiplication with $\bigwedge^2g_A\otimes g_C$ and right multiplication with $g_A^{-1}\otimes g_B^t$. Using $\det(\bigwedge^2g_A)=(\det g_A)^2$ gives
$$
 P(gT)=(\det g_A)^n(\det g_B)^3(\det g_C)^3 P(T).
$$
Here and below determinant powers arise from square matrices of polynomial size. The determinant $P$ has weight $\chi^k$ with $k=\gcd(3,n)$.

To see $P\neq0$, in the ordered target basis $(e_2\wedge e_3,e_3\wedge e_1,e_1\wedge e_2)$ the block matrix is
$$
 \begin{pmatrix}
 0&-M_3&M_2\\
 M_3&0&-M_1\\
 -M_2&M_1&0
 \end{pmatrix}.
$$
If $M_1=I$, its kernel is identified with the kernel of $[M_2,M_3]$ by elimination. Choose $M_2$ diagonal with cyclically adjacent diagonal entries different, and $M_3$ the cyclic permutation matrix. Their commutator is a weighted permutation matrix with no zero weights. Three field elements suffice to color the cycle, in all lengths $n\geq2$. Over a finite field of any size the nonvanishing can also be seen by taking the underlying vector space of $\mathbb F_{q^n}$, with $M_2$ multiplication by $u\notin\mathbb F_q$ and $M_3$ the $q$-power Frobenius. Their commutator is the invertible Frobenius followed by multiplication by $u-u^q$. These are matrices over the original field.

If $3\nmid n$, this gives $\Omega=P$ on $P\neq0$ over algebraically closed fields. For finite fields with $\gcd(n,q-1)=1$, the scalar index is $n\gcd(3,n)$, coprime to $q-1$, and $k$ is also coprime to $q-1$. Thus $P$ suffices over the finite field, even when $3\mid n$. Both assertions use the scalar correction lemma. The same test with $P$ also works over algebraically closed fields of characteristic three, since cubing is injective, and over real closed fields when $n$ is odd, since all needed scalar powers are odd.

## A second determinant weight when $3\mid n$

Write $n=3m$. Over a field of characteristic zero or characteristic greater than $n$, define a degree-four relative invariant of ternary degree-$n$ forms. For
$D(x)=\sum_{|\alpha|=n}d_\alpha x^\alpha$, let $L_D$ be the linear functional on homogeneous degree-$n$ polynomials in a variable vector $a$ given by
$$
 L_D(a^\alpha)=d_\alpha/\binom{n}{\alpha}.
$$
With four variable vectors $a_1,a_2,a_3,a_4$, set
$$
 \Phi_m(D)=
 L_D^{\otimes4}\!\left(\prod_{1\leq i<j<k\leq4}
                                  \det(a_i,a_j,a_k)^m\right).
$$
Each vector occurs in exactly three brackets, so the input to each copy of $L_D$ has degree $n$. For $D(x)=(v\cdot x)^n$, the functional $L_D$ is evaluation at $v$. Consequently change of variables $D(x)\mapsto D(g_A^t x)$ transforms $\Phi_m$ by $(\det g_A)^{4m}$. One can verify this on sums of powers and extend multilinearly, since pure powers span degree-$n$ forms after passage to the algebraic closure. For example a functional vanishing on all powers gives a zero polynomial in the coordinates of $v$, and the multinomial coefficients are invertible. The transformation equality then holds over the original field as a polynomial identity.

Apply this construction to the slice determinant $D_T(x)=\det(\sum_i x_i M_i)$. It obeys
$$
 D_{gT}(x)=(\det g_B)(\det g_C)D_T(g_A^t x).
$$
Hence $Q(T)=\Phi_m(D_T)$ transforms by $\chi^4$, whereas $P(T)$ transforms by $\chi^3$. On their joint nonzero locus, the ratio
$\Omega(T)=Q(T)/P(T)$ has the primitive weight $\chi$. In the scalar correction scheme above, the kernel for $3\times n\times n$ is $\mu_{\gcd(3,n)}\times\mu_n$. Over the algebraically closed field this yields the stated splitting and many-one reduction.

## A nonzero family for the joint locus

Over an algebraically closed field where the definition of $\Phi_m$ is available, choose a primitive $n$-th root $\zeta$. Let $D e_j=\zeta^j e_j$, let $S$ be the cyclic shift, and let $R=D^{-1}S$. The matrices $D,S,R$ pairwise $\zeta$-commute in that order, and $D^n=S^n=I$, $R^n=(-1)^{n-1}I$. Consider the three slices of the pencil
$$
 M_t(x,y,z)=xI+yD+zS+t(x+y+z)R .
$$
To calculate its determinant, write $Y=yD+zS+t(x+y+z)R$. The root-of-unity binomial formula gives $Y^n=y^nI+z^nI+t^n(x+y+z)^nR^n$. Indeed if $AB=\zeta BA$, the middle coefficients of $(A+B)^n$ vanish by the Gaussian binomial formula, whose denominators $1-\zeta^j$, $1\leq j<n$, are nonzero. Apply the identity twice, since the sum of the first two summands has the same commutation with the third.

The trace of $D^uS^v$ is zero unless $u,v$ are both zero modulo $n$, by cyclic shift and geometric summation. A monomial in $Y^j$ reorders to a scalar times $D^{i-k}S^{h+k}$ with $i+h+k=j$. For $0<j<n$, the exponents cannot both be zero modulo $n$. Thus $\operatorname{tr}Y^j=0$ for $0<j<n$. Newton identities, with $1,\ldots,n$ invertible, give
$$
 \det M_t=x^n+(-1)^{n-1}(y^n+z^n)+t^n(x+y+z)^n .
$$
For $t\neq0$ this is a sum of four powers with nonzero coefficients and independent triples of covectors. In the expansion of $\Phi_m$, every surviving assignment to its four slots uses all four distinct covectors, since each pair of slots appears in some determinant. All $24$ remaining terms coincide. In fact an adjacent interchange has sign in exactly the two faces containing that pair, and the others are swapped without a sign. Their product has sign $+1$. The $24$ terms are nonzero and do not cancel under the characteristic hypothesis. Therefore $Q(T_t)\neq0$ for all $t\neq0$. At $t=0$, $P(T_0)\neq0$ because $[D,S]=(\zeta-1)SD$ is invertible. As $P(T_t)$ is a polynomial of degree at most $3n$, some $t\neq0$ gives joint nonvanishing. This proves nonemptiness and density of the specified open subset. For algebraically closed fields of characteristic greater than $n$, the same argument gives the same reduction on this joint locus.

## Evaluation cost and scope

The first determinant is on a $3n$-by-$3n$ matrix. In characteristic zero, compute the dense coefficients of $D_T$ by interpolation on a grid of $(n+1)^3$ points or by a polynomial-time division-free determinant over $F[x,y,z]$. The bracket product is in twelve variables and has degree $n$ per three-variable block. Multiplying its $4m$ determinant factors and making the final coefficient contraction therefore take polynomially many arithmetic operations in $n$. There are $\binom{n+2}{2}^4$ possible final monomials and polynomially many intermediate ones. Over finite fields the theorem uses only $P$, with polynomial bit complexity for the standard explicit field representation. Over algebraically closed fields the arithmetic reduction uses only the input field operations. The existence of scalar corrections is a property of the field and does not require computing roots in the reduction.

Strassen's commutation method and the Koszul flattening used here are classical. The four-bracket formula specializes at $m=1$ to the classical symbolic formula of the Aronhold invariant. The calculation uses their determinant weights jointly to decide the extra volume constraint in generic exact isomorphism, including when the Strassen weight alone is divisible by three in characteristic zero. [Strassen, Rank and optimal computation of generic tensors](https://doi.org/10.1016/0024-3795(83)80041-X) · [Landsberg and Ottaviani, Equations for secant varieties of Veronese and other varieties](https://arxiv.org/abs/1111.4567) · [Dolgachev and Kanev, Polar covariants of plane cubics and quartics, §5.13](https://sites.lsa.umich.edu/idolga-new/wp-content/uploads/sites/1467/2024/08/advances93.pdf)

Chen, Grochow, Qiao, Tang and Zhang ask for the unrestricted comparison of ordinary and special-linear tensor isomorphism. The reduction above addresses the stated nonvanishing classes. The proof is in prose, with no Lean claim or independent literature-priority claim. [Chen, Grochow, Qiao, Tang and Zhang, Actions by Classical Groups, Question 1.9](https://arxiv.org/html/2306.03135#S1.SS5)
