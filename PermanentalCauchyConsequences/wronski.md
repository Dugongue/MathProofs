# Prescribed-column Cauchy counterexamples and an elliptic criterion for rational poles

## Main theorem

Let $n\ge2$ and let $b_1,\ldots,b_{2n-2}$ be distinct real numbers. There are distinct real numbers $a_1,\ldots,a_n$ disjoint from the $b_j$ such that the Cauchy matrix $C_{ij}=1/(b_j-a_i)$ has every square determinant nonzero and permanental rank exactly $n-1$. Thus the extremal counterexample to Yu's Conjecture A6.2 can realize **any** prescribed set of column parameters. Over a characteristic-zero field, all such row sets are classified by split members of pencils in one Wronski fiber. Over the complex numbers a generic prescribed column set has exactly $\frac1n\binom{2n-2}{n-1}$ pencils, and this count also holds for distinct real column sets, with pencils defined over the reals. The assertion about real poles is existence in at least one pencil. [Yu, A6.2](https://www.preprints.org/manuscript/202603.0035) · [Earlier extremal construction](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/complexity.md#permanental-rank) · [Eremenko–Gabrielov](https://annals.math.princeton.edu/2002/155-1/p02)

For $n=3$ with prescribed rational columns, rational row sets exist exactly when one of at most two explicitly defined elliptic curves over $\mathbb Q$ has positive Mordell–Weil rank. The columns $0,1,2,3$ admit real realizations and admit no rational Cauchy row set.

## 1. Borchardt and the exact pencil correspondence

Use the convention $W(U,V)=U'V-UV'$. Let $F=\prod_j(z-b_j)$ and $A=\prod_i(z-a_i)$ be monic. A linear dependence among the rows of $C^{\circ2}$ is equivalent to
$$
\sum_{i=1}^n c_i\prod_{k\ne i}(z-a_k)^2=\lambda F(z).
$$
Indeed the numerator on the left has degree at most $2n-2$ and vanishes at every $b_j$. Evaluation at the $a_i$ shows the numerator map is injective, so a nonzero dependence has $\lambda\ne0$. It is unique up to scale and each coefficient $c_i$ is nonzero since $F(a_i)\ne0$. Equivalently $F/A^2$ has double poles but all simple-pole coefficients zero. All square Cauchy determinants are nonzero, and Borchardt's identity equates their permanents with the corresponding determinants of $C^{\circ2}$ divided by their determinants. Thus the dependence is equivalent to vanishing of all maximal permanents, and rank $n-1$ of $C^{\circ2}$ shows that some order-$n-1$ permanent is nonzero. [Borchardt identity and the elementary proof](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/complexity.md#permanental-rank)

A rational function $F/A^2$ of this form is $\sum_i d_i/(z-a_i)^2$. It has a rational primitive $-\sum_i d_i/(z-a_i)=B/A$ with $\deg B\le n-1$, so $W(B,A)=F$. Conversely if $W(B,A)=F$ up to a nonzero constant, differentiation of $B/A$ gives no simple poles. Hence valid row sets are precisely the degree-$n$ squarefree split members of the two-dimensional subspaces $P\subset k[z]_{\le n}$ with projective Wronskian $[F]$. Such a pencil is unique for a row set. Any second primitive differs by a constant in characteristic zero. A full-degree squarefree member cannot share a root with $F$ in this setting. At a root $a$ of the member its Wronskian is the product of its nonzero derivative and the value of the other member, up to sign. A common zero of both pencil members would make the Wronskian divisible by $(z-a)^2$, which is excluded.

Over $\mathbb C$, each pencil with this squarefree $F$ has an open set of admissible members isomorphic to a projective line minus finitely many points. The polynomial with degree exactly $n$ exists because the Wronskian has degree $2n-2$, and squarefreeness fails only at the finite branch values of the associated rational map. The Wronski map on $\operatorname{Gr}(2,n+1)$ is the linear Plücker projection defined by the Wronskian coefficients. It has no base point in characteristic zero by the quotient derivative, and is finite because it pulls the hyperplane class back to the ample Plücker class. The generic fiber count is the Plücker degree, the Catalan number above. Eremenko and Gabrielov give that same number of distinct real pencils for every set of distinct real critical points. A real pencil can have nonreal fibers. The next argument directly builds one with a completely real regular fiber. [Eremenko–Gabrielov, rational functions and Catalan count](https://annals.math.princeton.edu/2002/155-1/p02)

## 2. Direct construction for arbitrary real columns

Order the $b_j$ increasingly and choose $n-1$ points $x_i$ in the disjoint intervals $(b_{2i-1},b_{2i})$. Maximize
$$
\Phi(x)=\frac{\prod_i |F(x_i)|}{\prod_{i<j}(x_i-x_j)^2}
$$
on the product of their closures. The denominator never vanishes because the closed intervals are disjoint. The function is positive in the interior and zero on the boundary, so a maximum is attained in the interior. At this point the logarithmic first derivatives give
$$
\frac{F'(x_i)}{F(x_i)}=2\sum_{j\ne i}\frac1{x_i-x_j}.
$$
For $D=\prod_i(z-x_i)$ the right side equals $D''(x_i)/D'(x_i)$. Expanding $F/D^2$ at $x_i$ shows its simple-pole coefficient is
$$
\frac{F'(x_i)D'(x_i)-F(x_i)D''(x_i)}{D'(x_i)^3}=0.
$$
It tends to one at infinity, so it is $1+\sum_i d_i/(z-x_i)^2$. Its rational primitive is $z-\sum_i d_i/(z-x_i)=U/D$ with $U$ monic of degree $n$. In particular $W(U,D)=F$.

For every sufficiently small nonzero real $\epsilon$, the member $D+\epsilon U$ has one simple real root near each $x_i$. This follows from persistence of simple real roots. The remaining root is real because a real polynomial has its nonreal roots in conjugate pairs. It lies outside every fixed bounded interval for small $\epsilon$, since the other roots already account for all roots of the limiting degree-$n-1$ polynomial. Equivalently, the coefficient of $z^{n-1}$ shows the sum of all $n$ roots is $-1/\epsilon$ plus a bounded quantity. Hence all roots are distinct and disjoint from the prescribed columns. The pencil correspondence gives the desired matrix.

## 3. Three rows over the rationals

Write $F=z^4+s_1z^3+s_2z^2+s_3z+s_4$ with distinct $b_j\in\mathbb Q$. Any pencil in the fiber has a unique normalized basis
$$
U=z^3+a z+b,\qquad V=z^2+c z+d .
$$
The highest degree in the pencil must be three and the degree of the line obtained by canceling it must be two, since the Wronskian has degree four. Monic normalization and deleting the degree-two term of $U$ gives the basis. Expanding its Wronskian gives
$$
 W(U,V)=z^4+2cz^3+(3d-a)z^2-2bz+(ad-bc).
$$
Thus $c=s_1/2$, $b=-s_3/2$, $a=3d-s_2$, and $d$ solves $3d^2-s_2d-(s_4+bc)=0$. Rational-pencil candidates are therefore parametrized by the rational square roots of
$$
\Delta=s_2^2+12s_4-3s_1s_3 .
$$
For the four columns $0,1,2,3$, $\Delta=13$ and no rational pencil exists. Any valid rational row set would recover a rational pencil by partial fractions, so no such row set exists.

For each rational pencil candidate, let $f=U/V$ as a map of projective lines and let $E_f$ be the smooth projective curve whose generic points order all three distinct preimages of a value of $f$. An explicit model is obtained by adjoining to $\mathbb Q(x)$ the square root of the discriminant in $z$ of
$$
\frac{U(z)V(x)-U(x)V(z)}{z-x}.
$$
Using homogeneous coordinates gives the same extension if one root is at infinity. The map $f$ has degree three, since a common root of $U,V$ would give a double root of $F$. Its four critical points are the four distinct rational roots of $F$, all with simple ramification. Their four branch values are rational and distinct, since a degree-three fiber cannot contain two double points. Over the algebraic closure, the connected degree-three cover has transitive monodromy containing a transposition and hence group $S_3$. The ordering curve is therefore geometrically connected with a degree-six Galois map to the target projective line. It is ramified over each of the four branch values with inertia of order two and has no other ramification. Riemann–Hurwitz gives $2g-2=-12+4\cdot3=0$.

There are three rational ordering-curve points above each branch value. In the corresponding cubic fiber the repeated point is rational and the remaining simple point is rational. The three limits choose the position of the simple point. Locally each limit normalizes to one ramified point. For example the quadratic residual extension over the simple point has, after dividing a square, an equation $y^2=u(x)(x-x_0)$ with $u(x_0)\ne0$, giving one rational point over $x_0$. The same argument in a local coordinate covers infinity. In particular the curve has a rational point. Choose as origin a branch point fixed by a selected transposition $s$. The involution $s$ is inversion on this elliptic curve. Its four fixed points, one above each branch value, are rational, giving the full rational two-torsion.

The order-three subgroup acts without fixed points, since all geometric inertia groups have order two. Any fixed-point-free elliptic automorphism is a translation. In fact if its origin-preserving part differs from the identity, that part minus the identity is a nonzero endomorphism and is surjective over the algebraic closure, giving a fixed point. Thus the three-cycle is translation by a rational point of order three. The orbit of the rational two-torsion under this translation consists of the twelve branch points. Mazur's theorem forces the rational torsion group to have exactly twelve elements, since it contains $\mathbb Z/2\times\mathbb Z/6$. Every rational point outside those twelve therefore has infinite order. If the rank is positive, there are infinitely many such points. Omit the finitely many lying over the value $f(\infty)$ to obtain three finite distinct rational poles for a pencil member. Conversely three such poles order to a rational point away from the branch values and give positive rank. This proves the claimed criterion. [Mazur, rational torsion theorem](https://www.numdam.org/item/PMIHES_1977__47__33_0/)

## 4. Exact finite-field count in size three

Over a finite field of characteristic greater than three with four fixed distinct column parameters, the same quadratic pencil equation and simply branched ordering curves apply. There are no Cauchy solutions if $\Delta$ is a nonsquare. For each rational pencil over the finite field, let $E_f$ denote its ordering curve. It has exactly twelve rational points over branch values, by the same local argument, and every completely split unramified fiber contributes exactly six rational points. One unramified fiber may have a point at infinity in the domain. This occurs among the counted split fibers exactly when the normalized $V$ has two distinct roots in the field. Put $\varepsilon_f=1$ in that case and $0$ otherwise. The exact number of unordered valid row sets is
$$
\sum_f \left(\frac{\# E_f(\mathbb F_q)-12}{6}-\varepsilon_f\right).
$$
The summation is over rational pencils, with one term per pencil by uniqueness. When $q\ge29$, the Hasse bound gives $\#E_f(\mathbb F_q)>18$, so every rational pencil supplies a completely split regular fiber with no pole at infinity. Thus for $q\ge29$ in this characteristic range the four columns are realizable if and only if $\Delta$ is a square, including zero. [Hasse bound for elliptic curves over finite fields](https://www.math.brown.edu/johsilve/Presentations/WyomingEllipticCurve.pdf)

## Verification and scope

The Wronski, real-existence, Mordell–Weil, and finite-field criteria have written proofs. The companion Lean file verifies the quintuple of cubic coefficient equations and the rational obstruction for the specified quartic at the scalar level. The elliptic criterion is an exact equivalence and does not assume a general effective algorithm for computing rational rank. The result concerns Cauchy-form counterexamples with prescribed nodes. Earlier work supplies the general width threshold and the classical Wronski fiber count.
