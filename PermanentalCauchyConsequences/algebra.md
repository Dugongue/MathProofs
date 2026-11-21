# Permanental rank of Cauchy matrices across characteristics

Let $K$ be a field. Take pairwise distinct row parameters $a_1,\ldots,a_n$ and pairwise distinct column parameters $b_1,\ldots,b_m$, with the two sets disjoint, and put $C_{ij}=(b_j-a_i)^{-1}$. Such a matrix is totally nonsingular, meaning every square submatrix is nonsingular. Write $r=\operatorname{prk}(C)$ for the largest order of a nonzero subpermanent. These results build on the $2n-2$-column construction in result #40. [Previous Cauchy construction](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/complexity.md#permanental-rank) · [Yu, Corollary A6.1 and Conjecture A6.2](https://www.preprints.org/manuscript/202603.0035)

## 1. A common kernel calculation

Borchardt's identity says $\det(T^{\circ2})=\det(T)\operatorname{per}(T)$ for every square Cauchy submatrix $T$, where the square on the left is entrywise. The identity holds over an arbitrary field as a rational-function identity. Total nonsingularity therefore gives $r=\operatorname{rank}(C^{\circ2})$. Let

$$
 A(z)=\prod_{i=1}^n(z-a_i),\qquad A_i(z)=A(z)/(z-a_i),\qquad F(z)=\prod_{j=1}^m(z-b_j).
$$

The left kernel of $C^{\circ2}$ is identified with the polynomials $P(z)=\sum_i c_i A_i(z)^2$ divisible by $F$, through the coefficient vector $(c_i)_i$. The map is injective by evaluation at the $a_i$'s. In particular $r=n$ when $m\ge 2n-1$ since $\deg P\le2n-2$. For $m\le2n-2$, set $\ell=2n-2-m$ and write $P=FH$. The kernel is isomorphic to the following space of dimension $n-r$:

$$
 \left\{H\in K[z]:\ \deg H\le\ell,\quad
 H'(a_i)=\left(2\frac{A_i'(a_i)}{A_i(a_i)}-\frac{F'(a_i)}{F(a_i)}\right)H(a_i)\ \text{for all }i\right\}. \tag{1}
$$

Indeed, the displayed equations say exactly that the coefficient of $(z-a_i)^{-1}$ in the partial fraction expansion of $FH/A^2$ vanishes at each pole. There is no polynomial part by degree. Thus the equations are sufficient as well as necessary for $FH/A^2$ to equal a sum of the double-pole terms $c_i/(z-a_i)^2$. [Borchardt identity and the preceding construction](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/complexity.md#permanental-rank)

## 2. A Wronskian bound in characteristic zero and large characteristic

**Theorem.** Suppose $m\le2n-2$ and the characteristic is zero or greater than $\ell=2n-2-m$. If the Cauchy matrix has permanental deficiency $\delta=n-r>0$, then

$$
 n(\delta-1)\le \delta(\ell-\delta+1),\qquad
 m\le r-1+\frac{n}{n-r}.
$$

In particular every square $n$-by-$n$ Cauchy matrix in these characteristics satisfies $r\ge n-\lfloor(\sqrt{4n+1}-1)/2\rfloor$.

Take the Wronskian of a basis $H_1,\ldots,H_\delta$ of (1), using derivatives of orders $0,\ldots,\delta-1$. It is nonzero. To see this, choose a basis of distinct degrees $d_j$ by elimination. The coefficient of its highest possible power is the product of leading coefficients times the determinant of the falling factorials of the $d_j$'s, a Vandermonde determinant. The hypothesis on the characteristic keeps the degrees distinct in $K$. Summing the degrees and subtracting $0+\cdots+(\delta-1)$ shows the Wronskian has degree at most $\delta(\ell-\delta+1)$.

At a pole $a_i$ change to a basis with distinct vanishing orders. Equation (1) forces every member vanishing there to have order at least two. The vanishing orders are therefore at least $0,2,3,\ldots,\delta$ if one member is nonzero there, and at least $2,3,\ldots,\delta+1$ otherwise. Each Wronskian determinant term has order at least the sum of these orders minus $0+\cdots+(\delta-1)$, hence at least $\delta-1$. The basis change scales the determinant by a nonzero constant. Its order at all $n$ distinct poles gives the first inequality. Rearrangement gives the second, and for $m=n$ it yields $\delta(\delta+1)\le n$. [Wronskian and vanishing orders](https://academic.oup.com/imrn/article/2024/17/12343/7725886)

## 3. Sharp width over cubic finite-field extensions

**Theorem.** For every odd prime power $n$, there exists a totally nonsingular $n$-by-$(2n-2)$ Cauchy matrix over $\mathbb F_{n^3}$ with permanental rank exactly $n-1$. Given an explicit finite-field presentation, one can construct it deterministically in polynomial time in $n$.

Choose $s\in\mathbb F_n$ outside the image of $x\mapsto x^3/(x^2-1)$ on $\mathbb F_n\setminus\{-1,1\}$. This is possible because there are only $n-2$ inputs, and $s\ne0$ since $0$ is attained. The polynomial $X^3-sX^2+s$ has no root in $\mathbb F_n$, including at $\pm1$, so it is irreducible. Take one root $t\in\mathbb F_{n^3}$ and put $\alpha=1+t$, $\beta=1-t$. The trace, second elementary symmetric sum and norm of $t$ are respectively $s,0,-s$. Consequently $\operatorname{Nm}(1+t)=\operatorname{Nm}(1-t)=1$. The two values are distinct and neither is zero or one. They have sum two and product different from one.

Use $A(z)=z^n-z$, with row poles the subfield $\mathbb F_n$, and $B(z)=z^{n-1}-\alpha\beta$. The derivative numerator of $B/A$ is

$$
 B'A-BA'=-(z^{n-1}-\alpha)(z^{n-1}-\beta).
$$

The image of $z\mapsto z^{n-1}$ on $\mathbb F_{n^3}^{\times}$ is exactly the norm-one subgroup by cyclicity and order. Therefore the displayed polynomial has $2n-2$ distinct roots in the field. None is a pole since $z^{n-1}=1$ on nonzero poles. Use these roots as column parameters. As the derivative of a rational function with only simple poles, $(B/A)'$ has only double-pole terms. The numerator consequently gives a nonzero left-kernel vector. Every left-kernel numerator has degree at most $2n-2$ and vanishes at those $2n-2$ roots, so it is a scalar multiple of this one. The kernel is one-dimensional. Enumerating $\mathbb F_n$ and $\mathbb F_{n^3}$ carries out all choices in polynomial time in $n$. One can also construct the extension with the irreducible cubic just found.

The quadratic extension cannot realize this particular binomial construction. In it, the conjugate of a norm-one element $\alpha$ is $\alpha^{-1}$. If $2-\alpha$ also has norm one, the equation $(2-\alpha)(2-\alpha^{-1})=1$ gives $\alpha+\alpha^{-1}=2$, hence $\alpha=1$. This restriction concerns the construction with $B=z^{n-1}-\alpha\beta$ and $A=z^n-z$.

## 4. Exact linear deficiency in every fixed odd characteristic

**Theorem.** Let $p$ be an odd prime and $n=p^k$ with $k\ge1$. Over an algebraically closed field of characteristic $p$ there is a totally nonsingular $n$-by-$(n+1)$ Cauchy matrix of permanental rank exactly $n-n/p$. Deleting any one of its columns gives a square Cauchy matrix of the same permanental rank. Thus the sublinear deficiency bound in §2 is specific to characteristic zero and the stated large-characteristic regime.

Again use row poles in $\mathbb F_n$, so $A=z^n-z$. Its derivative is constant, which implies $2A_i'(a_i)=A''(a_i)=0$ at every pole. Choose $d\in\mathbb F_n$ such that $-2d$ is a nonsquare and let

$$
 F=z^{n+1}-z^2/2+d.
$$

Here $F'=A$, and $F(a)=a^2/2+d\ne0$ for $a\in\mathbb F_n$. Consequently $F$ has $n+1$ distinct roots, all off the poles. Take these as column parameters. Equation (1) says $H'(a_i)=0$ for all poles, with $\deg H\le n-3$. Thus $H'=0$ identically by the degree bound. Conversely every polynomial in $z^p$ of degree at most $n-3$ satisfies (1). The kernel dimension is $\lfloor(n-3)/p\rfloor+1=n/p$.

If the column at $b$ is deleted, replace $F$ by $F_0=F/(z-b)$. The logarithmic derivative of $F_0$ at a pole is $-1/(a_i-b)$. Equation (1) now says that $(z-b)H'-H$ vanishes at the $n$ poles with $\deg H\le n-2$. Again the polynomial vanishes identically by its degree. Expanding about $b$ shows that the permitted exponents are precisely those congruent to $1\pmod p$. The space has dimension $\lfloor(n-3)/p\rfloor+1=n/p$ again.

There is also a finite splitting-field description. Choose $u$ satisfying $u^2=-2d$ in $\mathbb F_{n^2}$, so $u^n=-u$. Then the roots are exactly

$$
 z=u\frac{1+w}{1-w},\qquad w^{n+2}=1,\quad w\ne1.
$$

To check this, the fractional linear map $T(z)=(z-u)/(z+u)$ takes $(z+u^2/z)/2$ to $T(z)^2$, while $T(z^n)=T(z)^{-n}$. Thus each of the stated $z$'s satisfies $z^n=(z+u^2/z)/2$. Their denominators are nonzero, none is zero since $n+2$ is odd, and they provide $n+1$ distinct roots of $F$. In particular an extension of degree $\operatorname{lcm}(2,\operatorname{ord}_{n+2}(n))$ over $\mathbb F_n$ contains all the roots.

These are paper proofs. The bounds and constructions are for Cauchy matrices.
