# A quintic upper bound for arbitrary dense conjugacy in characteristic zero

For any field of characteristic zero and any nonconjugate matrices $A,B$ of side $n$, ordinary Polynomial Calculus on the original entrywise equations $H=XA-BX=0$, $XY=YX=I$ has a refutation of degree at most three with $O(n^5\log(2n))$ monomial occurrences. The coefficient field may be nonalgebraically closed and the displayed coordinates are arbitrary. The same conclusion holds in positive characteristic whenever either an exact Jordan type is present on just one side or one of its two multiplicity counts differs in the field. In particular it applies unconditionally when the characteristic is greater than $n$. [Question and equations](https://arxiv.org/html/2305.19320#S7.SS3)

## One round of reverse linear equations

Derive $G=AY-YB$ entrywise from
$$
 G=Y H Y+(I-YX)AY+YB(XY-I).
$$
For a fixed entry this uses $O(n^2)$ terms. A term in the first matrix is a double single-variable multiple of one $H$ entry of sparsity at most $2n$. A term in each of the other matrices is a scalar-weighted single-variable multiple of one inverse entry of sparsity at most $n+1$. The intermediate lines at individual multiplications have $O(n)$ terms. Binary balanced summation gives $O(n^3\log(2n))$ per reverse entry, hence $O(n^5\log(2n))$ for all of them. Their final actual degree is one, and their sparse size per entry is at most $2n$.

## A bilinear certificate after that round

Pass temporarily to a splitting field. For a mismatched Jordan type consisting of eigenvalue $\lambda$ and length $\ell$, the functor on matrix modules
$$
 W(M)=\ker(M-\lambda I)^\ell/
 \bigl(\ker(M-\lambda I)^{\ell-1}+(M-\lambda I)\ker(M-\lambda I)^{\ell+1}\bigr)
$$
takes one dimension from each Jordan block of exactly that type. On a Jordan chain this is a direct calculation. It respects all intertwiners, identities and composition. Write $a=\dim W(A)$ and $b=\dim W(B)$. When $a-b$ is nonzero in the field let $\phi_A$ and $\phi_B$ be trace after this functor on the corresponding endomorphism spaces. For every pair of intertwiners $X:A\to B$, $Y:B\to A$,
$$
 \phi_A(YX)-\phi_B(XY)=0,\qquad \phi_A(I)-\phi_B(I)=a-b\ne0 .
$$
This is the ordinary rectangular trace identity. If $a=0<b$ and $b$ vanishes in the field, instead take $\phi_A=0$ and take one diagonal coordinate of the induced endomorphism on $W(B)$. Every $XY$ factors through a zero-dimensional space there and the identity has coordinate one. The reverse case is identical after exchanging the two sides.

Extend these two linear functionals arbitrarily to the two full matrix spaces. The bilinear form $\phi_A(YX)-\phi_B(XY)$ vanishes on the product of the two linear intertwiner spaces. Every such form is in the sum of the subspace spanned by products $(\text{one }Y\text{ variable}) H_{ij}$ and the subspace spanned by products $(\text{one }X\text{ variable}) G_{ij}$. Indeed the entries of $H$ span the annihilator of the first intertwiner space, and those of $G$ span the annihilator of the second. In bases adapted to the two kernels, the block on their product is zero and every other term uses at least one annihilator coordinate. Expanding these coordinates proves the assertion. Subtract $\phi_A(YX-I)-\phi_B(XY-I)$ and normalize the nonzero constant difference. We have shown that one is in the linear span of at most $2n^4+2n^2$ specified input or prepared polynomials: the two inverse families and the displayed products of one variable with $H$ or $G$.

This last span is specified by coefficient vectors over the original field, so solvability descends by linear algebra. No large extension representation is charged to the sparse proof. Generate the needed variable multiples of the original or already prepared linear lines, each of sparsity $O(n)$, and balance the sum of their scalar multiples. This costs $O(n^5\log(2n))$ including intermediate expanded lines. The preparation used degree three and the final stage uses degree at most two. The arguments give an explicit universal size bound and leave its optimal worst-case exponent unresolved.
