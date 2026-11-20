# Finite Lie exponent for the real special linear groups

**Theorem.** For every $n\ge3$ there are three closed Lie subgroups of $\mathrm{SL}(n,\mathbb R)$ with the triple product property and total dimension $3n(n-1)/2+n-2$. Hence the Lie exponent in Definition 4.1 satisfies

$$
\omega_{\mathrm{Lie}}(\mathrm{SL}(n,\mathbb R))\le \frac{3(n-1)}{n-2}<\infty.
$$

This resolves GP145 for every $n$ in its stated range. The source allows Lie submanifolds, and the construction gives Lie subgroups. This is a written proof. [Blasiak-Cohn-Grochow-Pratt-Umans, Definition 4.1 and Section 5](https://doi.org/10.4230/LIPIcs.ITCS.2023.19)

## The subgroups

Let $H_1=\mathrm{SO}(n)$, let $H_2$ be the upper unitriangular group, and put $p_k(B)=\prod_{i=1}^k B_{ii}$ for a lower triangular matrix $B$. Define

$$
H_3=\left\{B\in\mathrm{SL}(n,\mathbb R):
B\text{ lower triangular},\ B_{ii}>0,\ \prod_{k=1}^{n-1}p_k(B)=1\right\}.
$$

The prefixes $p_k$ are multiplicative, so $H_3$ is a subgroup. The $n-1$ real numbers $\log p_k$, for $1\le k<n$, are independent coordinates for the positive determinant-one diagonal because $\log B_{kk}=\log p_k-\log p_{k-1}$, with $p_0=p_n=1$. The product condition removes one diagonal dimension. If $N=\binom n2$, the subgroup dimensions are $N,N,N+n-2$. Each subgroup is closed in the ambient group. For $H_3$, an ambient limit is triangular and invertible, so none of its nonnegative diagonal entries can be zero.

## Triple product property

For subgroups each subgroup equals its quotient set. It suffices to show that $M A=B$ with $M\in H_1$, $A\in H_2$, $B\in H_3$ forces each matrix to be the identity. For $1\le k<n$, the wedge of the first $k$ columns of $A$ is $e_1\wedge\cdots\wedge e_k$. Orthogonality of $M$ gives

$$
\big\|Be_1\wedge\cdots\wedge Be_k\big\|=1.
$$

The coefficient on $e_1\wedge\cdots\wedge e_k$ is the leading principal minor $p_k(B)$, so $0<p_k(B)\le1$. Because the product of these prefixes is 1, each prefix is 1. The corresponding unit-norm wedge has all other coefficients zero. A nonzero decomposable wedge determines the span of its factors, so the first $k$ columns of $B$ span the first $k$ coordinate vectors. Consequently $B$ is upper as well as lower triangular. Its diagonal entries are 1, including the last by $\det B=1$. Thus $B=I$ and $M=A^{-1}$. An upper unitriangular orthogonal matrix is the identity, proving the property.

## Exponent

The Lie algebra has real dimension $n^2-1$ and Cartan subalgebra dimension $n-1$. Thus $(\dim G-r(G))/2=N$, while the average subgroup dimension is $N+(n-2)/3$. Substitution in Definition 4.1 gives the stated bound. At $n=3$ the allowed lower diagonal is $(a,a^{-2},a)$ with $a>0$, the dimensions are $3,3,4$, and the bound is 6.

The source's single-copy triple uses a lower unitriangular third subgroup and has denominator zero in Definition 4.1. Its direct-power construction couples diagonal entries across copies. The full sequence of exterior norms gives simultaneous inequalities within one copy, leaving one equation on the positive diagonal. [Blasiak-Cohn-Grochow-Pratt-Umans, Section 4.1 and Theorem 4.9](https://doi.org/10.4230/LIPIcs.ITCS.2023.19)

## Products and complex groups

For $G=\prod_j\mathrm{SL}(n_j,\mathbb R)$, let $R=\sum_j(n_j-1)>1$. Use the same first and second subgroups in each factor and impose one product equation across all prefixes in all factors of the third subgroup. Each prefix is at most 1 and their product is 1, so each prefix is 1. With $N=\sum_j\binom{n_j}{2}$, the dimension sum is $3N+R-1$, giving $\omega_{\mathrm{Lie}}(G)\le3R/(R-1)$. This covers powers of $\mathrm{SL}(2,\mathbb R)$ with at least two factors.

For $\mathrm{SL}(n,\mathbb C)$ viewed as a real Lie group, use $\mathrm{SU}(n)$, complex upper unitriangular matrices, and complex lower triangular matrices with positive real diagonal satisfying the same prefix-product equation. The Hermitian exterior norm gives the same triple product proof. The subgroup dimensions over $\mathbb R$ are $n^2-1$, $n(n-1)$, and $n(n-1)+n-2$. The Cartan dimension is $2(n-1)$ and $(\dim G-r(G))/2=n(n-1)$. Thus $\omega_{\mathrm{Lie}}(\mathrm{SL}(n,\mathbb C))\le6(n-1)/(2n-3)$ for $n\ge2$.

These bounds concern the Lie exponent. The relationship to the arithmetic exponent of matrix multiplication is the subject of a separate question in the source. [Question 4.2](https://doi.org/10.4230/LIPIcs.ITCS.2023.19)

## The remaining real rank-one case

For $\mathrm{SL}(2,\mathbb R)$ the Lie exponent is infinite even when arbitrary Lie submanifolds are allowed. The ambient dimension is 3 and the Cartan dimension is 1, so a qualifying triple would have dimension sum greater than 3. The pairwise dimension sums are at most 3 by the injectivity of $(x,y)\mapsto x^{-1}y$ on any pair of the submanifolds. Thus the only possible dimensions are $2,1,1$. Cyclically relabel the triple so the first two dimensions sum to 3. Fix $x_0$ and $y_0$ in those two submanifolds. By invariance of domain the injective map $(x,y)\mapsto x_0 x^{-1}y y_0^{-1}$ has open image containing the identity. This image is contained in the product of the first two quotient sets. The remaining positive-dimensional submanifold has quotient elements arbitrarily close to the identity and different from it. The inverse of any sufficiently close such element belongs to the open image, contradicting the triple product property. [Pairwise injectivity and the open-image argument, Proposition 4.3](https://doi.org/10.4230/LIPIcs.ITCS.2023.19)
