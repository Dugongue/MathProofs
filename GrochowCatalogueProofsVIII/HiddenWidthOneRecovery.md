# Deterministic hidden-coordinate recovery for width-one ROABPs

## GP-0690

Let $f\in\mathbb Q[x_1,\ldots,x_n]$ be given by exact rational evaluation access and an upper bound $D$ on its total degree. Suppose
$$
 f(x)=c\prod_{i=1}^n g_i(a_i^{\mathsf T}x+b_i),
$$
where $c\ne0$, the $a_i\in\mathbb Q^n$ are independent, $b_i\in\mathbb Q$, and every $g_i\in\mathbb Q[t]$ is nonconstant. There is a deterministic polynomial-bit algorithm recovering an invertible rational affine coordinate transformation and a width-one ROABP for $f$. It takes polynomially many oracle evaluations at polynomial-bit rational points. Its bit bound is polynomial in $n,D$ and the maximum coefficient bit length of $f$. This handles the concise affine width-one case without access to a decomposition, a variable order, or a factorization oracle for circuit polynomials. [Affine-orbit PIT context](https://arxiv.org/abs/2611.00634)

Let $L(x)$ be the matrix of second logarithmic derivatives of $f$, which is defined by rational functions wherever $f\ne0$:
$$
 L_{ij}(x)=\frac{f(x)\partial_i\partial_j f(x)-\partial_i f(x)\partial_j f(x)}{f(x)^2}.
$$
Put $A=[a_1\,\cdots\,a_n]$ and $h_i=(g_i g_i''-(g_i')^2)/g_i^2$. Differentiating the product yields $L(x)=A\operatorname{diag}(h_i(a_i^{\mathsf T}x+b_i))A^{\mathsf T}$. Each $h_i$ is nonzero and nonconstant: at infinity its leading Laurent term is $-\deg(g_i)/t^2$. Exact first and second partial derivatives at a point are computed by interpolating on coordinate lines and planes, using at most a polynomial number of values of degree-$\le D$ restrictions.

First choose a point $x_0$ where $f(x_0)\ne0$ and $L(x_0)$ is invertible. The moment curve $x=(t,t^2,\ldots,t^n)$ makes every affine linear form $a_i^{\mathsf T}x+b_i$ nonconstant. In particular the product of all denominators and all the nonzero numerators $g_i g_i''-(g_i')^2$, composed with this curve, is nonzero and has degree at most $3nD$. Testing $3nD+1$ integers therefore finds an $x_0$, by checking $f$ and the determinant of $L$ directly.

For each pair of distinct coordinate axes $e_j,e_k$, evaluate at the grid
$$
 x=x_0+u e_j+v e_k,\qquad 0\le u,v\le 6D.
$$
Discard points with $f(x)=0$ and collect the remaining matrices $M_x=L(x)L(x_0)^{-1}$. These commute, and in the $A$-basis their $i$th diagonal entry is $h_i(a_i^{\mathsf T}x+b_i)/h_i(a_i^{\mathsf T}x_0+b_i)$. For each $i\ne i'$, the two covectors $a_i,a_{i'}$ have a nonzero minor on some coordinate pair. On that coordinate plane the pair of their affine values ranges independently. Since the $h_i$ are nonconstant, the difference of these two diagonal entries is a nonzero rational function on the plane. Multiply its numerator by $f$ restricted to the plane, which is nonzero because the plane contains $x_0$. The result has degree at most $5D$, by using the explicit squared denominators from $g_i,g_{i'}$. A grid with more than $5D$ points in each coordinate therefore gives some retained point with distinct diagonal entries for this pair.

Number the collected matrices $M_1,\ldots,M_s$. In $M(t)=\sum_{j=1}^s t^{j-1}M_j$ the difference of each pair of diagonal entries is a nonzero polynomial of degree at most $s-1$. At most $\binom n2(s-1)$ integers can fail to give pairwise distinct entries. Test the characteristic polynomial for squarefreeness at the remaining integer candidates. Its roots are rational since $M(t)$ is diagonal in a rational basis. Deterministic rational univariate factorization and Gaussian elimination give the $n$ eigenlines, exactly the lines of the unknown $a_i$. For $n=1$, univariate interpolation alone suffices.

Choose rational representatives of the recovered covectors, form the invertible linear coordinate map with these as coordinate rows, and center it at $x_0$. In the resulting coordinates the polynomial is a product of univariate polynomials with nonzero constant terms. On each coordinate axis recover the normalized factor by interpolation of $f/f(x_0)$ with all other coordinates zero. Their product times $f(x_0)$ is exactly $f$. The matrices, grid points, interpolation systems, integer parameters in the pencil search, and intermediate rationals have polynomial bit length by the degree bound and the usual determinant bounds for linear algebra. The output is an explicit rational coordinate witness and a product of $n$ univariate layers.
