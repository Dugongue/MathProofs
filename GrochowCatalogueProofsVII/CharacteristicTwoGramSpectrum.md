# Squarefree spectrum of a rectangular dot-product Gram in characteristic two

## GP-0166

Let $q$ be even, $n\ge2$, and $M$ uniform in $\mathbb F_q^{n\times d}$. Write $S=MM^{\mathsf T}$. The following gives the exact probability that the characteristic polynomial of $S$ is squarefree, for every $n,d,q$. Thus the spectral claim concerns the actual rectangular Gram, with the standard nonalternating dot product on its width. [Odd-characteristic Gram comparison, Section 5](https://arxiv.org/html/2604.00591v2#S5)

Put $o_0=1$ and, for $j\ge1$, let
$$
 o_j=q^{j(j-1)/2}\prod_{\ell=1}^{\lfloor(j-1)/2\rfloor}(1-q^{-2\ell}).
$$
This is the order of the bilinear isometry group of the standard nonalternating dot product. Let $s_j=|\mathrm{Sp}_j(q)|$ for even $j\ge0$, with $s_0=1$. Define $A_j=(q-1)(q^j-(-1)^j)/(q+1)$ for $j\ge1$ and $A_0=1$. For $k\in\{0,1\}$ put $p_k=0$ when $d<n-k$. Otherwise set $t=d-(n-k)$ and
$$
 p_k=q^{-nd}o_d
 \left(
  {\boldsymbol 1}_{t\text{ even}}\frac{q^{tk}}{s_t}
  +{\boldsymbol 1}_{t\ge1}\frac{q^{(t-1)k}}{o_t}
 \right),
$$
where absent terms are omitted. The desired probability is
$$
 o_n\bigl(A_n p_0+A_{n-1}p_1\bigr).
$$
All squarefree monic polynomials of degree $n$ with nonzero constant term have probability $o_n p_0$ individually. Those with constant term zero have probability $o_n p_1$ individually. No such polynomial occurs when $d<n-1$.

### Self-adjoint matrices with a prescribed squarefree polynomial

Every nondegenerate nonalternating symmetric bilinear form over $\mathbb F_q$ is isometric to the standard dot product. Indeed split off scaled norm-one lines until the complement is alternating. Every alternating hyperbolic plane with one norm-one line is isometric to three orthogonal norm-one lines: for the coordinates with bilinear pairing $aa'+bc'+cb'$, the vectors $(1,1,0),(1,0,1),(1,1,1)$ give such a basis. Repeating absorbs the alternating complement. The alternating case has its usual single symplectic isometry type in each even dimension.

For the group order, the unique vector $w$ satisfying $B(x,x)=B(x,w)^2$ is fixed by every isometry. For the dot product it is the all-ones vector. When $j$ is odd, $w$ has norm one and its perpendicular is alternating and nondegenerate. The group is exactly $\mathrm{Sp}_{j-1}(q)$. When $j$ is even, take $z$ with $B(w,z)=1$, and take the alternating nondegenerate complement $U$ of the span of $w,z$. Every isometry fixes $w$, sends $z$ to $z+u+c w$ with arbitrary $u\in U,c\in\mathbb F_q$, and sends $x\in U$ to $Hx+B(u,Hx)w$ for an arbitrary symplectic $H$ on $U$. The form identities force these expressions and show that all choices work. This gives $q^{j-1}|\mathrm{Sp}_{j-2}(q)|$. The displayed order follows by the formula $|\mathrm{Sp}_{2h}(q)|=q^{h^2}\prod_{\ell=1}^h(q^{2\ell}-1)$.

For a monic squarefree polynomial $f=\prod_i f_i$ of degree $n$, the matrices with polynomial $f$ form one linear conjugacy class, with centralizer order $\prod_i(q^{\deg f_i}-1)$. Fix one such operator. Its invariant primary spaces are the fields $K_i=\mathbb F_q[x]/(f_i)$, with the operator acting as multiplication by $x$. A symmetric nondegenerate bilinear form making it self-adjoint pairs different primary spaces orthogonally. On $K_i$ it must be $(a,b)\mapsto\operatorname{Tr}_{K_i/\mathbb F_q}(c_iab)$ for some $c_i\ne0$, because adjointness extends to all multiplication maps, and the trace pairing is nondegenerate. Each of these forms is nonalternating: squaring is bijective and the trace functional with $c_i\ne0$ is nonzero. Consequently the number of compatible nondegenerate forms is exactly the centralizer order, and all are of the dot-product type. Double-count the compatible operator-form pairs and divide by the $\mathrm{GL}_n$-orbit size of the dot product. This gives exactly $o_n$ symmetric matrices with each $f$.

For each of these symmetric matrices, its own, possibly degenerate bilinear form equals $(a,b)\mapsto B(a,Sb)$ for the fixed standard dot product $B$. On the primary factor $f_i$ this multiplies $c_i$ by the image of $x$. Hence the rank is $n-k$, with $k=1$ exactly when $x\mid f$, and its nondegenerate part is nonalternating since $n\ge2$. Thus only one Gram point probability for each $k$ has to be counted.

### The point probability for the actual Gram

A matrix producing this prescribed Gram is a linear map of the $n$-dimensional form space into the standard nonalternating $d$-space, pulling back the form. The nondegenerate quotient of the domain form can be realized as any nondegenerate complement to its radical. Its image is an isometrically embedded nonalternating $(n-k)$-space. The perpendicular complement of its image has dimension $t$ and is either alternating (possible exactly for even $t$, including zero) or nonalternating (possible exactly for positive $t$). Both possibilities exist when their dimensions permit them because their sum with the prescribed nonalternating part is of the standard dot-product type. For each complement type the ambient group acts transitively on the embeddings of the fixed nondegenerate domain part: extend an isometry between the embedded parts by one between their complements. The pointwise stabilizer of an embedding is the isometry group of the complement. This gives the two ratios involving $o_d$ in the formula.

The radical has dimension $k\in\{0,1\}$, so when $k=1$ its basis vector can go to any vector of norm zero in that complement. This gives $q^t$ choices if the complement is alternating, and $q^{t-1}$ if it is nonalternating, since in the latter case norm zero is a hyperplane. The count is one for $k=0$. Multiplying and dividing by $q^{nd}$ yields $p_k$. The number of monic squarefree degree-$n$ polynomials is $q^n-q^{n-1}$ for $n\ge2$, as follows by separating the square part of every monic polynomial in the generating function. The count with zero constant term equals the count $A_{n-1}$ with nonzero constant term in degree $n-1$. Starting with $A_1=q-1$ gives the displayed formula for $A_j$ by subtraction and induction. This completes the exact probability calculation.

### Uniform control when the width grows

For completeness the full Gram law has a simple second-moment formula. Index its additive characters by the coefficients of quadratic forms $Q$ on $\mathbb F_q^n$, using the independent upper-triangle entries of a symmetric matrix. On a single column $x$ such a character is $\psi(Q(x))$. If the polar form has rank $2r$, its mean squared magnitude is $q^{-2r}$ when $Q$ vanishes on the polar radical, and zero otherwise. This follows by differencing the square of the sum: averaging in the original variable kills all shifts outside the polar radical. On the radical the quadratic is a square of a linear functional, whose character averages to zero unless it vanishes. For each polar form of rank $2r$ there are exactly $q^{2r}$ quadratic refinements vanishing on its radical, because any two refinements differ by the square of a linear form, and restriction to the radical is onto. Let $C_{2r}$ count alternating forms of rank $2r$ on the $n$-space. Plancherel therefore gives
$$
 \chi^2(\mathcal L(S)\Vert\mathrm{Unif}(\mathrm{Sym}_n(q)))
 = \sum_{r\ge1} C_{2r}q^{2r-2dr}.
$$
Bounding $C_{2r}$ by choosing a radical and then an arbitrary alternating form on its quotient gives $C_{2r}\le Cq^{2nr-2r^2-r}$ for an absolute constant $C$. For $d=n+c$ with $c\ge0$, the total variation distance is consequently at most $C' q^{-c-1/2}$. In the uniform matrix model the squarefree probability is exactly $(1-q^{-1})\prod_{\ell=1}^{\lfloor(n-1)/2\rfloor}(1-q^{-2\ell})$ by the count above. Thus when $q$ is fixed and $d-n\to\infty$, the actual Gram has limit $(1-q^{-1})\prod_{\ell\ge1}(1-q^{-2\ell})$. The exact point-count formula covers bounded differences and the deficient widths as well.
