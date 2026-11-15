# Small Geometric IPS certificates from additive orbit elimination

**Theorem.** Let $F$ contain $\mathbb F_q$ and let $f=(f_1,\dots,f_m)$ be polynomials over $F$ in $x_1,\dots,x_n$. Suppose $f$ includes $x_i^q-x_i$ for each $i$, and write $u_i$ for those coordinates among the placeholder variables $y$. Suppose an Ideal Proof System refutation is supplied in the form
$$
 H(x,y)=h(\ell(x,y),y), \qquad \ell(x,y)=\sum_{i=1}^n a_i(y)x_i, \qquad \deg_T h(T,y)\le D.
$$
Thus $H(x,0)=0$ and $H(x,f(x))=1$ as formal identities. Given division-free circuits for $h$ and the $a_i$ of total size $s$, a Geometric IPS certificate $G(y)$ has a division-free circuit of size polynomial in $n,m,s,D,\log q$. The construction is uniform in these parameters and takes time polynomial in them in the arithmetic circuit model. It only introduces the field constants $0,1,-1$ and copies the original constants.

The certificate satisfies $G(0)=1$ and $G(f(x))=0$. This gives a sufficient condition for polynomial overhead in Grochow–Pitassi’s question on simulating IPS by Geometric IPS. In particular, the theorem applies to Boolean systems in characteristic two when the supplied proof has the indicated form. The affine-linear case $H(x,y)=a_0(y)+\sum_i a_i(y)x_i$ follows with $h(T,y)=a_0(y)+T$. [Definition C.1 and Open Question C.2 in Grochow–Pitassi’s preprint](https://arxiv.org/pdf/1404.3820) · [Journal version, Appendix B.2](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf)

## The additive orbit polynomial

Put $e=q^n$ and define
$$
 L_j(T)=\prod_{\alpha\in\mathbb F_q^j}\left(T-\sum_{i=1}^j\alpha_i a_i(y)\right).
$$
Then $L_0(T)=T$. If $L_j$ is a linear combination of the powers $T^{q^v}$, it is additive and $\mathbb F_q$-linear, so
$$
 L_{j+1}(T)
 =\prod_{\beta\in\mathbb F_q}\bigl(L_j(T)-\beta L_j(a_{j+1})\bigr)
 =L_j(T)^q-L_j(a_{j+1})^{q-1}L_j(T).
$$
Thus all $L_j$ have the indicated powers. The recurrence remains valid when the $a_i$ are dependent and orbit points are repeated. The coefficient circuits of $L_n(T)=\sum_{j=0}^n c_j(y)T^{q^j}$ follow from the recurrence with sharing. Evaluating a power $q^j$ or $q-1$ takes $O(j\log q+1)$ multiplication gates by repeated squaring. In particular there is no enumeration of $q^n$ roots. Note that $c_n=1$ and $L_n(a_i)=0$ for every $i$.

For each $i,j$ let $V_{ij}(y)=\sum_{0\le v<j}u_i^{q^v}$. Under $y=f(x)$ we have $x_i^{q^j}=x_i+V_{ij}(f(x))$ by Frobenius telescoping. Define
$$
 w(y)=\sum_{j=0}^n c_j(y)\sum_{i=1}^n a_i(y)^{q^j}V_{ij}(y).
$$
Expanding the $q^j$ powers now gives the formal identity
$$
 L_n(\ell(x,f(x)))=w(f(x)),
$$
where all linear $x_i$ terms cancel by $L_n(a_i)=0$. Also $w(0)=0$. The above circuits for $w$ have size polynomial in $s,n,\log q$.

For the affine-linear case, this already suffices. Take $G(y)=L_n(1-a_0(y))-w(y)$. When $y=f(x)$, the IPS identity gives $1-a_0(f(x))=\ell(x,f(x))$, so $G(f(x))=0$. When $y=0$, the IPS identity forces every $a_i(0)$ and $a_0(0)$ to be zero, hence $L_n(T)$ specializes to $T^e$ and $G(0)=1$.

## A resultant of a sparse reciprocal against a short polynomial

For $D=0$, take $G(y)=1-h(0,y)$ directly. Assume $D\ge1$. Define
$$
 b(y)=1-h(0,y),qquad
 Q(Z)=Z^D(1-h(1/Z,y)),qquad
 R(Z)=Z^e(L_n(1/Z)-w(y)).
$$
These are polynomials in $Z$, and the leading coefficient of $Q$ is $b$, with $b(0)=1$ because $\ell(0,y)=0$ and $H(0,0)=0$. The sparse polynomial $R$ has at most $n+2$ terms:
$$
 R(Z)=\sum_{j=0}^n c_j Z^{e-q^j}-w Z^e.
$$
Its constant term is one. To obtain the coefficients of $h$ from its circuit, evaluate the circuit with arrays of length $D+1$ over $F[y]$, adding componentwise and using convolution truncated above degree $D$. This computes all coefficients of the final $h$ even if individual gates have higher degree. The output is exact because the supplied final degree bound is $D$. This costs polynomially many gates in $s,D$.

Work over $F[y,b^{-1}]$. Let $M$ be the $D$-by-$D$ companion matrix for the monic polynomial $Q/b$, meaning the multiplication-by-$Z$ matrix in the basis $1,Z,\dots,Z^{D-1}$ of its quotient algebra. Compute
$$
 \det(R(M))=\frac{N(y)}{b(y)^K}.
$$
This serves as a resultant without a matrix of size $e$. Each exponent $e-q^j$ and $e$ has binary length $O(n\log q+1)$. Repeated squaring and ordinary matrix multiplication compute each power of $M$ in a polynomial number of arithmetic gates, and a division-free determinant circuit computes the determinant of the resulting $D$-by-$D$ matrix. [Berkowitz determinant algorithm](https://doi.org/10.1016/0020-0190(84)90018-8)

For a division-free circuit for the numerator $N$, represent each gate in the localized computation by a pair of polynomial circuits for numerator and denominator. Initialize companion entries with denominators $1$ or $b$. At addition use $(N_1D_2+N_2D_1,D_1D_2)$, and at multiplication use $(N_1N_2,D_1D_2)$. Subtraction is the addition formula with its second term negated. Reuse previously computed gates. Every denominator remains a power of $b$, and the size grows by only a constant factor in the number of arithmetic gates of the localized circuit. The large exponent $K$ need not be represented by an expanded polynomial or computed for the construction.

## Certificate identities

Set $G=bN$. If $b(f(x))$ vanishes as a formal polynomial, then $G(f(x))=0$ directly. Otherwise evaluate in the field of rational functions in $x$, so $b(f(x))$ is invertible. The original IPS identity makes $\ell(x,f(x))$ a root of $1-h(T,f(x))$. This root is nonzero since $b(f(x))\ne0$. The additive orbit identity also makes it a root of $L_n(T)-w(f(x))$. Its reciprocal is therefore a common root of $Q(Z)$ and $R(Z)$ after substitution. Evaluation at this root is a nonzero functional on the quotient algebra of $Q/b$ over the rational function field and annihilates the image of multiplication by $R$. Hence $R(M)$ is singular and $N(f(x))=0$. This case analysis proves the identity for the same fixed output circuit $G$, and the construction does not perform identity testing to select a case.

At $y=0$ we have $b=1$ and hence $N(0)=\det(R(M)|_{y=0})$. If every $a_i(0)=0$, the orbit polynomial at zero is $T^e$ and $R$ at zero is the constant one. Otherwise $\ell(x,0)$ is a nonzero linear polynomial. Substitution of such a polynomial into the univariate ring $F[T]$ is injective, so $h(\ell(x,0),0)=0$ forces $h(T,0)=0$. In this case $Q(Z)|_{y=0}=Z^D$, $M|_{y=0}$ is the nilpotent shift, and $R(M)|_{y=0}$ is triangular with diagonal one because $R$ has constant coefficient one. In either case $N(0)=1$, so $G(0)=1$.

## Scope and relation to prior work

The result concerns arithmetic circuit size, matching the definition of Geometric IPS. The degrees of the resulting polynomial can be exponential, so the construction makes no bounded-degree or bounded-depth assertion. Its hypothesis is on the supplied IPS certificate, and general IPS certificates need not come in the one-linear-form representation. The field equations in the input are used as coordinates of the output certificate. In characteristic two with $q=2$ these are precisely the usual Boolean equations.

The norm over additive conjugates is classical. The complexity statement uses the succinct linearized orbit polynomial together with the short reciprocal companion computation. Both identities are characteristic-independent within the stated finite-subfield hypothesis. A federated DAG search located the linearized and subspace polynomial constructions in the imported Cslib source. The proof here was checked informally. Publication priority remains unestablished. [Grochow–Kumar–Saks–Saraf on Geometric IPS and hitting sets](https://arxiv.org/html/1701.01717#S4.SS2) · [Andrews on Geometric IPS circuit bounds](https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.15/LIPIcs.CCC.2025.15.html)
