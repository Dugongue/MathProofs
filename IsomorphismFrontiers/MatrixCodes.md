# Matrix-code conjugacy in polynomial time on a constant fraction of inputs

Li, Li, Qiao, Tao, and Wang ask for a polynomial-time matrix-code conjugacy test that works on a $1/\Theta(q)$ fraction of first tensors of shape $n\times n\times m$ for arbitrary $m$. The question is Problem 1.5 in the first version and Problem 1.6 in the second. The algorithm below works on a positive absolute constant fraction, uniformly in $n,m,q$. It compares each good first tensor against every second tensor. The proof is informal. [Published question, version 2, §1.5](https://arxiv.org/html/2604.00591v2#S1.SS5)

Let $k=\mathbb F_q$, set $N=n^2$, and view the slices of each input as generators of a subspace $C\subseteq M_n(k)$. Two tensors are equivalent under simultaneous conjugation on the matrices and arbitrary invertible change of the slice coordinates precisely when their generated matrix subspaces are conjugate. In fact two surjections $k^m\to C$ can be aligned by an invertible map on $k^m$, by choosing bases of their kernels and complementary subspaces.

**Theorem.** There is a deterministic algorithm of bit time polynomial in $n,m,\log q$, with outcomes yes, no, or failure. Every yes and no answer is correct. For every $n,m$ and every supplied finite field $k$, there is a set of first tensors of uniform density at least an absolute constant $c>0$ on which the algorithm returns yes or no against every second tensor. The density is at least $1-O(1/q)$ with an absolute implied constant.

## Extracting two matrices

Use the symmetric nondegenerate pairing $\langle X,Y\rangle=\operatorname{Tr}(XY)$ on $M_n(k)$, and let $\pi_C$ be orthogonal projection to a subspace $C$ on which this pairing is nondegenerate. This projection is computed by solving the Gram system in any basis. Define the ordered pair
$$
                   A=\pi_C(I),\qquad B=\pi_C(A^2).
$$
Conjugation commutes with these constructions. The algorithm returns failure if the first code is degenerate or the simultaneous centralizer of $A,B$ has dimension greater than one. For a first code passing both tests, compare the rank and nondegeneracy of the second code and extract its pair $A',B'$. A rank or nondegeneracy mismatch certifies nonconjugacy. Solve
$$
                 XA=A'X,\qquad XB=B'X .
$$
If there is an invertible solution $X_0$, the entire solution space is $X_0$ times the common centralizer of $A,B$, so it is one-dimensional. Thus a space of any other dimension, or a singular generator of a one-dimensional space, certifies nonconjugacy. If a generator is invertible, verify directly whether it conjugates the two codes. All nonzero solutions then differ by a scalar and induce the same conjugation, which proves the decision is exact.

Replacing both codes by their trace orthogonal complements preserves conjugacy and sends a uniform $d$-subspace to a uniform $(N-d)$-subspace. It suffices to count good $d$-subspaces for $2\le d\le N/2$ and $n\ge 10$. The remaining cases are dealt with below.

## Counting possible first matrices

Write $e=I$. A useful matrix $A$ is cyclic, meaning its minimal polynomial has degree $n$, and satisfies
$$
          \langle A,A\rangle=\langle A,e\rangle .
$$
We impose one additional condition according to the characteristic and $d$:

- In odd characteristic require $\operatorname{Tr} A\ne0$.
- In characteristic two and even $d$, require $\operatorname{Tr} A=0$ and $\operatorname{Tr}(A^3)\ne0$.
- In characteristic two and odd $d$, require $\operatorname{Tr} A=1$.

There are $\Omega(q^{N-1})$ such $A$ in each case, with an absolute implied constant. To count them, take one companion matrix for each monic degree-$n$ polynomial satisfying the conditions and take its full conjugacy class. For a cyclic companion at most $q^n$ invertible matrices commute with it, since its centralizer algebra is $k[A]$. Also $|\operatorname{GL}_n(k)|=q^N\prod_{i=1}^n(1-q^{-i})\ge c_1q^N$ for an absolute constant $c_1>0$.

For a monic polynomial with first coefficients $c_1,c_2,c_3$ after its leading term, Newton identities give $\operatorname{Tr} A=-c_1$ and $\operatorname{Tr}(A^2)=c_1^2-2c_2$. In odd characteristic each nonzero trace fixes exactly one choice of $c_2$, while all remaining coefficients are free. This gives $(q-1)q^{n-2}$ polynomials. In characteristic two $\operatorname{Tr}(A^2)=(\operatorname{Tr} A)^2$. For trace zero the third Newton identity gives $\operatorname{Tr}(A^3)=c_3$, so there are again $(q-1)q^{n-2}$ choices. For trace one all coefficients except $c_1$ are free, giving $q^{n-1}$. Distinct polynomials give disjoint conjugacy classes. The stated count follows.

## Counting possible second matrices

Fix one of these $A$. Put $r_1=e-A$, $r_2=A^2-B$, $W=\langle A,B\rangle_k$, and $R=\langle r_1,r_2\rangle_k$. To ensure $W\perp R$, the three conditions on $B$ are
$$
\langle B,e-A\rangle=0,\qquad
\langle B,A\rangle=\operatorname{Tr}(A^3),\qquad
\langle B,B\rangle=\langle B,A^2\rangle.
$$
Exclude $B\in\langle e,A,A^2\rangle_k$. This makes $W+R$ four-dimensional because $e,A,A^2$ are independent. It also excludes $A^2$ and the other cases where the projection constraints describe a degenerate choice of anchors.

In odd characteristic write $t=\operatorname{Tr} A\ne0$ and $u=\operatorname{Tr}(A^3)$. Impose $\langle B,A^2\rangle=z$ for any $z\ne u^2/t$. The first two conditions and this one define an affine space of dimension $N-3$, because $e,A,A^2$ are independent and the trace pairing is nondegenerate. On its space of differences the trace pairing has radical dimension at most three, by the codimension bound for orthogonal spaces. Hence the quadratic polynomial $\langle B,B\rangle-z$ restricted to this affine space has quadratic part of rank at least $N-6$.

Its quadratic part has a hyperbolic plane. Indeed in an odd-order finite field, any nonsingular ternary diagonal form $a x^2+b y^2+c z^2$ is isotropic, because for $z=1$ the sets of values $a x^2$ and $-c-b y^2$ have sizes $(q+1)/2$ and intersect. From a nonzero isotropic vector in the nondegenerate part, choose a partner with nonzero pairing and make it isotropic by adding a multiple of the first vector. This gives a hyperbolic plane. After fixing all remaining coordinates and translating the two plane coordinates, the equation reduces to $xy=v$ for some $v\in k$, with at least $q-1$ solutions. Thus each allowed $z$ admits at least $(q-1)q^{N-5}$ matrices $B$. Summing over $z$ gives $\Omega(q^{N-3})$ before the exclusions. The Gram determinant on $W$ is $tz-u^2\ne0$.

In characteristic two the first two conditions imply $\operatorname{Tr} B=\operatorname{Tr}(BA)=u$, so $\langle B,B\rangle=u^2$. Thus the last condition is the linear constraint $\langle B,A^2\rangle=u^2$. The three linear constraints are independent and give $q^{N-3}$ candidates. For even $d$ the Gram determinant on $W$ is $-u^2\ne0$, because $\operatorname{Tr} A=0$ and $u\ne0$. For odd $d$ use the norm-one line of $A$ in the completion count below.

We also exclude $B$ with nonscalar joint centralizer. For any nonscalar $T\in M_n(k)$, its centralizer dimension is at most $(n-1)^2+1=N-2n+2$. To see this, extend scalars to an algebraic closure, which preserves the dimension of the kernel of the commutation equations. If $T$ has distinct eigenvalues, the centralizer dimension is at most the sum of the squares of the primary-component dimensions. If there is only one eigenvalue, its Jordan blocks give dimension $\sum_j h_j^2$, where $h_j$ is the number of blocks of size at least $j$. This formula follows by summing $\min(a,b)$ for maps intertwining blocks of sizes $a,b$. In either case the numbers being squared are nonnegative, sum to $n$, and the largest is at most $n-1$, giving the bound. Since the centralizer algebra of cyclic $A$ has $q^n$ elements, at most $q^{N-n+2}$ matrices $B$ commute with a nonscalar matrix that commutes with $A$. Subtracting these matrices and the at most $q^3$ elements of $\langle e,A,A^2\rangle_k$ leaves $\Omega(q^{N-3})$ candidates in every case, uniformly for $n\ge 10$. For example the odd-characteristic count before subtraction is at least $(1-1/q)^2 q^{N-3}$.

## Counting codes through the pair

We use two elementary counts for a formed space $U$ of dimension $s$ whose radical has dimension $a$. For a symmetric form in odd characteristic, the number of nondegenerate $t$-subspaces is $\Omega(q^{t(s-t)})$ whenever $t\le s-a$. For an alternating form the same bound holds for even $t\le s-a$. To see the nondegenerate case, choose one $t$-subspace with nondegenerate restriction by taking part of an orthogonal or symplectic basis. The orbit under the ambient isometry group has size equal to its order divided by the product of the two isometry-group orders of that subspace and its orthogonal complement. For odd-characteristic symmetric spaces of dimension $j$, these orders are within absolute constant factors of $q^{j(j-1)/2}$. For alternating spaces of even dimension $j$ they are within absolute constant factors of $q^{j(j+1)/2}$. Both estimates follow from the classical order formulas and the uniformly bounded products $\prod_{i\ge1}(1-q^{-2i})$. The order quotient gives the stated exponent. To include a radical, pass to the nondegenerate quotient and lift each of its nondegenerate $t$-subspaces as the graphs of all $q^{at}$ linear maps to the radical. [Classical subspace counts and group order formulas](https://arxiv.org/abs/2109.10015)

In the alternating case with $2\le t\le s-a$, the number of such subspaces containing a fixed line outside the radical is $\Omega(q^{(t-1)(s-t)})$. In the nondegenerate quotient the symplectic group is transitive on lines. By counting incidences between nondegenerate $t$-subspaces and lines, a fraction $(q^t-1)/(q^{s-a}-1)$ of the nondegenerate subspaces contain the image of the fixed line. The graph maps must lift that line to the specified line and are free on the other $t-1$ basis elements, giving $q^{a(t-1)}$ lifts. Multiplying these factors proves the bound.

Fix a pair from the preceding two sections. In odd characteristic or characteristic two and even $d$, the plane $W$ is nondegenerate. Let $U=W^\perp\cap R^\perp$. The ambient space $W^\perp$ is nondegenerate, $R\subset W^\perp$ has dimension two, and hence $U$ has dimension $N-4$ and radical dimension at most two. In characteristic two, $U$ is alternating because for $Y\in U$,
$$
\langle Y,Y\rangle=(\operatorname{Tr}Y)^2=\langle e,Y\rangle^2=0,
$$
where $e=A+r_1$. For every nondegenerate $(d-2)$-subspace $U_1\subset U$, use $C=W\perp U_1$. The dimension bound $d\le N/2$ and $n\ge10$ ensure $d-2\le \dim U-\dim\operatorname{rad}U$, and $d-2$ is even when $U$ is alternating. This gives $\Omega(q^{(d-2)(N-d-2)})$ choices of $C$.

In characteristic two and odd $d$, we have $\langle A,A\rangle=1$. Define $B_0=B-(\operatorname{Tr}B)A$ and let $U=A^\perp\cap R^\perp$. The ambient space $A^\perp$ is nondegenerate and contains $R$. Thus $U$ has dimension $N-3$, radical dimension at most two, and is alternating since $e=A+r_1$. The matrix $B_0$ lies in $U$. It is nonzero and outside $\operatorname{rad}U=U\cap R$, by the independence of $e,A,A^2,B$. Take any nondegenerate $(d-1)$-subspace $U_1\subset U$ through its line and put $C=\langle A\rangle\perp U_1$. Here $d-1$ is even and at most $\dim U-\dim\operatorname{rad}U$. The line-count exponent is $(d-2)((N-3)-(d-1))=(d-2)(N-d-2)$, giving again $\Omega(q^{(d-2)(N-d-2)})$ choices.

In both cases the constructed code is nondegenerate, contains $A,B$, and is orthogonal to $r_1,r_2$. These are exactly the conditions that $A=\pi_C(e)$ and $B=\pi_C(A^2)$. They also imply that a particular code is counted for only one ordered pair, since the projections are unique. The three counts therefore multiply. The result is at least
$$
c_2q^{N-1}q^{N-3}q^{(d-2)(N-d-2)}
                      =c_2q^{d(N-d)}
$$
good $d$-subspaces for some absolute $c_2>0$. The total number of $d$-subspaces is the Gaussian binomial ${N\brack d}_q\le c_3q^{d(N-d)}$ with an absolute $c_3$, by the same uniformly bounded product as for $\operatorname{GL}_n(k)$. Hence each of these dimensions has a positive absolute constant fraction of good codes.

The counts also give density at least $1-O(1/q)$ uniformly as $q$ grows. The explicit product for $\operatorname{GL}_n(k)$ and the polynomial counts give at least $(1-O(1/q))q^{N-1}$ first matrices. The second-matrix counts and subtracted terms give at least $(1-O(1/q))q^{N-3}$ second matrices per first matrix. To sharpen the completion count in odd characteristic, use both possible discriminants of a nondegenerate $t$-subspace in the nondegenerate quotient of $U$, when both the subspace and its complement have positive dimension. Both equip $U/\operatorname{rad}U$ with an orthogonal direct sum of the ambient discriminant, so both occur by classification of finite-field quadratic forms. Each of these two orbits has size $\tfrac12(1+O(1/q))q^{t(s-a-t)}$, since an orthogonal group in positive dimension $j$ has order $2(1+O(1/q))q^{j(j-1)/2}$. When either dimension is zero the count is exact. In the alternating case the symplectic orders instead give $(1+O(1/q^2))q^{t(s-a-t)}$ from the single orbit. Conditioning on the line contributes a ratio $(1-q^{-t})/(1-q^{-(s-a)})=1+O(1/q^2)$ after extracting its power of $q$, because $t\ge2$. The graph lifts preserve all these relative estimates. Thus the product counting good codes is at least $(1-O(1/q))q^{d(N-d)}$. The Gaussian binomial is at most $(1+O(1/q))q^{d(N-d)}$, proving the strengthened density.

## Remaining dimensions and bit time

Dimension zero and the full ambient dimension are immediate. In dimension one compare nonzero generators $A_0,B_0$ by asking whether $A_0$ is similar to $\lambda B_0$ for some $\lambda\in k^\times$. Compute both ordered lists of monic invariant factors of $tI-A_0$ and $tI-B_0$. Rational canonical form is computable in deterministic polynomial time over an explicitly presented finite field. The invariant factor $f(t)$ of $B_0$ of degree $j$ becomes $\lambda^j f(t/\lambda)$ for $\lambda B_0$. Compare the degrees and all coefficient equalities in the corresponding factors. They produce a list of univariate equations in $\lambda$ of degree at most $n$. Take their polynomial greatest common divisor, ignoring identically zero equations. If no equations remain any nonzero $\lambda$ works. Otherwise take the greatest common divisor with $z^q-z$ by modular repeated squaring, remove the possible factor $z$, and test whether the result has positive degree. This decides the existence of $\lambda$ without factoring or enumerating the field. Orthogonal complements also handle codimension one. [Storjohann, *Deterministic Computation of the Frobenius Form*](https://doi.org/10.1109/SFCS.2001.959911)

For $n<10$, use a fixed-size system of polynomial equations for conjugacy. After computing bases of the two codes and comparing their dimensions, a matrix $X$ is required to satisfy $XA_i=\sum_j u_{ij}B_jX$ for each matrix of a basis, along with $v\det X=1$. Equal dimensions and invertible $X$ make inclusion equivalent to equality, so no invertibility equation is needed for the coefficient array $u$. There are at most $N$ basis vectors and $n<10$, so the equation count, variable count and degrees are bounded by absolute constants. Kayal's deterministic finite-field solvability theorem for a fixed number of variables decides existence in polynomial bit time in $\log q$. [Kayal, dissertation, Theorem 6.1.1](https://eccc.weizmann.ac.il/resources/pdf/kayal.pdf)

For a uniform tensor $n\times n\times m$, the $m$ independent uniform slices span a subspace of dimension $\min(m,N)$ with probability at least $\prod_{i\ge1}(1-q^{-i})$. This is bounded below by an absolute positive constant and is $1-O(1/q)$. Conditional on its dimension, their span is uniform on that Grassmannian, by invariance of uniform ambient vectors under all linear changes of coordinates in $k^N$. For $m>N$ a maximum-dimensional span is the full ambient space and is immediately handled. For every other $m$ the trace-orthogonal dimension reduction and the counting bound apply. All input preprocessing, Gram systems, commutation systems and code-equality tests have polynomial cost in $n,m,\log q$. These facts finish the uniform tensor-input theorem.

The authors' version 2 already uses the projection of $I$ to a trace-pairing complement of a one-dimensional hull and analyzes that projection by subspace incidence. The two-projection algorithm uses nondegeneracy of the whole code and counts the pair and code jointly. This eliminates the hull-line and eigenvalue conditions and gives the uniform constant density in every code dimension. A targeted search found the cited antecedents and no previous result with this guarantee. Priority remains unverified. [Li–Li–Qiao–Tao–Wang, §3.2](https://arxiv.org/html/2604.00591v2#S3.SS2)
