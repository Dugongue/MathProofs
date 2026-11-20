# Polynomial Turing reductions for even isomorphism of special exponent-three groups

## Statement

Work over $F=\mathbf F_3$. A succinct group input is an alternating bimap $\beta:X\times X\to Z$ whose values span $Z$ and whose common radical is zero, with specified bases. Its special group of exponent three has underlying set $X\oplus Z$ and multiplication
$$
(x,z)(y,w)=(x+y,z+w+\tfrac12\beta(x,y)).
$$
Here $X$ is the central quotient and $Z$ the center. Compare two inputs of matching dimensions. Order the underlying additive coordinates using the displayed bases. Even isomorphism in this ordering asks for an isomorphism of determinant $1$ on $X\oplus Z$.

There is a deterministic polynomial-time Turing reduction from even isomorphism to ordinary three-tensor isomorphism over $F$, and hence to ordinary isomorphism of succinct special exponent-three groups, in any of the following cases.

1. The dimension of $X$ is odd.
2. A polynomial-size complete isomorphism-invariant list of rational projective points spanning $X$ is available for each input.
3. A polynomial-size complete isomorphism-invariant list of rational projective points spanning $Z^*$ is available for each input.
4. Isomorphism-invariant flags in both $X$ and $Z$ are available and the total number of nonzero vectors in their successive quotients is polynomial in the input length. In particular it suffices to have graded dimensions $O(\log N)$ for input length $N$.

The lists and flags may be supplied with the indicated promises or computed deterministically in polynomial time. An isomorphism-invariant list means that any isomorphism transports the source list bijectively onto the target list in the indicated representation, and in particular each list is invariant under all automorphisms. Orderings within the lists are immaterial. Examples at the end give explicit unbounded-dimensional families with arbitrary alternating data, using ordinary contraction ranks for the complete lists. For supplied lists or flags the cost is polynomial in the total written input length, including the enumerated quotient vectors in case 4.

This is a Turing reduction. The proof gives many polynomial-size ordinary queries and uses their answers to compute generators of a permutation image. It requires no enumeration of the full underlying groups.

## Group coordinates and orientation

The multiplication law recovers the additive operation by multiplying two group elements and then removing half their commutator. Thus every group isomorphism is linear on the displayed additive coordinates. An isomorphism induces invertible maps $g:X_A\to X_B$ and $h:Z_A\to Z_B$ with
$$
\beta_B(gx,gy)=h\beta_A(x,y).
$$
Conversely any such transporter gives an isomorphism on the displayed direct sum, and every other lift differs by a central shear. The additive determinant of a lift is
$$
\chi(g,h)=\det(g)\det(h).
$$
The quotient and center use the same block ordering on both sides, so the formula is independent of the shear. The span of the values of $\beta_A$ makes $h$ unique once $g$ is given. [Baer, Groups with Abelian Central Quotient Group](https://doi.org/10.1090/S0002-9947-1938-1501972-1)

For completeness, the permutation sign of an invertible linear map on the elements of $\mathbf F_3^D$ is its determinant viewed as a sign. Elementary transvections have order dividing three, hence even sign. Multiplication by $-1$ on one coordinate swaps $1$ and $-1$ in each of $3^{D-1}$ coordinate fibers, hence has negative sign. These transformations generate the linear group by elimination. Accordingly the determinant condition is exactly the even condition in the prescribed coordinate ordering.

The pair $(-I_X,I_Z)$ is always an automorphism. If $\dim X$ is odd, its sign is negative and composing with it repairs either ordinary transporter. This proves case 1. The remaining arguments handle both parities independently.

## Ordinary queries with exact marked vectors

A rational projective point over $F$ consists of the two nonzero vectors $v,-v$ of its line. Replace each invariant projective list by the list $S$ of both vectors on every line. It is complete and invariant in the same representation, has twice the size, and spans the same space.

Given a partial list of prescribed vector images $v_i\mapsto w_i$, $1\le i\le j$, one ordinary TI query decides whether an ordinary group transporter has those images. The construction works for marks in $X$ or for marks in $Z^*$, whichever representation is used. Denote that representation space by $Y$. Take an auxiliary $F$-space $D$ with basis $e_1,\ldots,e_j$, the shift $J e_i=e_{i+1}$ for $i<j$, $J e_j=0$, and the vector $\eta=e_1$. Add the map $P_A:D\to Y_A$ with columns $v_i$ and the map $P_B:D\to Y_B$ with columns $w_i$. Regard the forms tensor $\beta\in X^*\otimes X^*\otimes Z$, the operator $J\in D^*\otimes D$, the vector $\eta\in D$, and $P\in D^*\otimes Y$ as an ordered tensor system. When $Y=Z^*$ the action on $Y$ is $h^{-\mathsf T}$, linked to the same center factor of $\beta$. When $Y=X$ the action on $Y$ is $g$.

Any isomorphism of the system acts on $D$ by a map $Q$ commuting with $J$ and fixing $\eta$. It therefore fixes $e_i=J^{i-1}\eta$ for every $i$, hence $Q=I_D$. Consequently the condition on $P$ is exactly the requested list of vector images under $g$ or $h^{-\mathsf T}$. Conversely, a bracket transporter meeting the marks extends by $Q=I_D$ to a system isomorphism. With $j=0$ only the form tensor is needed.

The system has at most four ordered tensors of order at most three in linked and dual spaces. The constant-size tensor-system compiler converts it to one ordinary three-tensor isomorphism instance of polynomial dimensions, independently of the number of marks. One can instead use an ordinary succinct special-group isomorphism oracle after the standard ordinary tensor-isomorphism to alternating-matrix-space isometry reduction. If that reduction yields a bimap with common radical, compare radical dimensions and factor them out. Any isometry of the quotient lifts to the full space after choosing an arbitrary isomorphism of the radicals. Using independent coordinate forms ensures the values span the output. Trivial resulting zero brackets can be decided directly. Thus the queries can all be implemented on the stated ordinary group domain. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2), [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110)

## Obtaining a representative and generators of the permutation image

Reject a difference in sizes of the relevant lists. Query ordinary equivalence with no marks. If it holds, find a full matching of signed source vectors to signed target vectors compatible with at least one transporter, by testing all still-available target images at each step with the existing marks. At least one choice remains feasible whenever the previous marks were feasible. The final matching represents the action of one ordinary transporter on the list.

Let $\Gamma_A$ be the permutation group induced by ordinary automorphisms of the source bracket on $S_A$. Fix a source list ordering $v_1,\ldots,v_L$, and let $\Gamma_i$ be the subgroup of $\Gamma_A$ fixing the first $i$ vectors, with $\Gamma_0=\Gamma_A$. For each $i$ and each possible image $w$ of $v_i$, query for an automorphism fixing the first $i-1$ vectors and carrying $v_i$ to $w$. In an affirmative case, extend those marks greedily to find a full matching. This gives a representative $\sigma_{i,w}\in\Gamma_{i-1}$ sending $v_i$ to $w$. For any $\sigma\in\Gamma_{i-1}$ with that image, $\sigma_{i,w}^{-1}\sigma\in\Gamma_i$. Thus these representatives together with $\Gamma_i$ generate $\Gamma_{i-1}$. Since $\Gamma_L$ is trivial, the collected representatives generate $\Gamma_A$.

There are at most $L^2$ representatives, and constructing each full matching takes at most $L^2$ further marked queries. Every query has at most $L$ marks. The group needed below is the permutation image, which may have very large order even though this generator list is polynomial.

## Recovering the orientation character

### Spanning list in the central quotient

For a fully marked matching, the $g$ of any transporter is determined exactly by the images of the spanning vectors. Obtain it by Gaussian elimination on a choice of source basis vectors from the list. Compute $h$ by expressing the images of the bracket values under the relation $\beta_B(gx,gy)=h\beta_A(x,y)$. Those bracket values span the center, so linear algebra recovers $h$ uniquely. The marked oracle already guarantees that these maps exist. Compute the sign $\det(g)\det(h)$ by Gaussian elimination. A pair inducing the identity on the signed list has $g=I$ and then $h=I$, so its sign is positive.

### Spanning list in the dual center

First compute generators of the group $K_A$ of common isometries of the source alternating forms that fix the center pointwise. The vector-valued alternating bimap is a Hermitian map with output involution $-I_Z$. The Brooksbank–Wilson algorithm for generators of its isometry group has a deterministic version polynomial in the field characteristic and written input parameters. Here the characteristic is $3$. If any generator has negative determinant, then any ordinary transporter can be made even by composing with this source automorphism. Return the ordinary-isomorphism verdict in this case. If every generator has positive determinant, every element of $K_A$ has positive determinant. Since a full signed dual-center list spans, this group is exactly the kernel of the permutation action of bracket automorphisms on that list. [Brooksbank and Wilson, Theorem 1.2 and Remark 2.1](https://doi.org/10.1090/S0002-9947-2011-05388-2)

For a fully marked matching, recover the unique action $h^{-\mathsf T}$ on the spanning dual center. To recover one lift $g$, let $\mu_i$ range over a target dual basis. Put $B_i=\mu_i\beta_B$ and $A_i=(h^{\mathsf T}\mu_i)\beta_A$. An actual lift satisfies
$$
g^{\mathsf T} B_i g = A_i\qquad\text{for all }i.
$$
The Ivanyos–Qiao ordered tuple isometry algorithm finds one such $g$. Theorem 7(1) gives a constructive deterministic version of running time polynomial in the characteristic and the tuple input parameters, so it applies here. The marked oracle already guarantees a solution for this $h$. Evaluate $\det(g)\det(h)$. All lifts have the same sign after the kernel check, since two lifts of the same center map differ by a common isometry fixing the center pointwise. No nonsingular individual form is required. [Ivanyos and Qiao, Theorem 7(1)](https://arxiv.org/pdf/1708.03495)

In particular, if $\dim Z=O(\log N)$ for written input length $N$, all nonzero dual center vectors form a polynomial-size invariant spanning list. If $\dim Z=O(\sqrt{\log N})$, one can instead decide the orientation in deterministic polynomial time without using a TI oracle. Enumerate all $3^{(\dim Z)^2}$ center matrices, retain the invertible ones, and run the ordered tuple test for each. For an affirmative tuple test, either sign of its lift can be achieved if $K_A$ has a negative generator. Otherwise the one computed lift's sign decides that center map.

If a nonsingular form $\lambda_0\beta_A$ is available, there is a direct determinant calculation in place of the two isometry algorithms. Set $\lambda'_0=h^{-\mathsf T}\lambda_0$, and put $A_0=\lambda_0\beta_A$ and $B_0=\lambda'_0\beta_B$ in the displayed quotient bases. The related forms satisfy $g^{\mathsf T}B_0g=A_0$. By the change-of-basis identity for the Pfaffian,
$$
\det g=\frac{\operatorname{Pf}(A_0)}{\operatorname{Pf}(B_0)}.
$$
The denominator is nonzero. The Pfaffian identity is an integer polynomial identity, proved in characteristic zero by the exterior power formula, then specialized. Compute the Pfaffians by alternating elimination, eliminating an off-diagonal pivot pair by congruence and proceeding recursively on the remaining block. If the center action is the identity for an automorphism, then this ratio is $1$, so the kernel test is automatic.

### Completing the decision

In either branch, after the kernel check in the dual-center case, the sign on the ordinary automorphism group factors through $\Gamma_A$. Evaluate the sign of each computed permutation generator using the corresponding full matching. The ordinary transporter sign is also computable from its full matching. If a generator has negative sign, composing any ordinary transporter with its lift achieves even sign. If all generators have positive sign, every ordinary automorphism has positive sign. In that case all ordinary transporters have the same sign, since they form a right coset of the source automorphism group, and that sign decides the instance. This completes both directions of the reduction and its polynomial complexity.

## Graded vectors of characteristic flags

Suppose that the flags of case 4 are given. A flag is isomorphism-invariant here when every ordinary bracket isomorphism respects its corresponding stages. Choose a basis of each stage by extending the lower-stage basis, using a common ordering of grades for the two inputs. Enumerate all nonzero vectors in each successive quotient. These lists are ordered by the grade for purposes of recording queries. Each ordinary group transporter gives a permutation between the source and target members of every grade. The signed determinant on the entire quotient or center is recovered from a full matching by taking the product of determinants on its successive quotients and the target adapted-basis determinant divided by the source adapted-basis determinant. This follows by triangularity in the adapted bases. A matching therefore determines the total additive determinant even when it does not determine the entire transporter.

Here is a constant-size tensor-system query that enforces arbitrarily many class images at once. Consider prescribed marks in one underlying space $Y$, either $X$ or $Z$. Mark $i$ is $v_i+U_i\mapsto w_i+U'_i$, where $U_i,U_i'$ are corresponding lower stages of the flag and $v_i,w_i$ belong to the corresponding upper stages. Both lower stages have dimension $a_i$. Fix written bases of them. Choose distinct monic irreducible polynomials $q_i(T)$ of a common degree $d=O(\log(j+1))$ over $\mathbf F_3$ for the $j$ marks. Put $E_i=F[T]/(q_i)$ and $D_i=E_i^{a_i+1}$. On $D=\bigoplus_i D_i$ use the fixed operator $J$ acting as multiplication by $T$ in every copy. For each $i$ choose a nonzero $F$-linear functional $\ell_i:E_i\to F$, for example constant coefficient in the polynomial basis. Use the single covector $\ell:D\to F$ given by the sum of $\ell_i$ on the last coordinate of each $D_i$.

To construct the required irreducibles deterministically, choose $d=2\lceil\log_3(j+1)\rceil+2$. At least $(3^d-\sum_{e\le d/2}3^e)/d\ge 3^d/(2d)\ge j$ distinct degree-$d$ irreducibles exist. Indeed every element of $\mathbf F_{3^d}$ of smaller degree belongs to a subfield of degree at most $d/2$, and each element of degree $d$ has $d$ conjugates. Enumerate monic degree-$d$ polynomials and test divisibility by monic polynomials of degree at most $d/2$. Both enumerations are polynomial in $j+1$. This uses the fixed base field only.

Define $P_A:D\to Y_A$ on each block by applying $\ell_i$ to its first $a_i$ coordinates to obtain the coefficients in the displayed basis of $U_i$, and applying $\ell_i$ to its last coordinate to obtain the coefficient of $v_i$. Define $P_B$ with $U'_i,w_i$ correspondingly. As for exact vector marks, use the ordinary tensor system consisting of $\beta$ and $J,\ell,P$. All bracket transporters preserve the flags by hypothesis. A tensor-system isomorphism acts on $D$ by an invertible $Q$ commuting with $J$ and preserving $\ell$. It preserves each $D_i=\ker q_i(J)$ and is $E_i$-linear there. On $D_i$ the equation preserving $\ell$ forces the last $E_i$ coordinate itself to be fixed. If the difference of that coordinate for some argument were a nonzero $b\in E_i$, multiplying the argument by a suitable element of $E_i$ would make its difference detected by $\ell_i$. That would contradict preservation and $E_i$-linearity. The equation $g_Y P_A=P_BQ$ then forces $g_Y(v_i)-w_i\in U'_i$, by evaluating on a last-coordinate vector on which $\ell_i$ takes value $1$.

Conversely, suppose the bracket transporter has the requested class images. For each block extend the $F$-matrix
$$
\begin{pmatrix}
g_Y|_{U_i}&g_Y(v_i)-w_i\\
0&1
\end{pmatrix}
$$
in the displayed lower-stage bases to an $E_i$-linear matrix on $D_i$. This is invertible and fixes the last coordinate. It commutes with $J$ and preserves $\ell$. Because its matrix coefficients lie in $F$, it commutes with the coordinatewise application of $\ell_i$ and gives exactly $g_YP_A=P_BQ$. Hence the mark query is sound and complete.

Use this construction independently for the marks in $X$ and in $Z$. With $\beta$ there are at most seven tensors, so the same ordinary TI compiler gives polynomial-size queries. Apply the previous stabilizer-chain procedure on the disjoint union of all graded lists, with corresponding grades as separate parts. A source automorphism trivial on this union induces identity on every quotient and has positive total determinant. Full matchings give the determinant values by the adapted-basis formula, so the same permutation-image test decides even isomorphism. The number of queried marks and dimensions of all auxiliary spaces are polynomial in the total number of enumerated grade vectors and the written flags and bracket inputs.

## Explicit unbounded-dimensional families

### Dual-center lists from symplectic blocks

Take any alternating data maps $B_1,\ldots,B_m$ on an $n$-dimensional space $V$ over $F$. They may be degenerate, linearly dependent, or zero. Put the data coordinates in $V\oplus V^*$, equipped with its standard nonsingular alternating matrix
$$
J_0=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}.
$$
Use output coordinates $z_0,\ldots,z_m$. On $V\oplus V^*$ take $J_0$ in coordinate zero and the extension of $B_i$ supported on $V$ in coordinate $i$. For each output coordinate $i$ add its own disjoint symplectic block $S_i$ of dimension $2R$ with fixed nonsingular form taking values only in $Fz_i$, where $R>n$. All cross-block brackets are zero.

For $\lambda=(\lambda_0,\ldots,\lambda_m)$, the rank of its contraction is
$$
2R\,|\{i: \lambda_i\ne0\}|+
\operatorname{rank}\!\begin{pmatrix}\sum_{i=1}^m\lambda_i B_i&\lambda_0 I_n\\-\lambda_0 I_n&0\end{pmatrix}.
$$
The second term is at most $2n$. Therefore the complete rational projective locus of rank at most $2R+2n$ in $Z^*$ consists exactly of the coordinate lines, since two nonzero coordinates already contribute $4R>2R+2n$. These lines span and are computed directly from the displayed input format. For the functional with every coordinate equal to $1$, the data block is nonsingular because the off-diagonal identities force both components of a kernel vector to vanish. Every symplectic marker block is also nonsingular at this functional. This supplies the nonsingular form in case 3 and proves the common radical is zero. Each marker produces its own output coordinate, so the values span the center. The dimensions and coefficient lists are polynomial in the explicitly given data. The complete list and the nonsingular witness depend on the template rather than on any unproved invariant-computation procedure.

In this general method the nonsingular functional requirement is compatible with a genuine orientation distinction. For the smallest Heisenberg example, take $X=F^2$, $Z=F$, $\beta_A(x,y)=\det[x,y]$ and $\beta_B=-\beta_A$. The center dual has one projective line and its nonzero forms are nonsingular. Every transporter has $h=-\det g$, so its total determinant is $-1$, even though an ordinary transporter exists.

### Quotient lists from incidence-graph brackets

A separate family uses a complete low-rank list in the quotient, without needing a nonsingular center form. Let $\beta_{\rm data}$ be any alternating bimap on an $n$-dimensional space whose outputs span its displayed data output. Choose a power of two $q_0\ge\max(n,2)$ of order $O(n+1)$. Form the point-line incidence graph of the projective plane over $\mathbf F_{q_0}$. This auxiliary field can be constructed by enumerating monic binary polynomials of degree $\log_2 q_0$ and testing irreducibility by trial divisors, which is polynomial in $n+1$. The graph has $2(q_0^2+q_0+1)$ vertices; it is bipartite and $(q_0+1)$-regular. Any two points lie on exactly one common line and two lines share exactly one point. These properties follow by taking spans and intersections of the one- and two-dimensional subspaces of $\mathbf F_{q_0}^3$.

Use one quotient coordinate over $F=\mathbf F_3$ for every graph vertex, placing the $n$ data coordinates among the point vertices. Add a fresh center coordinate for each graph edge $ij$, with form $x_i y_j-x_j y_i$. Extend the original data bracket by zero outside its data coordinates. There is no edge between data vertices. Hence the marker coordinates and original data output are individually spanned by bracket values, and the construction stays over $F$.

For a nonzero $x$ of support $S$ in the quotient, its marker contraction rank is
$$
|S\cup N(S)|-c(S),
$$
where $N(S)$ is the set of graph neighbors and $c(S)$ is the number of connected components of the induced graph on $S$. Indeed each inactive neighbor of an active coordinate has its corresponding kernel variable forced to zero. The other inactive variables are free. On an edge between active vertices the ratios $y_i/x_i$ must coincide, so there is one free ratio per active component. This computes the kernel dimension and proves the formula. In particular any nonzero $x$ has nonzero marker rank, so the common radical is zero.

Write $d=q_0+1$. A singleton support gives rank $d$. For any support of size two the marker rank is at least $2d-1$. If the vertices are adjacent, their closed neighborhoods intersect in just those two vertices and the active component count is one. If they are nonadjacent, the closed neighborhoods meet in at most one vertex and the component count is two. The rank formula is nondecreasing as a vertex is added to $S$. An added vertex adjacent to $S$ does not increase the number of active components. An added vertex with no neighbor in $S$ increases that number by one and itself supplies a new vertex of the closed neighborhood. Thus every support of size at least two gives rank at least $2d-1$ before adding the data output.

On a coordinate line the combined contraction rank is at most $d+n-1$, since the data part has rank at most $n-1$ by alternation. On any larger support it is at least $2d-1>d+n-1$ because $d>n$. Consequently the complete rational projective locus in the quotient of contraction rank at most $d+n-1$ is exactly the coordinate lines. This spans the quotient and supplies case 2. All dimensions are polynomial in the data dimensions; the incidence graph is only an indexing structure for the marker forms.

The results give polynomial reductions on stated infinite families and when the listed isomorphism-invariant data are available. The unrestricted reduction still requires a method for groups without the stated effective lists or flags. The proof does not establish the unrestricted reverse reduction or convert the use of multiple queries into one many-one instance. It is a paper proof with no Lean certificate.
