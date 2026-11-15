# Raw tensor isomorphism from a constant tuple of determinant factors

**Informal theorem.** Fix an odd finite field $F=\mathbb F_q$, constants $d,k$, and $C>0$. Let the raw tensor be represented by a square pencil $M_A:U\to\operatorname{Hom}(X,Y)$, with $\dim U=\ell$ and $\dim X=\dim Y=n$. Set $L$ to the binary input length, with $L\ge2$. Suppose the formal determinant $P_A=\det M_A$ is nonzero and all its absolute factors have degree at most $d$. Form a list of symmetric bilinear forms on $U$ by taking every $F$-rational absolute quadratic factor and the square of every $F$-rational absolute linear factor. Choose arbitrary nonzero representatives for these factor lines and use the symmetric matrix convention $Q(x)=x^{\mathsf T}Qx$.

Suppose there are at most $k$ such forms $Q_{A,1},\ldots,Q_{A,r}$ admitting a nonsingular combination $B_A=\sum_i c_iQ_{A,i}$ whose simultaneous commutant
$$
 \mathcal C_A=\bigcap_i \{Z\in\operatorname{End}_F(U):ZB_A^{-1}Q_{A,i}=B_A^{-1}Q_{A,i}Z\}
$$
has dimension at most $C\log_q L$. Then a deterministic polynomial-time algorithm given the raw pair $M_A,M_B$ computes the exact set of determinant triples of tensor transporters. The same algorithm produces a list of polynomial size containing every possible label map of a transporter, with no TI decision queries, matched factors, supplied anchors, or prescribed basis. In particular it solves SL-TI on this promise class with no restriction on the matrix-mode adjoint algebra and no dimension congruence requirement.

## Factor recovery and the label list

Use bounded-degree determinant factor recovery from [the bounded-degree factor recovery appendix](#appendix-bounded-degree-factor-recovery). The determinant needs only evaluation by ordinary matrix determinants, and the recovery deals with unrestricted multiplicity and separate fields of definition. Its simultaneous nonvanishing line search hits the good restrictions for bounded-degree geometric factors. Univariate root groups lift by monic Hensel over separate fields of polynomial extension degree, bounded-degree interpolation recovers the candidates, and the second line test recovers the inclusion-minimal root groups. Retain only factors whose normalized coefficients are fixed by $q$-Frobenius. The original recovery uses [Shoup's deterministic finite-field construction](https://www.shoup.net/papers/detirred.pdf).

There are at most $n$ distinct geometric factors. Enumerate the source tuples of size at most $k$, and for each enumerate at most $q^k$ coefficient vectors and compute the commutant by Gaussian elimination. Retain a qualifying tuple and coefficients. This search does not have to make a covariant choice. Relative to the one selected source tuple, enumerate every ordered target tuple of the same types and every tuple of multipliers $\lambda_i\in F^\times$. A genuine transporter $M_B(fx)=hM_A(x)g^{-1}$ takes the determinant factor lines to those of the other tensor. Since both $f$ and the selected forms are over $F$, the resulting equation is
$$
 f^{\mathsf T}Q_{B,i}f=\lambda_i Q_{A,i}
$$
for one of these branches, including when both forms are squares of linear factors. The multiplier used for a squared factor is its linear multiplier squared. Enumerating all of $F^\times$ also allows extra branches, which are checked below.

On the given branch put $Q'_{B,i}=\lambda_i^{-1}Q_{B,i}$ and $B_B=\sum_i c_iQ'_{B,i}$. Discard a singular $B_B$. Every genuine branch map satisfies
$$
 (B_B^{-1}Q'_{B,i})f=f(B_A^{-1}Q_{A,i})\qquad\text{for every }i.
$$
Solve these linear equations for $f$. If the solution space contains one invertible $f_0$, multiplication by $f_0$ identifies the **entire** solution space with $\mathcal C_A$. Indeed, $f_0^{-1}f$ commutes with every source operator precisely when $f$ solves the equations. Therefore discard any branch whose solution space has dimension greater than $C\log_q L$. On every remaining branch enumerate all vectors of the solution space, of which there are at most $L^C$, and retain invertible maps that satisfy the displayed form equations. The union has polynomial size and contains all transporter label maps. Applying the list of maps to any one chosen source anchor tuple gives a polynomial list of all its possible mates. The proof does not require a transporter to preserve an arbitrary choice of bases or representatives.

The bounded-degree determinant hypothesis on the source alone suffices. A target admitting a transporter has the same factor degree bound, so the target's bounded procedure must recover its true mates. A target outside the promise can still be processed within the same polynomial work bound. Final acceptance below requires a genuine transporter, even if the bounded factor routine produced extra candidates on such a target.

## Recover the matrix-mode determinant profile

Fix a candidate $f$ and a basis $(u_j)$ of the source label space. The equations
$$
 hM_A(u_j)=M_B(fu_j)g
$$
with $g,h$ invertible are constructive module isomorphism. Use on $X\oplus Y$ the two vertex projections, together with one operator for each slice, acting as that slice from $X$ to $Y$ and zero on $Y$. The two sets of operators define modules for the same free algebra on the generator symbols. Commuting with the projections forces an isomorphism to have block form $(g,h)$. The generated algebra on the direct sum of the two modules is obtained by linear-span closure, and has polynomial dimension. Apply [Brooksbank and Luks, Testing Isomorphism of Modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf).

If the module isomorphism succeeds, all solutions are a chosen solution $(g_0,h_0)$ composed with $D^\times$, where $D=\operatorname{End}_F(M_A)$ denotes the algebra of endomorphism pairs of the source ordered pencil. Compute $D$ by solving the same equations in the source alone, without invertibility. Write $J=\operatorname{Rad}D$, and compute
$$
 D/J\simeq\prod_i\operatorname{Mat}_{s_i}(K_i)
$$
and the quotient map. This is deterministic polynomial time at the fixed characteristic, with explicit quotient coordinates and lifts. [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495#S3.SS5.SSS1)

For $V=X,Y$ compute the layers $J^aV/J^{a+1}V$ by taking spans of basis actions. The sum over the layers of the dimensions of the image of central idempotent $i$, divided by $s_i[K_i:F]$, is the multiplicity $m_{V,i}$ of the one simple module of that Wedderburn component. On each layer, one copy of the simple module contributes the norm to $F$ of the determinant over $K_i$. Multiplying determinants over the filtration, allowing every norm value $a_i\in F^\times$, gives exactly
$$
 \left\{
 \left(\prod_i a_i^{m_{X,i}},\,\prod_i a_i^{m_{Y,i}}\right)
 :a_i\in F^\times
 \right\}.
$$
Finite-field norms are surjective, each determinant over $K_i$ occurs in its full matrix group, and every unit of the quotient lifts to a unit of $D$, since $J$ is nilpotent. The set is computed by successively multiplying subgroups of $(F^\times)^2$, which has fixed size. Multiply these pairs by the determinants of $g_0,h_0$ and append $\det f$. Taking the union over the candidate label maps gives exactly the determinant profile. Identity in all three components also gives identity on the dualized modes of the ordinary tensor convention.

## An unbounded balanced family with scalar stabilizer

The criterion works even with every quadratic determinant factor singular. The following family also has no rank-one slices, and its full stabilizer over $\mathbb F_3$ consists of the scalar triples.

Take odd $m\ge17$, $n=2m+1$, $F=\mathbb F_3$, and $E=\mathbb F_{3^m}$. Let $\theta$ generate $E$ over $F$. The trace pairing is nondegenerate, so there is $a\in E$ satisfying $\operatorname{Tr}a=\operatorname{Tr}(a\theta)=1$, since $1,\theta$ are linearly independent. On $U=E\oplus E\oplus F$ with coordinates $(x,y,t)$, set
$$
 \begin{split}
 Q_1&=\operatorname{Tr}(a x^2),\\
 Q_2&=\operatorname{Tr}(a y^2),\\
 Q_3&=\operatorname{Tr}(a\theta (x+y)^2),\\
 \ell_1&=t,\qquad \ell_2=t+\lambda(x),\qquad \ell_3=t+\eta(y),
 \end{split}
$$
where $\lambda,\eta:E\to F$ are nonzero linear forms with $\lambda(1)=\eta(1)=0$. The three quadratics have rank $m$, so they are absolutely irreducible and all singular as forms on $U$. There is a common nonzero point $v_0=(1,1,1)$ where all six polynomials are $1$.

The five forms $Q_1,Q_2,Q_3,\ell_1^2,\ell_2^2$ have nonsingular combination $B=Q_1+Q_2+\ell_1^2$. The relative operators of $Q_1,Q_2,\ell_1^2$ are the three coordinate projections. A map in the joint commutant is therefore of the form $\operatorname{diag}(C_x,C_y,\delta)$. The four $E$-to-$E$ blocks of $B^{-1}Q_3$ are all multiplication by $\theta$. Commuting with them gives $C_x=C_y$ equal to multiplication by a common $c\in E$. The $E$-to-$F$ block of $B^{-1}\ell_2^2$ is $\lambda$. Thus $\lambda(c x)=\delta\lambda(x)$, which implies $c=\delta$, since multiplication by any nonzero $c-\delta$ is surjective. The joint commutant is precisely $F I$.

Realize the three determinant factors in arrowhead blocks of size $s=(m+3)/2$. Over $F$ a nonsingular form of odd rank $m=2b+1$ is a sum of $b$ hyperbolic plane forms and one anisotropic square. This follows by splitting isotropic vectors successively, since a nonsingular ternary form over $\mathbb F_3$ has a nonzero isotropic vector. In a diagonalization of a ternary form every nonzero diagonal coefficient is $1$ or $-1$. A pair of opposite coefficients gives an isotropic vector, and if all three coefficients coincide use the vector with all three entries $1$.
Thus write $Q_i=u^{\mathsf T}v$ with $s-1$ linear coordinates on each side, with independent pairs for the hyperbolic part and one shared coordinate up to a nonzero coefficient for the anisotropic part. Use the matrix
$$
 A_i(w)=
 \begin{pmatrix}
 0&u(w)^{\mathsf T}\\
 -v(w)&\ell_i(w)I_{s-1}
 \end{pmatrix},
 \qquad
 \det A_i(w)=\ell_i(w)^{s-2}Q_i(w).
$$
Add one scalar block $\ell_2$, two scalar blocks $\ell_3$, and one field multiplication block of size $r=(m-13)/2\ge 2$, so the total size is $3s+3+r=n$. The field block is multiplication by $t+b(x)\zeta$ on $\mathbb F_{3^r}$, where $\zeta$ has degree $r$ and $b$ is any nonzero linear form killing $1$. Its geometric factors are distinct linear forms of multiplicity $1$, none defined over $F$ up to scaling. They are also distinct from the three $\ell_i$, since the $t$ coefficient is $1$ and the $\zeta$-coefficients have extension degree $r$. All the diagonal blocks are invertible at $v_0$.

Join the blocks by linear upper superdiagonal entries, vanishing at $v_0$, chosen as follows. Normalize on the left by the inverse slice at $v_0$. Each normalized arrowhead acts absolutely irreducibly. In fact its operator space contains the left-normalized generators $L e_0e_j^{\mathsf T},L e_je_0^{\mathsf T}$ for all hyperbolic-tail coordinates $j$, and $L(e_0e_z^{\mathsf T}+\kappa e_ze_0^{\mathsf T})$ for the last coordinate $z$, with $L=A_i(v_0)^{-1}$ and $\kappa\ne0$. The independence from $\ell_i$ follows from its nonzero coefficient on $t$. A nonzero invariant subspace containing a vector with a nonzero hyperbolic tail contains $Le_0$. If its vector has head zero and only last tail nonzero, the combined generator again gives $Le_0$. If its vector has head nonzero, it contains all $L e_j$ for the hyperbolic-tail coordinates. They are independent and number at least three, so their span cannot be supported on just the head and last tail. This gives $Le_0$ in every case. The head entry of $Le_0$ is nonzero by the cofactor formula, so applying the tail and last generators also gives every $Le_j$ and $Le_z$. Hence the invariant subspace is the whole module. The arrowhead modules are pairwise nonisomorphic because their normalized determinants have distinct quadratic factors. The field block is simple over $F$, as the span of its slices contains multiplication by $\zeta$. Its dimension differs from the arrowhead and scalar dimensions.

For adjacent diagonal blocks of dimensions $d_1,d_2$, normalized off-diagonal operators $R(w)$ are arbitrary linear maps in $w$ with $R(v_0)=0$. The two-block extension splits only if
$$
 R(w)=H N_2(w)-N_1(w)H
$$
for a fixed rectangular matrix $H$, by writing an invariant complement as a graph. This space has dimension at most $d_1d_2$, whereas the allowable $R$-space has dimension $(n-1)d_1d_2$. Choose outside the splitting space by linear algebra, independently for each adjacent pair. The resulting normalized module has only the submodules in its displayed prefix flag. Induct on flag length. A submodule of a prefix that maps surjectively onto its last simple factor would split the last adjacent extension if its intersection with the preceding prefix lay in the prefix two stages earlier. Since its intersection with the preceding prefix is itself a prefix by induction, it must be the whole preceding prefix, and then the submodule is the whole prefix. The first simple module occurs only once and has scalar endomorphism ring by absolute irreducibility. A nonzero endomorphism with a nonzero kernel would map a quotient lacking that simple module onto an image containing it, which is impossible by composition factors. Thus every nonzero endomorphism is invertible. Subtracting the scalar given by its restriction to the first block leaves an endomorphism with nonzero kernel, so leaves zero. Consequently the matrix-mode pair adjoint of the full pencil is scalar.

The formal determinant is unchanged by the off-diagonal entries. The lines $\ell_1,\ell_2,\ell_3$ occur with distinct multiplicities $s-2,s-1,s$, all greater than $1$. Every stabilizer fixes them. Modulo $F\ell_1$, the class of $\ell_2$ lies in the essential linear space of $Q_1$ only, among the three quadratic factors. The class of $\ell_3$ distinguishes $Q_2$ in the same way. Thus a stabilizer fixes each of the three quadratic factor lines. The radicals of the first two quadratic forms and the fixed line $\ell_1$ force its label map to be block diagonal on $E,E,F$. The radical of $Q_3$ forces the two $E$-blocks to agree, say $C$. Write $T$ for multiplication by $\theta$. The similitude equations for the first trace form and the mixed trace form yield $C^{-1}TC=\nu T$ for some $\nu\in F^\times$. Taking determinants, $\nu^m=1$, so $\nu=1$ since $m$ is odd and $F=\mathbb F_3$. Hence $C$ is multiplication by an element $c$ of $E$. Fixing $\ell_2$ gives $\lambda(cx)=\delta\lambda(x)$, where $\delta$ is the $t$-scale. As above this gives $c=\delta$. The label map is scalar, and the matrix-mode adjoint computation now makes the full stabilizer scalar. The other two pair adjoints are scalar as well. Conciseness identifies them with the left and right idealizer algebras of the slice space, up to reversing multiplication. An invertible element of either idealizer gives a tensor stabilizer that fixes the other matrix mode pointwise, so it must be scalar. A unital finite-dimensional algebra over $\mathbb F_3$ with only the two scalar units is $\mathbb F_3$: a nonzero radical would supply an additional unit of the form $1+j$, while every matrix algebra over a finite extension besides $\operatorname{Mat}_1(\mathbb F_3)$ has more than two units and a product of two or more simple components has at least four.

The pencil is concise by the nonsingularity at $v_0$ in its matrix modes, and because the three arrowheads jointly detect all coordinates in $E,E,F$. At a point with some $\ell_i\ne0$, the corresponding arrowhead tail has rank $s-1$. At a nonzero point with all $\ell_i=0$, at least one of $x,y$ is nonzero, so its first or second arrowhead has rank at least one. If both $x,y$ are nonzero, their diagonal blocks contribute at least two to rank. If just one of $x,y$ is nonzero, its arrowhead and the mixed arrowhead contribute at least two. The rank of a block upper triangular matrix is at least the sum of its diagonal block ranks, by restricting successively to the prefix flags. Thus there is no rank-one slice. The construction has arbitrarily large balanced odd dimensions and the proved polynomial profile algorithm works in independent arbitrary input bases.

## Geometric linear marks without a common splitting field

The theorem also holds with a constant number of additional geometric linear factors $\beta_{A,j}$, each represented separately in its minimal field $K_j/F$. In the commutant criterion, impose
$$
 \beta_{A,j}Z\in K_j\beta_{A,j}.
$$
The nonsingular combination $B_A$ still uses the rational forms. The reduced linear space now needs dimension at most $C\log_q L$. Compute that dimension by expanding each equation in an $F$-basis of $K_j$. A coefficient multiplier is uniquely determined by $Z$ because $\beta_{A,j}\ne0$, so introducing one field-valued unknown per mark does not increase the dimension.

For each linear mark enumerate its target mate in the recovered factor list. A true $F$-transporter preserves the field of definition of a normalized factor line, since both pullbacks, along $f$ and $f^{-1}$, are defined over $F$. Match factors with the same degrees of definition, represented in the same compatible $K_j$. Add
$$
 \beta_{B,j}f=\mu_j\beta_{A,j}
$$
to the linear relative-operator equations. The unknown $\mu_j$ is a vector in the $F$-basis of $K_j$. No elements of $K_j$ are enumerated. If an invertible branch solution $f_0$ with multipliers $\mu_{0,j}$ exists, all $\mu_{0,j}\ne0$, and $f=f_0Z$ transforms the equations into $\beta_{A,j}Z=(\mu_j/\mu_{0,j})\beta_{A,j}$. Thus the entire linear solution space identifies with the reduced source space. As before, discard larger dimensions and enumerate all members on the remaining branches, checking invertibility and the rational form equations. Each local extension degree is at most $n$, so all computations are polynomial, including when the common splitting degree is superpolynomial.

A non-rational quadratic mark also works if its relative operator has a nonzero eigenvalue over the algebraic closure. After matching the factor let $D_A=B_A^{-1}Q_A$ and $D_B=B_B^{-1}Q_B$ over its local field, where $B_B$ has already been set by the rational branches. A genuine branch satisfies $D_B f=\mu fD_A$. There is a nonleading, nonzero characteristic coefficient $a_i$ of $D_A$ in degree $\ell-i$. The corresponding coefficient $b_i$ of $D_B$ gives $\mu^i=b_i/a_i$. A zero $b_i$ rules out that branch. Otherwise find the at most $i$ roots in the local field by fixed-characteristic deterministic univariate factoring, as in the descent proof. Branch on these roots and expand each relative equation over $F$. The source space takes the additional commutant of $D_A$, expanded over $F$, and the same dimension argument applies. For a constant number of marks there are polynomially many branches.

### A growing family that requires the geometric marks in this criterion

Use $U,E,a,\theta,Q_1,Q_2,Q_3$ and $\lambda$ as above. Make all three arrowheads with the same denominator $t$, omit the added scalar blocks, and fill the remaining $r=(m-7)/2$ dimensions with the field block given by multiplication by
$$
 \beta=t+\zeta\lambda(x)+\zeta^2\lambda(y)
 \quad\text{on }\mathbb F_{3^r}.
$$
Choose $\zeta$ of degree $r$, so $1,\zeta,\zeta^2$ are independent over $F$. At $v_0=(1,1,1)$ all four diagonal blocks are invertible. Apply the same nonsplit superdiagonal construction. The arrowhead simplicity proof is unchanged, the field block is simple because its slices span multiplication by $\zeta$, and its dimension differs from the arrowhead dimension. The normalized module has its unique prefix flag and scalar endomorphism ring.

The only rational absolute factors are $Q_1,Q_2,Q_3,t$. Every rational relative-operator commutant in the original criterion contains all $\operatorname{diag}(c,c,\delta)$ for $c\in E,\delta\in F$, acting by multiplication on the first two summands. This space commutes with every operator $B^{-1}Q_i$ and $B^{-1}t^2$ for $B=Q_1+Q_2+t^2$. Replacing $B$ by another nonsingular combination replaces these operators by left multiplication with the inverse of a linear combination of them, which still commutes with the same space. The original criterion therefore has dimension at least $m+1$ for every choice, above $C\log_q L$ for sufficiently large $m$ with fixed $C$. For $B=Q_1+Q_2+t^2$ its full rational commutant is exactly the displayed space by the projection and mixed-trace argument above. The single geometric constraint $\beta Z\in K\beta$, $K=\mathbb F_{3^r}$, makes its multiplier equal to $\delta$ from the $t$ coefficient and forces $c=\delta$ by comparing the $\lambda(x)$ term. The reduced space has dimension one.

This family still has scalar full stabilizer. For any invertible anchor $w$, put $N_w(v)=M(w)^{-1}M(v)$. Then $N_w(v)=N_{v_0}(w)^{-1}N_{v_0}(v)$, and both generated unital algebras agree. One inclusion uses that $N_{v_0}(w)^{-1}$ is in its generated algebra by Cayley–Hamilton. The other uses $N_w(v_0)=N_{v_0}(w)^{-1}$ and the same inversion argument. For a stabilizer with $w=fv_0$, the map $g$ conjugates $N_{v_0}(v)$ to $N_w(fv)$. It preserves the unique prefix flag, since $f$ is invertible and the generated algebras agree. The map $h=M(w)gM(v_0)^{-1}$ preserves the corresponding flag in the other matrix mode, as both slices are invertible and block upper triangular. The induced transporter on each diagonal block preserves its formal determinant up to scale. This fixes $Q_1,Q_2,Q_3,t$ separately and gives $f=\operatorname{diag}(c,c,\delta)$ with $c\in E^\times,\delta\in F^\times$, by the same trace, radical, and odd-dimension argument. The norm factor line $\beta$ can map to a Frobenius conjugate $\beta_j=t+\zeta^{3^j}\lambda(x)+\zeta^{2\cdot3^j}\lambda(y)$. The equation $\beta_j f=\delta\beta$ gives
$$
 \lambda(cx)=\delta\frac{\zeta}{\zeta^{3^j}}\lambda(x),\qquad
 \lambda(cy)=\delta\left(\frac{\zeta}{\zeta^{3^j}}\right)^2\lambda(y).
$$
These must give the same scalar, since the linear form $\lambda$ is the same and nonzero on both copies of $E$. The nonzero ratio is therefore one. Thus $c=\delta$ and the scalar matrix-mode adjoint makes the entire stabilizer scalar. The other two pair adjoints are scalar by the same idealizer argument. The earlier rank bound uses only the arrowheads and remains valid with their shared denominator $t$.

## Scope

The tuple criterion does not establish a universal anchor list for arbitrary tensors. It covers cases where a constant tuple of determinant factors restricts the relative operator space to logarithmic dimension, including families where every individual quadratic factor is degenerate and where rank-one slice-frame extraction does not apply. The factor recovery uses the existing bounded-degree promise. This proof permits arbitrary absolute splitting degrees, arbitrary multiplicities, and arbitrary matrix-mode adjoints.

## Appendix. Bounded-degree factor recovery

This appendix uses the factor recovery from *An orientation test with factors in separate finite fields* (MathProofs).

### Finite field computations

At fixed characteristic $p$, univariate factoring over explicit finite extensions is deterministic polynomial time in the extension degree and polynomial degree. For completeness, given squarefree $h$ over a field $K$ of characteristic $p$, the algebra $C=K[t]/(h)$ is a product of finite fields. Compute $\ker(x\mapsto x^p-x)$ by $\mathbb F_p$-linear algebra. Its dimension is the number of factors, and an element therein outside the scalar $\mathbb F_p$ line has at least two distinct values on the factors. Compute the polynomial gcds with that element minus $a$ for each $a\in\mathbb F_p$ to split $h$, and repeat. The derivative and gcd identify the factors whose multiplicities are not divisible by $p$. Strip all their occurrences by division, then take coefficientwise $p$-th roots of the remaining $p$-th power and recurse. This also handles inseparable binomials. No enumeration of the field of coefficients is used. Use [Shoup's deterministic irreducible-polynomial construction for fixed characteristic](https://www.shoup.net/papers/detirred.pdf) to construct finite fields.

Use compatible field models over $\mathbb F_p$ for all represented degrees up to an explicit polynomial bound. For each prime power dividing a requested degree, build the largest needed prime-power extension. Its smaller members are the kernels of the corresponding Frobenius maps minus the identity. The field of a composite degree is the tensor product of its prime-power parts, which are of coprime degrees. Using a fixed ordering gives compatible embeddings for divisibility. One can prepare all prime-power fields below a polynomial numerical bound, since there are only polynomially many and factoring these small integer degrees is polynomial. Deterministic irreducible construction and the fixed-characteristic factor procedure above suffice here. For two represented degrees, the lcm gives a field containing both, and intersections are accessed by Frobenius kernels.

### Recover geometric factors in local fields

Here the determinant can be replaced by any nonzero homogeneous polynomial $P$ of degree $n$ accessible by polynomial-time evaluation over the represented fields, with the same bound $d$ on all distinct geometric factor degrees.

Choose an extension $E_0/F$ of polynomial cardinality, hence logarithmic degree for fixed $F$. Use deterministic line restrictions from the earlier two-quadratic proof. Explicitly, on $k$ parameters use the substitution $x_i=t^{w_i}$, with weights $w_i=\sum_{j=0}^{D} i^j b^j$, $b>Dk^D$, for a suitable constant $D=O(d^2)$. Monomials of total degree at most $D$ have distinct weights because equality gives the same no-carry power sums for multisets of size at most $D$. The curve hits the common nonvanishing locus of polynomially many nonzero polynomials of degree at most $D$: the product of their nonzero curve substitutions has polynomial degree, and $|E_0|$ is chosen greater than that total. Coefficients may lie in an extension of $E_0$. The parameter points in $E_0$ still obey the root bound.

Apply the curve to the $2\ell$ coordinates of an affine line $v+tu$. A good line has nonzero leading terms for all geometric factors and gives simple, disjoint roots for the distinct reduced factors. Each requirement is the nonvanishing of a coefficient, a discriminant, or a resultant of degree bounded in terms of $d$, regardless of the fields of definition. To see the discriminants are nonzero, take a direction with nonzero leading coefficient and nonzero directional derivative. Absolute irreducibility implies that the factor has a nonzero derivative and is coprime to such a derivative. Viewing that direction as the univariate axis proves nonvanishing of the generic-line discriminant. Distinct factors are coprime and the same argument applies to their resultant along a direction with nonzero leading coefficients. Thus a good line occurs on the curve. Interpolate each restriction, discard degree-dropping lines, and maximize the degree of the squarefree radical of the restriction, computed by univariate factoring. This degree is at most the sum of the distinct geometric factor degrees, and a good line attains it. Any maximizing full-degree line is good.

Fix the good line and complete $u$ to a basis with the columns of $C$. The polynomial $P(v+tu+Cz)/P(u)$ is monic in $t$, since $P$ is homogeneous. Let the irreducible residue polynomials of its squarefree part at $z=0$ have degrees $a_i\le n$ over $E_0$. Enumerate sets of at most $d$ such residue polynomials. For each set work over the field of degree $\operatorname{lcm}(a_i)\le n^d$ over $E_0$. Every chosen residue polynomial splits there. Enumerate subsets of size at most $d$ from their listed roots. There are polynomially many choices at fixed $d$, and every actual geometric reduced factor has one of these root subsets in some enumerated field.

In a local field, lift each selected root $a$ along directional substitutions $z=s\beta$. The residue root has multiplicity $e$, so lift the coprime factor $(t-a)^e$ against the other residue factor, by ordinary coefficientwise monic Hensel lifting. Its true formal lift is $(t-a_\beta(s))^e$, where $a_\beta(s)$ is the simple-root lift of the geometric reduced factor. Writing $e=p^j e'$ with $p\nmid e'$, the coefficient of $t^{e-p^j}$ is $-e'a_\beta(s)^{p^j}$. Lifting to precision $s^{dp^j+1}$ and taking inverse Frobenius of those coefficients recovers the simple-root lift through degree $d$. One lift has precision and polynomial degrees $O_d(n)$ and uses computations only in the selected local field.

Multiply the resulting simple-root factors for a subset of at most $d$ roots. The coefficient of $s^i$, truncated at $i=d$, is the evaluation at $\beta$ of a homogeneous polynomial of degree $i$ in $z$. This follows by restricting the unique multivariate simple-root lifts to $z=s\beta$. Interpolate these coefficients from the same bounded-degree curve substitution and obtain the candidate in $(t,z)$. Discard total degree above $d$. In the correct subset, all roots associated with a single reduced factor are included, so that factor's monic expression is recovered exactly. The truncated calculation takes polynomial time because $d$ is constant.

To certify the candidate, restore raw coordinates and test divisibility of $P$ on every line of another such curve family. A candidate coprime to all true factors fails on a full-degree line where its leading coefficient and all its resultants with those factors are nonzero. The curve hits this simultaneous nonvanishing condition by bounded factor degrees. A passing candidate must therefore share a true factor. That factor's good-line root subset is contained in the candidate's subset, using monicity on that line. Both are present in the same local field and within the same selected residue-polynomial set. Thus the inclusion-minimal passing subsets recover exactly the geometric reduced factors present there. On equality of subsets, both monic polynomials have the same degree in $t$ and the true factor divides the candidate, so they coincide.

Normalize in raw coordinates by dividing by the leading coefficient for a fixed monomial order. Read the factor multiplicities from its good-line roots. Use the compatible embeddings to compare normalizations occurring in different local fields. For each factor, the minimal field containing its raw normalized coefficients over $F$ can be computed by iterating $q$-Frobenius until all coefficients return. Its degree is at most $n$, since Frobenius permutes at most $n$ geometric factors. Recover its coordinates in that subfield by a linear solve. This provides all factors in fields of degree at most $n$ over $F$, without realizing their common compositum.
