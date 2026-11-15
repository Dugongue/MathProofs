# Exact determinant profiles from singular quadratic factors

This is an informal deterministic polynomial-time algorithm for a class of raw tensor pairs over any fixed finite field, including characteristic two. It permits every combination of the chosen polar forms to be singular. Only the ordered-pencil indecomposable summands supplying the chosen factors have a bounded-degree condition. Other summands may be rectangular, singular, or contain arbitrary high-degree determinant factors.

## The criterion

Fix $F=\mathbb F_q$ and constants $d,k,C$. Write the input as two pencils $M_A,M_B:U\to\operatorname{Hom}(X,Y)$ in their raw bases. The three mode dimensions can differ. Each ordered-pencil module has one generator for each label basis vector, acting by the corresponding arrow $X\to Y$ on $X\oplus Y$ and by zero on $Y$. Include the two vertex projections.

Suppose we can select at most $k$ determinant factor lines, each from the determinant polynomial of an indecomposable summand of this module. Each summand supplying a chosen mark must have equal vertex dimensions, nonzero formal determinant, and absolute determinant factors all of degree at most $d$. The selected factors are $F$-rational geometric quadratics $Q_i$ or geometric linear forms $\ell_j$. Linear factors may be non-rational, in which case each has its coefficients in its own finite field $K_j$. Write $P_i$ for the polar bilinear form of $Q_i$, represented as a map $U\to U^*$. In characteristic two put $R_i=\ker P_i$ and $\rho_i=(Q_i|_{R_i})^{1/2}$. This is an $F$-linear functional on $R_i$, since the polar form vanishes there and the square root is the inverse of square Frobenius.

Form an affine linear system in $Z:U\to U$ and $W:U^*\to U^*$. Impose
$$
 P_i Z=W P_i,\qquad
 \ell_jZ=\ell_j\ \text{for rational }\ell_j,\qquad
 \ell_jZ\in K_j\ell_j\ \text{for other }\ell_j.
$$
In characteristic two also impose $\rho_i Z|_{R_i}=\rho_i$; the first equation already forces $Z(R_i)\subseteq R_i$. Impose this as ordinary affine linear equations by extending $\rho_i$ arbitrarily to $U$. In the non-rational linear equations, express the field-valued scalar unknowns and coefficients in their individual $F$-bases. Let $\mathcal V$ be the projection of the solution space onto $Z$. The identity is in $\mathcal V$. Suppose its affine dimension is at most $C\log_q L$, where $L\ge2$ is the raw input length.

Then the algorithm computes the exact determinant profile
$$
 \{(\det f,\det g,\det h): M_B(fv)=hM_A(v)g^{-1},\
     f,g,h\text{ invertible over }F\}.
$$
In particular it decides SL-TI without ordinary TI decision calls. The identity determinant condition is the same in the covariant tensor convention, which uses inverse duals on the dualized modes. There is no bound on the matrix-mode adjoint dimension.

## Recover candidate factor lines

Compute the ordered-pencil end algebra $D\subseteq\operatorname{End}(X)\oplus\operatorname{End}(Y)$ from the linear intertwiner equations. Compute its Jacobson radical $J$, the Wedderburn quotient $D/J$, and the quotient map. These algorithms are deterministic polynomial time in fixed characteristic. [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495#S3.SS5.SSS1)

In the product of full matrix algebras for $D/J$, use the diagonal matrix units as a system of primitive orthogonal idempotents. Lift them successively, each in the corner complementary to the sum of earlier lifted idempotents. A linear solve gives a preimage, and compression into the corner retains the desired quotient image. If $a$ is such a preimage in characteristic $p$, $a^2-a$ is nilpotent in $J$. The element $a^{p^b}$ is idempotent for $p^b\ge \dim D+1$, since
$$
 (a^{p^b})^2-a^{p^b}=(a^2-a)^{p^b}=0.
$$
Its image in $D/J$ is unchanged. The sum of the resulting orthogonal lifts is $1$, since the complementary idempotent lies in $J$ and is nilpotent. Each image module is indecomposable. A nontrivial idempotent in its endomorphism corner would project to zero or one in the division-algebra quotient of that corner, making the idempotent or its complement zero by nilpotence.

Choose bases for these image blocks. The source module is a direct sum of them. For extraction ignore blocks of unequal vertex dimensions. The full pencil may be rectangular or, if square, have identically zero determinant.

Run the [bounded-degree factor recovery](#appendix-bounded-degree-factor-recovery) separately on every square block. Use its fixed polynomial bounds on all curve sizes, field degrees, subset sizes and lift precisions. On a block with no full-degree restriction discard that block, and discard any failed local reconstruction. Keep only nonzero homogeneous candidate polynomials of degrees one or two in raw label coordinates. A block satisfying the bounded-degree hypothesis has a good restriction and yields all its true factor lines. On other blocks we may encounter unverified candidates. Each procedure is still polynomial under the same work bounds, since the restriction degrees and multiplicities never exceed the matrix side of the block and the number of chosen residue polynomials is capped by $d$. We need only the union of the true recovered marks and possible extra candidates. The final test will require a genuine full tensor transporter.

Every ordinary tensor transporter preserves this supply of eligible low-degree factors. Its label isomorphism $f$ changes the generators of the ordered-pencil module by invertible linear combinations of the arrows, fixing the two vertex projections. This preserves direct sums and indecomposability. It takes any source indecomposable decomposition to such a decomposition on the target. The computed target decomposition has the same modules up to ordered module isomorphism and permutation by Krull–Schmidt, applied to the finite-dimensional modules of the algebra generated by the arrows and projections. A module isomorphism fixes the label on its matching blocks and takes the block determinant polynomial to a nonzero scalar multiple. Thus every genuinely selected source factor from a bounded-degree block has its mate present in the target candidate list, with unchanged absolute degree and coefficient field. The algorithm enumerates all constant-size source tuples as well as target tuples. It does not choose just one eligible-looking source tuple, since unverified candidates on other blocks can coexist.

## Solve and project the matching equations

Let $P_{A,i},P_{B,i}$ be the rational quadratic polars of one source and candidate target tuple. Enumerate the base-field proportionality constants $\lambda_i\in F^\times$ for these factors and $\mu_j\in F^\times$ for the rational linear factors. For geometric linear factors match only lines with equal degree of definition, use compatible local field models, and keep their multipliers as field-valued unknowns. The branches add the equations
$$
 P_{B,i}f=\lambda_i H P_{A,i},\qquad
 \ell_{B,j}f=\mu_j\ell_{A,j}.
$$
In characteristic two include on $R_{A,i}$ the affine linear equation
$$
 \rho_{B,i} f|_{R_{A,i}}=\sqrt{\lambda_i}\rho_{A,i}.
$$
The polar equations ensure that the expression on the left is evaluated on $R_{B,i}$. All equations are linear or affine in $(f,H,\mu_j)$, with $H$ a separately variable map $U_A^*\to U_B^*$.

A transporter $f_0$ for the selected marks and multipliers satisfies the system with $H_0=f_0^{-\mathsf T}$. Every solution can be written $f=f_0Z$ and $H=H_0W$. Substituting gives $P_{A,i}Z=WP_{A,i}$. For rational linear marks it gives $\ell_{A,j}Z=\ell_{A,j}$. For other linear marks the target multiplier divides by its nonzero value for $f_0$, giving exactly the source's field-valued line constraint. In characteristic two the transported radical functional introduces the same nonzero square-root multiplier on both sides and the source restriction is exactly $\rho_{A,i}Z|_{R_{A,i}}=\rho_{A,i}$. Thus whenever a branch has a genuine solution its projection onto $f$ is $f_0\mathcal V$. This is true without imposing $H=f^{-\mathsf T}$ during linear solving, and even when the ambiguity in $H$ has large dimension.

For source tuples satisfying the dimension bound, compute the target branch affine projection by Gaussian elimination. Skip inconsistent branches and projections of dimension larger than $C\log_q L$. Otherwise enumerate the at most $L^C$ maps $f$, and retain invertible ones. There are polynomially many tuples and branches because $d,k$ and $q$ are fixed constants and local coefficient field degrees are polynomial. The guarantee that a genuine branch projects to $f_0\mathcal V$ proves completeness. Every retained map still has to pass the actual tensor transporter equations.

For each retained $f$, solve the ordered matrix arrows from $M_A(v_j)$ to $M_B(fv_j)$ by deterministic constructive module isomorphism on the two vertex projections and the arrow operators. The resulting block-diagonal isomorphism gives $g,h$. If one exists, all such matrix pairs for this $f$ are a coset of $D^\times$. [Brooksbank and Luks, Testing Isomorphism of Modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

The determinants of $D^\times$ on $X,Y$ are computed from the $J$-filtrations. For each simple block $\operatorname{Mat}_{s_i}(K_i)$ of $D/J$, its central idempotent gives the dimension of its part of $J^aV/J^{a+1}V$ for $V=X,Y$. The sum of these dimensions divided by $s_i[K_i:F]$ gives the simple multiplicity $m_{V,i}$. Its contribution to the determinant pair is $(a_i^{m_{X,i}},a_i^{m_{Y,i}})$, where $a_i$ ranges over $F^\times$ by surjectivity of the finite-field determinant and norm. These contributions vary independently because quotient units lift through the nilpotent radical. Multiply the resulting subgroup of the fixed-size group $(F^\times)^2$ by $(\det g,\det h)$, append $\det f$, and take the union over the tested maps. This gives the exact profile.

## A balanced characteristic-two family requiring the singular-form method

Fix $F=\mathbb F_{2^a}$ with $a\ge2$. Choose arbitrarily large $m\ge7$, let $E=\mathbb F_{q^m}$, and take $\theta$ generating $E/F$. Let $L_0:E\to F$ be a linear functional with $L_0(1)=1$. Write
$$
 U=W_1\oplus W_2\oplus Ft,\qquad W_i=E^2,\qquad
 w_i=(x_i,y_i),\qquad \dim U=n=4m+1.
$$
Use $\operatorname{Tr}=\operatorname{Tr}_{E/F}$ in the three quadratics
$$
 \begin{split}
 Q_1(w)&=\operatorname{Tr}(x_1y_1)+t^2,\\
 Q_2(w)&=\operatorname{Tr}(x_2y_2)+t^2,\\
 Q_3(w)&=\operatorname{Tr}\big(\theta(x_1+x_2)(y_1+y_2)\big)+t^2.
 \end{split}
$$
Use determinant linear factors $\ell_1=L_0(x_2)$, $\ell_2=L_0(y_1)$, $\ell_3=L_0(x_1+y_1)$. The polar rank of each quadratic is $2m>2$, so it is absolutely irreducible. A product of two linear forms has polar rank at most two, including over the algebraic closure. All three polars and all three $\ell_i\otimes\ell_i$ kill $Ft$. Their common polar kernel is precisely $Ft$ since the trace pairing is nondegenerate.

On $U/Ft$ the sum $P_1+P_2$ is nonsingular. For a source affine solution, $Z$ preserves $Ft$, and $W$ preserves its annihilator, by the equations for $P_1,P_2$. Hence the induced operation on $U/Ft$ commutes with all three relative operators for $P_1+P_2$. The first two are the projections onto $W_1,W_2$. The third has the four blocks given by multiplication by $\theta$ on $E^2$. Thus $Z$ acts on the quotient by the same $E$-linear $2\times2$ matrix $D_0$ on both copies. The equations $\ell_1Z=\ell_1$ and $\ell_2Z=\ell_2$ imply $D_0=I$. Indeed a nonzero linear functional $L_0$ cannot vanish on the image of multiplication by a nonzero element of $E$, which is surjective. The first coordinate of $D_0$ is therefore the first coordinate projection, and the second is the second coordinate projection. The radicals $R_1=W_2\oplus Ft$ and $R_2=W_1\oplus Ft$ each have square-root functional $t$. Their fixed affine constraints force the $t$ coordinate of $Z$ to be $t$ on their sum, which is all of $U$. Thus the projected affine source space is $\{I\}$. Without these radical constraints, every map $Z=I+e_t\otimes\alpha$, with $e_t$ the $t$-direction vector and any $\alpha\in U^*$, solves the polar and line equations with $W=I$. Thus those equations alone admit an affine space of dimension at least $n$.

The marks occur together in one indecomposable pencil summand. Realize each $Q_i$ by an arrowhead of size $m+2$ with its corresponding $\ell_i$ as the scalar tail diagonal. The trace quadratic is a sum of $m$ products of independent paired linear coordinates, by choosing bases dual for the indicated trace pairing, and $t^2$ adds the one repeated linear coordinate $t$. Write $Q_i=u_i^{\mathsf T}v_i$ in these $m+1$ products. The arrowhead
$$
 A_i(w)=\begin{pmatrix}0&u_i(w)^{\mathsf T}\\-v_i(w)&\ell_i(w)I_{m+1}\end{pmatrix}
$$
has determinant $\ell_i^m Q_i$. Each $\ell_i$ is independent of the coordinates used by its $Q_i$. For the first two this follows from the other copy of $E^2$, and for the third a nonzero functional of $w_1$ alone cannot be a functional of $w_1+w_2$ and $t$.

Choose $x_2=y_1=1$, $y_2=0$, and $x_1\in F\setminus\{0,1\}$ in their embedded base-field copy. All three $\ell_i$ are nonzero. There are at most three forbidden values of $t^2$ from the equations $Q_i=0$. Since $q\ge4$, some $t$ makes all three quadratics nonzero. This gives an invertible base slice $v_0$ for the arrowheads.

After left normalization at $v_0$, each arrowhead is absolutely irreducible. Let $A=A_i(v_0)^{-1}$, let $e_0$ be the head coordinate, and let $e_z$ be the last tail coordinate, representing the shared $t$ variable. For every other tail $j$, the normalized operator span contains $Ae_0e_j^{\mathsf T}$ and $Ae_je_0^{\mathsf T}$ from the independent trace-product coordinates. It also contains $A(e_0e_z^{\mathsf T}-e_ze_0^{\mathsf T})$. Take a nonzero vector in an invariant subspace. A nonzero coefficient in a nonshared tail gives $Ae_0$ by the first generators. A vector supported only on $e_z$ gives $Ae_0$ by the combined generator. A vector with nonzero head gives every $Ae_j$ for nonshared tails. These independent vectors number more than two, so one has a nonzero nonshared tail and the subspace again contains $Ae_0$. The head entry of $Ae_0$ is nonzero by the inverse cofactor formula. Applying the generators now gives every $Ae_j$ and $Ae_z$, so the subspace is all of the arrowhead. This argument works over the algebraic closure. The three simple modules are pairwise nonisomorphic because their normalized determinant polynomials have distinct quadratic factors.

Join these three arrowheads by upper superdiagonal linear blocks vanishing at $v_0$, choosing each adjacent normalized extension nonsplit. For adjacent dimensions $s_1,s_2$, the splitting blocks have the form $H N_2(w)-N_1(w)H$ for a fixed $s_1\times s_2$ matrix $H$, by the graph description of an invariant complement. Their span has dimension at most $s_1s_2$, and the admissible blocks have dimension $(n-1)s_1s_2$, so deterministic linear algebra chooses blocks outside it. The joined module has only the prefix submodules. Indeed a submodule surjecting onto the last simple of a prefix must contain the previous prefix, or its image modulo the prefix two stages earlier would split the last adjacent extension. Apply induction to its intersection with the preceding prefix. The first simple occurs only once. Every nonzero endomorphism has zero kernel, as a nonzero image contains the first simple and a quotient by a nonzero prefix kernel lacks it. Its restriction to the first block is scalar by absolute simplicity, and subtracting that scalar makes its kernel nonzero and thus gives zero. The end algebra is $F$. Normalized endomorphisms are exactly ordered-pencil endomorphism pairs once the base slice is invertible, so this summand is indecomposable.

Fill the remaining $r=m-5\ge2$ dimensions by a separate $r\times r$ pencil
$$
 A_{\mathrm{high}}(w)=\operatorname{diag}(a_1(w),\ldots,a_r(w))+z(w)S,
$$
where $S$ is the cyclic shift and $a_1,\ldots,a_r,z$ are independent linear forms on $W_1\oplus W_2$, chosen with $a_i(v_0)=1$, $z(v_0)=0$. Such a list exists by extending a functional taking value $1$ at the nonzero quotient of $v_0$ and using independent functionals that vanish there. The base slice of this block is $I$. The normalized algebra contains the diagonal matrix units and $S$, hence all matrix units. Thus the block is simple. Its determinant is $\prod_i a_i+z^r$ in characteristic two. It is absolutely irreducible, since it is degree one in $a_1$ with coprime leading coefficient and constant term in the remaining variables. Independent coordinates preserve irreducibility after adjoining unused variables. The full pencil has a geometric determinant factor of unbounded degree, while the indecomposable arrowhead summand supplies all six low-degree marks.

The full tensor is concise. The base slice is invertible in the matrix modes, and the first two arrowheads together detect $w_1,w_2,t$ in their independent entries. There is no rank-one slice for large $m$. If any $\ell_i$ is nonzero the corresponding tail has rank $m+1$. If all vanish and $t\ne0$, every arrowhead has a nonzero shared variable, so at least two diagonal blocks are nonzero. If $t=0$ and only one of $w_1,w_2$ is nonzero, its unmixed arrowhead and the mixed one are nonzero. If both are nonzero, both unmixed blocks are nonzero. Rank of an upper triangular block matrix is at least the sum of its diagonal ranks, by the induced maps on the successive flag quotients. This exhibits balanced tensors in arbitrary bases with all selected polar and squared-line combinations singular and with no global bound on the geometric determinant-factor degrees.

The full pencil can even be balanced, concise, and identically singular. For $m\ge11$ replace the high-degree block by one of size $m-8$, and add two separate rectangular blocks of shapes $2\times1$ and $1\times2$. Take the first as a column of two independent linear forms and the second as a row of two independent linear forms. The vertex dimensions both remain $n$. Each rectangular block has no common kernel or proper common image in its respective dimensions, so the full tensor remains concise. Their combined rank over the rational function field is at most two in total vertex dimensions three. Thus the full determinant vanishes, and the three arrowheads still supply all six marks from their square regular indecomposable block.


## Scope

The theorem closes the exact determinant-profile task for the stated condition on a constant determinant-factor tuple and the dimension of its affine label projection. It leaves open universal extraction, including pencils where useful low-degree factors are embedded inside an indecomposable block with high-degree factors and no other qualifying tuple is available.

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
