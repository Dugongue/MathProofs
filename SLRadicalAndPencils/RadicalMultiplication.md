# Determinant-one tensor isomorphism for associative multiplication isotopes

A finite-dimensional algebra in this note is nonzero, unital and associative. The multiplication tensors may be given in independent raw bases. Over a fixed finite characteristic, the criterion below gives a deterministic polynomial-time many-one reduction to one ordinary tensor-isomorphism instance over the same field. It allows arbitrary Jacobson-radical length and multiplicities. A second result computes the exact determinant profile for every square-zero-radical multiplication isotope by a polynomial-time graph-isomorphism oracle reduction.

## Unit determinants and the raw basis calibration

Let $F=\mathbb F_q$, $A$ be an $F$-algebra, $J=\operatorname{rad}(A)$, and
$$
 S=A/J=\prod_i M_{n_i}(E_i).
$$
Write $\ell_i$ and $r_i$ for the total multiplicities of the natural simple left and right $S_i=M_{n_i}(E_i)$-modules on all the grades $J^k/J^{k+1}$, including $J^0=A$. Multiplication by a unit preserves the filtration. On the associated graded it descends to the quotient algebra. If a unit $u$ has residue $(u_i)_i$, then
$$
 \det_F L_u=\prod_i N_{E_i/F}(\det_{E_i}u_i)^{\ell_i},
 \qquad
 \det_F R_u=\prod_i N_{E_i/F}(\det_{E_i}u_i)^{r_i}.
$$
Indeed, on a natural module the determinant is the indicated field norm. Calculate $\ell_i$ on each grade as the $E_i$-dimension of the image of a standard $e_{11}$ acting from the left, and calculate $r_i$ with the right action. All quotient units lift to units because the kernel is nilpotent. Matrix determinants and finite-field norms are surjective. The exact images of the two unit actions and of inner algebra automorphisms are therefore
$$
 C_L=(F^\times)^{g_L},\quad C_R=(F^\times)^{g_R},\quad
 I=(F^\times)^{g_I},
$$
where
$$
 g_L=\gcd(q-1,(\ell_i)_i),\qquad
 g_R=\gcd(q-1,(r_i)_i),\qquad
 g_I=\gcd(q-1,(\ell_i-r_i)_i).
$$
The last formula uses $\operatorname{Ad}_u=L_uR_{u^{-1}}$ with the same $u_i$ in both factors. In particular, the left and right images need not agree.

For a raw bimap $T:U\times V\to W$, the ordinary action is $T'(P x,Q y)=R T(x,y)$. The determinant-one conditions are the same in the covariant convention. There is deterministic polynomial-time recognition and normalization to multiplication. Compute the adjoint pair algebra
$$
 \{(X,Y):T(Xu,v)=T(u,Yv)\text{ for all }u,v\}.
$$
For multiplication its two projections are the right and left regular operator algebras, up to the raw coordinate changes. On each mode, compare the evaluation module of its projected algebra with the left regular module of that algebra. A constructive module isomorphism gives a cyclic vector as the image of the identity. If the input is an isotope, these cyclic vectors $\alpha\in U,\beta\in V$ correspond to units because a one-sided inverse in a finite-dimensional unital algebra is an inverse. The slices $K_1=T(-,\beta)$, $K_2=T(\alpha,-)$ are invertible. In the output coordinates use multiplication $x*y=T(K_1^{-1}x,K_2^{-1}y)$. In hidden coordinates with $\alpha,\beta$ corresponding to units $a,b$, this product is $x*y=x(ab)^{-1}y$, hence is associative and unital. Verify explicitly that the slices are invertible and that the normalized table is associative and unital. These checks prove soundness on arbitrary inputs. In particular $(K_1,K_2,I)$ normalizes the raw tensor. [Brooksbank and Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

For two normalized algebras $A,A'$, every multiplication-tensor transporter has the form
$$
 (L_a\phi,R_b\phi,L_aR_b\phi)
$$
for units $a,b\in A'$ and an algebra isomorphism $\phi:A\to A'$. In fact, if $R(xy)=P(x)Q(y)$, then $a=P(1)$, $b=Q(1)$ are units by evaluating at $1$ in each argument, and $\phi(x)=a^{-1}R(x)b^{-1}$ is an algebra isomorphism by substitution. In the raw output bases put $r=\det_F\phi$ and $\lambda_i=\det K_i/\det K_i'$. The exact set of raw determinant triples is
$$
 \left\{(\lambda_1 u r,\lambda_2 v r,uvr):
             u\in C_L,\ v\in C_R,\ r\in\det_F\operatorname{Iso}_{\rm alg}(A,A')\right\},
$$
with the subgroups computed on the target. In particular special-linear isomorphism is equivalent to the three checks
$$
 \lambda_2\in C_L,\qquad
 \lambda_1\in C_R,\qquad
 (\lambda_1\lambda_2)^{-1}\in\det_F\operatorname{Iso}_{\rm alg}(A,A').
$$

## A determinant correction from the radical

Put
$$
 K=\{x\in J:xJ=Jx=0\},\qquad W_0=K/(K\cap J^2).
$$
This is an intrinsic $S$-bimodule because all elements of $J$ annihilate $K$ on both sides. Let $\varepsilon_i$ be the $i$-th simple central idempotent of $S$. The subgroup
$$
 C_{W_0}=
 (F^\times)^{\gcd(q-1,\{n_i n_j: \varepsilon_i W_0\varepsilon_j\ne0\})}
$$
consists of determinants of actual algebra automorphisms of $A$.

To prove this, choose a Wedderburn–Malcev section $S\hookrightarrow A$. The semisimplicity of $S\otimes_F S^{\rm op}$ follows from the finite-field separability of the centers. Choose an $S$-bimodule complement $U$ to $K\cap J^2$ in $K$, and choose a complement $V$ to $U$ in $J$ containing $J^2$. This is possible because $U\cap J^2=0$ and the bimodule category is semisimple. In $A=S\oplus U\oplus V$, every $S$-bimodule automorphism of $U$, acting as identity on $S$ and $V$, is an algebra automorphism. Mixed products with $U$ inside $J$ vanish, and $V^2\subseteq J^2\subseteq V$. Each simple constituent for $(i,j)$ is the natural module of a matrix algebra of size $n_i n_j$ over a finite extension $L/F$. The multiplicity-space group on this constituent acts with determinant $N_{L/F}(\det)^{n_i n_j}$. Independent multiplicity actions and surjectivity of norms give exactly the displayed correction subgroup from these automorphisms. If $J^2=0$, then $W_0=J$.

For $J^3=0$ one may add a further explicitly computable subgroup. Split $J=V_1\oplus J^2$ as an $S$-bimodule. Independently scale every nonzero $\varepsilon_i V_1\varepsilon_j$ and $\varepsilon_i J^2\varepsilon_j$ by a scalar $t_{k,i,j}\in F^\times$, where $k=1,2$ indicates the grade. This gives all automorphisms of this specified diagonal form subject to
$$
 t_{1,i,j}t_{1,j,l}=t_{2,i,l}
$$
whenever the corresponding product from $J/J^2$ into $J^2$ is nonzero. This is necessary by applying the equation to a nonzero product and sufficient by bilinearity and $J^3=0$. Product support is intrinsic in the grades. Let $P$ be the integer matrix of these exponent relations and $w$ the row of $F$-dimensions of the blocks. For a Smith form $UPV=D$, with missing diagonal entries interpreted as zero, the correction subgroup is $(F^\times)^{g_{\rm sc}}$, where
$$
 g_{\rm sc}=\gcd\left(q-1,\left\{(wV)_j
                \frac{q-1}{\gcd(q-1,D_{jj})}\right\}_j\right).
$$
In exponent coordinates modulo $q-1$, write the original vector as $V z$. Its $j$-th Smith coordinate $z_j$ must be a multiple of $(q-1)/\gcd(q-1,D_{jj})$, so the displayed gcd is exactly the determinant image. The determinant corrections used by the reduction are constructed from these exponents without computing a discrete logarithm. [Kannan and Bachem, polynomial Smith form with multipliers](https://doi.org/10.1137/0208040)

The block-scalar subgroup can matter even when both $I$ and $C_{W_0}$ are trivial. For $A=F[t]/(t^3)$, it is $(F^\times)^3$, since the square of a first-grade scalar acts on $J^2$. More generally, consider $A=F[x_1,\ldots,x_m]/(x_1,\ldots,x_m)^3$. Here $K=J^2$, and common degree-one scaling has determinant exponent $m+2\binom{m+1}{2}=m(m+2)$. For any fixed $q$, infinitely many $m$ satisfy $\gcd(m(m+2),q-1)=1$. Choose $m$ outside the two residues $0,-2$ for each odd prime dividing $q-1$, and odd if $2\mid q-1$, then apply the Chinese remainder theorem. The sufficient criterion therefore covers this family in unbounded dimension even though the other two correction subgroups are trivial.


## Matrix corners and a one-query reduction

Allow $C$ to be the product of $I$, $C_{W_0}$, and, if applicable, the block-scalar subgroup above. It is an explicitly computable subgroup of determinants of algebra automorphisms. Set $C=(F^\times)^g$ and $d=\gcd_i n_i$.

A full $d\times d$ system of matrix units in $A$ is obtained by lifting the diagonal inclusion of $M_d(F)$ in each simple quotient factor. An idempotent lift is explicit. For a quotient idempotent, lift an arbitrary element $x$ and replace it by $x^{p^a}$ for $p=\operatorname{char}F$ and $p^a$ at least the nilpotence index of $J$. The element $x^2-x$ lies in $J$ and commutes with $x$, so the replacement is idempotent. Lift the diagonal idempotents one at a time in the complementary corner, with the last the complement of their sum. For each $i$ choose $u_i\in e_iAe_1$ and $v_i\in e_1Ae_i$ lifting the inverse off-diagonal quotient pairs. Correct $v_i$ by left multiplication by $(v_i u_i)^{-1}$ in $e_1Ae_1$. After the correction $v_i u_i=e_1$, and $u_iv_i$ is both idempotent and a unit in its corner, hence equals $e_i$. Take $u_1=v_1=e_1$ and $e_{ij}=u_i v_j$. The corner $B=e_1Ae_1$ gives
$$
 M_d(B)\longrightarrow A,\qquad (b_{ij})\longmapsto\sum_{i,j}u_i b_{ij}v_j.
$$
This is a unital algebra isomorphism with inverse $a\mapsto (v_i a u_j)_{ij}$. Conversely any full matrix system of size $d$ implies $d\mid n_i$ for every $i$, by taking ranks in each simple quotient factor.

Any two full matrix systems of size $d$ in $A$ are conjugate. Indeed in each quotient simple factor, each diagonal idempotent has rank $n_i/d$ and the off-diagonal units give identifications of the corresponding subspaces. Choosing and transporting a basis of the first subspace gives a conjugation of the full units. Lift the quotient conjugator to an actual unit. The resulting two systems $e_{ij},f_{ij}$ coincide modulo $J$. Then $w=\sum_i f_{i1} e_{1i}$ is one modulo $J$ and satisfies $w e_{ab}=f_{ab} w$. It is an actual unit, and conjugates the systems.

Choose any basis in each corner $B,B'$, used identically on every matrix entry. Let $\kappa$ be the determinant of the entrywise basis matrix on $A'$ divided by that on $A$, each measured in its raw output coordinates. Any algebra isomorphism $\Phi:A\to A'$ can be conjugated by a target unit to align the matrix systems. It is then entrywise an algebra isomorphism $\psi:B\to B'$ and its determinant in entrywise bases is $(\det_F\psi)^{d^2}$. Conversely every such $\psi$ lifts entrywise. Consequently the determinant set modulo $C$ is exactly
$$
 \kappa\,\{(\det_F\psi)^{d^2}:\psi:B\overset{\sim}{\longrightarrow}B'\}\,C.
$$
This union of cosets is also the full determinant set because every value in $C$ is attained by a target automorphism. For a specified required algebra determinant $r_*$, the residual condition on $\psi$ is
$$
 (\det_F\psi)^{d^2} \,C=(r_*/\kappa)\,C
$$
in the cyclic group of order $g$. The character on the left has order $g/\gcd(g,d^2)$.

**Sufficient same-field reduction.** If $g\mid d^2$, a required algebra determinant occurs exactly when $r_*/\kappa\in C$ and $B\cong B'$. Compare quotient types first, so that the two inputs have the same $d$ whenever they could be isomorphic. For coordinatewise SL-TI, perform the two raw unit checks above and the indicated membership check with $r_*=(\lambda_1\lambda_2)^{-1}$. If these pass, return the ordinary TI instance on the corner multiplication tensors. If any check fails, return a fixed negative instance. In particular $q-1\mid d^2$ works for arbitrary radicals, even when the inner correction is trivial. The $C_{W_0}$ contribution also gives $C=F^\times$ for arbitrary radical length whenever $W_0$ has a constituent supported on two matrix-size-one factors. Examples include $F[t,x]/(t^n,tx,x^2)$ for arbitrary $n\ge2$.

A witness of the ordinary corner query normalizes to an algebra isomorphism. Lift it entrywise, correct its determinant using the exhibited target automorphisms, and choose the two target units as in the raw formula. This gives an actual determinant-one transporter in the given raw bases. The reduction concerns arbitrary radicals on the stated locus, and the residual corner determinant condition displayed above holds for all other matrix sizes as well.

## Computation and witnesses

Ordinary linear algebra over $F$ computes $K,J^2$, all grades once $J$ is given, and all the module multiplicities from a represented Wedderburn quotient. The algorithm of Ivanyos and Qiao, applied to the faithful left regular representation, computes the radical and the explicit quotient and lifts. It runs in deterministic polynomial time for fixed characteristic and Las Vegas expected polynomial time in the algebra input length and $\log q$ in variable characteristic. All membership checks for $(F^\times)^h$, $h\mid q-1$, are exponentiations to $(q-1)/h$. [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495)

The Wedderburn–Malcev section used for witnesses can be constructed from that quotient. Lift its orthogonal central idempotents successively, then lift matrix units in each corner by the preceding algorithm. In the first corner of a simple factor, choose a generator of its residue field. One elementary construction for an extension of degree $e$ takes the sum of elements of Frobenius periods $r^a$ for the distinct prime powers $r^a$ exactly dividing $e$. Find them by Frobenius nullspaces. If a Frobenius power $m$ fixes the sum, for each $r^a$ take a multiple of $m$ congruent to $m$ modulo $r^a$ and to zero modulo all the other prime powers. Such a multiple exists by the Chinese remainder theorem applied to its multiplier. It fixes every other summand, hence also the $r^a$ summand. Thus $r^a\mid m$ for all $r^a$. Compute the generator's separable minimal polynomial $f$. Lift the generator to $a$ and iterate $a\leftarrow a-f(a)f'(a)^{-1}$ in the commutative subalgebra generated by $a$. The derivative is a unit and each step squares the ideal containing the error, by the polynomial Taylor identity. The result is a root that gives the field section. Extend it by the lifted matrix units. All complements of bimodules used above are computed by solving for a bimodule projection, a linear system which has a solution by semisimplicity.

For an image subgroup generated by $h_i$-th powers, compute Bézout coefficients for $\gcd(q-1,(h_i)_i)$. To realize $z$ in that subgroup, first take a root of degree the gcd, then use the coefficients to prescribe its powers in each unit norm, multiplicity scalar norm or Smith-coordinate correction. If all $h_i\equiv0\bmod q-1$, the subgroup is trivial and no root is necessary. Otherwise one may use any nonzero representative exponent bound known from the construction. In the unit and detachable cases the gcd is at most $\dim_F A$. For the Smith-coordinate subgroup, one can avoid roots of superpolynomial degree as follows. In the setting $g\mid d^2$ the combined gcd is at most $d^2\le\dim_F A$. If it is necessary to correct a determinant not on this locus, the decision reduction above only calls for membership. Power roots of the indicated polynomial degree are found by finite-field polynomial factorization, deterministic in fixed characteristic and Las Vegas in general. Norm preimages in finite field extensions can be computed in deterministic polynomial time. A diagonal quotient matrix and its unit lift realize any prescribed norm in the unit formulas. On $U$, choose a matrix-unit model for one simple constituent via the represented semisimple enveloping algebra, and apply a scalar of the prescribed norm to one multiplicity coordinate. This implements all the claimed corrections. [Van de Woestijne, Theorem 7.1](https://math.leidenuniv.nl/scripties/Woestijne.pdf)

## Exact square-zero profiles with a graph-isomorphism oracle

Assume $J^2=0$. The extension is $S\oplus J$, with products $(s,x)(t,y)=(st,sy+xt)$. The following construction computes every determinant coset over the same field in polynomial time with colored graph-isomorphism queries, deterministically in fixed characteristic and with the same Las Vegas preprocessing in variable characteristic.

Write $e_i=[E_i:F]$ and, for each ordered pair $i,j$, put $b_{ij}=\gcd(e_i,e_j)$ and $l_{ij}=\operatorname{lcm}(e_i,e_j)$. Use a fixed field model for each degree occurring, using a field isomorphism for every center of that degree. For each degree $b_{ij}$ choose a standard model for the degree-$b_{ij}$ subfield in every eligible degree model. Frobenius and linear algebra give the subfields, and finite-field isomorphism gives the identifications. For a degree-$b_{ij}$ generator let $\alpha_i,\alpha_j$ be its images in the two centers. Decompose $\varepsilon_i J\varepsilon_j$ by the $b_{ij}$ tests
$$
 x\alpha_j=\alpha_i^{q^t}x,\qquad t\in\mathbb Z/b_{ij}\mathbb Z.
$$
The corresponding subspace dimension divided by $l_{ij}n_i n_j$ is a simple bimodule multiplicity $m_{ijt}$. Indeed $E_i\otimes_F E_j$ is a product of $b_{ij}$ copies of $\mathbb F_{q^{l_{ij}}}$. The simple field factors are identified by which $q^t$-power relates the two images on their common subfield. Matrix-unit actions identify the natural bimodule factor in each one. This computes the multiplicities without building a field that contains all the centers simultaneously. [Lenstra, Finding isomorphisms between finite fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

On the graph use an oriented cycle of length $e_i$ with positions $(i,a)$, of common vertex color $(n_i,e_i)$. Include the binary relation on ordered pairs $((i,a),(j,b))$ with label $m_{ij,a-b\bmod b_{ij}}$. Cycle adjacency and pair labels are distinct relation types. These are polynomial-size directed colored structures, convertible to ordinary colored graphs with an incidence vertex and separate initial and terminal roles for every ordered pair. The colors and cycle edges force any isomorphism to be a type-preserving permutation $\pi$ of cycles and a rotation $k_i$ on each. Preservation of the pair labels imposes exactly
$$
 m_{ijt}=m'_{\pi(i)\pi(j),\,t+k_i-k_j}.
$$
The ordered shifts have this sign because the image of $x\alpha_j=\alpha_i^{q^t}x$ has right center power $k_j$ and left center power $t+k_i$. Removing $k_j$ makes the relative shift $t+k_i-k_j$. These conditions are exactly the existence of an isomorphism of the radical bimodules along the given quotient permutation and center Frobenius powers. Each such graph isomorphism lifts to an algebra isomorphism, by the square-zero product formula and a constructive simultaneous-module comparison of the two radicals along the explicit quotient map. Quotient inner conjugation can be aligned by target inner automorphisms. The determinant subgroup of these corrections is $I$.

A graph-isomorphism decision oracle constructs one graph isomorphism if one exists, by pinning one vertex at a time. The same method obtains generators of the graph automorphisms. For each position of an ordered vertex list, fix all previous vertices and find a representative mapping that position to each possible point in its orbit. The representatives together with the next pointwise stabilizer generate the current stabilizer, which proves the claim by descending induction. Lift one reference isomorphism and every chosen automorphism generator. For the target algebra, all automorphism determinants are generated by determinants of these graph lifts together with $I C_J$, where $C_J=C_{W_0}$. To see completeness, first remove the graph image using products of lifts, then remove the quotient-inner part using a target unit. Move the image of the chosen Wedderburn–Malcev section back to that section by conjugation by a unit in $1+J$, which has determinant one. The remaining map is the identity on $S$ and an arbitrary $S$-bimodule automorphism of $J$. Its determinant is exactly in $C_J$. Every generator used is itself a genuine automorphism. [Wedderburn–Malcev conjugacy](https://doi.org/10.1007/978-1-4419-8616-0)

If $J\ne0$, the known subgroup $I C_J=(F^\times)^h$ has index at most $\dim_F A$. Computing the enlarged subgroup from the generator determinants therefore only requires a cyclic quotient of polynomial order. It can be represented by the map $z\mapsto z^{(q-1)/h}$, so one can compute the subgroup and a witness product by multiplication in that quotient. If $J=0$, match simple types directly and construct a reference isomorphism. Its possible corrections are generated by the explicit Frobenius cycles on each factor and swaps of equal types, together with inner conjugations. In either case the reference determinant times the computed group is the exact algebra-isomorphism determinant set. The raw formula then gives the whole tensor transporter determinant coset and the SL decision. Each colored graph query can be replaced by an ordinary TI query over $F$ by the usual graph-to-tensor reduction. [Grochow and Qiao, Section 3.2](https://arxiv.org/html/1907.00309#S3.SS2)

## Verification and scope

These are informal proofs. The raw recognition and regular-module norm calculations extend the existing semisimple and square-zero sign calculations. The new ingredients are the exact matrix-corner compression with correction groups, the intrinsic detachable radical quotient, and the graph-oracle construction for full determinant profiles across arbitrary finite fields. The one-query result holds when the computed determinant subgroup absorbs the full $d^2$-power image. The graph-oracle result has polynomially many queries and applies to all square-zero radicals. Publication priority for the stated refinements is unverified.

Bounded checks independently compared direct regular-matrix determinants with the predicted left and right exponents for 975 invertible block-triangular units over five finite fields. They also verified 59,049 equalities and inequalities for the Frobenius twist rule over a cubic finite field, and exhausted 98 scalar choices for the determinant weight in the truncated cubic example. These controls supplement the written proof.
