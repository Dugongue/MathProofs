# Determinants from multiplication by a finite extension field

Informal mathematics. Fix $F=\mathbb F_q$ and set $m=q-1$. The constructions work on raw rectangular matrix pencils, with the convention $M_B(fx)=hM_A(x)g^{-1}$. They apply to pencils that have no square determinant. There are two sufficient reductions.

1. Suppose the ordered-slice adjoint algebra is a field $E$. Write $a=\dim_E X$, $b=\dim_E Y$ for the two matrix-mode dimensions. For $\gcd(a,b,m)=1$, a logarithmic bound on the determinant-active matrix widths of one computed algebra gives a deterministic reduction from SL-TI to one ordinary TI instance, with no width bound on $a$ or $b$.
2. For the same raw field promise, a polynomial bound on the number of normalized projective coordinates of that computed algebra gives a deterministic polynomial-time algorithm for the complete determinant triple, for arbitrary $a,b$. A growing rectangular example has no determinant factors to analyze and satisfies the second result for all of its parameters.

## 1. The raw data and the ambient action

For $M:V\to\operatorname{Hom}_F(X,Y)$, use the algebra of pairs $(s,t)$ with $tM(v)=M(v)s$ for every $v$, with componentwise composition. Solve its equations by linear algebra. If this algebra is a field $E$, its projections via $s,t$ make $X,Y$ into $E$-modules, provided both have positive dimension; a unital field action on a nonzero space is faithful. Each slice is then $E$-linear. Choose $E$-bases, and identify
$$
Z_M=\operatorname{Hom}_E(X,Y)\simeq E^{ab},\qquad W_M=M(V)\subseteq Z_M
$$
as explicit $F$-linear spaces. If only the source has the field promise, reject a target whose computed algebra or dimensions disagree. Compare the fields by deterministic fixed-characteristic arithmetic and use one finite-field model for both. The field promise, its degree, and the $E$-bases are computed from the raw tensor. [Ivanyos–Qiao, constructive finite-field algebra decomposition](https://arxiv.org/abs/1708.03495).

A genuine transporter acts on the two adjoint projections by conjugation by $g,h$, so they induce the same $\sigma\in\operatorname{Gal}(E/F)$. Both $g,h$ are semilinear with respect to $\sigma$. The ambient map $u:Z_A\to Z_B$ is $u(z)=hzg^{-1}$, also semilinear with respect to $\sigma$. It maps $W_A$ onto $W_B$. Include the two $E$-module actions on $X,Y$, the module action on $Z$, and its evaluation $Z\times X\to Y$. The latter ties the unique $u$ to the actual $g,h$. Include the original slice map and its factorization $V\to W\hookrightarrow Z$, so all maps on $W$ are forced.

If the label map $M$ is injective, $f$ is identified with the restriction of $u$ to $W$ through $M$. Account for the known change of basis. In general, ranks must agree, and $V/\ker M$ is identified with $W$. Any chosen quotient map lifts to an invertible $f$. If $\ker M$ has positive dimension its determinant can be chosen freely and independently of $g,h$, by taking one basis vector of the kernel to a suitable nonzero scalar multiple of the corresponding target vector. When deciding SL-TI, omit the label determinant equation in this case. If $M=0$ on both sides, the problem has an immediate positive answer, including zero-dimensional modes. A difference in full input format or a zero pencil only on one side rejects. The remaining proof may therefore assume positive matrix-mode dimensions and $W\ne0$.

## 2. Semilinear extension with a computed algebra of multipliers

Consider arbitrary paired $F$-subspaces $W_A,W_B$ of copies of $E^k$ with $k=ab$ in the application. Compute
$$
A=\{z\in\operatorname{End}_E(E^k):zW_A\subseteq W_A\}.
$$
Its units are precisely the $E$-linear invertible maps of the ambient space that preserve $W_A$. Indeed any invertible ambient endomorphism taking $W_A$ into itself gives equality by dimensions, so its inverse also belongs to $A$. The algebra is a computed $F$-linear space of matrices. Its radical $J$ and semisimple quotient
$$
A/J\simeq\prod_j\operatorname{Mat}_{d_j}(K_j)
$$
are obtained by fixed-characteristic finite-algebra algorithms. Here $K_j$ are finite extensions of $F$. Each $d_j\le k$. For example, a Wedderburn–Malcev complement exists because the quotient is separable over $F$. The $d_j$ nonzero pairwise orthogonal diagonal units of a factor give nonzero independent $E$-linear projections on $E^k$.

For every Frobenius power $\tau$ test whether $\tau(W_A)$ has an $E$-linear isomorphism onto $W_B$ induced by an ambient invertible map, and find one if so. Use an ordered representation with the inclusion $W\hookrightarrow E^k$ as an arrow, the source and target vertex projections, and multiplication by named generators of $E$ as loops on the ambient vertex. The constructive module isomorphism algorithm then gives exactly the desired $E$-linear part. This only tries $[E:F]$ field powers. The same procedure with target $W_A$ computes one representative $r_\tau$ of each feasible source semilinear coset. Denote by $\sigma_0$ the field part of one source-to-target reference $s$, and take target representatives $s r_\tau$. A genuine $u$ maps the corresponding frame labels by its field part, since the group of source semilinear stabilizers has kernel $A^\times$ in its projection to $\operatorname{Gal}(E/F)$. [Brooksbank–Luks, constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf).

## 3. Read several determinants on the same semilinear map

Both $Z_A=E^k$ and $W_A$ are $A$-modules. For $R=Z_A$ or $W_A$, let $e_{R,j}$ be the total multiplicity of the natural simple module of factor $j$ in the radical layers $J^iR/J^{i+1}R$. These numbers are computable from matrix units on those layers. For a unit $v$ of $A$ its determinant on $R$ is
$$
\det_F(v|R)=\prod_j N_{K_j/F}(\det_{K_j}\overline v_j)^{e_{R,j}}.
$$
Indeed the radical filtration is invariant, and on a simple summand the determinant over $F$ is the norm of its determinant over $K_j$. For a requested exponent $\ell_R$, a factor is active if $\ell_R e_{R,j}\not\equiv0\bmod m$. Let $w$ be the maximum $d_j$ among all active factors used for the requested lines. A factor with zero exponent requires no determinant readout.

For each active factor choose one simple copy in a radical layer in which it appears, using the explicit semisimple module decomposition. An $A$-unit preserves this copy as a subspace and commutes with its $K_j$-action. On each source frame transport all of these inclusions, quotients and $K_j$-actions through $r_\tau$. On each target frame transport them through $s r_{\tau'}$. Keep the field bases in the resulting scalar sorts calibrated by those choices. Add one label per frame, even if the transported diagrams happen to coincide. Choose an element $\alpha$ of degree $[E:F]$. Mark the source frame by $\tau(\alpha)$ in the shared field sort and the target frame by $\sigma_0\tau'(\alpha)$. Such an element is obtained by deterministic finite-field algorithms. [Shoup, fixed-characteristic construction](https://www.shoup.net/papers/detirred.pdf).

If $u$ carries a source frame $\tau$ to a target frame $\tau'$, the field label forces
$$
v=(s r_{\tau'})^{-1}u r_\tau\in A^\times.
$$
The field part is the identity because its action on $\alpha$ is the identity, and it preserves $W_A$ by construction. Conversely every ambient semilinear transporter carries the frames as indicated by its field part. The actual map between each pair of corresponding selected simple copies acts in their calibrated coordinates by $\overline v_j$. The $K_j$ field basis pins are consistent because $v$ is an $A$-unit. The original ambient field $E$ remains free to act by Frobenius.

Attach the $K_j$ exterior algebra to each selected copy, and read the norm of its top-line multiplier by powers of lines and the exponent $(|K_j|-1)/(q-1)$. These operations use polynomial size in the input and $2^{d_j}$. Combine the resulting scalar lines with exponents $e_{R,j}\ell_R$ to obtain $(\det_F(v|R))^{\ell_R}$ in the frame. Across frames use maps to one common line with respective source and target scalar calibrations $(\det_F(r_\tau|R))^{\ell_R}$ and $(\det_F((s r_{\tau'})|R))^{\ell_R}$, using the appropriate designated bases of $R,R'$. The multiplier on the common line is exactly $(\det_F(u|R\to R'))^{\ell_R}$. A field label prevents comparing the wrong two frames, which is needed when inactive factors are omitted. The identity for the common scalar holds for every correctly matched frame by multiplicativity of determinant. Every transporter therefore extends consistently across all the common lines.

The frame incidence makes this one fixed-signature typed tensor system. The primitive idempotents of an auxiliary coordinate algebra index the frames. Their map to the shared field sort records their Frobenius labels. Direct sums of each role carry the corresponding coordinate actions, and incidence maps link each frame to its inclusions, quotients, and norm-chain data. Coordinate bases on top lines choose structure constants and impose no restriction on those line maps. Only a final vector pin prescribes the common scalar. The compiler applies once to the entire system, retaining all the original data and hence coupling all readouts to the same transporter. Construction size is polynomial in the input and $2^w$. [Typed tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4).

## 4. Convert the ambient determinant into both matrix-mode constraints

Choose matching $E$-bases for the two matrix modes and fix their expansion to $F$-bases using one fixed basis of $E/F$. In these coordinates write $g=G\sigma$ and $h=H\sigma$. Put $\delta=\det_F(\sigma|E)$. Let $C_g,C_h$ be the explicit changes from expanded bases to the original input bases. Then
$$
\det_F g=C_g N_{E/F}(\det_E G)\delta^a,\qquad
\det_F h=C_h N_{E/F}(\det_E H)\delta^b .
$$
The $E$-linear part of $u$ on $E^{ab}$ has determinant $(\det_E H)^a(\det_E G)^{-b}$. Its $F$-determinant is the norm of this value, while the semilinear coordinate action contributes $\delta^{ab}$. Consequently
$$
(\det_F h)^a(\det_F g)^{-b}
 = C_h^a C_g^{-b}(\det_F u)\delta^{-ab}.
$$
Here $\det_F u$ uses the ambient $F$-basis obtained from the fixed $E$ coordinates. The scalar $\delta$ is one when $[E:F]$ is odd. In even degree it equals the determinant of $\sigma$ on the unique quadratic subfield: in a normal basis a Frobenius generator is a full cycle, and its powers have the same sign as on that quadratic subfield. Attach its two-dimensional exterior algebra so that $\delta$ depends on the actual $\sigma$.

Common scalar changes $(g,h)\mapsto(cg,ch)$ preserve the original tensor relation and do not change $u$. Their determinant correction values are $(z^a,z^b)$ with every $z\in F^\times$, since the finite-field norm of $c$ is surjective. When $\gcd(a,b,m)=1$, this subgroup equals the kernel of $(x,y)\mapsto y^a x^{-b}$. Indeed the latter is surjective by Bézout and the scalar correction map is injective, so both groups have size $m$. Thus the ratio one condition decides whether both matrix determinant values can be corrected to one. Use Section 3 for the actual determinant of $u$ on $Z$, along with the label determinant on $W$ if the label map is injective. The latter includes its input-basis calibration. Combining this with the free kernel correction in Section 1 gives the first reduction.

Independently, if $a,b=O(\log L)$ one can instead read each matrix determinant directly by its $E$-exterior algebra, the norm chain and the Frobenius sign. With this change the same frame construction needs no coprimality hypothesis.

## 5. Construct the full determinant profile with small projective multiplier sets

Let
$$
D=\{\beta\in E\mid\beta W_A\subseteq W_A\}\subseteq E.
$$
This is a field by the same finite-unital-subring argument. It acts by ambient scalars in the center of $A$. Compute $D$ by linear equations. The number of one-dimensional $D$-subspaces of $A$ is $(|A|-1)/(|D|-1)$. Assume it is polynomial in the input length, or equivalently $q^{\dim_F A-[D:F]}$ is polynomial. This allows $|D|$ itself to be exponential. Obtain a $D$-basis by repeatedly adjoining an element outside the $F$-span of the selected $D$-multiples. Enumerate the nonzero coordinate lists with first nonzero entry one. If $\dim_D A=1$ there is only one such list, with no enumeration of $D$; otherwise the promised bound controls the field enumeration. Reject nonunits by checking ambient invertibility.

For every feasible field action $\sigma$, use the ambient $W_A\to W_B$ reference in Section 2 and compose it with each enumerated $A$-unit representative. This enumerates all candidate ambient transporters up to postmultiplying their output by a scalar $\beta\in D^\times$. In fact $\sigma$ preserves the unique subfield of its degree, and the scalar field of $W_B$ is the same $D$. Remove the coordinate Frobenius part to get an $E$-linear map $C$ on $Z$. View it inside
$$
\operatorname{End}_E(Y)\otimes_E\operatorname{End}_E(X^*)
\cong\operatorname{End}_E(\operatorname{Hom}_E(X,Y)).
$$
Its coefficient array as a two-factor tensor is obtained by permuting matrix indices. Rank one in that array is precisely decomposability as $H\otimes G^{-\mathsf T}$. If the rank is one, factor the array by elementary linear algebra. The factors must be invertible because $C$ is invertible. Rank one is invariant under a nonzero scalar multiple, so one exact check suffices for each enumerated class.

For a passing class obtain $g_0=G\sigma$, $h_0=H\sigma$, and the quotient label map by restriction to $W_A$. Every lift to a pair $(g,h)$ in this ambient class has the form
$$
g=cg_0,\qquad h=c\beta h_0,\qquad c\in E^\times,\quad \beta\in D^\times.
$$
Indeed, for a fixed nonzero decomposable array its two factors are unique up to opposite scalar. The quotient label map for $\beta$ is its reference followed by multiplication by $\beta$ on $W_B$. Thus relative to the three reference determinants, the attainable corrections are
$$
\left(
 v^{\dim_F W/[D:F]},
 z^a,
 z^b v^{[E:D]b}
\right),\qquad
v=N_{D/F}(\beta),\quad z=N_{E/F}(c).
$$
Each $v,z$ can be chosen independently in $F^\times$ by surjectivity of the two finite-field norms. If the label kernel is zero, convert quotient bases to raw label bases; if it is nonzero, replace the first component by an arbitrary scalar as in Section 1. This is the exact full determinant profile without ordinary TI queries. There is no restriction on $a,b$. All computation is deterministic polynomial on the stated promise. A rejected rank-one check omits only a class with no genuine matrix-mode lift.

## 6. A raw growing family with scalar multiplier algebra

Let $a,b\ge 2$ be arbitrary and distinct, put $k=ab$, and choose a prime $e>4k+2$ with $e=O(k)$, using Bertrand’s postulate and elementary search. Let $E/F$ have degree $e$ and let $\alpha$ be a field generator. Identify $E^k$ with the $b$-by-$a$ matrices over $E$ by the standard coordinate units. Take $v_1,\ldots,v_k$ as the coordinate vector basis and $v_{k+1}$ as the vector of all ones. Set $S=\{k+1,\ldots,2k+1\}$ and assign its distinct indices $s_j$ to these vectors. Use
$$
W=F^k\ \oplus\ \bigoplus_{j=1}^{k+1}F\alpha^{s_j}v_j
$$
as an injective label space. The pencil $M$ is the inclusion of $W$ into the indicated $E$-linear matrices, viewed over $F$ in any raw bases.

The adjoint pairs commuting with every coordinate matrix unit in $W$ must act on every copy of $E$ by a common $F$-linear map, by comparing their components across each coordinate arrow. Commuting with a corresponding matrix unit with coefficient $\alpha^{s_j}$ forces this common map to commute with multiplication by $\alpha^{s_j}$. This element is outside $F$, since $s_j<e$ and the minimal polynomial of $\alpha$ has degree $e$. Since $e$ is prime, $\alpha^{s_j}$ generates $E$, so the common map is multiplication by a scalar of $E$. Thus the raw ordered-slice adjoint is exactly the displayed field.

For an $E$-linear ambient operator preserving $W$, its values on $F^k$ show that it has the unique form
$$
A_0+\sum_j\alpha^{s_j}B_j,\qquad A_0,B_j\in\operatorname{Mat}_k(F),
\qquad \operatorname{im} B_j\subseteq Fv_j.
$$
Apply it to $\alpha^{s_\ell}v_\ell$. The terms with exponents $s_\ell+s_j$ have distinct powers below $e$, all outside $S\cup\{0\}$. They must vanish, so $B_jv_\ell=0$ for all $j,\ell$. Hence every $B_j=0$. The coefficient in degree $s_\ell$ shows $A_0v_\ell\in Fv_\ell$. Preserving the coordinate lines makes $A_0$ diagonal, and preserving the all-ones line makes it scalar. Therefore $A=F\cdot I$, and Section 5 applies with one projective class. The pair may be given in arbitrary bases, and an otherwise unpromised target is accepted only by a genuine transporter. Both relative mode sizes $a,b$ can grow, and these rectangular pencils have no determinant polynomial.

The construction uses the intrinsic adjoint field and keeps the original tensor equations throughout. Arbitrary residue tensors can have only the base field as ordered-slice adjoint and a large computed ambient algebra, so the unrestricted case remains open.
