# Constructive rational binary-pencil isomorphism with moving slice symmetries

**Theorem.** Ordinary tensor isomorphism of all rational binary pencils, including rectangular and singular pencils, has a deterministic polynomial-bit-time algorithm that returns a transporter when one exists. For determinant-one isomorphism, the same is true when the regular elementary divisors all split over the rationals. On all rational binary pencils, determinant-one isomorphism reduces in deterministic polynomial time to a polynomial disjunction of weighted number-field norm-image tests, allowing rational power images as norms from $\mathbb Q$. The two-conjugate-root regular case is polynomial-time Turing equivalent to rational quadratic norm membership.

Here regular means a square pencil $A(x,y)$ with nonzero determinant polynomial, including pencils whose two slices are dependent. A transporter is a triple of invertible rational matrices satisfying $P A(R(x,y)^{\mathsf T})=B(x,y) Q$. The determinant-one test is independent of whether tensor coordinates use transposes or inverses. These are informal proofs.

## Finite versus moving slice symmetries

The earlier proof handles a determinant divisor with at least three distinct geometric roots by enumerating the finite set of rational projective matches, using fixed-variable elimination. At a fixed slice map, evaluation at a common nonsingular point gives one matrix similarity problem over the rationals. Constructive rational canonical form provides strict witnesses or proves their absence. The determinant image of the source strict stabilizer is

$$
 \prod_{(f,\ell):\,m_{f,\ell}>0}
       N_{\mathbb Q[t]/(f)\,/\,\mathbb Q}
         \big((\mathbb Q[t]/(f))^\times\big)^\ell .
$$

Here $m_{f,\ell}$ is the number of primary blocks with annihilator $f^\ell$. Both determinant coordinates receive the same multiplier from a strict automorphism. Consequently when all roots are rational, this image is the rational $g$-th powers, with $g$ the gcd of the block lengths. At a fixed determinant-one slice map an exact $g$-th-root test therefore completes the algorithm. The missing cases were one or two geometric roots, where a finite enumeration of projectivities does not apply. [Prior rational norm and finite-stabilizer proof](https://github.com/Dugongue/MathProofs/blob/main/TensorIsomorphismAdvances/PENCILS.md) · [Mackey–Mackey–Mehl–Mehrmann on Möbius changes of elementary divisors](https://eprints.maths.manchester.ac.uk/2089/) · [Pervouchine on pencil orbits over $\mathbb C$](https://doi.org/10.5802/jolt.345)

## A strict transporter for one homogeneous Jordan block

At a root with linear vanishing form $l$, use blocks $l I_\ell+m N_\ell$, where $m$ complements $l$ and $N_\ell$ is a nilpotent Jordan block. Suppose a slice change expresses its two coefficients in the target frame as $a l'$ and $b l'+c m'$, with $a,c\ne0$. Put $U=aI+bN_\ell$. The transformed pencil is $l' U+m' cN_\ell$. The matrix $N'=cN_\ell U^{-1}$ has the same Jordan block size. In the Jordan basis with $N_\ell e_i=e_{i-1}$, set

$$
 S=( (N')^{\ell-1}e_\ell,\ldots,N'e_\ell,e_\ell).
$$

Then $N'S=SN_\ell$ and $\det S=(c/a)^{\ell(\ell-1)/2}$ by triangularity. Taking $P=S^{-1}$ and $Q=PU$ gives an actual strict transporter. Its determinant pair is

$$
 \det P=(a/c)^{\ell(\ell-1)/2},\qquad
 \det Q=(a/c)^{\ell(\ell-1)/2}a^\ell.
$$

This is valid over the rationals or any field used for a block below. The scalar shear $b$ has no effect on these determinants. The determinant conversion back to original input bases is exact. If $P_A A=A_{\rm can}Q_A$ and $P_B B=B_{\rm can}Q_B$, the chosen strict transporter on canonical pencils must have determinant pair
$(p_0,q_0)=(\det P_B/\det P_A,\det Q_B/\det Q_A)$ to give determinant one on the original first two modes. The original transporter is $P_B^{-1}P_{\rm can}P_A,Q_B^{-1}Q_{\rm can}Q_A,R$.

## One or two rational roots

Compare elementary-divisor block length lists at the roots. In a proposed matching reorder both lists compatibly. With one root choose each frame $(l,m)$ of determinant one. An arbitrary determinant-one map matching the roots has dilation $a$ on $l$, dilation $a^{-1}$ on the second form, and free shear. Set $E=\sum_{\ell}\ell(\ell-1)$, summing over every block. The block formula gives determinants $a^E,a^{E+n}$, where $n$ is the matrix side.

With two roots choose frames $(l_1,l_2)$ of determinant one in the matched orders. At the roots choose complements $m_1=l_2$ and $m_2=-l_1$. Try both target root orders. The slice map has dilations $a,a^{-1}$ on the ordered pair, so the determinant pair on canonical pencils is

$$
 (a^{E_1-E_2}, a^{E_1-E_2+n_1-n_2}),
 \qquad E_i=\sum_{\ell\ {\rm at}\ i}\ell(\ell-1),\quad
 n_i=\sum_{\ell\ {\rm at}\ i}\ell.
$$

For one root put $e=E,d=n$, and for two put $e=E_1-E_2,d=n_1-n_2$. In either case $g\mid e$. Allowing all strict stabilizer corrections, the determinant-one test becomes exactly

$$
                      p_0\in(\mathbb Q^\times)^g,\qquad
                      a^d=q_0/p_0\ \text{for some }a\in\mathbb Q^\times.
$$

When $d=0$, the second test means $q_0=p_0$. Negative exponents are treated by inversion. Exact integer root tests on reduced numerator and denominator, with the sign check, suffice. Build the chosen slice map with zero shear. After constructing its canonical strict transporter, choose a rational $g$-th root of $p_0/a^e$. Scalar multiplications on the blocks realize this correction by Bézout among the block lengths. To keep the exponents polynomially bounded, search residues modulo the first block length $\ell_0$ using steps given by the other lengths. A shortest path to $g\bmod\ell_0$ uses at most $\ell_0-1$ steps. Adjust the coefficient of $\ell_0$ to obtain exactly $g$. This constructs determinant-one witnesses with polynomial bit length. All split pencils with one or two geometric roots are covered, including a single root at infinity in the original coordinates.

## Two conjugate roots

Every nonsplit divisor with two geometric roots is supported on the roots of one irreducible rational quadratic. The two pencils must have the same quadratic splitting field $K$. This is decidable by testing whether the quotient of the discriminants is a rational square, which also gives an explicit identification of the fields. Choose in each pencil a root form $l_X$ with coefficients in $K$, write its conjugate $\bar l_X$, and set $F_X=\binom{l_X}{\bar l_X}$, $\delta_X=\det F_X$ and $\Delta=\delta_A/\delta_B$. The determinants $\delta_X$ are anti-invariant under the nontrivial conjugation, so $\Delta\in\mathbb Q^\times$. Try both choices of root form on the target. All rational slice maps for one matched order are exactly

$$
     R=F_A^{-1}\operatorname{diag}(a,\bar a)F_B,\qquad a\in K^\times.
$$

Conjugation swaps both rows, so these maps are rational. Their determinant is $N_{K/\mathbb Q}(a)/\Delta$. After picking a nonsingular evaluation, rational primary cyclic blocks are represented by $\mathbb Q[t]/f^\ell$, where $f$ is the irreducible quadratic for that evaluation. They can be converted constructively to the restriction of scalars of blocks $l_X I_\ell+\bar l_XN_\ell$. The substitution $t\mapsto\lambda+s$ into $K[s]/s^\ell$, with $\lambda$ the chosen root of $f$, induces the isomorphism on primary blocks. In fact $f(\lambda+s)$ is $s$ times a unit and a rational polynomial vanishes under substitution exactly if $f^\ell$ divides it. Equality follows also by the dimension $2\ell$. Converting the complementary form to $\bar l_X$ uses the homogeneous block calculation above. A match exists for ordinary TI exactly when both pencils have the same multiset of lengths after the root correspondence. Construct it with $a=1$.

For an SL slice map we need $N(a)=\Delta$. On a block the strict transporter over $K$ has determinant pair $((a/\bar a)^{\ell(\ell-1)/2},(a/\bar a)^{\ell(\ell-1)/2}a^\ell)$. Restricting scalars takes the norm of each determinant. Thus before strict corrections the entire canonical determinant pair is $(1,\Delta^{n/2})$. The actual determinant-one conditions are consequently

$$
        N(a)=\Delta \text{ for some }a\in K^\times,\qquad
        q_0/p_0=\Delta^{n/2},\qquad
        p_0\in N(K^\times)^g.
$$

Here $g$ is the gcd of the lengths at one geometric root. The last condition is an exact rational root test followed by a norm membership test on each possible signed root. This uses at most three ordinary quadratic norm queries per matched order. With a norm witness, scalar multiplication on the primary blocks realizes the strict correction via the same bounded Bézout construction. The polynomial preprocessing does not include solving a general rational norm equation.

The quadratic norm test already appears on $2\times2\times2$ rational pencils. Let $A(x,y)$ be multiplication by $x+\alpha y$ on $K=\mathbb Q(\alpha)$, with $\alpha\notin\mathbb Q$, and let $B=DAD^{-1}$ for $\det D=c^{-1}$. The pencils have identical determinant polynomials. An SL slice map preserving a matched root choice has $\Delta=1$ and $N(a)=1$, hence acts by determinant-one left multiplication on the canonical pencil. One exchanging the roots has $\Delta=-1$, hence multiplies the determinant polynomial by $-1$ and cannot occur in an SL transporter. For the root-preserving correspondence, the remaining strict multiplier is the determinant of multiplication by an element of $K^\times$. It must be $c$. The given instance is therefore equivalent to $c\in N(K^\times)$ by a polynomial-time construction. This establishes exact mutual polynomial-time Turing reducibility for the quadratic two-root class and rational quadratic norms, with a many-one reduction in the norm-to-TI direction.

## Singular and rectangular pencils for ordinary TI

For an arbitrary pencil, its rank-drop divisor means the reduced set of projective points where its rank is less than its generic rank (r). Recover it without constructing an entire Kronecker basis. Among the evaluations at ((1,0),(1,1),ldots,(1,min(m,n))), one has rank (r) because some nonzero (r)-minor has degree (r). Put that point at infinity and choose a maximal minor nonzero there. Write that minor as a polynomial in the affine coordinate, factor it over the rationals, and check which factors (f) actually cause a rank drop. For each factor compute rank over (mathbb Q[t]/(f)). An elementary way to bound this step in bits is to replace every entry by its rational multiplication matrix. The resulting rational rank is (deg(f)) times the desired rank, and the matrix entries have polynomial bit length. Homogenizing the product of the retained factors gives the reduced rank-drop divisor. The rank-zero case is the zero pencil.

The Kronecker classification identifies that divisor with the support of the regular elementary divisors. A slice projectivity permutes their support and preserves their lists of lengths at the matched points. This follows by applying the local ring coordinate isomorphism to the Smith forms at these points. The same slice projectivity preserves the left and right minimal indices. Indeed the dimensions of the homogeneous coefficient spaces of polynomial kernel vectors are invariant under substitution, and the first differences of those dimensions count minimal indices up to each degree. Apply this argument to both the pencil and its transpose.

When the support has at least three points, the earlier fixed-variable projective matching enumerates every candidate using the reduced rank-drop form. With one or two support points, test one representative for each Galois-compatible correspondence. The rational and quadratic frame constructions above give these representatives, without imposing determinant one. When there are no points, test the identity. The Kronecker classification and the preservation facts imply that choosing one representative for a specified correspondence is enough. For each candidate strict equivalence is polynomial-bit-time module isomorphism over the rational path algebra of the two-arrow Kronecker quiver. Concretely a module has the vector space (mathbb Q^noplusmathbb Q^m), the two vertex projections and the two coefficient matrices acting by off-diagonal blocks from the first vertex space to the second. An invertible module homomorphism respects the projections and supplies the two strict matrices. This also returns a witness for singular and rectangular inputs. [Kronecker classification](https://www.stat.uchicago.edu/~lekheng/courses/309/books/Bernstein.pdf) · [Chistov–Ivanyos–Karpinski on module isomorphism](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf) · [Rational polynomial factorization](https://doi.org/10.1007/BF01457454)

## The singular and rectangular determinant-one cases

In addition to the regular blocks, the Kronecker form has right singular blocks of mode dimensions $(\ell,\ell+1)$ and left singular blocks of mode dimensions $(\ell+1,\ell)$. The dimension-zero convention applies when $\ell=0$. Every determinant-one slice map $R$ acts on either singular block with a strict canonical transporter whose two determinants are both one. To see this for a right singular block, use directional differentiation

$$
 L_{\ell}(v)=\partial_v:
 \operatorname{Sym}^{\ell}((\mathbb Q^2)^*)\longrightarrow
 \operatorname{Sym}^{\ell-1}((\mathbb Q^2)^*).
$$

The divided-power monomial bases give the standard singular pencil. Pullback by $R^{-1}$ obeys $\partial_{Rv}\rho_\ell(R)=\rho_{\ell-1}(R)\partial_v$. Both representations have determinant one since the determinant of the $k$-th symmetric power in dimension two is a power of $\det R$. The transposed block uses transposes and inverses, so its determinants are also one. For the zero blocks take identities.

The strict determinant image can be calculated on the Kronecker decomposition. Consider the representation of the Kronecker quiver with a linear map for each slice. By the finite-dimensional Krull–Schmidt theorem its endomorphism algebra modulo the Jacobson radical is a product of matrix algebras, one for each distinct indecomposable type, over the residue field of that type's local endomorphism algebra. A regular block with primary polynomial $f$ and length $\ell$ has local endomorphism ring $\mathbb Q[t]/f^\ell$, hence residue field $K_f$. A singular block has scalar endomorphisms. In the usual bidiagonal pair its two coefficient equations identify the top and bottom shifted square submatrices of the domain endomorphism with the same codomain endomorphism. The recurrence makes their entries constant along diagonals, and the two boundary zero strips eliminate the off-diagonals. The $\ell=0$ blocks are one-dimensional at their supported vertex.

The kernel of the map on units to the semisimple quotient consists of one plus radical elements. These are unipotent at both vertices because the radical is nilpotent, so contribute determinant one. The regular residue group $\mathrm{GL}_{m_{f,\ell}}(K_f)$ contributes the same multiplier $N_{K_f/\mathbb Q}(\det U)^\ell$ at both vertices, as seen from its $f$-adic filtration. A singular type of dimensions $(u,v)$ contributes all pairs $(z^u,z^v)$ with $z\in\mathbb Q^\times$, the determinants of its multiplicity matrices. These images have lifts by block-scalar multiplication on one copy of the corresponding indecomposable. This computes the whole strict image.

With at least one singular block, pick its dimensions $(u_0,v_0)$ and put $\delta_0=v_0-u_0$, so $\delta_0$ equals $1$ or $-1$. It can absorb any residual determinant ratio $q/p$ via its scalar. More precisely a pair $(p,q)$ lies in the strict image if and only if its normalized coordinate

$$
 C(p,q)=p(q/p)^{-u_0/\delta_0}
$$

lies in the image of the resulting one-coordinate subgroup. The map $C$'s kernel is exactly the scalar subgroup of the chosen block. Every regular block still contributes $N_{K_f/\mathbb Q}(K_f^\times)^\ell$. Each singular type $(u_j,v_j)$ contributes rational powers of exponent $u_j-u_0(v_j-u_j)/\delta_0$.

When the rank-drop support has at least three points, enumerate the finitely many rational projective matches and their determinant-one lifts. Compute a strict transporter for each. Apply the one-coordinate test to the required determinant correction. With one or two rational support points, take the canonical forms in the split regular frames above, together with the standard singular blocks. In each valid root correspondence the regular determinant pair varies as $(a^e,a^{e+d})$. After applying $C$ this adds the rational power image of exponent $e-u_0d/\delta_0$. With two conjugate roots use the quadratic frame, require $N(a)=\Delta$, and divide by $C(1,\Delta^{n_{\rm reg}/2})$ before the strict test, where $n_{\rm reg}$ is the size of the square regular part. The singular blocks' canonical transporter has determinant pair $(1,1)$ throughout. With empty support there is no regular block, and the identity slice map suffices because every determinant-one slice change has a determinant-one strict realization on the canonical form.

Constructing the canonicalizers can be reduced to strict module isomorphism by assembling abstract Kronecker blocks from their invariants. The degrees of the left and right minimal indices follow from ranks of the homogeneous kernel coefficient matrices, up to degree at most the pencil dimensions. The regular primary lengths can likewise be computed by kernel dimensions of the affine pencil on $(\mathbb Q[t]/f^j)^n$. The dimensions, divided by $\deg f$, are $(n-r)j + \sum_i\min(e_i,j)$, where the $e_i$ are the local Smith orders and $r$ is the generic rank. Taking differences recovers the list of positive orders. Their sum is at most $\min(m,n)$ since each maximal minor has degree at most that bound. All these checks therefore use polynomial-size rational linear systems.

In the split case every remaining norm subgroup is a rational power subgroup, including the extra slice dilation subgroup when present. Their product is the subgroup of powers of the gcd of their exponents. If all exponents vanish, this means $\{1\}$. Signed powers are handled by inverses. The residue-search Bézout method already used above applies since all exponents are polynomially bounded in the dimensions. It produces the slice dilation and determinant corrections with polynomial bit length, and the chosen singular block then corrects the remaining determinant ratio. This proves constructive polynomial-bit-time SL-TI for every split rational binary pencil as stated.

## Complexity and evidence

The determinant and its homogeneous root multiplicities can be computed by interpolation and rational univariate factorization after evaluating at a nonsingular rational point. Among $(1,0),(1,1),\ldots,(1,n)$ at least one works for a nonzero homogeneous binary form of degree $n$. Computing primary chains, changing coordinate frames and assembling block matrices use polynomial-size exact linear algebra. Their bit bounds follow from the bounds for rational factorization, rational canonical form and solving linear systems. Powers and block substitutions have exponents at most polynomial in $n$, rational or quadratic entries, and polynomial bit length. For three or more distinct rational roots, enumerating image triples also suffices to obtain the projective slice candidate set from the preceding proof. For each candidate SL lift, an exact common-evaluation similarity and the bounded block-scalar correction give a witness of polynomial length.

Federated lookup queried all 103 registered source catalogs for rational canonical forms, matrix pencils, Jordan blocks, strict equivalence, Smith normal form, determinant cosets, reduced norms and Kummer theory. The published predecessor supplied the strict norm-image formula and the finite-stabilizer case. No Lean certification or publication-priority claim is made here.

Ja’Ja’ and Atkinson already studied the ordinary three-mode orbit classification of pencils. The ordinary algorithm here is a constructive rational bit-complexity treatment of that classical classification. The determinant-one contribution is the exact arithmetic prescription for all slice stabilizer dimensions and the polynomial-time split case, including the singular blocks. Derksen, Klep, Makam and Volčič studied the two-mode special-linear action on matrix tuples over algebraically closed fields. Plût, Fouque and Macario-Rat studied the related finite-field problem for quadratic forms with simultaneous congruence. [Ja’Ja’](https://doi.org/10.1137/0137052) · [Atkinson](https://carleton.ca/scs/research/scs-technical-reports/technical-reports-1983/tr-29-another-addendum-to-kroneckers-theory-of-pencils/) · [Derksen–Klep–Makam–Volčič, Sections 5.2 and 7.2](https://arxiv.org/abs/2109.09418) · [Plût–Fouque–Macario-Rat](https://arxiv.org/abs/1406.3163)

The accompanying exact Python solver handles the one- and two-rational-root branch. Its elementary Jordan algorithm takes a basis of each `ker (C−λI)^j` and keeps vectors whose terminal vectors under `(C−λI)^(j−1)` enlarge the terminal span, processing lengths in descending order. The terminal space at length `j` is `ker(C−λI) ∩ im(C−λI)^(j−1)`. Selecting extensions in this order yields one chain per required Jordan block. Independence follows by applying the largest power that survives in a supposed chain relation and then using independence of its terminal vectors. Different primary eigenspaces are independent. Before returning a yes answer the solver verifies the determinants and both coefficient equations over exact rationals.

Run `python check_pencils.py --self-test` to reproduce 21 planted transporter tests, three no instances, and one nonsplit scope check. The tested yes cases include repeated blocks, equal and unequal root multiplicities, nonintegral rational basis changes and a root-order reversal. For the CLI, send a JSON object with keys `A` and `B`, each a pair of square coefficient matrices whose entries are integers or fraction strings.
