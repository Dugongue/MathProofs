# Decoding fixed-Hessian tensor orbits without the hidden bases

Let $R$ be a finite field $k$, or $\mathbb Z/p^e\mathbb Z$ for $e\ge2$ with residue field $k=\mathbb F_p$. In the field case set $s=1$. In the ring case set $s=p^{e-1}$. Use the fixed-Hessian symmetric tensor construction at a declared input format $(a_1,a_2,a_3)$. The input to the algorithms below is an arbitrary dense trilinear array over $R$; the isomorphism action uses three independent invertible basis changes. In particular, a promised input need not be symmetric in its supplied coordinates. [Fixed-Hessian construction](https://github.com/Dugongue/MathProofs/blob/main/SymmetricFinalFour/Tensor.md)

**Theorem.** In deterministic polynomial bit time, a promised tensor in the ordinary orbit of an encoded tensor can be decoded to an ordinary field tensor on its three support quotients. The algorithm requires neither a transporter nor the displayed bases of the encoder. Two promised arrays from the declared format are equivalent exactly when their decoded tensors are equivalent. At odd residue characteristic there is also deterministic polynomial-time recognition of the entire ordinary orbit saturation of the format, among arbitrary arrays. All these claims are uniform in the residue field size and, for prime-power rings, in the precision.

Let $r$ be the sum of the extracted support dimensions. Decision and canonization on promised arrays take time
$$
 \operatorname{poly}(\text{input bit length})+|k|^{O(r^2)}
       \operatorname{poly}(\text{input bit length}).
 \tag{1}
$$
At odd residue characteristic the decision bound improves to $ |k|^{\widetilde O(r^{3/2})}$ times polynomial overhead, after recognition. The postprocessing term depends on the support sizes and has no dependence on the carrier dimension in its exponent. The same canonization algorithm works on arbitrary inputs in odd characteristic by first rejecting arrays outside the saturation.

## 1. Recovering the algebra from two contractions

Recall the carrier. Put $n_0=a_1+a_2+a_3$, $h_i=2^i(n_0+7)$, and
$$
 O_i=X_i\oplus X_i^*\oplus H_i,\quad \dim H_i=h_i,\quad
 K=\bigoplus_i O_i,\quad L=K\oplus\langle z_1,z_2,z_3\rangle .
$$
The fixed split pairing $\beta_i$ on $O_i$ pairs each input direction with its dual and pairs the two halves of $H_i$. The marked symmetric form $C_t$ on $L$ consists of the original tensor $t$ on $X_1\times X_2\times X_3$, and $\beta_i$ on $z_i\times O_i\times O_i$, each copied to its argument permutations. All other summand triples are zero. The carrier over $R$ is $A=R1\oplus I$, $I=E\oplus Rz$, $E=L_R\oplus L_R^*\oplus Q$. The fixed middle metric $B$ is hyperbolic on $L_R\oplus L_R^*$ and is the prescribed form on $Q$. At odd residue characteristic $Q$ is zero or split hyperbolic. It is zero over fields. At residue characteristic two in the nonfield case it is the norm-one line. For $x,y\in E$,
$$
 xy=B(x,y)z+s\,C_t(\bar x_L,\bar y_L,-),\qquad Iz=0.
 \tag{2}
$$
Use the identification $k\cong sR$ for the second term, valued in $sL_R^*$. The tensor is $F_t(x,y,v)=\lambda(xyv)$, where $\lambda$ selects the $z$-coordinate.

View the given array as a bimap $T^\flat$ from the first two modes to the dual of the third. On a promised array each of these input modes has an invertible contraction at some standard basis vector. In the encoder coordinates the perfect unit pairing identifies this contraction with left multiplication. The invertible left multiplications are exactly those with unit augmentation, since $I^4=0$. Modulo the maximal ideal the exceptional set is a hyperplane, and an invertible basis change cannot make it contain a whole basis. Scan both input bases to find invertible maps $L_u=T^\flat(u,-)$, $R_v=T^\flat(-,v)$. Define a multiplication on the output by
$$
 x*y=T^\flat(R_v^{-1}x,L_u^{-1}y).
 \tag{3}
$$
Its unit is $T^\flat(u,v)$. On the promise this is isomorphic to (2). In fact, write $T^\flat(x,y)=H(f(x)g(y))$ in hidden coordinates and put $a=f(u),b=g(v)$. Then $(ab)^{-1}H^{-1}$ is a unital algebra isomorphism for (3), by substituting the formulas for the two contraction inverses. This calculation uses only associativity in the hidden multiplication.

Recover the augmentation ideal $I$ as the kernel of the augmentation. Over the nonfield rings the encoder chose $\dim A$ prime to $p$, so the augmentation is $\operatorname{tr}L_x/\dim A$. Over a finite field of characteristic $p$, let $\dim A=p^j d$ with $p\nmid d$. The coefficient of $X^{\dim A-p^j}$ in $\det(X-L_x)$ is $-d\,\alpha(x)^{p^j}$, because $L_x-\alpha(x)I$ is nilpotent. Invert Frobenius on that coefficient and do this for each basis vector. Find $Rz=\operatorname{Ann}_I(I)$ by linear equations. On promised arrays this is a free rank-one direct summand and its reduction is detected by unit pivots. In (2), any element of $E$ annihilating $I$ has zero $B$-pairing with all of $E$, and the pairing is perfect. In the nonfield case the same argument applies to the residue algebra, where the second term of (2) vanishes. [Berkowitz, division-free characteristic polynomial](https://www.sciencedirect.com/science/article/pii/0020019084900188)

Choose any generator $z$ of this line. Triple products on $I$ take values in $sRz$, and their coefficients after division by $s$ give a symmetric form on $I/\mathfrak mI$. Quotient its contraction radical by linear algebra. The result is a form $C$ on a space of dimension $\ell=\dim L$, equal to the hidden $C_t$ up to an invertible coordinate change and one nonzero scalar. The latter comes from choosing the generator of the socle. At no stage have the marker coordinates been supplied.

## 2. Finding the three hidden marker hyperplanes

Write $\alpha_i$ for the unknown coordinate dual to the $i$-th marker in the hidden $C_t$. This section shows how to compute $K=\bigcap_i\ker\alpha_i$, then all three $\ker\alpha_i$ with their order. Work over the rational function field on three independent variables. For a supplied basis $e_1,\ldots,e_\ell$, put $v(T)=\sum_{j=1}^{\ell}T^{j-1}e_j$, $u(S)=\sum_{j=1}^{\ell}S^{j-1}e_j$. For each $j$ use the univariate pencil in $Z$
$$
 M_j(Z)=C(Zv(T)+u(S)+Ue_j,-,-)
 \quad\text{over } k(S,T,U).
 \tag{4}
$$
Its three marker roots are
$$
 R_{ij}=-\frac{\alpha_i(u(S))+U\alpha_i(e_j)}
                    {\alpha_i(v(T))}.
 \tag{5}
$$
Every denominator is nonzero. The roots are distinct already at $U=0$. Otherwise $\alpha_i(v(T))/\alpha_h(v(T))$ would equal the same rational function in the independent variable $S$, making that rational function constant and contradicting independence of the covectors.

Outside the three roots $C(x,-,-)|_{K\times K}$ has rank $\ell-3$. Indeed its $H_i$-blocks are invertible, and the block on the $X_i,X_i^*$ has the form
$\left(\begin{smallmatrix}D&A\\A^{\mathsf T}&0\end{smallmatrix}\right)$
with $A$ block diagonal and invertible. At the single $i$-th root the $H_i$-block vanishes, so that restriction has rank at most $\ell-3-h_i$. Adding back the three marker rows and columns increases rank by at most six. Since $h_i>12$, this is strictly below $\ell-9$. These bounds hold over the algebraic closure of $k(S,T,U)$ as well.

Choose one nonzero $(\ell-9)$-minor $\Delta(Z)$ of (4) using generic linear elimination. Every marker root is a root of $\Delta$. Use the following exact rank-splitting procedure to discard additional roots of this minor.

- Start with the monic normalization of $\Delta$ as a branch modulus $f$. A branch maintains row and column index sets $I,J$ of equal size whose subdeterminant is nonzero at every root of $f$. Start with the empty sets. The numerator of a candidate Schur-complement pivot at $(i,j)$ is, up to sign, the minor with row and column $i,j$ appended to $I,J$. This determinant formula holds at every root on that branch.
- For a numerator $b(Z)$, put $g=\gcd(f,b)$ and $g_*=\gcd(f,g^{\deg f})$. This puts the entire prime-power factor for each vanishing root into $g_*$. If $g_*=f$, the pivot is zero at every branch root, so skip it. If $g_*=1$, the pivot works at every root, so extend $I,J$. Otherwise split the branch into the coprime moduli $g_*$ and $f/g_*$. Skip this candidate on the first branch and take it on the second. Each branch may start its scan again at the current rank, retaining the already selected rows and columns.
- If no candidate works, the selected minor size is the exact rank at all roots of that branch. If it reaches $\ell-9$, the branch can be discarded. Multiply the final moduli of the branches whose rank is below $\ell-9$.

At most $\deg\Delta$ nonempty branches can survive or terminate, since every proper split partitions the factors of $\Delta$ into coprime sets. Each path takes at most $\ell$ pivots and tests at most $\ell^2$ appended minors per pivot. All ranks are computed by determinants of submatrices of the given pencil, so coefficients from arbitrary sequences of pivot inversions never enter the representation. The retained product has exactly the three roots (5), even if the initially chosen minor has irreducible or inseparable extraneous factors. Its monic squarefree support polynomial is consequently
$$
 f_j(Z,U)=\prod_i(Z-R_{ij}).
$$
Take $\partial_U f_j(Z,0)$, meaning first differentiate in $U$ and then set $U=0$. The resulting degree-at-most-two polynomials are columns of a $k$-linear map into $k(S,T)[Z]_{\le2}$. At $Z=R_{i j}|_{U=0}$, the value on a vector $x$ is a nonzero rational scalar times $\alpha_i(x)$. This follows by differentiating the product and using distinctness of the roots at $U=0$. Its kernel is exactly $K$. Clear denominators and equate coefficients to find this kernel using ordinary $k$-linear algebra.

With $K$ known, restrict the same pencils to $K\times K$ and use the full determinant. In hidden coordinates it is a nonzero constant times
$$
 \prod_{i=1}^3 \alpha_i(Zv(T)+u(S)+Ue_j)^{h_i+2a_i}.
 \tag{6}
$$
Indeed the determinant of the $X,X^*$ corner is $(-1)^{n_0}\det(A)^2$, independent of $D$, and the split $H_i$ contribute powers $h_i$. The three multiplicities $m_i=h_i+2a_i$ are strictly ordered because consecutive gaps between the $h_i$ exceed $2n_0$. Thus they label the factors $Z-R_{ij}$. To extract the support of roots of multiplicity at least $m$, take the gcd of (6) with its Hasse derivatives in $Z$ of orders $1,\ldots,m-1$, then take squarefree support. A root of multiplicity $b$ annihilates all Hasse derivatives of order below $b$ and survives in the $b$-th with nonzero value. Successive quotients of the three nested support polynomials isolate the three labeled linear factors. Differentiating their constants in $U$ gives $\alpha_i(e_j)/\alpha_i(v(T))$. Divide this row by any of its nonzero entries to get the $i$-th marker covector over $k$, up to a nonzero scalar. In particular it is possible to choose representatives $w_i\in L$ of the three individually labeled marker lines in $L/K$.

### Exact arithmetic

The determinant and rank-splitting steps have deterministic polynomial bit cost. The determinants have degree polynomial in $\ell$ in four fixed indeterminates. A reduced numerator or denominator uses polynomially many monomials. For the univariate gcds one can use subresultants with fraction-free determinants. Each branch modulus or rank-test gcd has a primitive polynomial in $k[S,T,U,Z]$ dividing $\Delta$, so its degrees remain within those of that determinant. The saturation power has exponent at most $\deg\Delta$, so it too has polynomial degree. The coefficient contents and rational-function reductions use gcd recursively in a fixed number of variables, using the same subresultant degree bound and clearing contents at each stage. In each fixed-variable reduction the defining determinants have order at most the input degrees, so the number of field operations and the representation degrees are polynomial. The implementation uses no polynomial factoring subroutine. [von zur Gathen, exact polynomial arithmetic](https://doi.org/10.1137/0213050)

For clarity, squarefree support of a monic split polynomial $f$ can be computed even in small characteristic. If $f'\ne0$, then $f/\gcd(f,f')$ is squarefree, supported on the factors whose multiplicities are prime to $p$. Take its least common multiple with the recursively computed support of $\gcd(f,f')$. If $f'=0$ and $f$ is nonconstant, its multiplicities are all multiples of $p$. Its coefficients are $p$-th powers in $k(S,T,U)$ because the polynomial splits there. Take the $p$-th root and recurse. For a reduced rational coefficient that is a $p$-th power, the reduced numerator and denominator, up to nonzero constants, have exponent vectors divisible by $p$; take the root by dividing exponents and applying inverse Frobenius to their coefficients. All these steps decrease the univariate degree. For arbitrary inputs, a failed exact root extraction or specialization can simply reject. All promised inputs pass the arithmetic checks.

## 3. Extracting the ordered support tensor

Let $D$ be the radical of $C|_{K^3}$. In hidden coordinates $D=\bigoplus_i(D_i^0\oplus X_i^*\oplus H_i)$, with $D_i^0$ the contraction radical in role $X_i$. On $K\times D$ the slice $C(w_i,-,-)$ equals a nonzero scalar times the hidden $\beta_i$ and is unaffected by the choice of lift of $w_i$. Its left kernel, projected to $K/D$, is the sum of the two support roles other than $i$. Indeed in $O_i$ pairing against $X_i^*\oplus H_i\subset D$ leaves only vectors in $X_i^*$. All other $O_j$ pair to zero. Intersect the projected kernels for the two labels other than $i$ to get the $i$-th support space. Restrict the induced trilinear form to their ordered product. The output is exactly the support tensor in some bases, up to a common nonzero scalar that an ordinary transporter can absorb in one mode.

This proves the promised decoder. Two originals at the declared format are equivalent precisely when their supported tensors are, since quotient maps extend independently over contraction radicals. The encoder lifts field equivalences, so decoded equivalence also implies ordinary equivalence for arbitrary presentations of the ring outputs. Exhausting the three general linear groups on the small support proves (1). Canonization takes a canonical representative on those supports, pads its kernels to the declared dimensions, and re-encodes it. At odd $p$, Grochow–Qiao IV, Theorem 2.1 sends the decoded instance to alternating matrix space congruence of length $O(r)$. Theorem I.4 of Ivanyos, Mendoza, Qiao, Sun and Zhang then gives the stated $ |k|^{\widetilde O(r^{3/2})}$ decision bound. [Grochow–Qiao IV](https://arxiv.org/html/2306.16317#S2) · [Ivanyos et al., Theorem I.4](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf)

## 4. Odd-characteristic recognition of the entire orbit saturation

Here $2$ is a unit. The procedure first runs the preceding decoding algorithms, rejecting invalid dimensions, failed factorizations by the specified exact operations, and inconsistent ranks. The following tests give a sufficient acceptance certificate and pass on every promised input.

**Field markers.** Recover the true marker representatives in the full space $L$. Use the provisional slices $B_i^0=C(w_i,-,-)|_{K\times D}$ to compute
$D_i=D\cap\bigcap_{j\ne i}\ker B_j^0(K,-)$. In a hidden frame write $w_j=z'_j+b_j$, where $z'_j$ is the unknown true marker with the chosen quotient coordinate. If $d\in D_i$, then $C(w_i,w_j,d)=B_i^0(b_j,d)$ for $i\ne j$, and $C(w_i,w_i,d)=2B_i^0(b_i,d)$. The terms involving three vectors in $K$ vanish by the radical condition, and terms involving two true markers vanish. Solve these linear equations for replacements $c_j\in K$ for $b_j$. Then $w'_j=w_j-c_j$ differs from its true marker by a vector in $\bigoplus_i D_i^{\perp_{\beta_i}}\subseteq D$. Its one-marker slices $\beta_i'=C(w'_i,-,-)|_{K^2}$ are consequently the exact marker pairings. Recover $O_i$ as intersections of the radicals of the other two pairings on $K$. Use the preceding two-marker equations again with $d$ ranging over $O_i$ and $\beta_i'$ in place of $B_i^0$. The new unknown shifts lie in $D$, so all cubic error terms still vanish, and nondegeneracy on $O_i$ recovers them uniquely.

Verify that the resulting markers and $K$ give a direct sum. Check that the marker pairings are supported on their respective $O_i$, split and nonsingular of the prescribed sizes, and that every value on two or more markers is zero. Require $D=\bigoplus_i D_i$, $D_i^{\perp_{\beta_i'}}\subseteq D_i$, and $\dim(O_i/D_i)\le a_i$. Finally require that the induced form on $K/D$ is supported only on argument triples with one vector in each role. These checks imply that $C$ is a marked form $C_t$ in some basis. For each block a hyperbolic basis can be chosen with the isotropic subspace $D_i^{\perp_{\beta_i'}}$ as part of its dual half. Then $D_i$ is that subspace's perpendicular, and the remaining hyperbolic pairs split into unused input pairs and $H_i$; the unrestricted supported part defines $t$. No search for a hyperbolic basis is needed for recognition. Over an odd finite field, a nonsingular symmetric form of even dimension $2d$ is split exactly when $(-1)^d\det B$ is square. One proof splits off an isotropic plane whenever the dimension is at least three: in a diagonal ternary form the two translated sets of scalar multiples of squares intersect since each has size $(|k|+1)/2$. Finish with the elementary binary discriminant criterion.

**Ring presentation.** Check that the normalization (3) is a commutative associative unital algebra, and that the calculated augmentation gives an ideal $I$ complementary to the unit. Check that its annihilator inside $I$ is spanned by one primitive element $z$; unit pivots and Smith elimination over the prime-power ring suffice. Take a free complement $E$ to $Rz$ in $I$. Verify that every product of two $E$-vectors has its $E$-component in $sE$, and write
$$
 xy=B_1(x,y)z+s\,b(\bar x,\bar y).
$$
Check that $B_1$ is perfect. On $\bar E$ form $C_1(x,y,v)=\bar B_1(b(x,y),v)$, test symmetry, and take its contraction radical $D_1$. In the field case bars denote the identity. On genuine inputs this gives the same cubic as the triple-product step. Changing the complement to the annihilator alters the form $B_1$ only by a correction supported on $L_R\times L_R$, which does not affect perfectness or its pairing against the contraction radical. Changing the socle generator scales the form by a unit.

Require $D_1^\perp\subseteq D_1$ for $\bar B_1$, $\dim(\bar E/D_1)=\ell$, and that $D_1/D_1^\perp$ is the split middle form of the prescribed dimension. Apply the field marker tests to $C_1$ on $\bar E/D_1$. These conditions suffice to identify the full carrier. Choose a residue isometry of $\bar B_1$ to the standard pairing that induces the accepted identification of the marked cubic on the quotient. Such an extension follows by splitting the isotropic $D_1^\perp$ into hyperbolic pairs with chosen dual quotient basis and identifying the split middle form. Over the ring, lift that isometry arbitrarily, then correct it to an exact isometry of $B_1$ using a square root of its Gram error. Explicitly, if a chosen lift $P_0$ has $B_1^{-1}P_0^{\mathsf T}BP_0=1+E_0$, right multiply by $(1+E_0)^{-1/2}$. Its coefficients have only powers of $2$ as denominators and the series truncates over the nilpotent maximal ideal. Over the field no correction is required.

The resulting map, extended by the unit and socle, preserves the displayed multiplication. Its residue preserves $C_1$, and $b$ is uniquely specified by $C_1$ and the perfect residue pairing, so it preserves the products in $sE$ even at the full ring precision. The $z$-coordinates are preserved by the exact Gram isometry. This proves sufficiency. The previous steps show necessity on promised copies, so the tests recognize the saturation deterministically. Finding witnessing hyperbolic frames by a finite field search is also possible in time polynomial in $|k|$ and the input size. The polynomial bit bound for recognition uses only the split test and does not require that search.

## Relation to earlier work

The fixed-Hessian theorem gives isomorphism hardness and uses the marker ranks to prove reflection given a transporter. Here the pencil rank splitting makes those ranks computationally accessible in arbitrary bases, before finding any transporter. The preceding asymmetric final-digit recognizer recovers two radicals from a square-zero unitization and cannot directly identify these three marker hyperplanes. The present decoder recovers them even when $p=2$, where univariate multiplicities can be inseparable. Gharahi–Ottaviani characterize a class by a pure-power Hessian determinant. The common Hessian determinant here gives the unit chart but does not by itself identify the hidden support tensor. The smaller decoded field instance accounts for the parameter dependence in (1). The proof is in prose and priority remains open. [Previous final-digit algorithms](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Algorithms.md) · [Gharahi–Ottaviani, Theorem 2](https://arxiv.org/html/2510.07404v1) · [Grochow–Qiao IV](https://arxiv.org/html/2306.16317)

Run `python Algorithms.py` for finite controls. It checks 36 rank gaps on dimension-149 slice matrices after elementary congruences over $\mathbb F_2,\mathbb F_3,\mathbb F_5$. It recovers the three multiplicity labels $22,42,82$ using Hasse derivatives over $\mathbb F_3,\mathbb F_5,\mathbb F_7$. In a diagonal pencil over $\mathbb F_2$, the gcd rank splitting keeps both high-rank-drop roots and discards a spurious irreducible component. These controls test the indicated subroutines.
