# A compact determinant mark for local Frobenius algebras

Let \(k\) be a fixed finite field. Let \(A\) be a finite-dimensional associative unital algebra with Jacobson radical \(J\), scalar residue \(A/J=k\), and one-dimensional right socle \(\ell=\{x:xJ=0\}\). Choose a two-sided square-zero ideal \(I\) by an isomorphism-invariant polynomial-time rule. For example, try the powers \(J^j\) in order and select the first meeting the conditions below. Put
\[
 B=\operatorname{Ann}_r(I)=\{a:Ia=0\},\qquad R=B/I,\qquad Q=A/B.
\]

**Theorem.** Fix \(c>0\). For based scalar-residue local Frobenius algebras with \(\dim R\le c\log_2(2+L)\), where \(L\) is the dense input length, a constant-size list of tensor records of polynomial dimension attaches a line that acts by the raw determinant of the algebra isomorphism. Every algebra isomorphism extends to the unpinned records, and every isomorphism of the records has its actual raw determinant on the line. Pinning that line to any prescribed nonzero scalar therefore gives one ordinary three-tensor isomorphism instance over \(k\). The construction uses no exterior algebra on \(I\), and no positive-dimensional exterior algebra when \(I=B\).

## 1. Exact determinant from the Frobenius pairing

The line \(\ell\) is a two-sided ideal. The left action of \(J\) on it is nilpotent, hence zero. Choose a basis \(s_0\) of \(\ell\) and \(\lambda:A\to k\) with \(\lambda(s_0)=1\). The pairing \((a,b)\mapsto\lambda(ab)\) is nondegenerate. Every nonzero right ideal meets \(\ell\), by taking the last nonzero term of its products with powers of \(J\). Thus \(aA\) for \(a\ne0\) cannot lie in \(\ker\lambda\), giving zero left kernel in the square Gram matrix.

The right annihilator \(B\) is a two-sided ideal containing \(I\). The pairing
\[
 I\times Q\longrightarrow k,\qquad (i,\bar a)\longmapsto\lambda(ia)
\tag{1}
\]
is perfect. Indeed, if \(\lambda(ia)=0\) for every \(i\in I\), then for fixed \(i\) one has \(\lambda(bia)=0\) for every \(b\in A\), since \(bi\in I\). Nondegeneracy implies \(ia=0\), so \(a\in B\). The left kernel is zero by nondegeneracy on \(A\). In particular \(\dim I=\dim Q=d\), say.

Let \(g:A_X\to A_Y\) be an algebra isomorphism, and write \(s\) for its socle multiplier in the chosen bases. There is a unique \(u\in A_X\) with \(\lambda_Y(g(a))=\lambda_X(au)\) for every \(a\). Evaluating on the source socle basis shows \(u\bmod J_X=s\). Right multiplication by \(u\) on \(Q_X\) has determinant \(s^d\) since its difference from scalar multiplication by \(s\) is nilpotent.

Choose bases of \(I,R,Q\) with lifts to an adapted basis of \(A\) in that order. Let \(K_X\) be the determinant of the adapted-to-original basis matrix, and \(G_X\) the Gram matrix of (1). Set \(\kappa_X=K_X/\det G_X\), and make the analogous definitions at \(Y\). The equation on products gives \(g_I^{\mathsf T}G_Yg_Q=G_X[R_u|_{Q_X}]\). The adapted matrix of \(g\) is block triangular. Taking determinants and changing to the raw bases yields
\[
 \det_{\rm raw}g=(\kappa_Y/\kappa_X)s^d\det g_R.
\tag{2}
\]
Empty Gram matrices and zero-dimensional determinants use \(1\).


## 2. The constant-size attachment

Record multiplication of \(A\), inclusion of \(\ell\) and of \(B\) into \(A\), and the quotient \(B\to R\). If \(R\ne0\), record multiplication of \(\Lambda R\), the degree-one embedding, and its top-line inclusion. Any map on this exterior algebra is forced by the induced \(g_R\), and the top line acts by \(\det g_R\). Its dimension is \(2^{\dim R}\).

Similarly use the polynomial algebra on \(\ell\) truncated above degree \(d\), with its multiplication and the degree-one and degree-\(d\) inclusions. Its degree-\(d\) line acts by \(s^d\) and the algebra has dimension \(d+1\). Use a fixed scalar line for either neutral contribution. Add a line \(D\) and a bilinear map from the two contribution lines to \(D\) with coefficients \(\kappa_X,\kappa_Y\) at the respective ends. Compatibility forces the multiplier of \(D\) to equal (2), exactly the determinant in the input bases. Every algebra isomorphism extends. Mark the source basis of \(D\) against \(\delta\) times the target basis to impose determinant \(\delta\).

The tensor list has constant size, and each array has order at most three and polynomial size. The same-field tensor-system compiler gives one ordinary comparison. Its decision equivalence is used here, and (2) applies to every typed isomorphism before compilation. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

For the rectangular multiplication cubic, keep \(D\) without its vector pin. It gives the actual raw algebra-isomorphism determinant line for coupling to the scalar multiplier on the same transporter. [Rectangular multiplication cubics](ExactCubicOrientation.md)

The radical-power recipe is polynomial-time recognizable. Find the unit by linear equations and test associativity. For \(n=\dim A\), take \(q^r\ge n\), where \(q=|k|\). On the stated class every \(a1+j\) has \(q^r\)-th power \(a1\). Compute these powers on the basis, read scalar values, and extend linearly to a candidate residue map. Verify multiplicativity, its value on the unit, and nilpotence of its kernel. These tests certify that the kernel is \(J\) and the residue is \(k\). All remaining spaces and constants are found by linear algebra.

## 3. Examples with large paired spaces

If the associated graded has perfect complementary products and odd socle degree \(2h-1\), then \(J^h\) is square-zero and half-dimensional. Equation (1) gives \(I=B\) for \(I=J^h\). This includes the standard graded algebras \(k\oplus V\oplus V^*\oplus kz\) attached to arbitrary symmetric trilinear forms \(\tau\) with zero common radical, with products \(vv'=\tau(v,v',-)\) and \(v\alpha=\alpha(v)z\) in positive degrees, with commutativity and the other products zero. Symmetry proves associativity, and the common-radical condition makes the quadratic products span \(V^*\).

For an example whose associated graded is not Frobenius, take the basis \(1,x,\ldots,x^{2h-1}\), \(h\ge2\), and a nonzero extra space \(Y\) with \(xY=0\) and \(yy'=q(y,y')x^{2h-1}\) for a perfect symmetric form \(q\). Its socle is \(kx^{2h-1}\). For \(I=J^h\) one has \(B=I\oplus Y\), so \(\dim R=\dim Y\) may be logarithmic. The associated graded has extra socle in degree one because the products of elements of \(Y\) have moved to higher degree.

### A nongraded family with no determinant correction

Over \(k=\mathbb F_3\), let \(p\equiv2\pmod4\), \(p\ge6\), and set
\[
 A_p=k[x,y]/(x^p,\ y^3+x^{p-1}y).
\]
The monic relation in \(y\) gives the basis \(x^i y^j\) with \(i<p,\ j<3\). The relation replacing \(y^3\) by \(-x^{p-1}y\) raises total degree, so the associated graded is \(k[x,y]/(x^p,y^3)\). In particular it has perfect complementary products with odd socle degree \(p+1\). Directly, the simultaneous annihilator of \(x,y\) is spanned by \(x^{p-1}y^2\). Thus the square-zero ideal \(J^{(p+2)/2}\) is self-annihilating and its dimension \(3p/2\) is odd.

In \(A_p\), cubes of elements in \(J^2\) contain only pure powers of \(x\). Indeed, a normal monomial with \(y\)-degree \(1\) in \(J^2\) has positive \(x\)-degree, and its cube is zero by the relation. A monomial with \(y\)-degree \(2\) has cube zero because \(y^6=0\). In characteristic three the cube map is additive on this commutative algebra. An element of \(J\) with nonzero \(x\)-linear part has nonzero initial cube in degree \(3\). An element with nonzero \(y\)-linear part and zero \(x\)-linear part has a nonzero \(x^{p-1}y\) cube term that cannot cancel. The associated graded has a cube-zero element \(y\) outside \(J^2\), while \(A_p\) has none. Hence \(A_p\) is not isomorphic to its associated graded.

If \(g\) is an automorphism, its linear terms have the form \(g(y)=b y\bmod J^2\), \(g(x)=a x+c y\bmod J^2\), with \(a,b\ne0\). The form of \(g(y)\) follows since \(g(y)^3\in J^p\), whereas a nonzero \(x\)-linear part gives a nonzero degree-three cube. In the image of the defining relation, the coefficient of \(x^{p-1}y\) is \(-b^3+a^{p-1}b\). Cubes of higher terms cannot change this coefficient. The degree-\(p\) initial term of \(g(x)^{p-1}g(y)\) gives the second summand, using the displayed associated graded. Therefore \(a^{p-1}=b^2=1\), which implies \(a=1\) over \(\mathbb F_3\). The socle multiplier read on degree \(p+1\) is \(a^{p-1}b^2=1\). Formula (2) now gives determinant one for every automorphism. Reflecting one basis vector at the target gives an ordinarily isomorphic pair all of whose isomorphisms have determinant minus one in the two bases. Thus the determinant pin distinguishes these based comparisons without any odd automorphism for correction.

These are written proofs without Lean kernel verification.
