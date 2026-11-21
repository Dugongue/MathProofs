# Bounded-degree proofs for cubic equivalence and jet-algebra isomorphism

The intrinsic jet-algebra reduction preserves more than the existence of an isomorphism. It admits explicit polynomial substitutions with bounded-degree ideal certificates in both directions. For cubics, the substitution degrees are 3 and 2, and the certificate degrees are 6 and 33. This transfers Polynomial Calculus, Nullstellensatz, and real Sum-of-Squares refutation degree, and it gives circuit-size translations for the Ideal Proof System. As a consequence of the lower bounds of Galesi, Grochow, Pitassi, and She, square-free commutative cubic equivalence has instances requiring degree linear in the number of form variables. The corresponding jet algebras of dimension \(N\) require degree \(\Omega(N^{1/3})\).

## 1. The equation systems

Fix a field \(F\), a form degree \(d\ge3\), and \(n\ge2\) variables. Work with formal homogeneous polynomials \(f,g\in\operatorname{Sym}^d V\). The system \(\mathcal C\) has matrix variables \(S,T\), the equations \(ST=TS=I\), and all coefficients of \((\operatorname{Sym}^d S)f-g=0\). Use column matrices for maps on linear forms.

Let
\[
 A_f=\operatorname{Sym}(V\oplus Fz)/(J^{d+1},zV,f-z^d),
\]
where \(J\) is the positive-degree ideal. Use the basis consisting of the ordinary \(V\)-monomials of degrees \(0,\ldots,d\) and \(z,z^2,\ldots,z^{d-1}\). In particular, the degree-\(d\) basis contains the ordinary monomials only. The second algebra \(A_g\) has the corresponding basis. The system \(\mathcal A\) has matrices \(P:A_f\to A_g\) and \(Y:A_g\to A_f\), both inverse identities, both unit equations, and the multiplicativity equations for each map on all pairs of its source basis elements. All equations have degree at most two. These are full ungraded algebra-isomorphism equations.

A polynomial has a degree-\(b\) ideal certificate from input equations \(h_i=0\) if it is an explicit sum \(\sum_i u_i h_i\) with \(\deg(u_i h_i)\le b\) for all summands. In the estimates below, a linear combination takes the higher of the bounds being combined, and multiplication by a polynomial of degree \(k\) adds at most \(k\) to the bound. Vector and matrix identities are read entrywise.

**Theorem.** There is a substitution from the variables of \(\mathcal A\) to polynomials in those of \(\mathcal C\) of degree at most \(d\) whose pulled-back axioms have degree-\(2d\) ideal certificates. In the opposite direction, there is a degree-two substitution whose pulled-back axioms have degree-\(b_d\) ideal certificates, where \(b_d=(d+1)^2+3d+8\). Both transformations and the local certificates are constructible in polynomial time for each fixed \(d\) on explicit coefficient input.

Adding multiplicativity of \(Y\) introduces no extra power beyond degree five over the two inverse identities and multiplicativity of \(P\). For fixed source elements \(u,v\) of \(Y\), write \(w=Y(u)Y(v)\). The difference \(uv-P(w)\) has a degree-four certificate, by replacing \(u,v\) with \(PY(u),PY(v)\) and applying the bilinear multiplicativity equations of \(P\) to \(Y(u),Y(v)\). Then
\[
 Y(uv)-w=Y(uv-P(w))+(YP-I)w
\]
gives the claimed degree-five certificate. Likewise unit preservation of one map and the inverse identities imply unit preservation of the other in degree two.

## 2. Lifting the form equations

Map \(P\) to homogeneous substitution by \(S\) on \(V\), fixing \(z\) and \(1\). On ordinary monomials of degree \(k\) the entries are those of \(\operatorname{Sym}^k S\). Map \(Y\) by the same prescription with \(T\). The only multiplication checks beyond formal substitution and fixed zero products are products of pure \(z\)-powers whose degrees sum to \(d\). They give \((\operatorname{Sym}^d S)f=g\) and \((\operatorname{Sym}^d T)g=f\), respectively. The latter follows by applying \(\operatorname{Sym}^d T\) to the former and using \(TS=I\). Products of \(k\) entries of \(TS\) reduce to the corresponding products of identity entries by telescoping one factor at a time, at degree \(2k\). This also certifies both inverse identities on each homogeneous degree, proving the first bound.

## 3. Extracting the form equations without division

Write \(\pi_j\) for the projection to grade \(j\) in either fixed algebra basis. Put \(W=V\oplus Fz\), \(U=\pi_1 P|_W\), and \(U'=\pi_1 Y|_W\). At this point these are submatrices of the full variables. Their inverse relations will be derived.

**Generator constants.** Let \(c^H_i=\pi_0 H(w_i)\) for \(H=P\) or \(Y\) and a degree-one generator \(w_i\). For each word of length \(k\le d+1\), the coefficient vector of
\[
 H(w_{i_1}\cdots w_{i_k})-H(w_{i_1})\cdots H(w_{i_k})
\]
has a degree-\(k\) certificate for \(k\ge2\). Induct on \(k\) using multiplicativity on the fixed algebra element \(w_{i_1}\cdots w_{i_{k-1}}\) and then multiplying the preceding certificate by \(H(w_{i_k})\). The algebra kills every word of length \(d+1\). Its constant coordinate therefore gives a degree-\((d+1)\) certificate for every product of \(d+1\) generator constants of either map, with repetition allowed.

Take the degree-one part of \(YP=I\) on \(W\). A basis element \(b\) of grade \(k\ge2\) is a word of length \(k\) in degree-one generators. Replace \(\pi_1Y(b)\) by the degree-one part of the product of its generator images. That expression consists of terms with one degree-one coordinate and \(k-1\) generator constants of \(Y\). The terms from the unit vanish by the unit equation, and the terms from \(W\) give \(U'U\). We obtain
\[
                        U'U+E-I=0
\]
with certificate degree at most \(d+1\). Here \(E\) is the explicit sum of the higher-grade contributions multiplied by their corresponding entries of \(P\). Its entries have degree at most \(d+1\), and each monomial contains a generator constant of \(Y\). Each monomial of \(E^{d+1}\) is divisible by a previously certified product of \(d+1\) such constants, giving a certificate of degree \(B=(d+1)^2\).

Set \(\widehat U=(I+E+\cdots+E^d)U'\). The identity
\[
 \widehat U U-I=(I+E+\cdots+E^d)(U'U+E-I)-E^{d+1}
\]
certifies \(\widehat U U-I\) at degree \(B\). Write \(c_i=\pi_0P(x_i)\) and \(c_z=\pi_0P(z)\). The degree-one part of the multiplicativity equation for \(x_i z=0\) is \(c_z Ue_i+c_i Ue_z=0\). Multiply this certificate by \(\widehat U\) and subtract the corresponding multiples of \(\widehat U U-I\). Its coordinates give \(c_z=c_i=0\) with certificate degree at most \(B+1\). Interchanging \(P\) and \(Y\) gives the same conclusion for the constants of \(Y\). Eliminating the constant factors in \(E\) now certifies \(U'U=I\) at degree \(B+d+1\). The symmetric argument gives \(UU'=I\) with the same bound.

**Off-block coefficients.** In degree one write \(Uz=t+az\) with \(t\in V\), and \(Ux_i=s_i+b_i z\) with \(s_i\in V\). For \(w\in W\), let \(M(w):W\to(A_g)_2\) be multiplication by \(w\) on this grade. Let \(r=\pi_2P(z^2)\). The projected equations for \(z x_i=0\) and \(z^2\) give
\[
                   M(Uz) U=r e_z^{\mathsf T}.
\]
The product has no contributions from degree zero after the certified constant equations are used. This step has certificate degree at most \(B+2\). Right-multiplication by \(U'\) and use of \(UU'=I\) give \(M(Uz)=r e_z^{\mathsf T} U'\) at certificate degree at most \(B+d+2\). The matrix on the right is an outer product. Expanding each \(2\times2\) minor and substituting those identities one entry at a time gives certificates of degree at most \(B+d+4\), since each substituted entry has degree at most two.

For \(i\ne j\), the minor using rows \(x_i^2,x_j^2\) and columns \(x_i,x_j\) is \(t_i t_j\). For \(i\ne j\), rows \(x_i^2,x_i x_j\) and columns \(x_i,x_j\) give \(t_i^2\). Rows \(x_i^2,z^2\) and columns \(x_i,z\) give \(a t_i\). These identities use the ordinary monomial basis, including in characteristic two. Let \(a'\) be the \(z,z\) entry of \(U'\). The \(z,z\) entry of \(U'U=I\) reads \(\sum_j U'_{z,j}t_j+a'a=1\). Multiplying by \(t_i\) and using the minor certificates gives \(t_i=0\) at degree \(B+d+5\). The same inverse entry gives \(a'a=1\) at degree \(B+d+6\). The \(z^2\) coefficient of \(P(z)P(x_i)=0\) gives \(a b_i=0\), so \(b_i=0\) at degree \(B+d+7\). Swapping the two maps handles the off-block entries of \(U'\).

**The top relation.** Put \(S_0=U|_{V\to V}\) and \(T_0=U'|_{V\to V}\). The inverse identities now give \(S_0T_0=T_0S_0=I\) at degree at most \(B+d+8\). The grade-\(d\) part of \(P(f)=P(z)^d\) gives
\[
                     (\operatorname{Sym}^d S_0)f=a^d g.
\]
Indeed, expand each side using the word-product identities. Once constant and off-block terms are eliminated, only degree-one coordinates can enter a product of length \(d\) in grade \(d\). Each eliminated factor is multiplied by a polynomial of degree at most \(d-1\). This certifies the displayed equation at degree at most \(B+2d+6\).

The desired substitution is \(S=a'S_0\), \(T=aT_0\). Their inverse identities follow from \(a'a=1\) and those of \(S_0,T_0\). Their form equation follows by multiplying the top relation by \((a')^d\) and using \((a'a)^d=1\), obtained by telescoping. These bounds are at most \(b_d\). For fixed \(d\) all expressions have bounded degree, so explicit sparse coefficient lists and their summands can be expanded in polynomial size. The construction uses the given inverse variables and ordinary multiplication identities. No inverse-principle inference is needed.

## 4. Consequences for proof systems

For a substitution of degree \(\delta\) with pullback certificates of degree \(b\), a Polynomial Calculus refutation of degree \(D\) of the system whose variables are substituted becomes a refutation of degree at most \(\max(\delta D,b)\) of the system providing the certificates. Apply the substitution to each line, expand each substituted multiplication into monomial multiplications, and use the ideal certificates for the substituted axioms. The same reasoning applies to PC with the inversion rule, since that rule is already closed under arbitrary polynomial substitution. A Nullstellensatz identity, or a real equality-only Sum-of-Squares identity, becomes one of degree at most \(\delta D+b\) by substitution followed by replacement of the axiom factors. The Sum-of-Squares convention here is that every square and every ideal summand has degree at most the stated degree. [Galesi, Grochow, Pitassi, and She, Definition 2.1 and Section 2](https://arxiv.org/html/2305.19320#S2)

Let \(C(x,y)\) be an Ideal Proof System refutation circuit for equations \(f_i(x)=0\), with \(C(x,0)=0\) and \(C(x,f(x))=1\). For a substitution \(x=\sigma(x')\) and certificates \(f_i(\sigma(x'))=\sum_j c_{ij}(x')h_j(x')\), use the circuit
\[
       C\left(\sigma(x'),\left(\sum_j c_{ij}(x')y'_j\right)_i\right).
\]
It satisfies the two IPS identities for the equations \(h_j=0\). The local certificate circuits have polynomial size for fixed \(d\); sharing substituted subcircuits gives polynomial overhead on the IPS circuit size in both directions. Linearity in placeholders is preserved when present initially. This is a circuit-translation theorem for these equation systems. [Grochow and Pitassi, *The Ideal Proof System*](https://arxiv.org/abs/1404.3820)

The degree statements concern formal polynomial identities and therefore refute absence of solutions over the algebraic closure for PC and Nullstellensatz. For a fixed finite field \(\mathbb F_q\), both simulations also work with added field equations \(x^q-x=0\) on every variable. The pullback \(p^q-p\) of such an equation has a certificate of degree at most \(q\deg p\): expand in monomials using Frobenius and telescope their factors using \(x^q-x\). The lower bounds below use the systems without added field equations.

## 5. Hard square-free cubics and their jet algebras

Galesi, Grochow, Pitassi, and She give 3-tensor instances of side lengths \(O(n)\) requiring degree \(\Omega(n)\) in PC over every field and in SoS over the reals. Their Section 5 construction makes the frontal slices independent: the nonzero code matrix occupies its original rows and the other slices each have a distinct private nonzero coordinate in the added rows. Use those instances. [Galesi et al., Theorem 5.2 and Proposition 5.5](https://arxiv.org/html/2305.19320#S5)

Here is the forward proof-degree check on the two successive Grochow–Qiao IV gadgets. For the first, write the input frontal matrices as \(D_i\) of size \(u\times v\). Include symmetric matrices \(C_i\) with the only off-zero blocks \(D_i,D_i^{\mathsf T}\) between disjoint groups of sizes \(u,v\). A final anchor \(C_0\) has an identity pairing the first group with a fresh group of size \(u\), and pairs two more groups of size \(r\), with \(2r>u+v\). These are the symmetric version of Section 2, with diagonal entries zero. All these matrices are alternating in characteristic two. For tensor transporter variables \((X_1,X_2,X_3)\) with explicit inverse variables \((X'_1,X'_2,X'_3)\), use the first gadget’s congruence matrix and slice map
\[
 L=\operatorname{diag}(X_1,X_2,(X'_1)^{\mathsf T},I_{2r}),
 \qquad R=\operatorname{diag}(X_3,1).
\]
Their proposed inverses are obtained by exchanging primed and unprimed matrices. Under substitution the linear combination of transformed \(D_i\)-blocks gives exactly the original tensor equations, and the identity pairing gives \(X_1X'_1=I\).

For the second gadget, use a variable family \(x\) for the rows of the \(C_i\), a family \(z_i\) for their slices, a dual family \(u\) for \(x\), and a fresh anchor \(h\) with auxiliary pairs \(p_j,q_j\). Its commutative polynomial is
\[
  H_C=\sum_i z_i\sum_{\mu<\nu}(C_i)_{\mu\nu}x_\mu x_\nu
             +h\left(\sum_\mu x_\mu u_\mu+\sum_j p_jq_j\right).
\]
If the matrices have side length \(s\) and there are \(k\) slices including the anchor, use \(\lfloor(s+k+1)/2\rfloor+1\) auxiliary pairs \(p_j,q_j\). The linear substitution on the families is \(\operatorname{diag}(L,R,(L')^{\mathsf T},I)\), with inverse obtained by exchanging primes again. The \(C_i\) entries occur only between distinct preserved groups in \(x\). The changed coefficient of each such pair is exactly its congruence-matrix entry, with no factor of two. The new identity pairing reduces to \(LL'=I\). Thus the final cubic transporter and its inverse are affine-linear polynomials in the original tensor variables, and every pulled-back cubic equation or inverse equation is a linear combination of the original tensor and inverse equations.

For correctness in the reverse direction, the unnormalized polarization of \(H_C\) is exactly the Section 6 symmetric trilinear gadget, since the displayed monomials are square-free. In characteristic two it is exactly the alternating gadget, since all permutation signs equal \(1\) and repeated-index entries are zero. A formal polynomial equivalence implies equivalence of these polarized tensors by functoriality. The published reverse implications for the two gadgets then recover the original tensor equivalence. They apply over extension fields as well. In characteristic two the cross-block matrices are alternating, so the block Z in Equation (19) has zero diagonal and equals its strict upper part plus its transpose, as needed for the upper-triangular shear. This reasoning uses no division by \(2\) or \(3\), and the output has \(O(n)\) variables. [Grochow and Qiao IV, Sections 2 and 6 and Theorem 6.1](https://arxiv.org/html/2306.16317)

The linear substitution therefore transfers the degree lower bound to the cubic equations. The forward homogeneous lift from Section 2 of this note transfers it again to the jet-algebra equations. For \(d=3\), the jet dimension is \(N=\binom{n+3}{3}+2\) when the input cubic uses \(n\) variables. Thus the lower bounds are \(\Omega(n)\) in the cubic variable count and \(\Omega(N^{1/3})\) in the jet-algebra dimension. The same lower bound holds for Nullstellensatz by the PC bound. This consequence uses the proved substitutions on the specified equations. A decision many-one reduction alone would give no degree transfer.

The prior jet construction builds on ordinary truncated algebras for cubic equivalence. The bounded-degree certificate analysis, including the treatment of ungraded maps, is the contribution here. Optimization.py independently checks 4,608 filtered jet products, 946 complete minor cases in four small rings, and 64 geometric-inverse controls over \(\mathbb Z/16\mathbb Z\). One minor control shows the role of the inverse row: modulo \(4\), \(t=(2,0)\) and \(a=0\) give vanishing minors despite \(t\ne0\), while the full degree-one column is not unimodular. The proofs are mathematical prose without a Lean kernel receipt. Literature priority remains unverified. [Agrawal and Saxena, *On the Equivalence of Cubic Forms*](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf)

