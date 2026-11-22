# A last-layer determinant law

Let \(t\ge3\) be odd, \(r\ge1\), and let \(Q\) be a symmetric \(r\times r\) matrix over an odd prime field. Define the commutative algebra \(A_Q\) with basis
\[
  1,x,\ldots,x^t,\ y_1,\ldots,y_r,\ xy_1,\ldots,xy_r
\]
by the ordinary truncated powers of \(x\) and the relations
\[
       x^{t+1}=0,\qquad x^2y_i=0,\qquad y_i y_j=Q_{ij}x^t.
\]
All triple products involving any \(y_i\) vanish if all three factors belong to the maximal ideal. These rules give an associative algebra: the two associations agree on triples of powers of \(x\), and terms with any \(y_i\) agree by the displayed relations. Its dimension is \(d=t+1+2r\). Its radical \(J\) is the span of the basis excluding 1; \(J^2\) has basis \(x^2,\ldots,x^t,xy_1,\ldots,xy_r\); \(J^j=(x^j)\) for \(3\le j\le t\).

**Theorem.** In these bases the algebra-isomorphism determinants from \(A_Q\) to \(A_{Q'}\) are precisely
\[
   \delta=a^{t(t+1)/2+r}(\det B)^2,\qquad
   a\ne0,\ B\in{\rm GL}_r,\quad B^T Q' B=a^t Q .
\]
The three-mode transporter determinants of the two multiplication tensors are precisely
\[
            (u^d\delta,\ v^d\delta,\ (uv)^d\delta),\qquad u,v\in F^\times.
\]
Over the ternary field this gives a constructive polynomial-time solver for any \(Q,Q'\), including singular forms. The family admits deterministic recognition up to independent based tensor transformations.

**Proof.** In \(J/J^2\), the radical in any slot of the triple product to \(J^3/J^4\) is exactly \(Y=\langle\bar y_i\rangle\); the sole nonzero based product is \(\bar x^3\). Every isomorphism therefore has \(X=\phi(x)=a x+h\) modulo \(J^2\), with \(h\in Y\), and sends \(Y\) by a matrix \(B\) modulo \(J^2\). Write \(Y'_i=\phi(y_i)=\sum_j B_{ji} y_j+\sum_j C_{ji}xy_j+f_i(x)\), with \(f_i\in(x^2)\). From \(X^2Y'_i=0\) we get \(x^2 v(x) f_i(x)=0\) with \(v(0)=a^2\). Indeed \(X^2\) is \(x^2v(x)\) plus an \(xY\) term, and both kill \(Y\) and \(xY\). Thus \(f_i\) is divisible by \(x^{t-1}\). Its products with the other corrections vanish. Now \(Y'_iY'_j=(B^TQ'B)_{ij}x^t\), and \(X^t=a^t x^t\). This proves the congruence condition, and \(x\mapsto ax,\ Y\mapsto BY\) realizes every solution.

Telescoping determinants along the radical filtration gives the displayed determinant. The degree-one block contributes \(a\det B\); the degree-two block has diagonal blocks \(a^2\) and \(aB\), including possible off-diagonal terms. Subsequent nonzero blocks contribute \(a^j\) for \(3\le j\le t\). For isotopisms write \(H(xy)=P(x)D(y)\). Setting either input to 1 shows that \(P(1),D(1)\) are units (their multiplication maps are bijections), and \(\phi=(P(1)D(1))^{-1}H\) is a unital multiplicative isomorphism. Thus \(P,D,H\) act by \(\phi\) followed by multiplication by the first unit, second unit, and their product. A unit of residue \(u\) acts on each associated grade by \(u\), so its determinant is \(u^d\).

**Recovery from dense tables.** For an isotope, the invertible left slices are the complement of a hyperplane, since nonunits form precisely the radical; the right side has the same property. Search the given basis vectors for one invertible slice on each side. With \(R_0:U\to W\) the chosen right slice and \(L_0:V\to W\) the left one, define \(z*w=T(R_0^{-1}z,L_0^{-1}w)\). For an isotope of the model this is multiplication rescaled by a unit, so is isomorphic to the model. Verify commutativity, associativity, and a unit by linear algebra. Recover \(J\) as the kernel of \(z\mapsto z^{p^h}\) for \(p^h\ge d\), which is linear. Check the residue dimension is 1. Read \(t\) from the radical length, \(r=\dim J/J^2-1\), and recover \(Y\) by the triple product. Choose any \(x\) whose tangent lies outside \(Y\); lift a basis of \(Y\) in \(\operatorname{Ann}(x^2)\cap J\) by linear equations. These lifts always exist in the model, as its original \(y_i\) are killed by the square of every such \(x\). Check the displayed monomials form a basis and verify their entire multiplication table against the claimed rules. This last check certifies membership and provides an explicit change of basis. The tangent and graded calculations above prove that in a genuine model the arbitrary admissible choices pass. Keep the determinants of the two slice maps and all endpoint frame maps when translating prescribed targets. Equivalently, compose the actual endpoint transformations, solve in the displayed normal form and undo the transformations on the three matrices.

Over \(F_3\) test both \(a=\pm1\). For each, congruence of the symmetric forms, with a witness \(B\), follows by diagonalization, comparison of radicals and nonsingular discriminants, and ordinary ternary basis operations. Then read the three signs from the formula; units have determinant \(+1\) since \(d\) is even, and \((\det B)^2=1\). This proves polynomial bit complexity and gives a witness for every feasible triple.

**Variable odd primes.** For nonsingular \(Q,Q'\) this also constructs witnesses deterministically in time polynomial in dense size and \(\log p\), using the previous effective norm and bounded-exponent root theorems. In the displayed bases, for targets \(D_1,D_2,D_3\) put \(\delta=D_1D_2/D_3\), \(k=\det Q/\det Q'\), \(E=t(t+1)/2+r\). Solve simultaneously
\[
 u^d=D_1/\delta,\quad v^d=D_2/\delta,\quad
 a^{E+tr}=\delta/k,\quad z^2=a^{tr}k.
\]
Smith form gives an equivalent diagonal system. Its four rows have polynomially bounded entries, hence the nonzero invariant factors are polynomially bounded as integers by the maximal minors. Power membership gives unconditional decision. The previous small-exponent solver supplies witnesses using the verified Dirichlet theorem at this step. Crucially \(a\) and the square condition must be solved together. Equal discriminants modulo squares are necessary and sufficient for congruence of nonsingular forms of the same dimension over a finite field of odd order. For constructive diagonalization normalize diagonal entries to 1 or a fixed nonsquare by square roots. Pairs of nonsquare entries can be converted to square ones by solving \(X^2+Y^2=\nu\) for a prescribed nonzero scalar and using the orthogonal columns \((X,Y),(-Y,X)\). When \(-1\) is a nonsquare this is a quadratic-extension norm equation, solved by the prior norm algorithm. When it is square, choose \(i^2=-1\) and prescribe \(X+iY=1,\ X-iY=\nu\). This gives \(B\), and its squared determinant automatically equals \(a^{tr}k\). The remaining scalars give the unit multiplications. [Prior norm and root algorithms](https://github.com/Dugongue/MathProofs/blob/5d2a1a370c051bbdcb0406ecce525b2125b730e0/DirichletGrochowPrimeTests/OrientedTransport.md) · [Independent verification of the Dirichlet theorem used in the nonresidue search](https://math.mit.edu/~drew/grh/)

**A sign first visible at arbitrary depth.** Over \(F_3\) choose \(t\equiv3\bmod4\), odd \(r\), and nonsingular \(Q,Q'\) of opposite discriminants. Then \(B^TQ'B=a^tQ\) forces \(a=-1\) and a solution exists by form classification. Since \(E\) is odd, every ordinary transporter has signs \((-1,-1,-1)\). Yet for every \(1\le j\le t\), the based algebras \(A_Q/J^j\) and \(A_{Q'}/J^j\) have identical multiplication: the only discrepancy is killed with \(x^t\). This refutes the implication from compatible identity maps on every proper truncation to a special-linear map at the top. It also gives an exact positive solver at arbitrary depth and tangent rank. At \(t=3,r=1\), the two tensors have dimensions \(6\times6\times6\). Exhaustive enumeration of the possible images of \(x,y\) gives 4,374 algebra isomorphisms between the two forms, all with negative determinant, and 4,374 automorphisms of the source, all positive. [Executable check](checks.py)
