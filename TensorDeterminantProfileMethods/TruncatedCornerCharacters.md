# Every finite-field determinant character reduces to unit-side special-linear tensor isomorphism

Informal proof. Fix a finite field \(F=\mathbb F_q\), and write \(m=q-1\). For every character
\[
\chi(d_1,d_2,d_3)=d_1^{w_1}d_2^{w_2}d_3^{w_3}
\]
of \((F^\times)^3\), there is a deterministic same-field many-one reduction from the problem of finding a transporter with \(\chi=1\) to special-linear isomorphism of two cubic tensors of side length \(N\equiv1\bmod m\). The side length is \(O_q(n_1+n_2+n_3+1)\). The target tensors are multiplication tensors of unital associative algebras whose radicals have nilpotence index bounded in terms of \(q\). The construction preserves the exact character image, with inversion for the covariant multiplication-tensor convention.

The exponents may be units, zero, or arbitrary zero divisors modulo \(m\). In particular the reduction applies to non-squarefree \(q-1\). This reduces all SL-TI over every fixed finite field to a constant conjunction of balanced unit-side instances of this form. An ordinary-TI reduction for the resulting target class would give a one-instance reduction for the original problem. [Chen–Grochow–Qiao–Tang–Zhang, Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## 1. Parameters and the algebra

View the tensors as bilinear maps \(T:X_1\times X_2\to X_3\) and \(S:Y_1\times Y_2\to Y_3\), with \(\dim X_i=\dim Y_i=n_i\). The first two spaces are the duals of the indicated tensor modes. An original transporter \(g=(g_1,g_2,g_3)\) corresponds to maps \(a=(g_1^{-\mathsf T},g_2^{-\mathsf T},g_3)\) satisfying
\[
S(a_1 x,a_2 y)=a_3 T(x,y).
\]
Use the fixed coordinates of the dense inputs in these formulas. Unequal formats and zero-dimensional formats can be disposed of directly by constant outputs. Assume all \(n_i>0\). For \(q=2\), ordinary and special-linear isomorphism coincide. The algebra construction works with every length equal to two and no field padding. The parameter choices below are for \(m\ge2\).

Put \(v=(-w_1,-w_2,w_3)\) modulo \(m\). Choose integers \(k_i\ge2\) with \(k_i\equiv v_i\bmod m\) and \(k_3\le\min(k_1,k_2)\). Take \(k_3\) in \([2,m+1]\) and \(k_1,k_2\) in \([k_3,k_3+m-1]\). Write \(R_j=F[t]/(t^j)\). Choose three lengths \(M_p\ge\max_i k_i\) for \(p=0,1,2\), to be specified below. Define an algebra \(A_T\) by the following triangular array:
\[
A_T=
\begin{pmatrix}
R_{M_0}&X_1\otimes R_{k_1}&X_3\otimes R_{k_3}\\
0&R_{M_1}&X_2\otimes R_{k_2}\\
0&0&R_{M_2}
\end{pmatrix}.
\]
The diagonal rings act on each incident corner by truncation. The product of the \(01\) and \(12\) corners is \(T\) extended \(R_{k_3}\)-bilinearly after truncation, with value in the \(02\) corner. All other off-diagonal products are zero. Associativity follows from the bimodule identities for the truncated rings and the bilinearity of the only off-diagonal product. The diagonal identity is a unit. Construct \(A_S\) with the same lengths.

The Jacobson radical is the sum of all off-diagonal corners and the diagonal ideals \((t)\). This ideal is nilpotent, since an ordered product has at most two off-diagonal factors and a run at vertex \(p\) of \(M_p\) radical diagonal factors gives zero. The quotient is \(F^3\), so the nilpotent ideal is exactly the radical.

## 2. The determinant of an arbitrary algebra isomorphism

Let \(\alpha:A_T\to A_S\) be an algebra isomorphism. Modulo the radical it permutes the three primitive idempotents. If \(e_p\) are the target standard idempotents and \(f_p\) are their corresponding images in the order of that permutation, then \(\sum_p f_p e_p\) is one modulo the radical and satisfies \(u e_p=f_p u\). Thus inner conjugation by a radical unit aligns the two systems of idempotents. Inner conjugation by \(1+r\) has determinant one, since left and right multiplication by \(1+r\) are unipotent. After alignment the permutation preserves the directed pattern of nonzero corners. That pattern is the total order on three elements, so the permutation is trivial.

On the diagonal at vertex \(p\), the normalized isomorphism sends \(t\) to \(\lambda_p t+O(t^2)\), with \(\lambda_p\ne0\). On an incident corner of length \(k\) it is semilinear for the truncated diagonal actions. Since the original left and right actions of \(t\) coincide on the corner, applying the isomorphism shows that their new actions coincide. Modulo \(t^2\), this gives \((\lambda_p-\lambda_{p'})t\,a_i(x)=0\) on the corner joining \(p,p'\), where \(a_i\) is the induced isomorphism modulo \(t\). Since \(k\ge2\) and \(n_i>0\), the two scalars coincide. Write \(\lambda\) for their common value. The corner maps preserve the \(t\)-adic filtrations in both directions.

On the associated graded layer of degree \(j\) of corner \(i\), the map is \(\lambda^j a_i\) in the natural vector-space bases. On the diagonal its layer of degree \(j\) scales by \(\lambda^j\). Consequently
\[
\det_F\alpha=
\left(\prod_{i=1}^3(\det a_i)^{k_i}\right)
\lambda^{\,\sum_{p=0}^2\binom{M_p}{2}+\sum_{i=1}^3 n_i\binom{k_i}{2}}.
\]
Reduction of the corner product modulo \(t\) gives exactly \(S(a_1 x,a_2 y)=a_3T(x,y)\). Conversely, each such \(a\) gives an algebra isomorphism by acting coefficientwise on each corner and by identity on the diagonals.

## 3. Canceling the parameter change

Choose the \(M_p\) so that
\[
\sum_{p=0}^2\binom{M_p}{2}
\equiv -\sum_{i=1}^3 n_i\binom{k_i}{2}\pmod m.
\]
Here is an elementary modular existence proof. For a power \(2^e\), the values \(\binom{j+1}{2}\) for \(0\le j<2^e\) are a permutation modulo \(2^e\). Indeed equality for \(a,b\) implies that \((a-b)(a+b+1)\) is divisible by \(2^{e+1}\). One factor is odd, and the other has absolute value below \(2^{e+1}\). Thus a collision requires \(a=b\). For each odd prime power \(p^e\), use \(8\binom{M}{2}=(2M-1)^2-1\). Every element of \(\mathbb F_p\) is a sum of two squares since the set of squares has size \((p+1)/2\). Every residue has a representation as a sum of three squares with at least one nonzero summand: for a zero residue take the third square equal to one and represent minus one with two squares. A nonzero coordinate has invertible derivative \(2x\) and can be adjusted to lift the equation one power of \(p\) at a time. Thus the desired sum of three triangular numbers is possible modulo each odd prime power. Apply the Chinese remainder theorem independently to the three arguments, using their residues modulo \(2^{e+1}\) at the even prime. Adding \(2m\) to any length preserves its triangular number modulo \(m\). Choose lengths at least \(\max_i k_i\). Equivalently, a finite search of triples of residues modulo \(2m\) followed by these length increases constructs them at fixed \(q\).

The exponent of \(\lambda\) now vanishes modulo \(m\). The determinant formula and the coefficientwise lifting give the exact equality of sets
\[
\{\det_F\alpha:\alpha:A_T\cong A_S\}
=
\{\chi(\det g_1,\det g_2,\det g_3):g\cdot T=S\}.
\]
Both sets can be empty. The choices of lengths depend only on the field, format and character, so both sides use equal-dimensional algebras with a common convention for the displayed order of bases.

## 4. Padding to a unit side length

There are no proper nonzero central idempotents in \(A_T\). A central element commutes with the three standard idempotents, so it is diagonal. Each diagonal local ring has only zero and one as idempotents, and every off-diagonal corner is nonzero, forcing the same value on all vertices. The same holds for \(A_S\). Their radicals are nonzero.

Adjoin the same direct product of at most two distinct odd-degree extension fields of \(F\) to both algebras so that the new dimension \(N\) equals one modulo \(m\). If \(m\) is odd, any residue is represented by an odd degree. If \(m\) is even, an odd residue is represented by one odd degree and an even residue by the sum of two distinct odd degrees. Choose positive bounded representatives larger than one. When the current dimension suffices, no padding is necessary. These field factors are intrinsically separate by the central primitive idempotents. Their degrees are distinct and the original algebra has nonzero radical, so no swaps with each other or the original factor occur. Every automorphism of an odd-degree finite field extension has determinant one: over a splitting field the Frobenius generator permutes the geometric coordinates in an odd-length cycle. Thus padding leaves the exact algebra-isomorphism determinant set unchanged.

## 5. Multiplication tensors and special-linear isomorphism

For unital associative algebras \(E,F'\), any vector-space isotopy \(f,g,h\) with
\[
 f(x)g(y)=h(xy)
\]
is of the form \(f=L_a\theta,\ g=R_b\theta,\ h=L_a R_b\theta\), for units \(a=f(1)\), \(b=g(1)\), and a unital algebra isomorphism \(\theta:E\cong F'\). In fact the equations with one input equal to the unit make left multiplication by \(a\) and right multiplication by \(b\) invertible. They therefore make \(a,b\) units in the finite-dimensional algebra. Substituting \(\theta(x)=a^{-1}h(x)b^{-1}\) gives multiplicativity and the displayed identities. Conversely all such choices give an isotopy.

For the covariant multiplication tensor the three maps are \(f^{-\mathsf T},g^{-\mathsf T},h\). Their determinant product is \((\det\theta)^{-1}\), since the determinants of the unit multiplications cancel. In particular an SL transporter gives \(\det\theta=1\). Conversely a determinant-one algebra isomorphism itself gives an SL transporter by using \(a=b=1\). The exact set of total determinant values is the inverse of the character set in Section 3. Since \(N\equiv1\bmod m\), scalar triples alone can correct every determinant triple of product one in the target. The output is the pair of multiplication tensors of the padded algebras in their standard bases.

All lengths and field padding degrees are bounded in terms of \(q\), and each corner has dimension \(k_i n_i\). Thus both output side lengths are \(O_q(n_1+n_2+n_3+1)\), and constructing their dense tables takes polynomial time. The radical nilpotence index has a bound depending only on the three diagonal lengths. A trivial-character test can encode ordinary TI itself using the same construction.

## 6. What this establishes for Question 1.9

The determinant triples of an ordinary transporter coset are an empty set or a coset \(dH\) of a subgroup \(H\) of \((F^\times)^3\). A nonempty coset contains one if and only if its image under each character contains one, since a character of the quotient by \(H\) separates any coset distinct from \(H\). Including the trivial character rejects the empty case. Conjoining the corresponding tests reduces arbitrary SL-TI to a constant number of balanced unit-side SL-TI instances on these multiplication tensors. If each of these can be reduced to ordinary TI, the conjunction can be packed into one ordinary TI instance by the ordered typed tensor-system construction. The reduction here leaves the target orientation constraint in place.

The triangular tensor-to-algebra encoding is due to Grochow and Qiao. The additional construction here uses independently truncated corners to program all three weights, and cancels the common automorphism on their parameter by the three diagonal truncations. The reduction is informal. Publication priority for this extension is unestablished. [Grochow–Qiao, tensor-to-algebra reductions](https://doi.org/10.1137/21M1441110) · [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)
