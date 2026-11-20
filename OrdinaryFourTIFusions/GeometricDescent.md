# Geometric descent and exact extension degrees for almost all four-tensors

Let \(k=\mathbb F_q\), let \(n\ge2\), and let \(V=(k^n)^{\otimes4}\) with the ordinary action of \(G=\operatorname{GL}_n^4\). The geometric stabilizer is the stabilizer group scheme after passing to an algebraic closure. Put

\[
Z=\{(u_1 I,u_2 I,u_3 I,u_4 I):u_i\in\mathbb G_m,\ \prod_i u_i=1\}.
\]

**Theorem.** For uniform \(A\in V\), except on a set of probability \(q^{-n^3+O(n^2\log(n+1))}\) with an absolute implied constant, the full stabilizer group scheme of \(A\) is \(Z\). On every such source, the following assertions hold.

1. Ordinary isomorphism to any second tensor over \(k\) descends from the algebraic closure, or from any extension field, to \(k\).
2. For any prescribed determinant quadruple in \(k^\times\), the set of extension degrees with a transporter having exactly those determinants is empty or the multiples of a single explicitly computable divisor of \(n\). Thus all successful degrees descend to their greatest common divisor, and the first successful degree is at most \(n\).
3. Let \(R\) be any finite commutative local ring with residue field \(k\). Every lift of \(A\) has scalar stabilizers over every commutative \(R\)-algebra. Ordinary equivalence between a lift of \(A\) and any target over \(R\) descends along every injective homomorphism of commutative rings \(R\to S\). This includes faithfully flat extensions and arbitrary changes of ramification in such extensions.

The ordinary field comparison and transporter algorithms on the recognizable density-one family in [FourTIAlmostAll](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/RESULTS.md) then give, on the intersection of the two high-density families, deterministic polynomial-bit-time geometric comparison, ambient-field transporters, and computation of the exact determinant extension spectrum over a fixed \(k\). The probability estimate in this theorem does not itself give a computational test that certifies geometric scalarity on every input.

## 1. Bounding stabilizers over the algebraic closure

We first use a counting fact over a finite field. If \(f\colon\bar k^D\to\bar k^m\) is a polynomial map of coordinate degrees at most \(d\), at most

\[
\binom{D+d m(q-1)}{D}
\]

points in its image lie in \(k^m\). For each such point \(a\), choose a preimage and use the polynomial \(I_a(x)=\prod_{j=1}^m(1-(x_j-a_j)^{q-1})\). The pullbacks \(I_a\circ f\) are linearly independent, since evaluation on the chosen preimages gives the point indicator basis. They belong to the space of \(D\)-variate polynomials of total degree at most \(d m(q-1)\), giving the bound. The chosen preimages need not be defined over \(k\).

Consider a putative stabilizing tuple \(g\) over \(\bar k\) with a nonscalar mode \(g_i\). Among the vectors \(e_j\) and \(e_1+e_j\) for \(2\le j\le n\), there is a vector \(v\) whose line is moved. Otherwise the basis vectors diagonalize \(g_i\) and the sums force all diagonal entries to agree. Complete each such test vector \(v\) to a fixed basis in mode \(i\), with first vector \(v\). One of its \(n-1\) coordinate functionals \(\ell\) vanishing on \(v\) satisfies \(\ell(g_iv)\ne0\).

Fix the mode, basis, and functional. Write \(A=\sum_j e'_j\otimes A_j\) in this basis, with each slice \(A_j\) occupying \(m=n^3\) coordinates. Condition on all slices except \(A_1\). The known slice \(\ell(A)\) does not use \(A_1\). Apply \(\ell\) to the mode in the stabilization equation and undo the other three maps. Then

\[
A_1=\alpha\Bigl(\bigotimes_{h\ne i}g_h^{-1}\Bigr)\ell(A)
      +\sum_{j>1}c_j A_j,
\quad
\alpha=\ell(g_iv)^{-1},\qquad
c_j=-\alpha\ell(g_i e'_j).
\]

Allow all entries of the other three inverse matrices and the \(n\) scalars \(\alpha,c_2,\ldots,c_n\) to vary independently. This gives a polynomial image of degree at most four in \(D=3n^2+n\) variables containing every possible constrained slice. The missing slice is uniform over \(k^m\), even after conditioning. The probability of a stabilizer with these fixed mode, basis, and functional choices is therefore at most \(q^{-n^3}\binom{D+4n^3(q-1)}{D}\). Union over at most \(4(2n-1)(n-1)\) choices. If all mode maps are scalar, the product of their scalars must be one except on the zero tensor. This proves the claimed estimate on geometric points: using \(\binom{N}{D}\le(eN/D)^D\), the bound is \(q^{-n^3+O(n^2\log(n+1))}\) uniformly in \(q\ge2\).

For the group-scheme assertion also exclude the event that the infinitesimal stabilizer is larger than the scalar tangent space. For each nonscalar tuple of matrices \(X_i\) over \(k\), choose in one nonscalar mode a vector \(v\) with \(X_i v\) outside its span. On tensors with fixed factor \(v\) in that mode, projection modulo its line kills all the other derivative terms, and the surviving term is injective. Thus the linear infinitesimal equation has rank at least \(n^3\) for each such tuple. Union over \(q^{4n^2}\) tuples. The scalar tuples in the kernel at a nonzero tensor are exactly the ones with scalar sum zero. Extending scalars preserves the dimension of this linear kernel. Over \(\bar k\), the stabilizer has underlying reduced group \(Z\), so its dimension is three. Tangent dimension three makes its local ring at the identity regular. Translation by any geometric point gives the same property at every closed point. Hence the stabilizer is reduced and is equal to \(Z\) as a closed subgroup scheme. Equality descends to \(k\) by faithful flatness of the field extension. In particular, the equality holds on points over every commutative \(k\)-algebra, including nonreduced ones.

## 2. Ordinary descent over fields

Suppose \(B\) is defined over \(k\) and that \(g\) transports \(A\) to \(B\) over \(\bar k\). The coordinatewise Frobenius of \(g\) is another transporter, so each \(g_i\) and its Frobenius differ by a scalar, with the four scalar ratios of product one. Choose a nonzero entry \(a_i\) of each factor and normalize by that entry. Each \(g_i/a_i\) is now Frobenius fixed and has entries in \(k\). The product \(\prod_i a_i\) is also Frobenius fixed. Multiplying one normalized factor by this product gives a transporter over \(k\). Existence over any field extension implies existence over \(\bar k\) because the transporter equations with determinant inverses define an affine scheme of finite type over \(k\). A point over any extension makes its defining ideal proper, and base change to \(\bar k\) preserves properness. This proves ordinary descent.

## 3. Exact determinant extension spectrum

If there is an ordinary transporter anywhere, choose one \(g\) over \(k\) by ordinary descent. For a requested tuple \((\delta_i)_i\), put \(v_i=\delta_i/\det g_i\). On every extension field the set of transporters is exactly \(gZ\). A prescribed tuple is attained over \(k_r=\mathbb F_{q^r}\) precisely when \(\prod_i v_i=1\) and each \(v_i\) is an \(n\)-th power in \(k_r^\times\). Indeed, take one root per component. Their product is an \(n\)-th root of one, which can be removed by adjusting the final root.

Assume the product condition. Let \(o_i\) be the order of \(v_i\) over \(k\). With \(M=q^r-1\), the cyclic-group test is \(o_i\mid M/\gcd(M,n)\). For each prime \(\ell\mid o_i\), writing \(b=v_\ell(o_i)>0\) and \(a=v_\ell(n)\), this is exactly the valuation threshold \(v_\ell(M)\ge a+b\). Equivalently, \(r\) is divisible by the multiplicative order of \(q\) modulo \(\ell^{a+b}\). The least successful degree is the least common multiple of these orders over all \(i,\ell\), taking the empty least common multiple to be one. Each individual order divides \(\ell^a\). In fact \(q\equiv1\pmod{\ell^b}\), and raising a number congruent to one modulo \(\ell^j\) to the \(\ell\)-th power improves the congruence to \(\ell^{j+1}\) by the binomial formula. Thus the least successful degree divides \(n\).

For fixed \(q\), computing the order of each \(v_i\) and factoring it costs a field-dependent constant. All subsequent modular orders can be computed by testing the powers with exponents \(1,\ell,\ldots,\ell^a\). This is polynomial in the dense input bit length and needs no construction of extension fields. The upper bound \(n\) is attained within the generic domain for infinitely many dimensions. For example, take fixed \(q\equiv1\pmod\ell\) for an odd prime \(\ell\), put \(b=v_\ell(q-1)\), take \(v\) of order \(\ell^b\), and let \(n=\ell^a\). Starting from a generic \(A\), use a transporter whose first two determinants are \(v^{-1},v\) and whose other determinants are one. For the all-one requested profile the first successful degree is \(\ell^a\): for odd \(\ell\) and \(j\ge1\), if \(u=1+c\ell^j\) with \(\ell\nmid c\), then \(u^\ell-1\) has valuation exactly \(j+1\) by its binomial expansion. The remaining exponent factor coprime to \(\ell\) does not change the valuation, by the same expansion. This gives the sharp example. [Related special-linear descent and worst-case extension spectra](https://github.com/Dugongue/MathProofs/blob/main/OptimalMaxRankAndDescent/ExtensionSpectra.md)

## 4. Descent over arbitrary finite local coefficient rings

Let \(R\) have maximal ideal \(\mathfrak m\), and let \(T\) be a lift of a residue tensor satisfying the group-scheme and tangent conditions just proved. Use the normalized matrix entries and coordinate slice of the [formal coordinate proof](LocalRingCoordinates.md). The same polynomial map and uniqueness proof work over any commutative \(R\)-algebra \(S\) with nilpotent ideal \(I=\mathfrak mS\). Indeed its Jacobian at the residue is the fixed invertible matrix over \(k\) mapped into \(S/I\), so every Newton correction is possible and the quadratic remainder still squares the error ideal. Thus the inverse coordinates commute with extension from \(R\) to \(S\).

If a tuple over \(S\) fixes the slice representative of \(T\), its reduction modulo \(I\) is scalar of product one by the group-scheme equality on \(S/I\). Units modulo a nilpotent ideal lift to units, so divide by a scalar tuple of product one to make the residue identity. Normalize the three prescribed entries by a second scalar tuple of product one. This gives a normalized matrix tuple in the slice chart with parameters in \(I\). Uniqueness forces that tuple to be the identity. Conjugation by the original coordinate change shows that the same scalar condition holds for the stabilizer of \(T\) itself over every \(S\).

Now suppose \(R\to S\) is injective and a transporter over \(S\) maps \(T\) to a target \(D\) over \(R\). Since \(I\) is nilpotent, \(S/I\ne0\). Pass from \(S/I\) to one of its residue fields. This gives an ordinary equivalence of the two residue tensors over an extension field of \(k\), so by Section 2 they are already equivalent over \(k\). Lift a residue transporter to an invertible tuple \(h\) over \(R\) and compare \(T\) with \(h^{-1}D\) in the same residue fiber. Over \(S\) their slice coordinates must agree. The proof is the same normalization argument using group-scheme equality on \(S/I\) and uniqueness of the chart. Since the chart commutes with extension and \(R\to S\) is injective, those coordinates already agree over \(R\). The two framed coordinate changes over \(R\) compose to give a transporter over \(R\). This proves descent even when the coefficient extension is not given as a flat algebra.

The prior [ordinary four-tensor search and lifting theorem](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/SearchAndLifting.md) proves scalarity of rational stabilizer points and of the tangent space on almost all residue inputs. The new counting step excludes additional geometric stabilizers, even when their individual coefficients could require extensions of unbounded degree. It turns the ordinary extension spectrum into a two-way alternative and gives the exact divisor-of-\(n\) bound for signed extension spectra. The local conclusion uses the full group scheme and the explicit coordinate slice. The proofs are informal, and publication priority has not been determined.
