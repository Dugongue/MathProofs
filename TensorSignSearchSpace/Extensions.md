# Prime degree extensions preserve exact determinant profiles

**Theorem.** Let \(F=\mathbb F_q\) and let the three mode dimensions be \(n_1,n_2,n_3\). Choose a prime \(\ell\) that does not divide \(B=\prod_i |\mathrm{GL}_{n_i}(F)|\), and take \(E=\mathbb F_{q^e}\) for \(e=\ell^k\), \(k\geq1\). For any pair of tensors \(T,S\) over \(F\) of this format and any tuple \(d\in(F^\times)^3\), the following are equivalent.

1. There is a transporter over \(F\) with determinant tuple \(d\).
2. There is a transporter over \(E\) with determinant tuple \(d\), viewed in \(E^\times\).
3. There is a transporter over \(E\) for which the three determinant norms to \(F\) equal \((d_1^e,d_2^e,d_3^e)\).

With the determinant constraints omitted, ordinary isomorphism over \(E\) is also equivalent to ordinary isomorphism over \(F\). The prime can be chosen with polynomial degree in the explicit input length, without knowing the stabilizers. In particular the entire determinant profile over \(F\) equals the intersection of the exact profile over \(E\) with \((F^\times)^3\). The same conclusion follows by taking the coordinatewise norm of the profile over \(E\) and then raising to the inverse of \(e\) modulo \(q-1\) if \(q>2\).

## Proof by counting transporters

Write \(\Gamma_E=\prod_i\mathrm{GL}_{n_i}(E)\). The group order formula is
\[
 |\mathrm{GL}_a(\mathbb F_Q)|=Q^{a(a-1)/2}\prod_{j=1}^a(Q^j-1).
\]
For \(e=\ell^k\), Fermat's congruence gives \(q^e\equiv q\pmod\ell\). Therefore \(|\Gamma_E|\equiv B\pmod\ell\), and \(\ell\) does not divide \(|\Gamma_E|\).

Fix the determinant or norm tuple required above. The set \(X\) of extension transporters meeting this requirement, if nonempty, is a right coset of a subgroup of \(\Gamma_E\). Indeed one transporter identifies the set with the source stabilizer intersected with the kernel of the specified homomorphism. The homomorphism used in assertion 2 is the coordinatewise determinant, and that in assertion 3 is its composition with coordinatewise norm. The same argument with the trivial homomorphism applies to ordinary TI. It follows that \(|X|\) divides \(|\Gamma_E|\) and is nonzero modulo \(\ell\).

The Frobenius \(x\mapsto x^q\) acts on \(X\), since the inputs and specified determinants lie in \(F\) and the norm is unchanged under Frobenius. Its action has period dividing \(\ell^k\). Every orbit other than a singleton has cardinality divisible by \(\ell\). Therefore \(X\) has a Frobenius-fixed transporter. Its entries lie in \(F\). In assertion 2 this is the desired transporter. In assertion 3 its norm tuple is the componentwise \(e\)th power of its actual determinant tuple. Positive dimensions imply \(q-1\mid B\), so \(\gcd(e,q-1)=1\). Thus the \(e\)th power map on \(F^\times\) is injective and the actual determinant tuple equals \(d\). The converse implications follow by extending scalars.

More generally this counting argument preserves feasibility for any Frobenius-stable subset of the transporter set that is a coset of a subgroup of \(\Gamma_E\) whenever it is nonempty. It requires no connectedness or component information. Counting certifies a fixed point without enumerating transporters or requiring the orbit to be small.

## Effective degree choice

The number of distinct prime divisors of \(B\) is at most \(\lfloor\log_2 B\rfloor\). From the group order formula,
\[
 \log_2 B\ \leq\ \Big(\textstyle\sum_i n_i^2\Big)\log_2 q.
\]
Include an extra prime in the search to avoid the characteristic as well. We can find a safe prime by sieving the first \(\lfloor\log_2 B\rfloor+2\) primes, using the standard bound that the \(j\)th prime has size \(O(j\log(2+j))\). Divisibility is tested by the displayed formula modulo a candidate prime. For fixed \(F\), a defining irreducible polynomial for the extension can be constructed deterministically in polynomial time by finite-field algorithms in fixed characteristic. For variable \(q\), the same prime selection and degree bound apply, and randomized finite-field construction suffices if an explicit extension is needed. The prime-power form lets the field size exceed any specified finite bound by raising \(k\). Effective polynomial size requires a polynomial bound on \(e\) in the application. [Shoup on construction of irreducible polynomials](https://www.ams.org/mcom/1990-54-189/S0025-5718-1990-0993933-0/S0025-5718-1990-0993933-0.pdf)

## The restriction on extension degree matters

Let \(F=\mathbb F_3\), let \(r\) be any odd prime, and let \(A=\mathbb F_{3^r}\). Compare the multiplication map \(T(x,y)=xy\) with the map \(-T\), using \(A\) as a vector space of dimension \(r\) over \(F\). For a multiplication map an autotopism is a triple \((U,V,W)\) such that \(U(x)V(y)=W(xy)\). Every autotopism has the form
\[
 (U,V,W)=(m_a\phi,m_b\phi,m_{ab}\phi)
\]
where \(m_a\) is multiplication by the unit \(a\), likewise for \(b\), and \(\phi\) is an algebra automorphism. To see this, set \(a=U(1)\), \(b=V(1)\), and substitute \(1\) in each slot. Invertibility makes \(a,b\) units and yields the displayed form with \(\phi=(ab)^{-1}W\). Multiplicativity of \(\phi\) follows from the autotopism equation. This argument applies to both a field and its split product after scalar extension.

Write \(\varepsilon=\det\phi\) over \(F\). The product of the three determinants of the autotopism equals \(\varepsilon\), since multiplication by a unit in \(A\) has determinant its field norm and every element of \(F^\times\) squares to one. Base-field automorphisms have odd order, hence \(\varepsilon=1\). The ordinary transporter \((-I,-I,-I)\) from \(T\) to \(-T\) has all three determinants \(-1\). Every other transporter differs by an autotopism, so all transporters have product of determinants \(-1\) over \(F\). The inversion or transposition incurred by identifying a bilinear map with a three-tensor leaves all three signs unchanged over \(F\).

Over the degree-\(r\) extension \(A/F\), the extended algebra splits as \(A^r\), by separability and its \(r\) embeddings. Swapping two factors gives an algebra automorphism whose determinant is \(-1\). Its diagonal autotopism cancels all three \(-1\) determinants of the displayed transporter. Thus \(T,-T\) become SL-isomorphic over the odd prime extension while they are not SL-isomorphic over \(F\). This raw multiplication tensor example shows that odd degree alone is insufficient.

## Implication for the reduction

Algebraic methods for the signed transporter may work over a field large enough for a generic choice or for polynomial interpolation. The theorem supplies a uniform family of lifts where a signed solution upstairs is already a signed solution downstairs in the exact decision sense. After restricting scalars, determinants of the extended linear maps are exactly their field norms, so the criterion also specifies the determinant predicate appropriate to that representation. The theorem supplies the descent step for such a method. Its quantitative prime selection does not construct a polynomial signed transporter test over the extension.

This is an informal deduction using the finite matrix group order, Frobenius and orbit counting. Publication priority for this formulation is unverified.
