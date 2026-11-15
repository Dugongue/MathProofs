# Perfect evolution-algebra counts are polynomial on residue classes

Informal proof of Conjecture 8 in Kaygorodov, Martín González and Viruel, *Evolution algebras: A survey of results and a list of open problems*, §2.3. It asks whether, for every fixed \(n\), the number \(N_n(q)\) of isomorphism classes of perfect \(n\)-dimensional evolution algebras over \(\mathbb F_q\) is a polynomial in \(q\) on each residue class modulo a fixed positive integer. We prove this for all prime powers, including those of small characteristic. The polynomial coefficients may be rational, as in the usual definition of PORC. [Original Conjecture 8](https://arxiv.org/html/2610.22248v1#S2.SS3)

## 1. Burnside reduces the problem to similarity of monomial cycle blocks

A natural basis \(e_1,\ldots,e_n\) has \(e_i e_j=0\) for \(i\ne j\). The structure matrix \(M\) has columns \(e_i^2\). Perfectness means that these columns form a basis, so \(M\) is invertible. In another natural basis having change-of-basis matrix \(P\), the vanishing of mixed products forces \(P_{ij}P_{ik}=0\) for every row \(i\) and \(j\ne k\), by independence of the squares. Thus the invertible \(P\) is monomial. Conversely a monomial matrix takes natural bases to natural bases.

The isomorphism types are therefore the orbits of the monomial group \(G_q\) on \(\mathrm{GL}_n(\mathbb F_q)\) under
\[
M\longmapsto PM(P^{[2]})^{-1},
\]
where \(P^{[2]}\) squares the entries. This is a group action. Entrywise squaring respects products of monomial matrices, as each product entry is a single nonzero product or zero. In particular the fixed points of \(P\) are exactly the invertible solutions of \(PM=MP^{[2]}\). There are none unless \(P\) and \(P^{[2]}\) are similar as ordinary matrices. If similar, the invertible solutions form a coset of the invertible centralizer of \(P\).

Fix a permutation \(\sigma\) of cycle lengths \(\ell_1,\ldots,\ell_r\). The product \(a_j\in\mathbb F_q^\times\) of the entries along cycle \(j\) specifies its companion block \(X^{\ell_j}-a_j\), since a coordinate vector on the cycle is cyclic. Every tuple of products occurs for \((q-1)^{n-r}\) monomial matrices with that \(\sigma\). For \(P^{[2]}\) the polynomials are \(X^{\ell_j}-a_j^2\). Write \(W_\sigma(a,q)\) for zero when they fail similarity and for \(|C_{\mathrm{GL}_n(q)}(P)|\) when they pass. Burnside's formula becomes
\[
N_n(q)=\frac1{n!}\sum_{\sigma\in S_n}
 \frac{1}{(q-1)^{r(\sigma)}}\sum_{a\in(\mathbb F_q^\times)^{r(\sigma)}}
 W_\sigma(a,q).
\]

## 2. Roots of cycle blocks are classified by finitely many monomial patterns

Treat each possibility for the characteristic \(p\le n\) separately, together with one case \(p>n\). These regimes can be recognized by residues modulo the product of the primes at most \(n\), on the domain of prime powers. In each regime the integers \(\ell_j=p^{v_j}m_j\) with \(p\nmid m_j\) give fixed \(m_j\) and fixed \(p^{v_j}\), including \(p^{v_j}=1\) in the large-characteristic regime.

Let \(D=\mathrm{lcm}(1,\ldots,n)\), \(E=\mathbb F_{q^D}\) and \(h=\mathrm{lcm}(m_1,\ldots,m_r)\). All cycle roots lie in \(E\), because each has minimal polynomial of degree at most \(n\), hence degree dividing \(D\). Also \(h\mid q^D-1\). In fact the order of \(q\) modulo each \(m_j\) divides \(\varphi(m_j)\le n\), so is a divisor of \(D\). Ignore the vacuous \(m_j=1\) when speaking of an order modulo \(m_j\).

Take variables \(z_1,\ldots,z_r,\xi\in E^\times\) subject to
\[
z_j^{\ell_j(q-1)}=1,\qquad
\xi^h=1,\qquad \xi^{h/u}\ne1\quad(u\text{ prime},\ u\mid h).
\]
These set \(a_j=z_j^{\ell_j}\in\mathbb F_q^\times\) and make \(\xi\) a primitive \(h\)-th root of unity. For tuple \(a\), there are exactly \(\varphi(h)\prod_j m_j\) lifts of this form, with \(\varphi(1)=1\). The roots in the first and second lists of cycle blocks are represented by the slots
\[
z_j \xi^{(h/m_j)b},\qquad z_j^2\xi^{(h/m_j)b},
\quad 0\le b<m_j,
\]
respectively. Each first-list slot and each second-list slot contributes one Jordan block of size \(p^{v_j}\) at its eigenvalue. That is because \(X^{\ell_j}-a_j\) has exactly the distinct roots shown, each of multiplicity \(p^{v_j}\), and its companion module is cyclic. The same applies with \(a_j^2\). This also handles characteristic two.

Record a pattern consisting of all equalities of slots and all equalities of the \(q\)-th power of a slot with a slot. It is a finite pattern on at most \(2n\) slots, independent of \(q\) within each regime. Equal slots recover the multiset of Jordan lengths from each side at every eigenvalue. The \(q\)-power data recover its Frobenius orbit, hence the degree of its irreducible factor over \(\mathbb F_q\). The two matrices are similar exactly when at every eigenvalue the two lists of lengths agree. One can see this either from the elementary divisor theorem, or from the primary cyclic blocks grouped by each irreducible factor. The same pattern gives the invertible centralizer size as a fixed polynomial in \(q\). Here is the needed formula.

For one irreducible \(f\) of degree \(d\), let \(t_s\) be the number of elementary divisors \(f^s\) in the first matrix. The primary endomorphism algebra has dimension \(D_f=d\sum_{a,b} t_a t_b\min(a,b)\), as the homomorphism space between cyclic summands of lengths \(a,b\) has dimension \(d\min(a,b)\). Its quotient obtained by reducing same-length diagonal blocks modulo \(f\) is \(\prod_s M_{t_s}(\mathbb F_{q^d})\). The map is multiplicative since any composition through a different length reduces to zero on returning to the original length modulo \(f\). Its kernel is nilpotent. Indeed an element of valuation at least \(v\) in a cyclic summand of length \(a\) maps under an off-diagonal kernel block to valuation at least \(v+\max(b-a,0)\) in length \(b\). This strictly raises the weight \(2v-a\) if \(a\ne b\). On a same-length kernel block the valuation rises by at least one. There are only finitely many possible weights for nonzero layers, proving nilpotence. Thus quotient units lift and the unit count on this primary part is
\[
q^{D_f-d\sum_s t_s^2}
\prod_s |\mathrm{GL}_{t_s}(\mathbb F_{q^d})|.
\]
This is polynomial in \(q\), since \(|\mathrm{GL}_u(\mathbb F_{q^d})|=\prod_{i=0}^{u-1}(q^{du}-q^{di})\). Homomorphisms between distinct primary parts vanish and the total centralizer count is the product of these polynomials. This proves the pattern claim.

## 3. Monomial pattern counts are PORC

Every condition defining a pattern is a homogeneous monomial equality or inequality in the nonzero variables \(z_j,\xi\). All exponents are integer polynomials in the variable \(q\), because Frobenius raises to \(q\) and all listed root exponents are fixed integers. We recall an elementary proof of the requisite PORC counting fact. This is the monomial-counting method of Higman as simplified by Vaughan-Lee. [Vaughan-Lee, *Choosing elements from finite fields*](https://arxiv.org/abs/1707.09652)

For equalities alone, choose an abstract generator of the cyclic group \(E^\times\) of order \(Q(q)=q^D-1\). With \(s\) variables and exponent matrix \(A(q)\), the count is the number of solutions of \(A(q)v=0\bmod Q(q)\) in \((\mathbb Z/Q(q))^s\). It equals the index of the lattice in \(\mathbb Z^s\) generated by the rows of \(A(q)\) and \(Q(q)I_s\). In fact it is the size of the group of characters of that lattice quotient with values in \(\mathbb Z/Q(q)\), equal to the number of elements of the quotient since its exponent divides \(Q(q)\). The index is the gcd of the \(s\)-row minors of the stacked matrix, by Smith normal form.

Write those finitely many minor polynomials as \(D_0(q)b_i(q)\), where \(D_0\in\mathbb Z[X]\) is their primitive polynomial gcd and \(b_i\in\mathbb Z[X]\) have gcd one over \(\mathbb Q[X]\). Gauss's lemma gives this integral division. An integer-polynomial combination of the \(b_i\) equals a fixed nonzero integer \(c\), by clearing denominators in Bézout's identity. Thus \(\gcd_i b_i(q)\) divides \(|c|\) and is determined by \(q\bmod |c|\). Also \(D_0\) divides the particular minor \((X^D-1)^s\), so its sign is constant on real \(q>1\). The desired gcd is therefore polynomial in \(q\) on residue classes. Inclusion–exclusion now handles all required nonequalities. This proof works with any characteristic regime fixed in Section 2.

Sum the resulting counts against the fixed centralizer polynomial for each pattern passing similarity, and divide by \(\varphi(h)\prod_j m_j\), the uniform number of lifts. The sum \(\sum_a W_\sigma(a,q)\) is PORC. Taking common periods over the finitely many permutations and characteristic regimes in the Burnside formula gives, on each residue class, a rational function of \(q\) with denominator a power of \(q-1\) times a nonzero integer.

## 4. Integrality removes the remaining denominators

For a fixed residue class, write that rational function as \(P(q)+R(q)\) by polynomial division over \(\mathbb Q\), where \(R(q)\to0\) as \(q\to+\infty\). There is a fixed positive integer \(B\) such that \(BP(q)\in\mathbb Z\) for every integer \(q\), by clearing its coefficient denominators. For every prime power in the residue class, \(N_n(q)\) is an integer. Therefore \(R(q)\in (1/B)\mathbb Z\) on those \(q\). If there are infinitely many, eventually \(|R(q)|<1/B\), hence \(R(q)=0\) on infinitely many values. Its numerator is identically zero, so \(N_n(q)=P(q)\) for every prime power in the class. If there are only finitely many prime powers in the class, a rational interpolation polynomial takes the prescribed finite values. The result is PORC on all prime powers. The dimension-zero convention, if included, is the constant count one.

The earlier work behind this argument is the general Higman–Vaughan-Lee monomial count. The application here uses the twisted action \(PM(P^{[2]})^{-1}\) to avoid counting invertible solutions of an arbitrary array of monomial constraints. Similarity reduces invertibility to a centralizer polynomial. Wei and Zou give the monomial orbit and Burnside framework and exact counts in dimensions two to four. A bounded search of arXiv, published sources, public settlement indexes and the MathProof source catalog found the general counting antecedents and the low-dimensional results, with no matching all-dimensional evolution-algebra proof. This is a literature-screen statement. The argument above supplies the full conjecture independently of any priority claim. [Wei–Zou](https://arxiv.org/abs/2310.12368), [Survey §2.3 and references](https://arxiv.org/html/2610.22248v1#S2.SS3), [Higman's PORC theorem survey](https://arxiv.org/abs/1808.04145)

## 5. Leading coefficient and finite controls

For \(n\ge3\) take the identity contribution in Burnside separately. It equals
\[
\frac{|\mathrm{GL}_n(q)|}{n!(q-1)^n}
=\frac{q^{n^2-n}}{n!}+O_n(q^{n^2-n-1}).
\]
A nonidentity scalar monomial cannot pass the similarity test since \(a=a^2\) in \(F_q^\times\) implies \(a=1\). For a nonscalar matrix the full centralizer algebra has dimension at most \((n-1)^2+1\). To see this, over an algebraic closure its dimension is the sum of squares of all its Jordan column lengths, summed over eigenvalues by the preceding endomorphism count. The lengths sum to \(n\), and nonscalarity excludes a single length \(n\). The sum of their squares is therefore at most \((n-1)^2+1\). Each nonidentity contribution to the averaged Burnside sum is \(O(q^{n^2-2n+2})\). This is \(O(q^{n^2-n-1})\) for \(n\ge3\). Thus every residue class containing infinitely many prime powers has polynomial degree \(n^2-n\) and common leading coefficient \(1/n!\).

As an independent finite control, direct monomial-orbit enumeration on invertible matrices gives \(N_2(2)=4\), \(N_2(3)=7\), \(N_2(5)=17\), \(N_2(7)=32\), \(N_3(2)=33\), and \(N_3(3)=249\).
