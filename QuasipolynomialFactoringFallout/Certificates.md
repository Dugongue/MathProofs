# Finite-quotient polynomial calculus and deterministic closed-point search

Let \(K=\mathbb F_q\) be an explicitly represented finite field. Assume a deterministic algorithm for complete univariate factorization over explicitly represented finite fields, taking
\[
 ((2+d)^{\log(2+d)}(1+\log q))^{O(1)}
\]
bit operations on degree \(d\) over \(K\). The proof below uses this premise only for producing closed-point coordinates. The polynomial-calculus compiler, the exact extension-field point counts, and the construction of negative certificates are unconditional.

## 1. A finite-quotient proof compiler

Let \(B=(b_1,\ldots,b_D)\), with \(b_1=1\), be an order ideal of monomials in \(K[x_1,\ldots,x_n]\). Set \(\rho=\max_j\deg b_j\). The input supplies border equations
\[
 L_{ij}=x_i b_j-\sum_{k=1}^D(M_i)_{kj}b_k=0 .
\]
If \(x_i b_j\in B\), the specified column is its coordinate unit vector and the equation is implicit. The matrices \(M_i\) commute; this is checkable over \(K\). Write \(A\) for the quotient by the border equations. Its given basis is \(B\).

Use a division-free arithmetic circuit with \(S\) gates to specify further functions. Assign each gate a fresh variable and impose its gate equation, so every gate is defined from constants, the \(x\) variables and earlier gates by \(+\), \(-\), or \(\times\). Each terminal constraint is either \(v=0\) or \(v z-1=0\), where \(v\) is a gate, input variable or constant and a separate \(z\) is introduced in each nonvanishing constraint. Let \(T\) be the number of terminal constraints. All sparse PC sizes below count the sum of expanded monomial counts over lines.

**Theorem 1.** Over any field \(K\), this input admits a deterministic polynomial-time algebraic test for geometric consistency. In the inconsistent case the test constructs an ordinary Polynomial Calculus refutation of degree at most \(\rho+2\) and sparse size \(O((n+S+T+1) D^3)\). The refutation uses the given border axioms, gate equations and terminal equations. The degree bound is independent of the degrees of the functions computed by the circuits. Over a finite field the algorithm runs in bit time polynomial in \(n,D,S,T,\log q\) and the explicit field representation size.

A condition \(x_i\in\mathbb F_{q^r}\) can be imposed by binary power gates specifying \(x_i^{q^r}-x_i=0\). This adds \(O(r\log q)\) gates per constrained variable. Thus the theorem gives the same degree bound for negative finite-field queries when all \(x_i\) are constrained. It also gives a deterministic polynomial-size Hilbert-like IPS certificate for the original equations after the gate variables are eliminated. For inverse terminal constraints the inverse variables stay in the original ring.

### Validity of the border presentation

The order ideal property gives \(M^b e_1=e_b\) for all \(b\in B\) by a chain of divisors. The notation \(M^b\) denotes the product of the commuting matrices according to the exponents of \(b\). Consequently evaluation \(f\mapsto f(M)e_1\) is onto \(K^D\). Each \(L_{ij}(M)e_1=0\), and \(L_{ij}(M)\) commutes with \(b(M)\), so each \(L_{ij}(M)\) acts as zero on all basis vectors. Evaluation therefore factors through the quotient. Any monomial reduces to a linear combination of \(B\) in that quotient, by induction on its degree using the border equations. The induced map is an isomorphism of vector spaces. It gives multiplication in \(A\), which can also be precomputed as a \(D\times D\) multiplication table with entries in \(K^D\) in polynomial time. In particular \(\rho\le D-1\) by the divisor-chain property. For \(a\in A\) write \([a]\) for its unique \(B\)-representative.

### Straight-line normalization in PC

For every circuit variable or \(x\) variable \(u\), let \(\bar u\in A\) be its value in the quotient. For each such \(u\) and each \(j\), derive the row
\[
 R(u,j)=u b_j-[\bar u b_j].
\]
The input rows are border axioms. For constant gates these rows are multiples of the gate definition by \(b_j\). For an addition or subtraction gate, multiply its definition by \(b_j\) and combine the two child rows, with the corresponding signs. For a product gate \(u=vw\), combine
\[
 (u-vw)b_j,\qquad
 v\big(wb_j-[\bar w b_j]\big),\qquad
 \sum_k c_k\big(vb_k-[\bar v b_k]\big),
 \quad [\bar w b_j]=\sum_k c_k b_k .
\]
The sum is \(R(u,j)\). This also works for \(v=w\) and for either operand constant, with the zero normalizations for constants omitted. Each multiplication by \(b_j\) is realized by at most \(\rho\) single-variable multiplications. Every line has degree at most \(\rho+2\). The sum with \(D\) coefficients is formed with binary linear combinations. All partial sums are supported in at most \(2D\) monomials, namely the \(vb_k\) and the \(b_k\). The other lines cost \(O(D)\) monomials for each \(j\), including the \(O(\rho)\) gate multiples, each with at most three monomials. Thus all normalizations cost \(O((n+S+1)D^3)\).

For a terminal equality \(v=0\), multiply it by each \(b_j\) and subtract the corresponding normalization. This derives the representatives of \(\bar v b_j\), spanning the ideal \(A\bar v\). Multiplication of an axiom by a monomial here means consecutive multiplication by its variables.

### Inverting a terminal value

For a terminal equation \(vz-1=0\), let \(M\) be multiplication by \(\bar v\) on \(A\); set \(E_i=\ker M^i\) for \(i\ge 0\). Stabilization occurs by \(E_D\). For each \(j\), combine \((vz-1)b_j\) and \(z R(v,j)\) to derive
\[
 z[M b_j]-b_j.
\]
For any \(a\in A\), a scalar linear combination of these rows gives \(z[Ma]-[a]\). Choose a basis of \(E_D\) extending a chosen basis of \(E_i\) at each step. For each new basis vector \(a\in E_i\), the vector \(Ma\) lies in \(E_{i-1}\). The induction hypothesis gives \([Ma]\) by a scalar linear combination of earlier derived basis lines. Multiply by \(z\) and subtract \(z[Ma]-[a]\) to derive \([a]\). If \(Ma=0\), the latter row already gives the conclusion up to sign. This uses at most \(D\) new basis vectors for each terminal nonvanishing, \(O(D^3)\) sparse size, and degree at most \(\rho+2\).

The ideal \(E_D\) is exactly the kernel of \(A\to A[1/\bar v]\). For a direct finite-dimensional proof, use the decomposition \(A=\ker M^D\oplus\operatorname{im}M^D\). Both subspaces are ideals and their intersection is zero, since the kernels stabilize by \(D\). Multiplication by \(\bar v\) is invertible on the image. Equivalently \(A/E_D\) already makes \(\bar v\) a unit, and every homomorphism making \(\bar v\) a unit kills \(E_D\).

Let
\[
 J=\sum_{v=0}A\bar v+\sum_{vz-1=0}\ker(M_{\bar v}^{D}).
\]
The gate equations eliminate the gate variables uniquely. The remaining quotient is obtained by imposing the terminal equalities and inverting the specified values. It is precisely \(A/J\), since the corresponding inverses already exist there and are unique. The field-valued points, including the inverse and gate coordinates, agree over every extension field. If \(A/J\ne0\), any maximal ideal yields a finite extension of \(K\), hence a geometric solution. If \(A/J=0\), Gaussian elimination gives the coordinates of \(1\) as a linear combination of the derived representatives. A basis of those representatives has at most \(D\) elements, so the concluding combination also costs at most \(O(D^2)\) sparse size. This proves Theorem 1.

### Eliminating the auxiliary gates in IPS

Track each line \(P\) of the PC proof by a circuit expression \(C_P(x,y,z;\mathcal Y)\) linear in axiom placeholders \(\mathcal Y\). At an axiom use its placeholder; at a scalar sum or variable multiplication perform the same operation on the expression circuits. Sharing intermediate lines keeps the arithmetic circuit size linear in the number of proof lines up to a constant. At the final line this gives a Hilbert-like IPS certificate: substituting axioms yields \(1\), and substituting zero for the placeholders gives zero. Now substitute each gate variable by its original division-free gate expression and each gate-definition placeholder by zero. Keep sharing the original circuit computations. The resulting IPS proof uses the border and terminal equations directly, with size \(O((n+S+T+1)D^3)\). The formal identities follow from the checked PC derivation, so this construction needs no test for arbitrary circuit identities. The resulting certificate may have high degree.

If the border equations have supplied ideal-combination certificates in a different list \(F\), substitute those certificates for the border placeholders as well. The IPS size grows by the total size of the shared substitution circuits. For identical solution sets in the positive branch it suffices also to check that each member of \(F\) reduces to zero in \(A\).

## 2. Every extension-field count without factoring

Let \(K=\mathbb F_q\) again and put \(A_*=A/J\). Write \(F(a)=a^q\) for its \(K\)-linear Frobenius. Compute this matrix on a basis by binary powering. For \(r\ge1\), form the ideal \(H_r\) in \(A_*\) spanned by the products of basis elements with \(F^r(\bar x_i)-\bar x_i\), for \(1\le i\le n\).

**Theorem 2.** Let \(c_e\) be the number of degree-\(e\) closed points of the original constrained system. From the finite quotient one can compute the entire \(c_e\) list deterministically in polynomial bit time without factoring. For every \(r\ge 1\) the number of \(\mathbb F_{q^r}\)-valued solutions is
\[
 N_r=\dim_K(A_*/H_r)=\sum_{e\mid r}e\,c_e .
\]
It is sufficient to compute the ranks for \(1\le r\le D\). For a specified \(r\) in binary, its count and feasibility also follow in polynomial time in \(\log r\). If \(N_r=0\), Theorem 1 produces its gate-lifted PC refutation and raw Hilbert-like IPS proof in time polynomial in \(r\log q\) and the original presentation size.

To prove the formula, the quotient \(A_*/H_r\) is generated by the \(\bar x_i\), all satisfying \(t^{q^r}-t=0\). After extension to \(\overline K\), the polynomial has \(q^r\) distinct roots. Before taking the quotient, imposing these equations on the polynomial ring gives a direct product of one copy of \(\overline K\) per point in \((\mathbb F_{q^r})^n\) by the Chinese remainder theorem. Taking the remaining quotient keeps exactly the solutions. The lifted gate and inverse coordinates are uniquely determined and lie in the same field. Separately, a closed point of residue degree \(e\) admits exactly \(e\) embeddings into \(\mathbb F_{q^r}\) when \(e\mid r\), and none otherwise. Every residue degree is at most \(\dim_K A_*\le D\). Möbius inversion gives
\[
 c_e=\frac1e\sum_{j\mid e}\mu(e/j)\dim_K(A_*/H_j).
\]
Successive Frobenius matrix products and ordinary ranks compute this list. For a binary query \(r\), either use the list and test divisibility or power the Frobenius matrix by repeated squaring. The latter calculation does not construct the powers as formal polynomials.

## 3. Factoring and deterministic affirmative witnesses

**Theorem 3.** Under the factorization premise, the same input yields a complete list of closed-point witnesses in
\[
 \operatorname{poly}(n,S,T,\log q,\text{representation size})
 \,((2+D)^{\log(2+D)}(1+\log q))^{O(1)}
\]
bit operations. For each point the output contains a monic irreducible \(h\in K[t]\) and all coordinates in \(K[t]/(h)\), with the base coordinates generating that field. Factorization calls are over \(K\) and have degree at most \(D\). Conversely, deterministic production of even one such closed-point witness for every nonempty input gives complete univariate factorization under polynomial-time Turing reductions, already in the one-variable case with no further gates or terminals. For rational-witness search over the base field alone, solving all base-field inputs likewise implies complete factorization of split polynomials over the base field.

Indeed let \(C=\{a\in A_*:F(a)=a\}\) and let \(s\) be its dimension. The Artinian decomposition of \(A_*\) gives one residue field per local Artinian factor. On one such factor a fixed element has residue in \(K\). Subtract that scalar. The difference is nilpotent and fixed by Frobenius, so it is zero after iterating Frobenius. Consequently \(C\cong K^s\), with one coordinate per closed point, even when \(A_*\) has nilpotents.

If the quotient is zero, return the empty list. Otherwise take any linear basis \(c_1,\ldots,c_s\) of \(C\). Starting with the idempotent \(1\), refine every current nonzero idempotent \(e\) using multiplication by \(ec_i\) on \(eA_*\). Its minimal polynomial is squarefree and split over \(K\), because \(ec_i\) acts by its scalar value on each local factor. Compute it by linear dependence of \(e,ec_i,(ec_i)^2,\ldots\) and factor it. For each distinct root \(a\), the smaller idempotent is
\[
 e\prod_{b\ne a}\frac{ec_i-be}{a-b},
\]
where the product is computed with unit \(e\) in \(eA_*\). For a one-root polynomial the result is just \(e\). Every basis element is constant on each eventual block, so the blocks are the primitive idempotents, since a basis of \(K^s\) separates each pair of coordinates. There are at most \(D^2\) factorization calls. This branch only needs factorization of squarefree split polynomials over the base field, the classical Berlekamp form of the splitting problem. [Berlekamp, Factoring Polynomials Over Finite Fields](https://doi.org/10.1002/j.1538-7305.1967.tb03174.x)

For each primitive idempotent, quotient \(eA_*\) by the kernel of \(F^j\) for the smallest \(j\) with \(q^j\ge D\). Nilpotent elements of a \(D\)-dimensional algebra have exponent at most \(D\); no nonzero field element is killed. Thus this kernel is exactly the nilradical, and the resulting multiplication table is its residue field \(L\cong\mathbb F_{q^m}\). All quotient maps and generator coordinates are obtained by linear algebra.

One can replace this table by a univariate presentation without additional factoring over fields. Factor the integer \(m\le D\) by trial division. For each prime power \(\ell^a\Vert m\), find an element \(\alpha_\ell\) of
\[
 \ker(F^{\ell^a}-1)\setminus\ker(F^{\ell^{a-1}}-1)
\]
by taking a basis of the first subspace and testing membership in the second. This element generates the degree-\(\ell^a\) subfield \(L_\ell\). When \(m>1\), take \(\alpha=\prod_\ell\alpha_\ell\). If \(F^r\) fixes \(\alpha\), the ratio \(F^r(\alpha_\ell)/\alpha_\ell\) is in \(L_\ell\) and equals the inverse of the product of all other ratios, which belongs to the compositum of the other degree-prime-power subfields. Their intersection is \(K\). Since each ratio belongs to \(K^\times\), iterating \(F^r\) through \(\ell^a\) steps shows its order divides \(\ell^a\). The ratios multiply to \(1\); their orders divide pairwise coprime integers, so every ratio is \(1\). Hence every \(\ell^a\) divides \(r\), and \(\alpha\) has degree \(m\). Its minimal polynomial \(h\) and the old coordinates in the basis \(1,\alpha,\ldots,\alpha^{m-1}\) are obtained by linear algebra. For \(m=1\), use the trivial presentation \(h=t\). These operations add polynomial bit cost only. The output has one residue field per closed point; conjugate geometric points correspond to the embeddings of that field. For a prescribed target field, the list specifies precisely which witness fields admit embeddings into it. When that field is supplied with its embedding of K, factor each admitted h there and evaluate the output coordinates at any root, or at all roots to list every point. These extra calls still have degree at most D and use the bit length of the target field order.

For the converse take \(A=K[x]/(f)\) for a nonconstant monic \(f\), with the standard power basis and the one nontrivial border equation \(f=0\). An algorithm that returns one closed-point witness returns a root \(a\) in an explicit finite extension. The minimal polynomial of \(a\) over \(K\) is an irreducible divisor of \(f\) and is computable by linear algebra. Divide out this factor to its full multiplicity and repeat. All calls have degree at most \(\deg f\); with rational-witness search alone the same procedure works on split \(f\). Thus the affirmative witness branch has a genuine factoring dependency even though its extension-degree spectrum, consistency and negative certificates can be found without factoring.

## 4. A sharp encoding separation

**Theorem 4.** For odd \(q\), choose a nonsquare \(a\in\mathbb F_q^\times\), an odd positive \(r\), and \(Q=q^r\). The two raw sparse axioms \(x^2-a=0\) and \(x^Q-x=0\) have ordinary PC degree exactly \(Q\), minimum PC line count and sparse size both \(\Theta(Q)\), and minimum Hilbert-like IPS circuit size \(\Theta(\log Q)\). The binary-power gate lift has an ordinary PC refutation of degree at most \(3\) and sparse size \(O(\log Q)\).

Modulo \(f=x^2-a\), the field axiom \(g=x^Q-x\) has remainder \(-2x\): a root of \(f\) has its sign reversed under \(q\)-Frobenius and therefore under the \(r\)th power of that Frobenius. Ordinary PC derives \(x^Q-a^{(Q-1)/2}x\) in \(O(Q)\) sparse size by multiplying the preceding two-term consequence twice by \(x\) and combining with a scalar times \(x f\). Here \(x f\) is derived once. This yields \(x=0\) and then the contradiction. All degrees are at most \(Q\). Any refutation must use \(g\), since \(f\) alone is consistent over \(\overline K\), proving degree at least \(Q\).

For the line lower bound discard zero lines, replacing their uses in linear combinations by scalar combinations of the other inputs. Track each remaining PC line as an expression \(A(x)f+B(x)g\) by following the proof rules. Each multiplication by \(x\) increases the possible degree of \(A\) by at most one, and addition cannot increase the maximum. In the final expression for \(1\), \(B\ne0\). Degree cancellation forces \(\deg A+2=\deg B+Q\), hence a path from \(f\) to the final line contains at least \(Q-2\) multiplication steps. This yields the same lower bound on the sparse size. In a Hilbert-like circuit the coefficient \(A\) is computed by setting the \(f\) placeholder to one and the \(g\) placeholder to zero. A fan-in-two arithmetic circuit with \(s\) gates computes a polynomial of degree at most \(2^s\), so its size is \(\Omega(\log Q)\). For the matching upper bound, use Theorem 1 and its IPS elimination with \(D=2\), \(B=(1,x)\), \(\rho=1\) and \(O(\log Q)\) gates computing \(g\). The same application gives the lifted sparse PC upper bound.

## Relation to earlier work

The border presentation and its commuting multiplication matrices are standard. Abbott, Bigatti, Palezzato and Robbiano already use Frobenius fixed spaces and minimal polynomials for finite-algebra decomposition. The conditional positive branch here specializes that algebra and records a precise factoring equivalence, with polynomial-size certificates on the opposite branch. The proof-complexity content is the degree-\(\rho+2\) sparse compiler for arbitrarily long circuits and terminal localizations, including the unconditional computable extension profile and the raw-versus-lifted quantitative example. [Kehrein and Kreuzer, Computing border bases](https://doi.org/10.1016/j.jpaa.2005.07.006) · [Abbott, Bigatti, Palezzato and Robbiano, Computing and Using Minimal Polynomials](https://arxiv.org/abs/1702.07262) · [Grochow and Pitassi, Circuit Complexity, Proof Complexity, and Polynomial Identity Testing](https://arxiv.org/abs/1404.3820)

For example, independent coordinate restrictions \(f_i(x_i)=0\), with each \(f_i\) monic of degree \(d_i\ge1\), give this presentation immediately with \(D=\prod_i d_i\) and \(\rho=\sum_i(d_i-1)\). Arbitrary division-free circuits of extra equalities and inequalities can then be processed with degree \(\sum_i(d_i-1)+2\), even when a circuit computes a polynomial of degree exponential in its length. The size guarantee is polynomial in the finite quotient dimension and can be exponential in the number of independent coordinates.

In the earlier bounded-mode tensor search, the terminal finite-system branch can use Theorems 1–3 once its finite quotient and any border derivations are available. Random chart selection and slicing precede that branch. The new PC degree claim applies to the stated gate-lifted presentation. It leaves the unrestricted ordinary tensor PC questions open. [Galesi, Grochow, Pitassi and She, On the Algebraic Proof Complexity of Tensor Isomorphism, Section 7](https://arxiv.org/html/2305.19320)

Exact finite arithmetic checks covered 13,816 extension-rank comparisons against direct irreducible-divisor counts, 1,860 localization-kernel computations, and nine irreducible-quadratic remainder calculations over small prime fields. The general arguments are written proofs. The finite-field factoring bound is an input assumption for Theorem 3. Theorems 1, 2 and 4 are unconditional. Publication priority of the proof-complexity formulation has not been established.
