# Inverting a quadratic on the Boolean cube is VNP-hard

Let \(K\) be a field and let \(\operatorname{ML}\) denote the unique multiaffine polynomial with prescribed Boolean-cube values over \(K\). Circuit size counts binary arithmetic gates in a division-free circuit with arbitrary field constants. A c-reduction may use oracle gates for the source polynomial on polynomial inputs.

For \(n\ge1\), define the perfect-matching defect by
\[
 h_n(X)=\sum_{i=1}^n\left(1-\sum_{j=1}^n X_{ij}
                      +2\sum_{1\le j<k\le n} X_{ij}X_{ik}\right)
       +\sum_{j=1}^n\left(1-\sum_{i=1}^n X_{ij}
                      +2\sum_{1\le i<k\le n} X_{ij}X_{kj}\right).
\]
At a Boolean matrix \(a\), this equals the sum of squares \(\sum_i(\operatorname{rowsum}_i(a)-1)^2+\sum_j(\operatorname{colsum}_j(a)-1)^2\) over the integers. Its integer values are in \([0,B_n]\), where \(B_n=2n^3\), and \(h_n(a)=0\) precisely at permutation matrices.

## Theorem

**Rational reciprocal.** In characteristic zero, \(R_n=\operatorname{ML}(1/(1+h_n))\) is a VNP-complete family under polynomial-size c-reductions. More precisely, put \(N=13n+6\). A size-\(s\) circuit for \(R_N\) yields a size-\(O(n^2(B_n+1)(s+1)+n^3)\) circuit for \(\operatorname{per}_n\). The pointwise size transfer and oracle construction also hold in characteristic \(p>2N^3+1\).

**Hilbert IPS.** Let \(p_i=X_i^2-X_i\), with the \(n^2\) entries indexed by \(i\). The minimum circuit sizes of \(R_n\) and of a Hilbert IPS refutation \(C=YG+\sum_i Z_i Q_i\) for the system \(1+h_n=p_1=\cdots=p_{n^2}=0\), with multiaffine \(Y\)-coefficient \(G\), are polynomially related. Over any fixed characteristic-zero field, polynomial-size refutations of this type for the family exist exactly when \(\mathrm{VP}_K=\mathrm{VNP}_K\).

**Cyclotomic reciprocal.** Let \(\ell\) be any prime in \((B_n+2,2(B_n+2))\) and let \(\alpha\) be a primitive \(\ell\)-th root of unity. A size-\(s\) circuit over \(\mathbb C\) for the single \(n\times n\) reciprocal
\[
 S_{n,\ell}=\operatorname{ML}\bigl(1/(\alpha-h_n)\bigr)
\]
yields a size-\(O(n^2(B_n+1)(s+1)+n^3)\) circuit for \(\operatorname{per}_n\) over \(\mathbb C\). If \(p>B_n\) and \(\operatorname{ord}_\ell(p)=\ell-1\), the polynomial reduces coefficientwise to \(\mathbb F_{p^{\ell-1}}\) and the same size bound holds over that field or its algebraic closure. For circuits over \(\mathbb F_{p^{\ell-1}}\), one obtains a circuit for \(\operatorname{per}_n\) over \(\mathbb F_p\) with a further \(O(\ell^2)\) factor. Under Dirichlet GRH, uniformly for such \(\ell\) and sufficiently large \(n\), at least
\[
 c\,\frac{\varphi(\ell-1)}{\ell-1}\frac{B_n}{\log B_n}
\]
primes in \((B_n,2B_n]\) meet the order condition, for an absolute constant \(c>0\). A deterministic scan polynomial in \(n\) finds such a prime. The finite-field complexity assertions are pointwise in \(n,p\).

## Multiaffine interpolation and permanent recovery

For a Boolean assignment \(a\), set \(L_a(X)=\prod_{i:a_i=1}X_i\prod_{i:a_i=0}(1-X_i)\). These polynomials have the Kronecker delta evaluation table and form a basis of the multiaffine polynomials. For each allowable \(u\), write \(g_{n,u}=\operatorname{ML}(1/(u-h_n))\) and let \(I_n=\sum_{a\text{ permutation}}L_a\).

Suppose \(0,\ldots,B_n\) are distinct in \(K\) and \(u_0,\ldots,u_{B_n}\) are distinct elements of \(K\) outside that list. Put \(D(T)=\prod_{j=0}^{B_n}(T-j)\). The polynomial
\[
 Z(X,T)=\sum_{a\in\{0,1\}^{n^2}} \frac{D(T)}{T-h_n(a)} L_a(X)
\]
has degree at most \(B_n\) in \(T\). At \(T=u_i\) it is \(D(u_i)g_{n,u_i}(X)\). At \(T=0\) each summand vanishes except those with \(h_n(a)=0\), and those have coefficient \(D'(0)=(-1)^{B_n}B_n!\). Scalar Lagrange interpolation at zero expresses \(I_n\) as an explicit linear combination of the \(B_n+1\) reciprocal polynomials. If each reciprocal circuit has size at most \(s\), this gives a circuit for \(I_n\) of size \(O((B_n+1)(s+1))\).

We recover the permanent using
\[
 \prod_i(1+tX_i)\, I_n\left(\left(\frac{tX_i}{1+tX_i}\right)_i\right)
      =t^n\operatorname{per}_n(X).
\]
For each \(L_a\), the product clears the denominators and leaves \(\prod_{i:a_i=1}tX_i\). To implement the substitution modulo \(t^{n+1}\), use \(U_i(t,X_i)=\sum_{k=1}^n(-1)^{k-1}t^kX_i^k\). Implement each gate of the circuit for \(I_n\) in the truncated polynomial ring by operating on coefficient vectors, using at most \(O(n^2)\) gates per old gate. The substituted input vectors and the product \(\prod_i(1+tX_i)\) each cost \(O(n^3)\) gates by successively updating coefficient lists. Extracting the coefficient of \(t^n\) gives the quantitative size bound.

For a black-box reduction, the expression \(\prod_i(1+tX_i)I_n((U_i(t,X_i))_i)\) is an ordinary polynomial of \(t\)-degree at most \((n+1)n^2\), since \(I_n\) is multiaffine. Its coefficient of \(t^n\) is still the permanent. Evaluate the expression at \((n+1)n^2+1\) distinct field scalars and apply univariate interpolation, using only polynomial inputs to each oracle. There are enough scalars in characteristic zero and in the finite-characteristic range of the rational theorem. For the cyclotomic size transfer, we use the explicit circuits because the conjugations act on circuit constants.

For membership in VNP, interpolate a univariate polynomial \(F\) of degree at most \(B_n\) with \(F(j)=1/(u-j)\) for \(0\le j\le B_n\). Then \(g_{n,u}(X)\) is the Boolean sum of
\[
 F(h_n(A))\prod_i\bigl(A_iX_i+(1-A_i)(1-X_i)\bigr).
\]
This summand has polynomial size and degree in \(A,X\). It gives \(R_n\) by using \(u=-1\) and changing the overall sign. It also gives the cyclotomic reciprocal for \(u=\alpha\), both over \(\mathbb C\) and over the stated residue fields. Valiant's completeness of the permanent in characteristic zero supplies VNP-hardness for the rational family by composition of c-reductions. [Valiant, *Completeness Classes in Algebra*.](https://doi.org/10.1145/800135.804419)

## Linear-size padding for rational shifts

Use \(m=2n\), \(d=3(m+1)\), \(t=\lceil\sqrt{m+1}\rceil\), and \(q=2d\). Inside a \(q\times q\) Boolean block take \(3m\) disjoint row pairs, with the other \(q-6m=6\) rows zero. In a row pair put exactly one 1 in each column, splitting them into row totals \(d+\Delta\) and \(d-\Delta\). Its row defect is \(2(d-1)^2+2\Delta^2\). All column sums stay \(3m\). In the successive groups of \(m\) row pairs, allow \(\Delta\) to be either 0 or, respectively, \(d,t,1\). The outside defect is of the form
\[
 c_0+2(a d^2+b t^2+c),\qquad a,b,c\in\{0,\ldots,m\},
\]
with \(c_0\) independent of \(a,b,c\). There are \((m+1)^3>B_n+1\) distinct shifts, since \(t^2>m\) and \(d^2>mt^2+m\). The latter follows from \(t^2\le4(m+1)\) and \(d^2=9(m+1)^2\). Comparing the largest place where two tuples differ proves distinctness. A row pair can be filled by putting the first \(d+\Delta\) ones in the first row and the remaining ones in the second.

Embed \(X\) beside this block as the two diagonal blocks of an \(N\times N\) matrix, \(N=n+q=13n+6\), with all off-block entries zero. The defect adds across the blocks on Boolean inputs. If the outside defect is \(c_*\), specializing \(R_N\) gives \(-g_{n,-1-c_*}\) by unique multiaffine interpolation. The distinct parameters \(-1-c_*\) avoid \(0,\ldots,B_n\) in characteristic zero. For \(p>2N^3+1\) the same holds because distinct shifts differ by less than \(p\) and all integers \(1+c_*+j\), \(0\le j\le B_n\), are positive and at most \(1+2q^3+2n^3\le 1+2N^3<p\). Interpolation and permanent recovery give the rational reduction and size bound.

## Hilbert IPS synthesis

Write \(f=1+h_n\). The system is unsatisfiable because the Boolean equations force a Boolean matrix and \(f(a)\) is a positive integer on this cube in characteristic zero. The same argument works for \(p>B_n+1\). Any Hilbert IPS refutation with multiaffine \(Y\)-coefficient \(G\) satisfies \(f(a)G(a)=1\) on the cube. Thus \(G=R_n\) and setting \(Y=1,Z=0\) gives its circuit.

Conversely, take a circuit \(G=R_n\). For a multiaffine polynomial \(H\) the exact local division is
\[
 X_iH=X_iH|_{X_i=1}+p_i\bigl(H|_{X_i=1}-H|_{X_i=0}\bigr).
\]
Expand \(f\) into its \(O(n^3)\) squarefree monomials. For each \(X_iG\) use this formula. For each \(X_iX_jG\), apply it first at \(i\) and then at \(j\) to the remainder, keeping the quotient already generated at \(i\) with its factor \(X_j\). The remainder is \(X_iX_jG|_{X_i=X_j=1}\). Summing gives
\[
 fG=H_0+\sum_i p_i T_i,
\]
with \(H_0\) multiaffine and a shared circuit of size \(O(n^3(s+1))\) to assemble the terms from specialized copies of \(G\). On the cube \(H_0=fG=1\), so \(H_0=1\). Hence \(YG-\sum_i Z_iT_i\) is a refutation. This construction restricts the \(Y\)-coefficient and allows arbitrary other coefficients. For unrestricted IPS, even a small circuit agreeing with the reciprocal on the cube would require an efficient multiaffine-recovery step for this argument to apply.

## Cyclotomic specialization and character averaging

Take \(\alpha\) in \(\mathbb Q(\zeta_\ell)\subset\mathbb C\). Its \(\ell-1\) conjugates \(\zeta_\ell^a\), \(1\le a<\ell\), are distinct and outside \(\mathbb Q\). Any cyclotomic automorphism extends to an automorphism of \(\mathbb C\) by fixing a transcendence basis and extending to the algebraic closure. Applying it to every circuit constant leaves the size unchanged and gives \(g_{n,\zeta_\ell^a}\). Choose \(B_n+1\) of these conjugates and use the interpolation argument.

For \(p>B_n\) of order \(\ell-1\) modulo \(\ell\), the cyclotomic polynomial \(\Phi_\ell\) is irreducible over \(\mathbb F_p\). Its roots form one Frobenius orbit by the order condition. In \(K_p=\mathbb F_p[T]/(\Phi_\ell(T))\) let \(\bar\alpha\) be the residue of \(T\). It has degree \(\ell-1>1\) over \(\mathbb F_p\), so each \(\bar\alpha-j\) is nonzero. The map \(\mathbb Z[\alpha,D(\alpha)^{-1}]\to K_p\), \(\alpha\mapsto\bar\alpha\), is defined on all coefficients of the interpolant and sends it to \(g_{n,\bar\alpha}\). Frobenius acting on circuit constants supplies \(B_n+1\) distinct parameters while fixing the prime field. This holds over \(K_p\) and over \(\overline{\mathbb F_p}\). For a circuit over \(K_p\), simulate each gate in the power basis, using \(O(\ell^2)\) base-field gates per multiplication by polynomial convolution and reduction modulo \(\Phi_\ell\). The coordinate of 1 computes the permanent.

For the quantitative Dirichlet step, write \(B=B_n\), \(M=\ell-1\), and \(\eta=\varphi(M)/M\). The indicator of a primitive residue among the units modulo \(\ell\) is
\[
 \mathcal P(a)=\eta\sum_{d\mid M}\frac{\mu(d)}{\varphi(d)}
                              \sum_{\operatorname{ord}\chi=d}\chi(a).
\]
Indeed, write \(a\) as the \(k\)-th power of a generator. The indicator of \(\gcd(k,M)=1\) is \(\sum_{e\mid\gcd(k,M)}\mu(e)\). Expand the subgroup indicator of \(e\mid k\) as \(e^{-1}\sum_{\chi^e=1}\chi(a)\) and collect orders. At order \(d\) the coefficient is \(\sum_{d\mid e\mid M}\mu(e)/e=\eta\mu(d)/\varphi(d)\). Both sides vanish on nonunits. The principal coefficient is \(\eta\), and the sum of absolute coefficients is \(\eta\,2^{\omega(M)}\), where \(\omega\) counts distinct prime factors.

Under Dirichlet GRH, the explicit-formula bound for \(\psi(x,\chi)=\sum_{j\le x}\Lambda(j)\chi(j)\) is
\[
 \psi(x,\chi)=\mathbf 1_{\chi=\chi_0}\,x+O\bigl(\sqrt{x}\log^2(\ell x)\bigr)
\]
uniformly for \(x\ge2\) and all characters modulo \(\ell\). For prime \(\ell\), nonprincipal characters are primitive. The principal-character case subtracts the \(\ell\)-powers from the zeta sum. Apply the bound at \(x=2B\) and \(x=B\) and expand \(\mathcal P\). The interval sum of \(\Lambda(j)\mathcal P(j)\) is \(\eta B+O(\eta\,2^{\omega(M)}\sqrt B\log^2 B)\). Prime powers of exponent at least two add at most \(O(\sqrt B\log^2 B)\). Because \(2^{\omega(M)}=O(M^{1/4})\) and \(\eta^{-1}\le2^{\omega(M)}\), both errors are \(o(\eta B)\). The bound on \(\omega\) follows by treating primes below 16 as a constant factor and bounding the factor 2 for each remaining prime \(r\) by \(r^{1/4}\). Each prime contributes a weight at most \(\log(2B)\), giving the claimed count. Trial division and order tests using the prime divisors of \(\ell-1\) give a deterministic scan polynomial in \(n\). Bertrand's postulate supplies a choice of \(\ell\). For the finitely many small \(n\) left out of this estimate, Dirichlet's theorem gives a prime above \(B_n\) in a primitive residue class. [Bhargava, Ivanyos, Mittal and Saxena, *Irreducibility and Deterministic r-th Root Finding over Finite Fields*, Lemma 6.6.](https://eccc.weizmann.ac.il/report/2017/016/)

## Relation to the announcement and prior work

Alpöge's announcement with Claude gives the Dirichlet \(L\)-function generalization and describes character averaging in its chronology. This theorem uses the stated Dirichlet scope for the twisted prime estimate. Its own finite character projection selects residues that generate the cyclotomic Galois group and thereby supply the conjugate evaluations. The prime count explicitly uses Dirichlet GRH. Sutherland reports that the released formal endpoints passed the standard-axiom audit, module-by-module Lean kernel replay, and independent nanoda export replay on 20 November 2026. The rational reduction and the finite reduction for a prime of the stated order are unconditional. [Alpöge, *Remark*](https://alpo.ge/remark.pdf) · [Sutherland, verification files](https://math.mit.edu/~drew/grh/).

Hrubeš showed that VNP-complete multiaffine interpolants already arise from monotone 2-CNFs or products of affine forms. The matching-indicator step uses the same relation between multiaffine interpolation and generating polynomials. The result here gives a reciprocal of a single quadratic defect, linear-size padding for rational shifts, and a same-size cyclotomic circuit recovery theorem that also holds for the polynomial reduced at the prescribed primes. The written argument establishes these claims. Priority remains unverified. [Hrubeš, *On hardness of multilinearization, and VNP-completeness in characteristics two*.](https://eccc.weizmann.ac.il/report/2015/067/)

Forbes, Shpilka, Tzameret and Wigderson study functional IPS lower bounds via inverse functions on the Boolean cube. The earlier separable-equation construction in this project also computes a grid reciprocal and lifts it by local divisions. The present proof adds quadratic interactions and uses shifts of a single reciprocal to recover the permanent. It yields an exact VP–VNP criterion for the stated restricted Hilbert IPS refutations. [Forbes, Shpilka, Tzameret and Wigderson, *Proof Complexity Lower Bounds from Algebraic Circuit Complexity*.](https://theoryofcomputing.org/articles/v017a010/)
