# Exact lifting and orientation of tensor witnesses over finite local rings

A residue-field tensor transporter class lifts deterministically if the residue Lie stabilizer has only the universal scalar directions. In each such class, every successful precision has exactly one transporter up to scalar change. For modes of unequal sizes, prescribed determinants reduce to explicit cyclic power equations. Wild principal units are handled by integer linear algebra.

## 1. The scalar tangent criterion

Let \(R\) be a finite commutative local ring, with maximal ideal \(\mathfrak m\), residue field \(k=\mathbb F_q\), and \(\mathfrak m^t=0\). Work with an effective presentation supplying the additive groups, multiplication, maximal ideal generators and coordinates for residue reduction. Additive group linear algebra then computes the ideal powers and quotient coordinates. For instance this includes explicit finite truncated discrete valuation rings, with arbitrary ramification. For \(j\ge1\), put \(R_j=R/\mathfrak m^j\). All algorithms below take the explicit ring and dense tensors as inputs.

For positive mode sizes \(n_1,\ldots,n_d\) with \(d\ge2\), put
\[
 C(S)=\{(\lambda_i I_{n_i})_{i=1}^d\mid\lambda_i\in S^\times, \prod_i\lambda_i=1\}.
\]
It acts trivially on every tensor. For a source tensor \(A\), the tangent map \(D_A\) sends \((X_i)_i\) to the sum of the tensors obtained by applying \(X_i\) in the \(i\)-th mode to \(A\). Test the following condition by linear algebra over \(k\):
\[
      \ker D_{\bar A}
        =\{(c_iI_{n_i})_i : \textstyle\sum_i c_i=0\}.
 \tag{1}
\]

**Theorem 1.** Suppose (1) holds. Given one residue transporter class modulo \(C(k)\) from \(\bar A\) to \(\bar B\), there is an unconditional deterministic polynomial-time algorithm that decides whether it lifts to \(R_j\) and returns a witness if so. At each precision it has either zero or exactly one lift class modulo \(C(R_j)\). The algorithm can double precision, using \(O(\log(t+1))\) correction steps. For each step the sole obstruction is a linear cokernel class, independent of the intermediate representative. Given a complete list of residue transporter classes, the total number of full witnesses is the number of surviving classes times \(|R^\times|^{d-1}\).

*Proof.* Choose a free complement \(E\) to the scalar Lie directions over \(R\), by setting the \((1,1)\) entry to zero in the first \(d-1\) matrices. Subtracting appropriate scalar matrices and using zero sum gives the indicated splitting over every ring. By (1), the restriction of \(D_A\) to \(E\) has a square minor of full column size which is a unit over \(R\). In particular it is split injective, and its image on any module of ideal coefficients is recovered by the inverse of that fixed minor and checked by applying \(D_A\) again.

To lift from \(R_j\) to \(R_{j'}\) with \(j<j'\le2j\), let \(I=\mathfrak m^j/\mathfrak m^{j'}\). It is a square-zero ideal of \(R_{j'}\). Choose any invertible entrywise lift \(\tilde g\) of the current tuple of matrices, and put \(e=\tilde g^{-1}B-A\in I\otimes_R V\), where \(V\) is the free tensor module. A correction is \(\tilde g(1+X)\) with matrix coefficients of \(X\) in \(I\). Since \(I^2=0\), the corrected equation is exactly \(D_A(X)=e\). Thus the obstruction is the class of \(e\) in the cokernel of this map on ideal coefficients. Changing the temporary lift changes \(e\) by an image. Scalar multipliers at precision \(j\) have scalar lifts with product one at precision \(j'\), so changing the current representative within its class also preserves the obstruction. The unit minor computes the unique solution in the chosen complement if one exists.

Two corrections above the same representative differ by the kernel on \(I\). By the splitting this is exactly the scalar Lie kernel with coefficients in \(I\), and \(1+X\) for these directions lies in \(C(R_{j'})\). Two lifts above representatives differing by a scalar at lower precision can first be aligned by lifting that scalar. Hence any successful class remains unique after the step. Induction and doubling give the algorithm. In an accepting residue class its entire fiber is one coset of \(C(R)\), whose cardinality is \(|R^\times|^{d-1}\). Distinct residue classes give disjoint fibers. \(\square\)

The rank test (1) concerns the Lie stabilizer, including infinitesimal directions. A finite list of geometric point stabilizers alone does not certify it. On the locus where the geometric point stabilizer is precisely \(C\), any single residue witness suffices to start Theorem 1. More generally the algorithm is polynomial in the number and size of supplied representatives. At all stages a failed class can be certified by the explicit residual vector and the verified unit minor. The successful precisions form an initial interval. Binary search using the doubling algorithm computes its endpoint in \(O(\log^2(t+1))\) correction steps and gives the whole precision count profile when the residue list is supplied.

## 2. Wild unit equations and prescribed determinants

**Lemma 2.** For the presented ring \(R\), one can compute in deterministic polynomial time cyclic coordinates, including both conversion maps, for its group of principal units \(1+\mathfrak m\). In particular arbitrary integer power equations and their exact fiber sizes in this group can be solved in deterministic polynomial time.

*Proof.* Put \(p=\operatorname{char}k\). In each quotient \(\mathfrak m^j/\mathfrak m^{j+1}\) choose an \(\mathbb F_p\)-basis with explicit lifts \(a_{j,i}\). The units \(u_{j,i}=1+a_{j,i}\) give an ordered system of digits for \(1+\mathfrak m\), with the lower levels first. For any principal unit, its first unprocessed coefficient is a vector in that level's ideal quotient. Taking its basis coordinates and dividing by the corresponding powers of the \(u_{j,i}\) removes the coefficient and passes to the next level. Each digit lies in \(\{0,\ldots,p-1\}\), and the expansion is unique. This gives computations in both directions using modular linear algebra and binary powering.

For each generator compute the digits of \(u_{j,i}^{p}\), which occur only at strictly higher levels. Use these words as relations in an abelian presentation. Its integer matrix is triangular with diagonal entries \(p\), and therefore presents an abelian group of order \(p^a\) for \(a=\sum_j\dim_{\mathbb F_p}(\mathfrak m^j/\mathfrak m^{j+1})\). It surjects onto the actual group of principal units, which also has order \(p^a\) by the uniquely determined digits. Hence it is an exact presentation. Integer Smith normal form with multipliers gives cyclic coordinates of orders \(p^{v_1},\ldots,p^{v_b}\) and their conversion maps. A power equation becomes an integer congruence on each such coordinate. Its fiber size, if positive, is the product of the corresponding gcds. \(\square\) [Kannan–Bachem, deterministic polynomial Smith form](https://doi.org/10.1137/0208040) · [Kreuzer–Walsh, unit group computations via exponent lattices](https://arxiv.org/abs/2405.07002)

Also \(R^\times\) is the direct product of its principal units and the roots of \(X^{q-1}-1\). Each nonzero residue element has a unique such lift by square-zero correction with a unit derivative. The lift is multiplicative by uniqueness. Thus integer power equations split exactly between a cyclic residue equation and the principal-unit equations of Lemma 2.

**Theorem 3.** Suppose (1) and the residue-list setup of Theorem 1 hold. One can decide, for any prescribed unit determinant \(D_i\) in each mode, which lifted classes contain a transporter with those determinants. The algorithm counts the full witness set in unconditional deterministic polynomial time in the size of the list. Under complete deterministic quasipolynomial finite-field factoring it constructs an explicit witness in each positive class, using factorization degrees at most the largest prime divisor of any mode size.

*Proof.* For a successfully lifted representative \(g\), put \(a_i=D_i/\det g_i\). All modifications are scalar, so the residual problem is \(\lambda_i^{n_i}=a_i\) with \(\prod_i\lambda_i=1\). Eliminate \(\lambda_d\). The remaining monomial map has the integer exponent matrix
\[
 W=\begin{pmatrix}
   \operatorname{diag}(n_1,\ldots,n_{d-1})\\
   -n_d&\cdots&-n_d
 \end{pmatrix}.
\]
Smith row and column operations, interpreted as multiplicative changes of coordinates, give \(d-1\) independent equations \(x_j^{s_j}=b_j\) and the condition that the last transformed target equals one. The invariants \(s_j>0\) have their prime divisors among those of the \(n_i\), since their product divides the nonzero maximal minor \(\prod_{i<d}n_i\).

For each equation split the unit into residue and principal components. The cyclic residue test is \(b_j^{(q-1)/\gcd(s_j,q-1)}=1\) after reduction. For an accepted residue equation, Bézout with \(q-1\) converts extraction to a power with exponent \(h=\gcd(s_j,q-1)\). Extract one prime root at a time by binomial factoring. An arbitrary choice of an \(\ell\)-th root stays compatible with the remaining factor \(h'\), since \(\ell h'\mid q-1\) and all \(\ell\)-th roots of unity are \(h'\)-th powers. The allowed primes are obtained by trial factoring the mode sizes. This requires no factoring of \(q-1\). Lemma 2 gives the principal roots and counts. Thus each positive class contributes exactly
\[
     \prod_j\left(\gcd(s_j,q-1)\prod_{a=1}^b\gcd(s_j,p^{v_a})\right)
\]
witnesses. Undo the coordinate changes and multiply by the chosen initial transporter. \(\square\) [Prime-by-prime extraction](https://github.com/Dugongue/MathProofs/blob/main/QuasipolynomialFactoringFallout/Profiles.md)

**Corollary 4.** In the unramified local extension setup of earlier simultaneous norm recovery, the powered norm equations \(N_{S/S_i}(x)^{m_i}=b_i\) have exact decision and counting algorithms for arbitrary positive integer \(m_i\), including those divisible by the residue characteristic. Under the same factoring premise there is explicit witness recovery with the previous factorization-degree bound, which involves only primes dividing the extension degree or a power \(m_i\).

*Proof.* Split Teichmüller and principal coordinates as above. The Teichmüller equations are exactly the earlier simultaneous powered residue norms. On principal units, compute the integer coordinate matrix \(M\) of the joint powered norm map by evaluating each norm on the source unit generators of Lemma 2 and converting it to the target coordinates. If the target group has diagonal relation matrix \(D\), the linear system is that \(b\) belong to \(M\mathbb Z^r+D\mathbb Z^s\) in \(\mathbb Z^s\). Integer Smith form tests membership and recovers the source exponents. The kernel cardinality is
\[
 \frac{|1+\mathfrak m_S|}{\prod_i|1+\mathfrak m_{S_i}|}
    [\mathbb Z^s:M\mathbb Z^r+D\mathbb Z^s],
\]
by taking the order of the image from its cokernel. Multiply this count by the accepted residue fiber size, and multiply the two witnesses. No power on principal units was inverted. This removes the tame-exponent hypothesis from the earlier method, and applies to the associated determinant targets in the irreducible residue pencil. \(\square\) [Prior powered norms and exact pencil transport](https://github.com/Dugongue/MathProofs/blob/main/DeterministicAverageCaseTI/Arithmetic.md)

## 3. Residue classes with ready-made deterministic search

### Even-order ordinary tensors

**Corollary 5.** Suppose the residue source belongs to the connected-support spectral class of the earlier even-order theorem. Ordinary witness recovery over \(R\) is unconditional deterministic polynomial time against every target. Decision and counting with prescribed determinants are also unconditional deterministic polynomial time. Explicit prescribed-determinant witnesses are deterministic quasipolynomial under the factoring premise. For equal side \(n\), each positive determinant fiber has size \(|R^\times[n]|^{d-1}\), with \(R^\times[n]=\{x:x^n=1\}\).

*Proof.* The residue algorithms find a transporter or reject, and the residue geometric point stabilizer consists of scalars. It remains to verify (1), which does not follow from geometric points alone. On the spectral class the balanced cut is invertible and the covariants are rational contractions of tensors and inverse cuts. Their conjugation equivariance holds for dual-number points as well: it is a contraction identity and all inverted matrices remain invertible. If \((X_i)_i\) stabilizes the residue tensor infinitesimally, each \(X_i\) commutes with its mode covariant. Over a splitting field the simple-spectrum covariants therefore make the \(X_i\) diagonal. Write the diagonal coordinates as \(x_{i,a}\). Each nonzero tensor coefficient at a tuple \((a_i)_i\) gives \(\sum_i x_{i,a_i}=0\). Two nonzero entries at the same context in all modes except \(i\) force equality of the two corresponding \(x_{i,a}\). The connected support graph in that mode makes the entire diagonal scalar. A nonzero tensor coefficient then says the sum of the scalars is zero. This proves (1) in every characteristic, including when a mode size vanishes in \(k\). Apply Theorems 1 and 3. For equal sides the scalar equations are simply \(\prod_i a_i=1\) and \(a_i\in(R^\times)^n\); choose roots in the first \(d-1\) modes and use the inverse product in the last. \(\square\) [Earlier field-level connected-support spectral algorithm](https://github.com/Dugongue/MathProofs/blob/main/DeterministicAverageCaseTI/EvenOrder.md)

### Orthogonal tensors and exact orientations

**Theorem 6.** Let the residue characteristic be odd. Consider ordinary three-tensors of side \(n\) under the standard orthogonal action. Suppose one first-mode Gram covariant of the source has simple spectrum, and that a first-mode slice \(A_1\) is invertible on reduction, with the ratios \(A_iA_1^{-1}\) having scalar common commutant over the residue field. Then each residue orthogonal transporter has either no lift or a unique orthogonal lift over \(R\). A lift can be tested and constructed deterministically with \(O(\log(t+1))\) linear correction steps. Given a complete polynomial-size residue transporter list, this determines every orthogonal transporter and every orientation profile over \(R\). In particular one can use the earlier capped orthogonal algorithm on the intersection of its recognized locus with these two rank tests.

*Proof.* Orthogonal tangent matrices in odd characteristic are skew-adjoint. The first-mode Gram matrix is conjugation-equivariant under the orthogonal action. Thus an infinitesimal stabilizer's first matrix commutes with the simple-spectrum Gram matrix. Its eigenspaces over the algebraic closure are distinct mutually orthogonal nondegenerate lines, so any commuting matrix is self-adjoint. A skew-adjoint such matrix is zero. For the other tangent matrices \(Y,Z\), the equations on slices are then \(YA_i+A_iZ^{\mathsf T}=0\). The invertible slice expresses \(Z^{\mathsf T}=-A_1^{-1}YA_1\), and the remaining equations say \(Y\) commutes with all the ratios. This makes \(Y\) scalar and hence zero by skew-adjointness, and also \(Z=0\). Consequently the augmented derivative consisting of the tensor derivative and the linearized Gram constraints in each mode is injective over the residue field.

For square-zero corrections write \(g=\tilde g(1+X)\), with \(X\) in the correction ideal. The orthogonal condition corrects its current defect by \(X_i+X_i^{\mathsf T}\), since \(\tilde g_i^{\mathsf T}\tilde g_i-I\) is in that ideal. Add these linear equations to the tensor correction equations of Theorem 1. A full-column unit minor now gives either the unique correction or an obstruction, with no scalar quotient. Doubling proves the assertion. An orthogonal unit determinant over the local ring has square one, so in odd residue characteristic it is exactly the lift in \(\{1,-1\}\) of its residue value. Thus the signs of the surviving representatives give exact orientations. \(\square\) [Earlier capped orthogonal source algorithm](https://github.com/Dugongue/MathProofs/blob/main/DeterministicAverageCaseTI/Orientation.md)

For \(n\ge3\), the two added tests discard at most
\[
      \frac{2n(n-1)+n+n(n^2-1)}{q}
\]
of uniform residue sources over an odd field. Indeed the discriminant of the Gram matrix is a polynomial of degree \(2n(n-1)\), nonzero by a weighted diagonal tensor with distinct squared weights over the algebraic closure. The determinant of the first slice has degree \(n\). For the commutant use all matrices \(A_i\operatorname{adj}(A_1)\), whose entries have degree \(n\). A nonzero rank-\((n^2-1)\) commutator minor exists, by taking slices \(I\), a simple diagonal, and the all-ones matrix over the algebraic closure. The three nonzero polynomials give the bound by Schwartz–Zippel. The tests are themselves deterministic and do not construct those witnesses at runtime.

## Scope

Grochow–Qiao–Stange–Sun Part V compares tensor actions over finite local principal ideal rings and lifts certain local matrix and involution equations. The results here give a different sufficient criterion for ordinary tensor transport in arbitrary tensor order: a single residue Lie-rank test reduces each supplied residue transporter class to a deterministic obstruction calculation and an exact count. The determinant step deals explicitly with the possibly nonsmooth power maps on wild units. The orbit lifting is unconditional. The stated use of the factoring premise is confined to residue field power extraction or to a residue algorithm that already uses the premise. These are written proofs. [Part V, §§3 and 5](https://arxiv.org/html/2611.00735)

Exact finite checks decoded and re-encoded principal-unit digits and checked power-fiber uniformity in 5,075 cases over equal-characteristic and mixed-characteristic dyadic truncations. An independent linear calculation found a 3-by-3-by-3 residue source over the two-element field with derivative rank 25 and an explicit coordinate obstruction to the identity class lifting from length one to length two over the integers modulo four. The proofs above establish the general statements.
