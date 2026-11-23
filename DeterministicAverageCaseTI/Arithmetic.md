# Simultaneous norm recovery and determinant-constrained tensor pencils

Simultaneous norm witnesses over an unramified finite local ring can be recovered deterministically in polynomial time. The finite-field factoring premise extends this to tame powered norms with a bound on the degrees of the polynomials that need factoring. For ordinary two-slice tensors with irreducible residue pencil, the method gives explicit determinant-constrained isomorphisms, including at characteristic two.

## 1. Field witnesses with controlled factor degrees

Let \(L=\mathbb F_{q^n}\) be presented explicitly, with the indicated subfields \(L_i=\mathbb F_{q^{d_i}}\) for \(d_i\mid n\). Write \(Q=q^n-1\), \(H_i=q^{d_i}-1\), and \(H=\operatorname{lcm}_i H_i\). Lists of subfields below are nonempty. Norms are for the supplied inclusions. All bit complexities allow the explicitly represented field sizes, including \(n\log q\), and the length of the constraint list.

**Theorem 1.** For given \(b_i\in L_i^\times\), the equations \(N_{L/L_i}(x)=b_i\) have a common unit solution precisely when the two targets have equal norms to \(L_i\cap L_j\) for every pair \(i,j\). In the positive case, there are \(Q/H\) solutions and one can construct a solution unconditionally in deterministic polynomial time, using one deterministic single-norm lift for each target.

*Proof.* Choose integers \(u_i\) with \(\sum_i u_i H/H_i=1\), and set \(y=\prod_i b_i^{u_i}\in L^\times\). If the equations hold they imply \(x^{Q/H}=y\). Conversely assume pairwise compatibility. Since the multiplicative order of \(L_i\cap L_j\) is \(\gcd(H_i,H_j)\), raising compatible norms to \(H/\operatorname{lcm}(H_i,H_j)\) gives
\[
              b_j^{H/H_i}=b_i^{H/H_j}.
\]
Thus \(y^{H/H_i}=b_i\) for all \(i\), and any lift of \(y\) under \(x\mapsto x^{Q/H}\) solves the system. Since \(y^H=1\), cyclicity gives exactly \(Q/H\) lifts. To construct one without enumerating a cyclic group, find any \(x_i\) with \(N_{L/L_i}(x_i)=b_i\) via van de Woestijne's deterministic algorithm. Then \(x=\prod_i x_i^{u_iH/H_i}\) satisfies \(x^{Q/H}=y\). \(\square\)

The field existence and count above are already proved by Fernandes, Panario and Reis, Lemma 3.1, and recorded again by Wu and Zhu, Proposition 6.6, using generalized Chinese remaindering on exponents of a cyclic generator. The displayed construction computes the common lift from given single-norm lifts without computing a generator or a discrete logarithm. Van de Woestijne's Theorem 7.1 even provides a field generator with the prescribed single norm. Thus a single norm step appearing as Las Vegas in classical-group algorithms does have an earlier unconditional deterministic replacement. [Fernandes–Panario–Reis, Lemma 3.1](https://arxiv.org/abs/2412.15384) · [Wu–Zhu, Proposition 6.6](https://arxiv.org/pdf/2610.36727#page=220) · [Van de Woestijne, Theorem 7.1](https://math.leidenuniv.nl/scripties/Woestijne.pdf) · [Constructive homomorphisms for classical groups, norm subroutine](https://arxiv.org/abs/1009.1672)

**Theorem 2.** For positive integers \(m_i\) given in binary, consider \(N_{L/L_i}(x)^{m_i}=b_i\). Put \(a_i=m_iQ/H_i\) and \(g=\gcd(Q,a_1,\ldots,a_s)\). With a Bézout relation \(g=u_0Q+\sum_i u_i a_i\), put \(y=\prod_i b_i^{u_i}\). The exact test is
\[
          y^{Q/g}=1,qquad y^{a_i/g}=b_i\quad\text{for every }i .
\]
The positive fiber has size \(g\). Under the deterministic complete finite-field factoring premise, one can recover a witness using factorization degrees at most the largest prime \(B\) of \(\gcd(g,Q/g)\), taken to be one if the gcd is one. Every such prime divides \(n\) or some \(m_i\). The bit running time is \(B^{O(1+\log B)}\) times a polynomial in the explicit input size.

*Proof.* The same Bézout relation shows that any solution satisfies \(x^g=y\). The displayed conditions are necessary, and they are sufficient since the first is the cyclic-group existence test for \(x^g=y\) and the remaining conditions turn any such root into a simultaneous witness. Therefore the fiber has size \(g\). For extraction put \(V=Q/g\) and take \(h\) to be the full part of \(g\) supported on primes dividing \(V\), computed as \(\gcd(g,V^{\lceil\log_2(g+1)\rceil})\). If \(V=1\) take the root one. Otherwise \(c=g/h\) is coprime to \(V\). Replace \(y\) by \(y^{c^{-1}\bmod V}\) and take an \(h\)-th root, prime by prime, using binomials of prime degree. Such a root exists since the new target has order dividing \(V\) and \(h\mid g\). At each extraction, arbitrary roots remain compatible with the remaining degree: if \(\ell j\mid Q\), the \(\ell\)-th roots of unity are \(j\)-th powers in \(L^\times\). This proves the extraction algorithm without factoring \(Q\).

For \(\ell\mid h\), there is an \(i\) with \(0<v_\ell(g)=v_\ell(a_i)<v_\ell(Q)\), so \(\ell\mid H_i\). If \(\ell\nmid n\), the geometric sum \(Q/H_i\) is congruent to \(n/d_i\) modulo \(\ell\), a nonzero residue. Then \(v_\ell(m_i)=v_\ell(a_i)>0\). This proves the support claim. Trial division factors \(h\) in time polynomial in \(B,\log Q\), and the number of extraction steps is at most \(\log_2 Q\). \(\square\) [Earlier prime-by-prime extraction for compact tensor witnesses](../QuasipolynomialFactoringFallout/Profiles.md)

## 2. Exact simultaneous lifts over unramified local rings

Let \(R\) be the quotient at length \(t\ge1\) of a complete discrete valuation ring with uniformizer \(\pi\) and residue field \(k=\mathbb F_q\). Let \(S/R\) be the truncated unramified extension of degree \(n\), with intermediate rings \(S_i\) of residue degrees \(d_i\mid n\). Their intersections are the intermediate rings of degrees \(\gcd(d_i,d_j)\). For the algorithms assume the usual explicit finite free bases and arithmetic, with efficient reduction, valuation, lifting and division by powers of \(\pi\) when divisible. In particular this includes equal-characteristic rings \(k[\pi]/(\pi^t)\) and Witt rings \(W_t(k)\) and their unramified extensions.

**Theorem 3.** A common unit with each norm \(N_{S/S_i}(x)=b_i\) exists exactly when the targets have equal pairwise norms to the intersection rings. There is an unconditional deterministic polynomial-time witness algorithm. For a positive input the number of witnesses is
\[
 \frac{Q}{H}\,q^{(t-1)(n-D)},\qquad
 D=\deg\operatorname{lcm}_i(T^{d_i}-1)\text{ in } k[T].
 \tag{1}
\]

*Trace compatibility.* Write \(L=S/\pi S\), \(L_i=S_i/\pi S_i\), and \(F(x)=x^q\). The map \(F\) on \(L\) is cyclic as a \(k[T]\)-module action with characteristic and minimal polynomial \(T^n-1\). Indeed any nonzero relation of degree less than \(n\) would give a nonzero linearized polynomial of ordinary degree at most \(q^{n-1}\) vanishing at all \(q^n\) elements. A linear map whose minimal polynomial has full degree is cyclic. In the resulting module \(k[T]/(T^n-1)\), the subspace \(L_i=\ker(F^{d_i}-1)\) is a \(k[T]\)-submodule. Decompose into primary factors of \(T^n-1\), with multiplicities allowed. On each primary cyclic summand the different \(L_i\) form a chain, since the submodules of a cyclic module \(k[T]/(f^a)\) are the powers of \(f\).

Suppose \(c_i\in L_i\) have compatible traces to every \(L_i\cap L_j\). The linear forms \(z\mapsto\operatorname{Tr}_{L_i/k}(c_i z)\) agree on all pairwise intersections by trace transitivity. They therefore glue to a linear form on \(\sum_i L_i\). On a primary component, one may take the form on the largest of the chain subspaces, since the remaining forms are its restrictions. The direct sum of these forms works on the total sum. Extend this functional to \(L\) and use the perfect trace pairing of the separable extension \(L/k\) to represent it by a single \(c\in L\). Trace transitivity and the perfect pairings on each \(L_i\) show \(\operatorname{Tr}_{L/L_i}(c)=c_i\). The algorithm solves the trace equations by one linear system over \(k\); the primary factor argument only proves consistency. Its homogeneous kernel has dimension \(n-D\), where \(D=\dim_k \sum_i L_i\). On each primary summand, the dimensions of the nested fixed subspaces are the degrees of their corresponding factors of \(T^{d_i}-1\), with multiplicities. Taking the largest on every primary yields the lcm formula for \(D\).

The simultaneous trace interpolation here is the unrestricted version of the cyclic-module calculation for normal elements with prescribed intermediate traces. The local argument uses this form on arbitrary discrepancy coordinates. [Wu–Zhu, §9.13](https://arxiv.org/pdf/2610.36727#page=360)

*Norm lifting.* Necessity of compatibility follows from norm transitivity. Starting at length one use Theorem 1. If a solution has been found modulo \(\pi^j\), arbitrarily lift it to a unit \(x\) modulo \(\pi^{j+1}\). The discrepancies \(b_i/N_{S/S_i}(x)\) at that precision have unique coordinates \(1+\pi^j c_i\) for \(c_i\in L_i\). Their pairwise norms to the intersections agree by hypothesis and by transitivity. Since
\[
 N_{S/S_i}(1+\pi^j c)\equiv
       1+\pi^j\operatorname{Tr}_{L/L_i}(c)\pmod{\pi^{j+1}},
]
the discrepancy coordinates have compatible traces. The congruence follows by expanding the determinant of identity plus \(\pi^j\) times the multiplication matrix, since \(2j\ge j+1\). Solve the simultaneous trace system and multiply \(x\) by \(1+\pi^j c\). All corrections exist for every lower-precision witness, and each step has \(q^{n-D}\) choices. The residue witness count is \(Q/H\) by Theorem 1. This proves (1) and the complexity. \(\square\)

**Corollary 4.** For powered targets \(N_{S/S_i}(x)^{m_i}=b_i\), assume every \(m_i\) is prime to the residue characteristic. There is an exact deterministic decision procedure, and under the factoring premise an explicit witness algorithm with the same factor-degree bound as Theorem 2 at the residue level. The positive fiber has size \(gq^{(t-1)(n-D)}\), where \(g\) is from Theorem 2.

*Proof.* Factor every unit in an intermediate ring uniquely into a Teichmüller unit, of order dividing \(q^{d_i}-1\), and a principal unit. For the former use the unique Hensel lift of the residue to a root of \(X^{q^{d_i}-1}-1\); the derivative is a unit and exponentiation costs polynomial time despite the large exponent. On principal units the \(m_i\)-th power is an automorphism, with inverse given by an inverse exponent modulo the order of the principal-unit group, a power of the residue characteristic. Norm respects this decomposition. Therefore the residue constraints are exactly Theorem 2, while on principal units the constraints reduce to Theorem 3 for the adjusted targets, with residue witness required to be one. Recombine the two witnesses. The count follows from their independent coordinates. \(\square\)

## 3. Deterministic recovery for ordinary two-slice tensors

Consider an ordinary \(n\times n\times 2\) tensor represented by its two matrix slices. Assume the first slice is invertible and the characteristic polynomial of the normalized second slice, in the convention \(A=A_0^{-1}A_1\), is irreducible on reduction to the residue field and has degree \(n\ge2\). The input format is explicit. Over a field take the local length \(t=1\).

**Theorem 5.** For two tensors of this type, ordinary tensor isomorphism has unconditional deterministic polynomial-time decision and witness algorithms, over fields and the finite local rings in Theorem 3. The algorithms determine all possible changes of the two-slice index up to a list of at most \(n\) linear kernels on four coordinates. For \(n\ge3\), each accepting kernel contributes one class of invertible slice changes up to scalar multiplication. In each class, one can impose arbitrary prescribed relative determinants of the right-mode witness over the intermediate unramified subrings. Those constraints are decided and solved in deterministic polynomial time. Tame powered relative determinant constraints admit the bound in Corollary 4.

*Proof.* Normalize both first slices to \(I\) by left multiplication, giving \((I,A)\) and \((I,B)\). Write \(C=\begin{pmatrix}a&b\\c&d\end{pmatrix}\) for the slice change. For the normalized tensors the witness equations in one consistent tensor convention are
\[
 P(aI+bA)Q=I,\qquad P(cI+dA)Q=B.
 \tag{2}
\]
Every unimodular pair \((a,b)\) gives an invertible \(aI+bA\), since the residue operator has no scalar eigenvalue. Eliminating \(P\) says that \(B\) is conjugate to \((aI+bA)^{-1}(cI+dA)\).

Use \(S=R[\alpha]\) with \(\alpha\) the class of the variable modulo the characteristic polynomial of \(A\). It is unramified of rank \(n\), and \(A\) is multiplication by \(\alpha\) in a cyclic basis. Such a basis is found by taking a vector nonzero on reduction: its residue powers give a basis in the simple residue module, so its powers form a basis over \(R\). List the \(n\) roots \(\beta\) of the characteristic polynomial of \(B\) in \(S\). Over the residue fields, obtain one by Lenstra's deterministic field-isomorphism algorithm and take its \(q\)-Frobenius conjugates. A prime-field isomorphism can be made to fix the presented copy of \(k\) by composing with an inverse prime-field Frobenius power on the target, found by testing its restriction on a basis of \(k\). Lift the roots uniquely by the simple-root Hensel procedure. For each \(\beta\) solve the linear system
\[
        (a+b\alpha)\beta=c+d\alpha
        \qquad\text{in }S .
 \tag{3}
\]
Every nonzero residue solution has invertible \(C\): if its first row vanished, so would its second row since \(\bar\alpha\notin k\). If its rows were proportional, the equation would force \(\bar\beta\in k\). It therefore suffices to find a kernel vector whose residue is nonzero. Over \(R\), reduce the matrix on four variables by picking a nonzero pivot of least valuation, scaling its unit part to one, and clearing its row and column. In the diagonal presentation, the image of the actual kernel under reduction modulo \(\pi\) comes from the free coordinates of zero diagonal entries. This gives the required vector, or correctly rejects that root. This calculation computes all kernels in polynomial time.

For an accepting \(C\), multiplication by \(\beta\) on \(S\) is cyclic because \(\bar\beta\) generates the residue extension. Its characteristic polynomial equals that of \(B\), since it satisfies the same degree-\(n\) monic polynomial in its cyclic basis. Mapping cyclic bases gives a conjugator \(Q_0\), and the first equation gives \(P\). Every tensor witness must occur in this process, since the ratio in (2) is multiplication by some \(\beta\) in \(S\) with that characteristic polynomial.

If \(n\ge3\), two invertible Möbius maps taking \(\bar\alpha\) to the same \(\bar\beta\) differ by a scalar: their quotient fixes \(\bar\alpha\), which would otherwise satisfy a nonzero quadratic equation. Hence an accepting residue kernel has dimension one. Three pivots in (3) are units. If an actual unit solution exists, any remaining equation on the last free coordinate must vanish identically because that coordinate is a unit in the solution. The whole kernel is then free of rank one and its invertible changes are unit multiples of \(C\).

For a fixed class of slice changes, every \(Q\) is \(M_zQ_0\) with \(z\in S^\times\), where \(M_z\) is multiplication by \(z\) in the source operator space. Indeed the centralizer of multiplication by a generator \(\beta\) is all multiplication maps by \(S\), as evaluation at one shows. The chosen cyclic correspondence induces intermediate-ring actions on both spaces. Given relative bases for these actions, the ratio of \(\det_{S_i} Q\) to \(\det_{S_i} Q_0\) is \(N_{S/S_i}(z)\). Thus the required relative determinants reduce to Theorem 3, or to Corollary 4 for tame powers. Normalize and undo the fixed left multiplications to return witnesses for the original slices. \(\square\) [Lenstra, finding isomorphisms between finite fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf) · [Möbius transformations of matrix polynomials](https://doi.org/10.1016/j.laa.2015.09.013)

**Corollary 6.** Under the factoring premise, for \(n\ge3\) the same subclass has a deterministic polynomial-time witness algorithm with arbitrary prescribed base-ring determinants in all three modes over finite fields, equal-characteristic truncations, Witt rings, and the explicitly presented rings of Theorem 3 in odd residue characteristic. The only calls to the assumed factoring oracle have degree two. This includes the all-determinants-one specialization.

*Proof.* Transport the desired determinants to the normalized equations, using the determinants of the fixed normalizing matrices. For an accepting generator \(C_0\), with first row \((a,b)\), all slice changes for that root are \(\lambda C_0\), \(\lambda\in R^\times\). The normalized ratio and its reference conjugator \(Q_0\) stay fixed. For target determinants \(D_P,D_Q,D_C\), choose \(Q=M_zQ_0\) with determinant \(D_Q\) by a single norm lift. With \(U=aI+bA\), equations (2) then require exactly
\[
        \lambda^n=(D_P D_Q\det U)^{-1},\qquad
        \lambda^2=D_C/\det C_0.
 \tag{4}
\]
Over any unit group, use a Bézout relation between \(n\) and \(2\) to derive the required \(\lambda^{\gcd(n,2)}\). Check its powers against both prescribed values. If these agree, any root for the derived power satisfies (4). The remaining extraction is therefore at most a square root.

If the residue characteristic is odd, find a residue square root by factoring a quadratic, and lift through the unit derivative. In equal characteristic two, square coefficientwise in the truncated uniformizer expansion: only even exponents can occur and the coefficient-field square roots are given by inverse Frobenius. In a Witt ring of residue characteristic two, first divide the unit by the square of the Teichmüller lift of its unique residue square root. The resulting unit is \(u\equiv1\pmod2\). Any candidate root has the form \(1+2y\), with square \(1+4(y+y^2)\). At lengths one or two the test is just \(u\equiv1\pmod{2^t}\). At length \(t\ge3\), require \(u\equiv1\pmod4\) and solve \(y+y^2=(u-1)/4\) modulo \(2^{t-2}\). The residue equation is linear over \(\mathbb F_2\) and the derivative is a unit, so the linear solution lifts. This gives the root and hence the explicit matrices in (2). Iterate over the at most \(n\) classes. \(\square\)

The claims concern the stated irreducible residue-pencil class and the simultaneous norm and determinant stages. General regular-slice search and general tensor isomorphism are separate algorithmic problems. The field-level fractional linear action on pencil spectra and the existence of deterministic single-norm solvers are earlier results. The specific contributions here are the simultaneous constructive lift and fiber count over unramified local rings, the powered-norm factor-degree bound, and their exact witness application. These are written proofs.

As an exact check, in length two over the degree-six unramified extension of the dual numbers over the two-element field, all 4,032 units were enumerated. For the degree-two and degree-three subrings, exactly 336 of the 672 target pairs were compatible and each compatible fiber had size 12. A separate enumeration over the degree-three pencil over the same base gave two unit slice changes in each of its three accepting linear classes. These checks complement the written proofs.
