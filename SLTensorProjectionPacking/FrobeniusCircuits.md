# Safe sign projections from Frobenius-stable factor dependencies

Work over \(F=\mathbb F_3\) with explicit three-tensors. Consider a square matrix pencil \(M_X(z)\) for each endpoint, with \(z\) in the contraction-argument space \(Z_X\). Set \(p_X=\det M_X\). Assume the source polynomial is nonzero and all its absolute factors are linear. The factors need not be defined over \(F\); no bound on the degree of their common splitting field is imposed. A deterministic test below determines when one two-sign instance suffices for SL-TI. It can recover the product of the two matrix-mode signs without finding an ordinary transporter.

## Factor data over separate fields

Let \(n\) be the matrix size and \(r=\dim Z_X\). Under the promise, over an algebraic closure write \(p_X=c_X\prod_i\ell_i^{m_i}\), with distinct linear factors normalized by setting their first nonzero coefficient to one. Frobenius permutes these forms and preserves their multiplicities. Since the resulting monic factor product is defined over \(F\), \(c_X\in F^\times\). Retain one form \(\ell_O\) from each Frobenius orbit \(O\), represented in its minimal coefficient field \(F_O\), with degree \(e_O=|O|\) and multiplicity \(m_O\).

Here is an explicit polynomial-time way to recover the data under the promise. Choose a probe field \(E/F\) whose size is polynomial in the input length and greater than \(n+r(1+n)^2\). Enumerating monic polynomials of logarithmic degree and testing irreducibility constructs one. On the moment curve with coordinates \(1,s,\ldots,s^{r-1}\) find \(a\) with \(p_X(a)\ne0\). Every nonzero linear factor has at most \(r-1\) zeros along this curve, even when its coefficients are in the algebraic closure. Choose \(b\) on the same curve maximizing the number of distinct geometric roots of \(p_X(b+ta)\), measured by the degree of its squarefree radical. A point that separates all distinct forms \(\ell_i/\ell_i(a)\) exists by the same moment-curve bound applied to their pairwise differences. Thus the maximizer separates them. The evaluations, univariate interpolation and deterministic factorization over \(E\) are polynomial time. The field \(E\) itself has polynomial cardinality. For repeated factors in characteristic three, use derivatives and cube roots in the squarefree decomposition.

For an irreducible factor of the probe polynomial, let \(\theta\) be its abstract root in its quotient field \(E'\) of degree at most \(n\) over \(E\). Exactly one geometric linear factor vanishes at \(b+\theta a\), with multiplicity \(m\) known from the probe. For each coordinate vector \(v_j\), interpolate
\[
  p_X\bigl(b+\theta a+u v_j+t a\bigr)
\]
in the two scalar variables over \(E'\), using \(n+1\) points in the embedded probe field for each variable. Its homogeneous part of total degree \(m\) is \(c(t+\eta u)^m\), where \(c\ne0\) and \(\eta=\ell(v_j)/\ell(a)\) for the unique vanishing factor. Write \(m=3^s m_0\) with \(3\nmid m_0\). The ratio of the coefficient of \(t^{m-3^s}u^{3^s}\) to that of \(t^m\) is \(m_0\eta^{3^s}\), by first taking the \(3^s\)-th power and then expanding the \(m_0\)-th power. Invert this Frobenius power in the explicit finite field \(E'\). This recovers each coordinate ratio, including in the inseparable-multiplicity case. Normalize the resulting covector. Finding its cube period and the corresponding fixed subfield gives its minimal field \(F_O\). Each absolute factor is conjugate over \(E\) to one of these recovered forms, so the list includes every \(F\)-orbit.

To compare forms recovered in different presentations of the same field degree, split the tensor product of the two fields using its cube-fixed algebra. The tensor product is a product of fields by separability. Its cube-fixed algebra is a split product of copies of \(F\), and its primitive idempotents are found by simultaneous eigenspace intersection. A component aligns the two fields by their embeddings. Compare the two normalized coefficient vectors after all \(e_O\) Frobenius conjugations in this alignment. This deduplicates whole orbits. Different field degrees cannot give the same orbit. In particular the algorithm never constructs the common splitting field.

Compute \(c_X\) by evaluating at \(a\). For each orbit the product \(\prod_{\ell\in O}\ell(a)\) is the determinant over \(E\) of multiplication by \(\ell_O(a)\) in \(F_O\otimes_F E\), where the coefficients of \(a\) are placed in the \(E\) factor. After extending to a splitting field, this is diagonal multiplication by all conjugate evaluations and gives the stated product, even if the tensor product is disconnected. This determinant, all field representations and all interpolation tables have polynomial size.

## A binary certificate for the sign

Call a union of whole Frobenius orbits a circuit when its geometric factor vectors are minimally dependent. Fix a constant \(k\), and enumerate unions containing at most \(k\) orbits. An orbit itself may have unbounded degree. To test whether a union \(D\) is a circuit, use the \(F\)-linear map
\[
  \bigoplus_{O\subseteq D}F_O \longrightarrow Z_X^*,\qquad
  (b_O)_O\longmapsto\sum_O\operatorname{Tr}_{F_O/F}(b_O\ell_O).
\]
After extension to a common splitting field this is the matrix having all factor vectors as columns, in the coordinates given by the field embeddings. Thus the geometric relation space has dimension equal to the \(F\)-kernel dimension. In dimension one test that a nonzero kernel tuple has every \(b_O\ne0\). That is equivalent to all conjugate coordinates being nonzero. A one-dimensional relation space with full support is exactly a circuit. This test and its coefficient calculation use separate minimal fields throughout.

Only use circuits \(D\) of even cardinality \(\sum_{O\subseteq D}e_O\). Their coefficient tuple from the trace kernel gives geometric relation weights \(b_i\) satisfying \(b_{\operatorname{Frob}(i)}=b_i^3\). The product
\[
 w_X(D)=\prod_{O\subseteq D}N_{F_O/F}(b_O)=\prod_{i\in D}b_i
\]
is a nonzero \(F\)-scalar. It is independent of the choice of kernel generator because the allowed rescaling is in \(F^\times\) and the circuit has even cardinality.

Group the circuits by the multiset of their pairs \((e_O,m_O)\). For each such type \(\tau\), form a binary column \(v_\tau\) indexed by the factor orbits, counting modulo two how many circuits of that type contain each orbit. Form \(w_\tau(X)=\prod_{D\text{ of type }\tau}w_X(D)\). Require the vector \((m_O\bmod2)_O\) to lie in the binary span of these columns. All search sizes here are polynomial for fixed \(k\), independent of the largest orbit size.

For an ordinary transporter \(M_S(Cz)=P M_T(z)Q^{\mathsf T}\), the linear map \(C\) matches factors by a permutation \(\sigma\) commuting with Frobenius, and
\[
   \ell_{S,\sigma(i)}(Cz)=\lambda_i\ell_{T,i}(z),\qquad
   \lambda_{\operatorname{Frob}(i)}=\lambda_i^3.
\]
Write \(d=\det P\det Q\). Determinants give \(d=(c_S/c_T)\prod_i\lambda_i^{m_i}\). On a matched pair of circuits \(D,\sigma D\), transporting a chosen relation on the target gives a nonzero scalar multiple of the chosen relation on the source. Both coefficient vectors are Frobenius-equivariant, so that common scalar is fixed by Frobenius and lies in \(F^\times\). Taking products over the even circuit cancels it, yielding
\[
  \prod_{i\in D}\lambda_i=w_S(\sigma D)/w_T(D).
\]
The product of the \(\lambda_i\) over a whole orbit lies in \(F^\times\), so incidence exponents there are binary. The actual transporter bijects the circuits of every given type. Multiplying these identities over each type and taking any binary span expression for \((m_O\bmod2)_O\) computes \(d\) as a raw frame ratio, using only the target and source products \(w_\tau\). It holds for every ordinary transporter. No factor matching is needed in the computation.

If the computed \(d=-1\), output a fixed NO pair. If \(d=1\), retain the sign of one matrix mode and the label mode sign on the original tensor pair. Their positivity and the computed product imply positivity of the other matrix mode on the same witness. This is a single two-sign instance, using the usual mode permutation. A failure of the target recovery can reject: any ordinarily isomorphic target inherits the splitting and span promises by the covariance identity. Any putative acceptance outside the target promise is still guarded by the ordinary comparison in the output instance. The source condition here is a promise of absolute splitting, rather than a general polynomial identity test for that property.

## Nonsplit examples with every dimension growing

Let \(K=\mathbb F_9\), and let \(K^4/\langle(1,1,1,1)\rangle\) have the semilinear involution given by cubing coordinates and swapping the first two and last two positions. The quotient descends to a three-dimensional \(F\)-space. Indeed for any vector \(u\) in a \(K\)-space with semilinear involution \(\Phi\), the two vectors \((u+\Phi u)/2\) and \((u-\Phi u)/(2\iota)\), where \(\iota^2=-1\), are fixed, and \(u\) is their indicated \(K\)-linear combination. The four images of the coordinate vectors form one four-element circuit. They come in two Frobenius pairs, and their lines are distinct, so no factor is rational over \(F\).

View the four images as covectors on the dual of the descended space. For one factor \(\ell\) per pair use the two-by-two \(F\)-matrix of multiplication by \(\ell(z)\in K\). The block diagonal of the two matrices is a four-by-four pencil whose determinant is the product of the four linear factors. Independent copies on disjoint label spaces give pencil formats \((4m,4m,3m)\). The only geometric circuits are the four-element sets within individual copies, each using two orbits of degree two. One circuit type covers every orbit once, so the test applies at \(k=2\). No factor is linear over the base field. The computed determinant product is positive on every automorphism because it is constant on the transporter set and includes the identity. A reflection of one matrix mode gives an ordinary-isomorphic pair with negative product, hence a negative SL verdict. This construction witnesses genuine sign detection over \(F\) with large tested and label dimensions.

## Scope and sources

The reduction retains the original transporter, in the same sense that the [pinned AgentAlphaXiv exact-verifier study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf) verifies the actual current state rather than a reference substitute. Here descent and the trace map justify every local record for the actual transported factors. The new matrix calculation extends the previous split-over-\(F\) [factor-dependency method](https://github.com/Dugongue/MathProofs/blob/main/RawTensorSignReductions/Results.md). The unrestricted three-to-two reduction remains open.