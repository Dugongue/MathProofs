# Sparse smoothing and exact isomorphism for symplectic three-tensors

This informal theorem combines the symplectic action of [the Lean-checked hyperbolic reduction](https://github.com/Dugongue/MathProofs/blob/main/TIEqTISp.lean) with the two algebra-generation tests and sparse smoothing method from [Problem 1.8](https://github.com/Dugongue/MathProofs/tree/main/Problem18) and [its smoothing extension](https://github.com/Dugongue/MathProofs/blob/main/Problem18FurtherExtensions/SparseSmoothing.md). The inputs here are arbitrary tensors in their symplectic spaces before perturbation.

## Statement

Let \(k=\mathbb F_q\) be explicitly presented. Use the independent standard symplectic actions on \(k^n\otimes k^c\otimes k^n\), with \(n,c\) even. In odd characteristic take \(n\ge4,c\ge2,D=6n^4\). In characteristic two take \(n\ge40,c\ge8,D=16n^4\). If \(q>D\), one can construct deterministically in polynomial bit time a tensor direction \(\Delta\) with at most \(7n\) nonzero coordinates and the following properties. In odd characteristic the construction uses at most \(6n\) coordinates in two paired middle slices. In characteristic two it uses four middle pairs.

* For each arbitrary source \(A\), all but at most \(D\) scalars \(t\in k\) put \(A+t\Delta\) into a deterministic polynomial-time recognizable set. For every source in that set, exact decision and exact transporter counting against every target take deterministic polynomial bit time. A transporter on a positive input can be constructed in zero-error expected polynomial bit time.
* A passing scalar can be found deterministically by checking \(D+1\) distinct values. The same direction can be used for every input of the format. For a uniformly random raw source, the fraction outside the recognized set is at most \(D/q\), without perturbation.

In particular this is an almost-all algorithm when \(q/n^4\) grows, uniformly in the middle dimension in the stated formats and with every characteristic allowed. The construction and action preserve the alternating forms. The test compares the perturbed source to the given target.

## Covariants

Write \(U,W,V\) for the three spaces, and \(J_U,J_W,J_V\) for their alternating form matrices. Identify \(U\otimes V\) with \(\operatorname{Hom}(V,U)\) by the alternating form on \(V\), and write the input as middle slices \(M_j\). If \((P,Q,R)\) is an isometry triple, the transformed slices are \(\sum_k Q_{jk}P M_k R^{-1}\). Write \(M^*=J_V^{-1}M^{\mathsf T}J_U\) for the adjoint of \(M:V\to U\), and use the corresponding convention for other maps. Put

\[
G_{jk}=\operatorname{tr}(M_j^*M_k),\qquad S=GJ_W,\qquad R_t=\sum_{j,k}(J_W S^t)_{jk}M_j^*M_k.
\]

The trace is symmetric in the slices because taking adjoints preserves trace. It is invariant under \(M\mapsto P M R^{-1}\). Consequently \(G\) changes to \(QGQ^{\mathsf T}\), \(S\) changes by conjugation by \(Q\), and \(J_W S^t\) changes by inverse congruence by \(Q\). On substitution in the sum, \(R_t\) changes by conjugation by \(R\). The relation \(S^{\mathsf T}J_W=-J_WS\) and symmetry of \(G\) show \(R_t^*=(-1)^{t+1}R_t\).

For a basis \((v_k)_k\) of \(V\) define a second family on \(U\) by

\[
Z^{(t)}_{k\ell}=\sum_{i,j}(J_W S^t)_{ij}(M_i v_k)(M_j v_\ell)^{\mathsf T}J_U.
\]

Under an isometry triple, this family is conjugated by \(P\) and transformed on its two labels by the basis change induced by \(R^{-1}\). It satisfies \((Z^{(t)}_{k\ell})^*=(-1)^t Z^{(t)}_{\ell k}\). In odd characteristic the test uses \(R_0,R_1\) and the \(Z_{k\ell}=Z^{(0)}_{k\ell}\). In characteristic two it uses both families for \(0\le t<4\). The test requires the first family to generate the full algebra on \(V\), and the second to generate the full algebra on \(U\), as unital algebras. This is an invariant test, computable by retaining a basis of words. Each retained word is obtained from an earlier retained word by multiplication by one generator, and length at most \(n^2-1\) therefore suffices if generation is full.

## A two-slice passing direction in odd characteristic

Use ordered symplectic pairs in all three modes. Identify the first and last standard forms. Let \(i\mapsto\hat i\) designate paired basis indices. Choose an invertible diagonal \(M\) such that \(C=M^*M\) has diagonal entries \(c_i=c_{\hat i}\) and \(\mu=\operatorname{tr}(C)\ne0\). Set every pair product to one except in the first pair and choose that product nonzero avoiding the sole value making the sum zero. Such a diagonal \(M\) is obtained by placing the pair product in one of the two entries. This works even when the field characteristic divides \(n\).

Choose a skew-adjoint diagonal \(K\) with \(K_{ii}=k_i=-k_{\hat i}\), such that both the \(k_i\) and the \(a_i=k_i/c_i\) are pairwise distinct. Choosing one new value per pair while avoiding zero and collisions in the two lists excludes at most \(4n+1\) field elements at each step. Select a self-adjoint matrix \(H\) with zero diagonal as follows. On the indices, join each member of the first pair to every index outside that pair. Require both directed entries on each edge to be nonzero and every other entry zero. This directed edge set is closed under \((i,j)\mapsto(\hat j,\hat i)\) and contains no pair of the form \((i,\hat i)\). The self-adjoint equations on it pair entries by signs, so one can assign \(1\) on one member of each two-element orbit and the required sign on the other. This graph is connected since \(n\ge4\).

Use \(M\) and \(N=(M^*)^{-1}(K+uH)\) as the only nonzero slices, in a middle symplectic pair in that order, with \(u\in k\) to be chosen. Their crossed trace is zero, since \(\operatorname{tr}(M^*N)=\operatorname{tr}(K+uH)=0\). Writing \(\nu=\operatorname{tr}(N^*N)\), the displayed formulas restrict to

\[
R_0=M^*N-N^*M=2K,\qquad R_1=-\nu C-\mu N^*N.
\]

In an off-diagonal position \((i,j)\), the coefficient of \(u\) in \(R_1\) is \(-\mu(a_j-a_i)H_{ij}\), by expanding \(N^*N=(-K+uH)C^{-1}(K+uH)\). On each directed edge the polynomial is nonzero and of degree at most two. There are at most \(4(n-2)\) directed edges. Choose \(u\) making all these entries nonzero. Then \(R_0\) supplies the diagonal matrix units by interpolation and \(R_1\) supplies the edge matrix units by multiplying with two of those diagonal ones. Products along directed paths supply all matrix units.

The same choice must pass the second test. At \(u=0\) its ordered family contains a nonzero multiple of \(e_k e_\ell^{\mathsf T}J_U\) for each \(k\ne\ell\), because \(N e_k=a_k M e_k\) and the \(a_k\) are distinct. Since row \(e_\ell^{\mathsf T}J_U\) is a signed coordinate row at \(\hat\ell\), this gives all elementary matrices \(E_{kj}\) except those with \(j=\hat k\). The missing matrix units are products through an index outside the paired indices. Thus words of length at most two in the second family span the full algebra at zero. The determinant of \(n^2\) such basis words evaluated at \(u\) has nonzero constant term and degree at most \(2n^2\), since each \(Z\) is linear in \(u\) for this pair of slices. At most \(2n^2+8(n-2)\) values fail either requirement. Testing one more trial than this bound finds a good \(u\) using the generation tests. The total number of supported entries of \(M,N\) is at most \(2n+4(n-2)\le6n\).

## Four middle pairs in characteristic two

Put \(m=n/2\) and use a basis arranged in \(m\) symplectic pairs. We specify four matrices \(A_i=L_i+L_i^*\), all supported on diagonal pair blocks or between consecutive pairs. In this paragraph a pair block has size two. Choose distinct nonzero \(a_j\) with nonzero sum \(\lambda_1=\sum_j a_j\). To do so, in the last choice avoid also the negative of the preceding sum. Take distinct nonzero \(\lambda_2,\lambda_3,\lambda_4\), distinct from \(\lambda_1\).

* Take \(L_1\) diagonal, with the two entries in pair \(j\) summing to \(a_j\). Choose all \(n\) diagonal entries distinct. For each new pair, once its first entry is chosen the second is that entry plus \(a_j\), so at most twice the number of already used entries are forbidden. Then \(A_1\) has pair blocks \(a_jI_2\).
* Take \(L_2\) with an identity block from pair \(j+1\) to pair \(j\) for each consecutive pair in a chain, plus one diagonal entry \(\lambda_2\) in pair one. Then \(A_2\) has identity blocks in both directions along the chain, and diagonal block \(\lambda_2 I_2\) in pair one.
* For \(L_3\), use a single \(E_{12}\) within the block from pair two to pair one, and one diagonal entry \(\lambda_3\) in pair one. For \(L_4\), use \(E_{21}\) in that block, and a diagonal entry \(\lambda_4\). The corresponding block of \(A_i\) is unchanged, since the adjoint puts its contribution in the reverse block.

These four \(A_i\) generate the full algebra. Interpolating in \(A_1\) supplies the pair-block projections. Cutting \(A_2\) with them and composing along the chain gives all \(m\)-by-\(m\) matrix units tensored with \(I_2\). The additional two blocks from \(A_3,A_4\) yield both off-diagonal \(2\)-by-\(2\) units in any pair block, by multiplying with the first family of units. Products give the internal diagonal units also. By construction \(\operatorname{tr}L_i=\lambda_i\).

Let \(P_i\) be the symplectic permutation of the \(m\) pairs by cyclic shift \(5(i-1)\), and choose the four pairs of middle slices \((M_i,N_i)=(P_i,P_iL_i)\). Since \(m\ge20\), the shifts have cyclic pairwise distance at least five. Crossed Grams between different middle pairs vanish. For example \(\operatorname{tr}(M_j^* N_i)\) is the trace of a nonzero pair shift followed by a matrix supported only at pair offsets \(0,\pm1\). For \(\operatorname{tr}(N_j^*N_i)\), multiply also by \(L_j^*\), with offsets \(0,\pm1\). The total offset cannot be zero. The argument for the two other mixed trace types is the same with one or two of the offset matrices absent. In characteristic two all diagonal slice Grams vanish: \(X^{\mathsf T}J_UX\) and \(J_V^{-1}\) are both alternating, so their product has trace zero by pairing the off-diagonal summands. The pairing within each middle pair is exactly \(\operatorname{tr}L_i=\lambda_i\).

Thus \(S\) acts on middle pair \(i\) by \(\lambda_iI_2\). Consequently \(R_t=\sum_i\lambda_i^t A_i\) for \(0\le t<4\). Vandermonde interpolation gives all four \(A_i\) in their linear span, so the first test passes. The same interpolation, for each pair of labels \(k,\ell\), isolates the contribution of the first middle pair in the second family. There \(M_1=I\) and \(N_1=L_1\) is diagonal with distinct entries. Exactly as in the two-slice argument its isolated \(Z\)-matrices generate the full algebra. This proves the second test. The four \(M_i\) have \(4n\) supported entries altogether, while the four \(L_i\) have at most \(n+(n-1)+2+2\) altogether. The shifts preserve support counts. The total is at most \(7n\), and the construction uses only polynomially many field trials.

## Comparison, search and counts

For a source that passes, solve the linear intertwining equations on the first family and its target version. A nonzero solution \(X\) is invertible because its kernel is invariant under the full source matrix algebra. All solutions are multiples of \(X\) by the scalar-commutant property. The adjoint signs of the generators make \(X^*X=d_V I\) with \(d_V\ne0\). A symplectic last factor must be \(rX\) with \(r^2=d_V^{-1}\), so a nonsquare rejects in odd characteristic.

Apply \(X^{-1}\) on the actual last tensor factor of the target to undo that projective map. If a genuine transporter exists, the adjusted target is obtained from the source by \((P,Q,r I)\). Consequently its second family at index \(t\), multiplied by \(d_V^{t+1}\), is the conjugate of the source second family by \(P\), using homogeneity of degree \(2t+2\). Solve that intertwiner system. Its nonzero solutions form another invertible line \(kY\), by generation, and the adjoint-mate relations imply \(Y^*Y=d_U I\). Again check the square condition for a symplectic lift, now \(p^2=d_U^{-1}\). These square tests are deterministic by modular powering. The characteristic-two roots are unique and found by inverse Frobenius.

Use the middle flattenings \(H,D'\) of \((Y,I,X)A\) and of the target, respectively. Put \(s=(d_Ud_V)^{-1}\). The last conditions are

\[
\ker H=\ker D',\qquad (D')^{\mathsf T}J_W D'=sH^{\mathsf T}J_W H.
\]

They are necessary, and they suffice by symplectic Witt extension: for any scalar normalizations \(p,r\), the columns of \(prH\) map to those of \(D'\) by a well-defined partial isometry. This argument uses the kernel check even when the column spans are degenerate. A witness can be produced by extracting two square roots and extending the partial symplectic isometry. The latter extension uses elimination and a symplectic basis extension, including hyperbolic partners for the radical of the marked span. Finite-field square roots can be obtained in expected polynomial bit time by zero-error polynomial factoring. Check the returned witness directly.

To count, let \(L\) be the radical of the column span and put \(a=\dim L\). Split off a nondegenerate complement of \(L\) in the span. Its orthogonal complement in \(W\) consists of \(L\), an isotropic dual space to \(L\), and a symplectic space \(B\) of dimension \(b\). The pointwise stabilizer of the span has order \(|\operatorname{Sp}(B)|q^{ab+a(a+1)/2}\). In the order \((L,B,L^*)\), such a matrix has upper triangular block form with diagonal \((I,g,I)\), \(g\in\operatorname{Sp}(B)\). The block from \(L^*\) to \(B\) is arbitrary. Its mate is determined by preserving the pairing with \(B\). The equation on the final upper corner is \(Z-Z^{\mathsf T}\) equal to a known alternating matrix, always soluble by choosing upper-triangular entries. Its homogeneous solutions are symmetric matrices, in every characteristic. Thus the formula includes degenerate spans. Each scalar normalization pair gives one coset of the pointwise stabilizer, so the full count is four times its order in odd characteristic and equals its order in characteristic two. The classical symplectic group order follows by counting successive symplectic pairs. All arithmetic and output bit lengths are polynomial in the dense input.

## Smoothing and coverage

Both covariants at index \(t\) are homogeneous of degree \(2t+2\) in the source entries. Choose \(n^2\) words from each family whose values at the explicit direction are independent, with length at most \(n^2-1\). The determinant of each list of vectorized matrices is homogeneous. In odd characteristic their degrees are at most \(4n^4\) and \(2n^4\), respectively. In characteristic two each degree is at most \(8n^4\). Their product is nonzero at \(\Delta\) and has degree at most the stated \(D\). Along \(A+t\Delta\) its leading coefficient is its value at \(\Delta\). All failures are roots of this polynomial. The same nonzero polynomial bounds failure under uniform raw sources by the elementary finite-field polynomial zero estimate. The witness words are needed only in the proof. The algorithm runs the two generation tests directly.

The relevant prior results compare orthogonal and unitary random tensors, or relate worst-case classical-group TI to ordinary TI. The present statement is a direct exact algorithm for the symplectic group on its raw three-mode representation, with an explicit sparse single-scalar perturbation and exact counts. The field-size guarantee uses growing finite fields in both characteristics. [Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/abs/2306.03135) · [Chizewer–Everett–Mithal–Qiao](https://arxiv.org/abs/2603.27128) · [Li–Li–Qiao–Tao–Wang](https://arxiv.org/html/2604.00591v2)
