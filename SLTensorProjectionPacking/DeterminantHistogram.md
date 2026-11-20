# Exact determinant counts with small slice-rank excess

This extends [the determinant-sum test](DeterminantSum.md). It gives an informal deterministic polynomial-time evaluation of the full determinant histogram for a square pencil over \(\mathbb F_3\) whose total slice-rank excess \(k\) is \(O(\sqrt{\log(2+\ell)})\), where \(\ell\) denotes explicit input length and the bound has a fixed constant. The histogram gives the same one-instance reduction when the counts at \(+1\) and \(-1\) differ. The counts can differ even when their reductions modulo three agree.

## A bounded matrix and two decomposable wedges as state

Use the rank factorizations and indexing in the companion note, with complementary-minor matrices \(K,N\), constants \(c_L,c_R\), and slice index blocks \(B_i\) of size \(d_i\). Write \(K_j\) for row \(j\) of \(K\), \(N_j\) for column \(j\) of \(N\), and \(x_j=K_j\otimes N_j\) in \(\Lambda F^k\otimes\Lambda F^k\). For any assignment of label values the determinant is \(c_Lc_R\) times the top-top coefficient of
\[
\prod_i\left(\sum_{J\subseteq B_i} z_i^{d_i-|J|}\prod_{j\in J} x_j\right).
\]
Here \(0^0=1\), and both products use the inherited index order. This is precisely the complementary-minor Cauchy–Binet expansion with the label weights still present.

For \(z_i\ne0\), extract the scalar \(z_i^{d_i}\) and replace the remaining factor by \(\prod_{j\in B_i}(1+z_i^{-1}x_j)\). For \(z_i=0\), every index of \(B_i\) must be in the complementary subset, so the sole remaining factor is \(\prod_{j\in B_i}x_j\). The algebra elements in equal bidegrees commute because the same exterior exchange sign occurs twice. We can group all zero-block factors into a single pair of decomposable wedges \(u\otimes v\). The two wedges are the exterior products of the \(K_j\) and \(N_j\) vectors, respectively, over all zero-block indices.

Define
\[
C=\sum_{i:z_i\ne0}z_i^{-1}\sum_{j\in B_i}N_jK_j,\qquad
s=\prod_{i:z_i\ne0}z_i^{d_i}.
\]
For any equal-size coordinate sets \(A,B\subseteq[k]\), the coefficient of the exterior-monomial pair \(e_B\otimes e_A\) in the product of the nonzero-block factors is \(\det C_{[A,B]}\). To see this, expand the minor of the matrix product built from the selected columns \(N_j\), the weights \(z_i^{-1}\) on those indices, and the selected rows \(K_j\). Cauchy–Binet gives the same weighted wedge expansion. Call this algebra element \(\Omega(C)\). It follows that the determinant is \(c_Lc_R\) times the top-top coefficient of \(s(u\otimes v)\Omega(C)\).

This gives a dynamic count. Start with \(C=0\), \(s=1\), and unit wedges. On a nonzero value at label \(i\), add \(z_i^{-1}\sum_{j\in B_i}N_jK_j\) to \(C\) and multiply \(s\) by \(z_i^{d_i}\). On zero, extend the two wedges by all their vectors in \(B_i\). A vanishing wedge remains zero, and all subsequent assignments then give zero determinant. Keep integer counts of every reachable state after each prefix. The three transitions count each label assignment exactly once.

The \(k\times k\) matrix has \(3^{k^2}\) possible values. Store each nonzero decomposable wedge as the row-reduced basis of its supporting subspace, with its scalar in that basis. Row reduction of the old basis followed by the appended vectors gives the next frame and scalar. The number of possibilities for each wedge, including zero and the degree-zero units, is at most \(1+2(k+1)3^{k^2}\). There are two possibilities for \(s\). Thus the state count is \(3^{O(k^2)}\), and the determinant conversion for each final state costs at most \(4^k\) times a polynomial in \(k\). The integer counters have at most \(O(r)\) bits. Rank-deficient factorizations are dealt with by assigning all inputs to value zero. The full histogram is therefore computable in \(3^{O(k^2)}\operatorname{poly}(\ell)\) time.

## The sign test

An ordinary transporter \(M_S(Cz)=P M_T(z)Q^{\mathsf T}\) either preserves or swaps the two nonzero entries of the histogram, according to \(\det P\det Q\). If an endpoint has unequal entries, the ratio sign is therefore determined from the two ordered counts on every actual transporter. A histogram mismatch beyond the allowed swap excludes ordinary equivalence. A negative product excludes an SL witness. A positive product permits keeping just the first and third signs. This is one two-sign instance on the evaluated domain.

## A family visible to counts and invisible to the field sum

In the coupled pencil from the companion note, replace its top-left block \(xI_4+yJ\) by \((xI_4+yJ)\oplus xI_2\), and keep the coupling \(xE\) supported on the first of the original four core rows, nonzero on each bottom block. The coordinate slice ranks are \(6,4,2,\ldots,2\). The new matrix size is \(6+2t\), so the excess is still four. Its determinant polynomial is
\[
x^2(x^2+y^2)^2\prod_i z_i^2.
\]
There are \(6\cdot 2^t\) assignments on which it takes value \(+1\), and none on which it takes value \(-1\). Its sum in \(\mathbb F_3\) is zero.

The cubic minor span remains precisely the cubics omitting all pure \(z_i^3\): the old row and column choices still supply every other monomial, and each \(z_i\)-slice still has rank two. The same recovery therefore identifies the intrinsic core label plane and the low-rank axes. After arbitrary rebasing any basis of the recovered core plane has slice ranks at most six each, so the total excess is at most six. Thus the histogram test applies after arbitrary rebasing.

The new pencil still has scalar centroid. In \(PM(z)=M(z)Q=M(Cz)\), the \(z_i\) equations remove the off-diagonal columns of \(P\) with bottom index and the off-diagonal rows of \(Q\) with bottom index. The bottom blocks then equal \(\lambda_i I_2\). The \(x\) equation implies \(P_{b0}=0\) for the map from core to bottom and makes the core block of \(P\) equal to \(aI_6+b(J\oplus0)\). The \(xE\) term satisfies \(P_0 E=aE\). Since \((J\oplus0)E\ne0\), this forces \(b=0\). The core block of \(Q\) is \(aI_6\). Its remaining off-diagonal block satisfies \(Q_{0b}=E(aI-\bigoplus_i\lambda_i I_2)\), by the \(x\) equation, and \((J\oplus0)Q_{0b}=0\), by the \(y\) equation. Its image lies in the first core coordinate, so it is zero. The nonzero restrictions of \(E\) give \(\lambda_i=a\). Slice independence makes the third action scalar as well.

This uses the same exact-step discipline as the pinned archive study: the transition retains the whole small determinant state needed by its continuation. No empirical result enters the proof. [AgentAlphaXiv study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf)