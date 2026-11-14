# Projection reductions from arbitrary tensors to alternating matrix spaces and matrix conjugacy

**Published question.** Remark 2.5 of Grochow and Qiao's *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I: Tensor Isomorphism-Completeness* asks whether the two reductions in Propositions 5.1 and 6.1 can satisfy all five properties in §2.2 on all 3-tensors. We give both reductions, with linearly bounded output side lengths. This is an informal proof. [Journal paper](https://doi.org/10.1137/21M1441110) · [Preprint, §6.2 and Propositions 7.3 and 8.1](https://arxiv.org/pdf/1907.00309#page=23)

## 1. Data with independent slices

Work over any field \(K\). Let the input be \(A\in U\otimes V\otimes L\), with fixed bases. For each target, first construct a data tensor \(D(A)\) supported on four disjoint matrix-axis blocks. Write \(E\) for a based copy of \(L^*\) and \(F_0=Kf\) for a line. Put \(N=\dim U+\dim V+\dim L+1\).

- **Alternating isometry.** Start with matrix space coordinates on \(W_0=U\oplus V\oplus E\oplus F_0\). Send each \(u\otimes v\) to \(u\wedge v\), and add \(\sum_i (e_i\wedge f)\otimes \ell_i\), with \((e_i)\) the basis dual to \((\ell_i)\) of \(L\). The alternating matrix representing \(a\wedge b\) is \(a\otimes b-b\otimes a\), also in characteristic two.
- **Conjugacy.** Start with \(W_0=U\oplus V^*\oplus E\oplus F_0^*\). Use matrix coordinates \(W_0\otimes W_0^*\) with \(U,E\) as row blocks and \(V,F_0\) as dual column blocks. Place \(A\) across \(U,V\) and add \(\sum_i e_i\otimes f\otimes\ell_i\) across \(E,F_0\).

The fixed summand makes the data contraction \(L^*\to\) matrices injective, even at \(A=0\). Write the ultimate matrix factors as \(H_1,H_2\), which will be \(W,W\) in the alternating case and \(W,W^*\) for conjugacy.

## 2. Mark the four blocks

Use eight tag lines \(Kz_j\) spanning \(Z\), with two distinct tags assigned to each original block \(B\). Put \(M=10(N+1)\), \(s_j=M+j(N+1)\), and \(p_j=s_j-\dim B\). Thus \(p_j\ge M\) and \(s_j<2M\). For each tag add fresh private spaces \(R_j,D_j\) of dimensions \(p_j,s_j\). Put \(R_j\) in the same factor as \(B\) and \(D_j\) in the opposite factor. In the alternating case both are primal summands of \(W\). In the conjugacy case a private dual summand is represented by adding its dual to \(W\). Pair the bases \((a_h)\) of \(B\oplus R_j\) and \((d_h)\) of \(D_j\) in order.

- In the alternating case set \(M_j=\sum_h a_h\wedge d_h\).
- In the conjugacy case set \(M_j=\sum_h a_h\otimes d_h\) for row markers and \(\sum_h d_h\otimes a_h\) for column markers. A marker for \(V\) or \(F_0\) is a column marker.

The output tensor is \(D(A)+\sum_j M_j\otimes z_j\), with slice axis \(L\oplus Z\). The eight private identities separately detect every tag coefficient, and the fixed data summand detects every remaining coefficient. Thus the slices form a basis of the output space. An output space isometry or conjugation lifts uniquely to a tensor transporter \((P,P,S)\) or \((P,P^{-T},S)\), respectively, by using the resulting change of slice basis. These tensor actions describe the usual matrix congruence and conjugation up to the convention for transposing the congruence matrix.

In the conjugacy case put all primal row blocks in \(X\) and all primal copies of column blocks in \(Y\), so \(W=X\oplus Y\). Every matrix is in \(X\otimes Y^*\), and the product of any two of them is zero.

## 3. Recover the source from every transporter

Contractions by covectors annihilating \(Z\) have rank at most \(N\). Any nonzero tag coefficient gives rank at least \(p_j>N\) on its private identity submatrix. The rank-at-most-\(N\) covectors therefore identify the annihilator of \(Z\), so a transporter preserves \(Z\) and induces \(\bar S\) on \((L\oplus Z)/Z=L\). Quotienting out \(Z\) recovers \(D(A)\).

For \(i=1,2\) let \(C_i\subset H_i\) be the span of the \(i\)-th factor supports of the matrices in this data tensor. The \(i\)-th factor support of a matrix tensor is the image of contraction by the dual of the opposite factor. These spans are contained in the original matrix coordinates and are carried to the corresponding spans for the target. Quotienting either matrix factor by \(C_i\) kills the data tensor. In the resulting matrix pencil the contraction depends only on the restriction to \(Z\), so each quotient defines a pencil on \(Z^*\).

Use the pencil obtained by quotienting the second factor to identify the individual tag lines in \(Z^*\).

- In the alternating case a single nonzero marker \(j\) has rank \(2s_j-\dim((B\oplus R_j)\cap C_2)\), which lies in \([2s_j-N,2s_j]\). The term with second factor \(D_j\) keeps rank \(s_j\). The reversed term loses exactly the dimension of the displayed intersection. Their supports on each axis are disjoint after quotienting, so the ranks add. A combination of at least two markers has rank at least \(4M\) on the disjoint private alternating submatrices.
- In the conjugacy case a single nonzero marker has rank in \([s_j-N,s_j]\), because quotienting a matrix factor by a space of dimension at most \(N\) loses at most \(N\) ranks. At least two nonzero coefficients give rank at least \(2M\) on the disjoint private identities.

In each case the single-marker rank bands are disjoint and strictly below the multiple-marker threshold. Each tag line is therefore individually preserved, including over the field of two elements.

For an alternating marker, its first-factor support in the second-factor quotient is \((B\oplus R_j)\oplus D'_j\) for some \(D'_j\subseteq D_j\). Indeed the term with second factor \(D_j\) gives all of \(B\oplus R_j\), and its reverse term contributes only in \(D_j\) with independent second-factor support. Intersect the supports of the two markers for \(B\) to recover exactly \(B\). For a conjugacy row marker, its first-factor support in the second-factor quotient is exactly \(B\oplus R_j\) because its second factor was private. For a column marker, use the already identified tag line with the first-factor quotient and take its second-factor support, which is again \(B\oplus R_j\). The two intersections recover the conjugacy blocks as well.

All four data blocks are now invariant under the appropriate factor actions. Taking the \(U,V\) block of the equation on \(D(A)\) gives a source transporter \((P|_U,P|_V,\bar S)\) for alternating isometry and \((P|_U,P^{-T}|_V,\bar S)\) for conjugacy. Only predetermined matrix blocks and the invariant quotient are needed for this extraction. The rank reasoning proves they are invariant and imposes no low-rank search on the algorithm.

## 4. Lift and verify the five properties

For a source transporter \((P_U,P_V,Q)\), use \(P_U,P_V\) in the input blocks, \(Q^{-T}\) on \(E\), the identity on the line, and \(Q\oplus I_Z\) on the slice axis. Act identically on every private \(R_j\). In its designated factor, act on \(D_j\) by the inverse transpose of the action on \(B\oplus R_j\). For conjugacy a prescribed action on a dual block is implemented on its primal copy by inverse transpose. The fixed data summand and every marker are fixed under this lift. Each block of the lift is algebraic in the input group matrices and their inverses, and the lift respects multiplication. The extraction retracts the lift. Restrictions and passage to the invariant quotient commute with composition, giving the section on target transporters required by the paper.

These two directions prove the kernel-reduction property. The output layout is independent of entries. Its matrix order is \(N+\sum_j(2s_j-\dim B_j)=2\sum_j s_j-N=O(N)\) and the number of slices is \(\dim L+8\). The dense output takes polynomial time to write by copying entries and writing constants. For alternating matrices use the independent coordinates of \(\bigwedge^2 W\), ordered by basis pairs \(i<j\), with \(U\) preceding \(V\). In these coordinates and in the ordinary conjugacy coordinates, each output entry is an unchanged input entry or a constant. The redundant full alternating matrix contains the prescribed negative transpose below the diagonal. The two maps are p-projections in the independent coordinates, hence affine algebraic containments. The lift and extraction give the functorial property on isomorphisms, as in §2.2 of the paper. The construction works over every field. The claimed bit-time bounds for standard finite-field and rational input representations use only copying field entries and writing constants.

If source formats differ, different \(N\) give different matrix orders and different \(\dim L\) give different slice counts. When \(N,\dim L\) agree, the rank bands identify the same labels. The recovered \(U,V\) dimensions must agree for a target transporter to exist.

## Prior work

The two original reductions and the five-property question are due to Joshua A. Grochow and Youming Qiao. Part IV uses private blocks to distinguish ranks and obtains the conjugacy transporter correspondence by first passing to nondegenerate tensors. Here the fixed copy of the slice axis and the quotient by the data support allow a single affine layout for every tensor. The comparison with Part IV does not establish publication priority. [Part I](https://doi.org/10.1137/21M1441110) · [Part IV, Remark 3.3 and Lemma 4.1](https://arxiv.org/html/2306.16317#S4.SS1)
