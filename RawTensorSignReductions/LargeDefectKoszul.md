# Koszul defect cancellation for two-sign tensor isomorphism

Work over \(F=\mathbb F_3\). Given two explicit tensors, the two-sign comparison asks for a single transporter having determinant \(+1\) in each of two designated modes. This note gives a deterministic polynomial-time, single-instance reduction to one-sign tensor isomorphism on an efficiently recognizable domain. All modes and both Koszul defect dimensions may grow. The unrestricted reverse reduction remains unresolved.

The starting point in the [AgentAlphaXiv step-decomposed exact-verifier study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf) is to pass the accepted state itself to the next constraint. Here the two defect maps are induced by the actual original tensor transporter, and the one-sign output tests a further determinant on that same transporter. The study supplies no mathematical premise.

## 1. Recognizing the domain

Use the convention that the tensor is a map \(B:X\to V\otimes Y\), with \(X,Y\) the two designated modes, one of them dualized. The determinant sign on a dual mode is the same as on the original mode. Suppose
\[
\dim_F X,\dim_F Y\text{ are even},\qquad c=\dim_F V\equiv3\pmod4.
\]
The order of \(X,V,Y\) can be chosen by permuting the input axes. In a basis \(e_1,\ldots,e_c\) of \(V\), write \(B(x)=\sum_i e_i\otimes M_i(x)\). Form the canonical map
\[
D: V\otimes X\longrightarrow\Lambda^2 V\otimes Y,\qquad
v\otimes x\longmapsto\sum_i(v\wedge e_i)\otimes M_i(x).
\]
Unequal input formats give a fixed negative instance. A zero-dimensional mode leaves the zero tensor, and matching zero formats are positive by the identity transporter. In the remaining cases the mode dimensions are positive. Write \(K=\ker D\) and \(C=\operatorname{coker}D\). Compute the unital pair-adjoint algebra
\[
E=\{(a,b)\in\operatorname{End}(X)\times\operatorname{End}(Y): M_i a=bM_i\text{ for all }i\}.
\]
Use componentwise ordinary composition on \(E\), so both actions are left representations: \(M_i(aa')=bb'M_i\) for two adjoints \((a,b),(a',b')\). The opposite multiplication sometimes used for a covariant pair-adjoint is absorbed by writing the first tested mode as the domain \(X\) of \(B\). Thus an adjoint unit \((a,b)\) gives a tensor automorphism with \(g_X=a,g_Y=b,g_V=I\) in this convention. Thus it acts compatibly on the domain and codomain of \(D\) and on both defects. For \(J=\operatorname{rad}E\), decompose
\[
E/J\cong\prod_j M_{d_j}(F_j).
\]
For \(M=K,C\), take the radical flag \(J^iM\) and the associated graded module. Define \(r_{j,M}\) to be the multiplicity of the natural simple \(F_j^{d_j}\) in the whole graded module, summing all its grades. Let \(H\) be the direct sum of the parts belonging to odd \(d_j\), in both graded modules. The sufficient conditions are
\[
  r_{j,K}+r_{j,C}\equiv0\pmod2\quad\text{for every even }d_j,
  \qquad \dim_F H=O(\log(2+L)),
\]
where \(L\) is the written input length and the constant in \(O(\log(2+L))\) is fixed. Neither the algebra \(E\) nor the defect maps nor any quotient labels are supplied. For a source meeting the conditions, an ordinarily isomorphic target must have compatible data and also meet the conditions.

All the spaces and operations above have polynomial sizes. Solve the intertwining equations by linear algebra and compute the radical by the deterministic finite-field radical algorithm. To split the semisimple quotient \(Q=E/J\), compute its center \(Z\) by linear equations. The fixed algebra \(\ker(z\mapsto z^3-z)\) in \(Z\) is a product of copies of \(\mathbb F_3\). Split its unit into primitive idempotents by intersecting the three projectors \(1-(z-\lambda)^2\) for each basis element \(z\) of that fixed algebra and each \(\lambda\in\mathbb F_3\). Every primitive factor is separated by this basis of the product. This gives the simple factors with their centers.

Use Rónyai's explicit finite-field matrix splitting algorithm on each factor over its center, which is presented by its multiplication table. This is a polynomial algorithm with a finite-field factoring subroutine. That subroutine is deterministic in the fixed characteristic \(3\). For a squarefree polynomial \(f\) over the center field, split the fixed algebra of the absolute cube in the product of fields \(F_j[t]/(f)\), just as above. Its primitive idempotents give the factors by polynomial gcds, and the usual derivative and Frobenius-root step handles multiplicities. Thus no random field search or enumeration of elements of an extension field is needed. [Ivanyos, deterministic radical algorithm](https://real-d.mtak.hu/260/1/Ivanyos_Gabor-dr.pdf) · [Rónyai, computing the structure of finite algebras](https://www.sciencedirect.com/science/article/pii/S074771710880017X) · [Finite-field explicit isomorphism case, discussion before Theorem 1](https://arxiv.org/html/1508.07755#S1)

Compute successive radical images by spans. In each grade apply the quotient central idempotents to split the isotypic spaces. For an \(M_{d_j}(F_j)\) isotypic piece, choose a basis over \(F_j\) for the image of a primitive matrix idempotent and apply the computed matrix units to obtain a module-coordinate basis. Field-coordinate and module-coordinate bases can be chosen deterministically at each endpoint. This computes the integer multiplicities and the frame calibration used below.

## 2. Character identity on the actual transporter

For a genuine transporter from \(T\) to \(T'\), write its maps on \(X,V,Y\) as \(g_X,g_V,g_Y\). We have
\[
D'(g_V\otimes g_X)=(\Lambda^2g_V\otimes g_Y)D.
\]
The product of the raw determinants of these induced maps on the domain and codomain of \(D\) is
\[
(\det g_X)^c(\det g_Y)^{\binom c2}
(\det g_V)^{\dim X+(c-1)\dim Y}=\det g_X\det g_Y.
\]
Use adapted bases in which the domain starts with a kernel basis, then a lift of an image basis, and the codomain starts with that very image basis, then a lift of a cokernel basis. In those bases the image-map determinant occurs twice, so its product is \(1\) over \(F\). The kernel and cokernel bases come from the radical flags and the module coordinates above, with lifts to the relevant filtered spaces. If \(\kappa_T\) denotes the product of the two frame determinants from the adapted domain and codomain bases to their raw bases, then
\[
\det g_X\det g_Y
   =(\kappa_{T'}/\kappa_T)\det(g_K)\det(g_C),
\]
where the last two determinants are in the adapted defect bases.

The original transporter conjugates \(E\) to \(E'\), sending the radical and these flags to their counterparts. Fix a corresponding pair of matrix factors of degree \(d_j\). In module coordinates its algebra map applies a field isomorphism \(\sigma:F_j\to F'_{j'}\), then conjugates by a matrix \(u\in\mathrm{GL}_{d_j}(F'_{j'})\). On a grade with multiplicity \(r\) its defect map is an ordinary tensor product \(u\otimes m\), preceded by coordinatewise \(\sigma\), for some \(m\in\mathrm{GL}_r(F'_{j'})\). It therefore contributes
\[
N_{F'_{j'}/F}(\det u)^r\,N_{F'_{j'}/F}(\det m)^{d_j}
  \big(\det_F\sigma\big)^{d_j r}.
\]
The same \(u\) can be used for every grade and both defects, since the algebra map is the same. If \(d_j\) is even, the second and third factors are \(1\). The first factors across both defects yield \(1\) by the parity hypothesis. A permutation of even-degree blocks also gives determinant \(1\), as each block has even dimension over \(F\). Order all even-degree pieces before the odd-degree pieces within each grade, and order \(H\) by the induced grade and defect order. Then all odd-degree permutations and all remaining local factors are included exactly once in \(\det(g_H)\). It follows that
\[
\det g_X\det g_Y=(\kappa_{T'}/\kappa_T)\det(g_H).
\]

## 3. Converting the character to a single live sign

The diagram includes the original tensor, the exterior-square map of the \(V\) role, \(D\), its kernel inclusion and cokernel projection, \(E\) with its natural actions, the radical flags and their quotients, and the direct sum of the grades with all grade inclusions, and the subspace \(H\) with its inclusion into that direct sum. The map on \(E\) is forced by its faithful inclusion into the represented pair of matrix spaces, and the quotient maps force the maps on the graded pieces. The sum of odd-degree isotypic parts is invariant under every algebra map, so the inclusions from this sum into the graded spaces force \(g_H\). Auxiliary field-factor labels need not be matched in preprocessing.

If \(H\ne0\), attach its exterior algebra and mark
\[
 \kappa_T^{-1}\omega_T\ \in \ \Lambda^{\dim H}H
\]
where \(\omega_T\) is the ordered coordinate volume. Its preservation is equivalent to the displayed product of the two raw signs being \(+1\). The exterior algebra has dimension \(2^{\dim H}\), which is polynomial. If \(H=0\), the sign product on every transporter is the known frame ratio. A mismatch gives a fixed negative output. Otherwise use the raw comparison with only the determinant on \(X\) constrained.

In the nonzero case, the unmarked diagram extends every genuine transporter with the forced auxiliary actions. The additional volume mark accepts exactly those whose two-sign product is positive. All links use tensors of order at most three. Use the [determinant-preserving tensor-system compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/SignedCompiler.md) with \(X\) designated as its one live sign. A positive output then gives an original transporter with \(\det g_X=1\) and \(\det g_X\det g_Y=1\), so both original tests pass on that single transporter. Conversely, a two-sign witness extends to a positive output. All computation is deterministic polynomial time. The pairing-of-defects argument uses exact sequence multiplication and the same simple-factor determinant formula as the [represented-adjoint width test](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/Swaps.md), applied here to a different module rather than either raw mode.

## 4. An explicit family with unbounded defects

For \(c\ge7\), \(c\equiv3\pmod4\), build two pencils with the common label space \(V=F^c\). On each pencil let \(X_0=\Lambda^2V\otimes F^2\), \(Y_0=V\otimes F^2\). For the input piece indexed by \(i<j\), the \(i\)-slice maps to the \(j\)-output piece by \(I\), and the \(j\)-slice maps to the \(i\)-output piece by \(-I\). All other slice maps on that piece are zero. Change only the positive coefficients on \((1,2)\) and \((3,4)\), replacing them by \(A\) and \(B\), respectively. Use the following choices:
\[
(A_0,B_0)=(I+E_{12},I+E_{21}),\qquad
(A_1,B_1)=\left(\begin{pmatrix}0&0\\0&1\end{pmatrix},-I+E_{12}\right),
\]
where the \(E_{ab}\) in the coefficients are elementary \(2\times2\) matrices.

The first pencil has invertible \(D\). Indeed without the two changes the map splits by multisets of three basis indices. A repeated-index block is a signed identity on \(F^2\). A distinct-index triple gives the matrix \(J_3-I_3\) tensored with \(I_2\) in oriented cyclic bases. The inverse of \(J_3-I_3\) is \(-I_3+J_3/2\). Each multiset sees at most one changed coefficient since the two index pairs are disjoint. For a repeated-index block the changed map is a signed \(A_0\) or \(B_0\), both invertible. For a distinct-index block with modified coefficient \(U\), the changed block is invertible exactly when \(I+(U-I)/2=(I+U)/2\) is invertible. To check this, write the perturbation as injection into one output coordinate composed with \(U-I\) and projection from one input coordinate. After multiplying by the unmodified inverse, the composition on \(F^2\) through those two coordinates is \((U-I)/2\). This rank-update calculation applies since the modified entry is off diagonal. Both \(I+A_0\) and \(I+B_0\) are invertible. The second pencil has a nonzero kernel since the repeated-index block for the multiset \(\{1,2,2\}\) is a signed \(A_1\), which is singular. Each pencil has \(D\) square, by \(\dim X_0=2\binom c2\) and \(\dim Y_0=2c\).

The strict intertwiner spaces of these pencils can be computed exactly. Write an intertwiner as \(P\) on the input and \(Q\) on the output, with \(M_i'P=QM_i\) for every \(i\). The zero slice maps on the input piece indexed by \(i<j\) force its image under \(P\) to stay in the target piece with the same pair. The only possible extra component is in the target \(\ker A_1\) in piece \((1,2)\), when \(2\in\{i,j\}\) but \(1\notin\{i,j\}\). This follows by intersecting the target kernels of all slices with labels outside \(\{i,j\}\). For every output index \(j\ne2\), the \(j\)-output piece is in the image of every source slice with label \(i\ne j\). Its image under \(Q\) must then lie in the intersection of the corresponding target images, which is contained in the \(j\)-output piece since the \(i\)-slice always misses the \(i\)-output piece. For \(j=2\), use the input piece \((2,3)\) and the \(3\)-slice. This slice is onto the \(2\)-output piece and kills the potential extra component. Hence \(Q\) preserves the indexed output pieces, and applying the \(2\)-slice rules out every extra component of \(P\).

On an unmodified pair \((i,j)\) the two equations now identify \(P_{ij}\), \(Q_i\), and \(Q_j\). The graph of unmodified pairs is connected. The unmodified reverse coefficients on \((1,2)\) and \((3,4)\) then identify their \(P\)-blocks with the same common map \(G\). Its remaining equations are \(A'G=GA\) and \(B'G=GB\). For each pencil separately the simultaneous centralizer is the scalars. Between the two different pencils the only \(G\) is zero, since \(B_0\) has sole eigenvalue \(1\) and \(B_1\) has sole eigenvalue \(-1\). Thus the pair-adjoint algebra on one copy of the first pencil plus \(d\) copies of the second is \(F\times M_d(F)\).

Take \(d\ge2\) even. The two Koszul defects occur entirely on the \(M_d(F)\) factor, since the first block is invertible. Their multiplicities for this factor agree since the second Koszul matrix is square. Consequently \(H=0\), while each full defect dimension is at least \(d\). The tested modes are even, and all three raw dimensions grow with \(d,c\to\infty\). The scalar factor carries large multiplicity spaces on both raw tested modes, so applying the raw width test directly with this pair-adjoint algebra leaves a large width. Its adjoint-unit determinants are positive on both tested modes, since the multiplicities of each active simple module in both raw modes are even. The other two pair-adjoint subgroups fix one tested mode, so the locked sign product forces positivity on the remaining tested mode too. The example has no usable sign correction from any one of the three paired adjoint-unit subgroups. The method nonetheless locks the product of the two tested signs. This separates the new defect cancellation condition from a bounded-corank assumption and from the older width test on this raw pair-adjoint algebra.

These are informal proofs. The theorem is for the stated recognizable class, including the displayed family, and gives no unrestricted tier collapse.