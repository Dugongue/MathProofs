# Rank- and support-optimal smoothed tensor isomorphism from a single scalar

Informal proof. This applies the two matrix-algebra generation tests from [Problem 1.8](https://github.com/Dugongue/MathProofs/tree/main/Problem18) to a sparse explicit tensor direction. It works over finite fields and also for the real and complex groups on explicit rational inputs. The same direction gives an exact algorithm for comparing arbitrarily long ordered tensor lists when they have a suitable marked member or a suitable common linear combination.

## 1. The theorem

Let \(n\ge 2\), \(c\ge n\), and \(D_n=(8n-2)n^2\). In the orthogonal case take \(K=\mathbb F_q\) with the standard symmetric bilinear form. In the unitary case take \(K=\mathbb F_{q^2}\) with its standard Hermitian form. The coefficients of the perturbation are in the fixed subfield \(k=\mathbb F_q\) in either case. Orthogonal characteristic two means the isometry group of the standard bilinear form.

If \(q>2n+8\), one can construct a tensor \(\Delta\in K^n\otimes K^c\otimes K^n\) with the following properties.

1. Its CP rank is exactly \(n\). It is supported on at most \(3n\) coordinates, all in two slices of the \(c\)-mode.
2. For every tensor \(A\) of the same format, at most \(D_n\) choices of \(t\in k\) make \(A+t\Delta\) fail the two Problem 1.8 matrix-algebra generation tests. For all other choices, the Problem 1.8 deterministic exact algorithm decides orthogonal or unitary isomorphism between \(A+t\Delta\) and **every** target tensor of the same format in time polynomial in their binary input lengths. A target may be chosen after \(t\) and the perturbed source are revealed.
3. For any explicitly supplied set \(S\subseteq k\) of more than \(D_n\) elements, a passing \(t\in S\) is found in deterministic polynomial time by testing the first \(D_n+1\) elements. For uniform \(t\in S\) the failure probability is at most \(D_n/|S|\). The rank bound \(n\) on the perturbation is optimal for a scheme that must take the zero source to a passing tensor.

When \(q>D_n\), Section 7 strengthens the support bound to exactly \(2n\), the minimum possible for these two generation tests, while preserving rank \(n\) and the bound \(D_n\) on failing scalars. A set of \(D_n+1\) distinct scalars can itself be constructed in polynomial time. If a randomized guarantee \(1-\varepsilon\) is desired, \(q\ge D_n/\varepsilon\) suffices to use one uniform scalar. The algorithm compares the *perturbed* source to the given target. A marked comparison preserving one common transporter is proved in Section 5.

## 2. Generation tests in slice coordinates

Write the slices along the \(c\)-mode of \(A\) as \(n\times n\) matrices \(M_j\), with row in the first mode and column in the last. Use an overbar for the field involution, trivial in the orthogonal case, and write \(M^*=\bar M^{\mathsf T}\). The middle-mode Gram matrix \(S\) has entries \(S_{jj'}=\sum_{i,k}(M_j)_{ik}\overline{(M_{j'})_{ik}}\). In these coordinates the two lists used in Problem 1.8 are
\[
 R_h=\sum_{j,j'}\overline{(S^h)_{jj'}}\,M_j^{\mathsf T}\overline{M_{j'}},
 \qquad
 Z_{k\ell}=\sum_j M_j(:,k)\,M_j(:,\ell)^* .
\]
Here \(0\le h<c\) and \(1\le k,\ell\le n\). Each list must generate the unital algebra \(\operatorname{Mat}_n(K)\). When all entries lie in \(k\), the bar has no effect. In particular, when \(S\) is diagonal with entries \(\lambda_j\), one has \(R_h=\sum_j \lambda_j^h M_j^{\mathsf T} M_j\), with \(\lambda_j^0=1\).

## 3. An explicit perturbation of rank \(n\)

Choose \(d_1,\ldots,d_n\in k^\times\) such that their squares are distinct,
\[
 d_1^2+d_2^2\ne 0,\qquad \mu=\sum_i d_i^2\ne 0.
\]
Choose \(d_1,d_2\) first, rejecting \(d_2^2\in\{d_1^2,-d_1^2\}\). For \(n=2\) the second condition follows already. For \(n>2\), exclude the negative of the previous sum when choosing \(d_n^2\). At any choice there are at most \(n+1\) forbidden squares, including zero, and at most two roots of any forbidden square. A polynomial-length list of distinct field elements therefore suffices.

Let \(M=\operatorname{diag}(d_1,\ldots,d_n)\), \(u=(d_2,-d_1,0,\ldots,0)^{\mathsf T}\), \(v=(1,\ldots,1)^{\mathsf T}\), and put \(z=v^{\mathsf T}M^{-1}u=d_2/d_1-d_1/d_2\ne0\). Choose \(\tau\in k^\times\) such that
\[
 \nu=\tau^2 (u^{\mathsf T}u)(v^{\mathsf T}v)\ne\mu,\qquad
 1+\tau^2 z^2\ne0 .
\]
Each condition excludes at most two values of \(\tau\), including when \(v^{\mathsf T}v=0\), since \(\mu\ne0\). Set the first two middle slices of \(\Delta\) to \(M\) and \(N=\tau u v^{\mathsf T}\), and the rest to zero. The formulas apply also in characteristic two.

The two slice vectors are perpendicular since \(u^{\mathsf T}Mv=0\). Thus \(S(\Delta)\) is diagonal with first two entries \(\mu,\nu\). The two moments \(R_0,R_1\) span
\[
 M^2,\qquad N^{\mathsf T}N=\tau^2(u^{\mathsf T}u)vv^{\mathsf T}.
\]
Lagrange interpolation in the distinct \(d_i^2\) expresses \(E_{ii}\) as a polynomial of degree at most \(n-1\) in \(M^2\). The products \(E_{ii}(N^{\mathsf T}N)E_{jj}\) are the nonzero scalar \(\tau^2u^{\mathsf T}u\) times \(E_{ij}\). Consequently the words of length at most \(2n-1\) in \(R_0,R_1\) already span the first algebra.

For the second list, a linear combination with coefficient matrix \(C=(C_{k\ell})\) has value
\[
 MCM+\tau^2(v^{\mathsf T}Cv)u u^{\mathsf T}.
\]
If this equals zero, multiplication by \(M^{-1}\) on both sides and application of the functional \(v^{\mathsf T}(\,\cdot\,)v\) give
\[
 (1+\tau^2 z^2)v^{\mathsf T}Cv=0.
\]
The functional value vanishes and \(C=0\). The \(n^2\) matrices in the list are therefore a basis of the second algebra.

The slices \(M,N\) have a simultaneous rank-one decomposition of size \(n\). Indeed \(M^{-1}N=\tau M^{-1}uv^{\mathsf T}\) is rank one with trace \(\tau z\ne0\). It is diagonalizable over \(k\), since it acts by \(\tau z\) on the span of \(M^{-1}u\) and by zero on \(\ker v^{\mathsf T}\), and these subspaces are complementary. If \(T\) is its eigenbasis matrix and \(\Lambda=T^{-1}M^{-1}NT\), then \(M=(MT)IT^{-1}\) and \(N=(MT)\Lambda T^{-1}\). Taking corresponding columns of \(MT\) and rows of \(T^{-1}\) gives the \(n\) pure-tensor summands with middle coefficients supported in the first two coordinates. The first slice \(M\) has rank \(n\), so fewer terms cannot suffice. The entry support bound is \(n+2n=3n\).

## 4. The entire affine line except polynomially many scalars

Choose \(n^2\) words of length at most \(2n-1\) in \(R_0,R_1\) whose values at \(\Delta\) are a basis. This choice is needed only for the proof. The determinant of their vectorized values at \(A+t\Delta\) is a nonzero univariate polynomial in \(K[t]\). Indeed \(R_0\) and \(R_1\) have respective degrees at most \(2\) and \(4\) in \(t\) along this line, with coefficients of these highest permitted degrees equal to \(R_0(\Delta)\), \(R_1(\Delta)\). The same product rule holds for the degree bound of each word and the leading permitted coefficient is its value at \(\Delta\). This uses \(t\in k\), so conjugating the entries leaves the scalar variable fixed. Multilinearity of the determinant yields a nonzero coefficient at the sum of all column bounds, with degree at most \(4(2n-1)n^2\). Likewise the determinant of the \(n^2\) vectorized \(Z_{k\ell}(A+t\Delta)\) has degree at most \(2n^2\) and its coefficient in degree \(2n^2\) is nonzero. The product has degree at most \(D_n\). Hence outside at most \(D_n\) field elements both generation tests pass.

For bit complexity, in the usual explicit finite-field representation, compute a basis of the fixed field in the unitary case by kernel computation for the \(\mathbb F_p\)-linear map \(x\mapsto x^q-x\). Enumerate the required polynomial number of distinct field elements via coordinate counters in that basis. Both generation tests use the closure algorithm from Problem 1.8, retaining at most \(n^2\) independent words for each. Each field operation and this number of tests have polynomial binary cost. The decision on a passing source uses the already proved Problem 1.8 search for ordered intertwiners and final Witt-extension criterion.

For rank optimality, any tensor of CP rank \(<n\) has all its columns in the last-mode flattening contained in a proper subspace \(L\subset K^n\), namely the span of the last-mode pure factors. Each \(R_h\) has image contained in \(L\), as seen from the displayed slice formula, and thus preserves \(L\). If \(L\ne 0\), their unital algebra is contained in the proper algebra of matrices preserving \(L\). If \(L=0\), the tensor is zero and the generated algebra consists of scalars. Such a tensor therefore fails the first test.

## 5. Exact simultaneous comparison with a common anchor

Let \(A_1,\ldots,A_r\) and \(B_1,\ldots,B_r\) be ordered lists of tensors of the same format. If a supplied shared coefficient tuple \((s_1,\ldots,s_r)\) makes \(A_*=\sum_i s_i A_i\) pass, there is a deterministic exact polynomial-time decision whether all \(A_i\) map to the corresponding \(B_i\) under a **single** orthogonal or unitary transporter. Take \(B_*=\sum_i s_i B_i\). Any simultaneous transporter must map \(A_*\) to \(B_*\).

Apply the first two ordered intertwiner steps of Problem 1.8 to this pair. They either reject soundly or produce invertible representatives \(P_0,X\) for the first and last modes, of squared norms \(d_a I,d_b I\). Every simultaneous transporter has first and last modes in the lines \(K P_0,KX\), respectively. This follows from full matrix algebra generation for each of the source families. In the second intertwiner step the target slice products are scaled by \(d_b\) as in Problem 1.8, to account for \(X\) being a similitude. The same square or norm tests establish that there are scalars \(\alpha,\beta\) with \(\alpha P_0,\beta X\) isometries. Write \(s=(d_a d_b)^{-1}\).

Form \(H\) by concatenating the \(c\)-mode flattened matrices of \((P_0,I,X)A_i\), and \(F\) by concatenating those of \(B_i\) in matching order. Test
\[
 \ker H=\ker F,\qquad F^*F=s H^*H
\]
for odd-characteristic orthogonal or unitary isomorphism. Given roots as above, \(\lambda=\alpha\beta\) has norm \(s\). Hence these two equations mean that the single linear map \(\lambda Hx\mapsto Fx\) between the two images is well-defined, injective and form-preserving. By Witt extension there is one ambient isometry implementing it, so \((\alpha P_0,Q,\beta X)\) maps every list member as required. The same equations are necessary, since a simultaneous transporter can be written this way, possibly with different normalization scalars of the same norms.

In characteristic two for the standard symmetric bilinear form, set \(e=(1,\ldots,1)^{\mathsf T}\) and use the unique \(\lambda\) with \(\lambda^2=s\). Keep the same Gram equality and replace the kernel equality by
\[
 \ker[\lambda H\mid e]=\ker[F\mid e].
\]
The forced cross-pairings with the marker \(e\) hold because \(\langle x,e\rangle^2=\langle x,x\rangle\) over \(K\). The marker-preserving extension argument of Problem 1.8 applies to the single augmented partial map. The unique square root is obtained by inverse Frobenius. Both kernel and Gram checks have polynomial cost in the total list input length.

In particular, append \(\Delta\) as a source member and append any tensor \(\Delta'\) as the corresponding target member. Choosing just that member as the shared linear combination gives a worst-case polynomial algorithm for deciding whether there is one isometry carrying \(\Delta\) to \(\Delta'\) and simultaneously carrying all original source members to their targets. Alternatively, if the source list includes one \(A\) and the marked \(\Delta\), Section 4 gives a polynomial-size menu of valid probes \(A+t\Delta\). The simultaneous test uses **all** the original members in its concatenated Gram and kernel comparisons, so selecting a probe cannot lose the shared-transporter condition.

## 6. Arbitrarily small rank-optimal noise over the real and complex fields

Take real orthogonal isomorphism on rational input tensors, or complex unitary isomorphism on Gaussian-rational input tensors. For any rational \(\sigma>0\), choose a grid \(S\subset[-\sigma,\sigma]\cap\mathbb Q\) of \(m>D_n\) equally spaced points. There is an explicit rational rank-\(n\) direction \(\Delta\), with \(2n\) nonzero entries in two middle slices, such that for every input \(A\), all but at most \(D_n\) choices of \(t\in S\) make \(A+t\Delta\) exactly comparable to every target in deterministic polynomial bit time. Every coordinate moves by at most \(\sigma\). For uniform \(t\), the undecided probability is at most \(D_n/m\). Choosing \(m\) a power of two with \(m\ge D_n/\varepsilon\) gives undecided probability at most \(\varepsilon\) using just \(\log_2 m\) random bits total. The algorithm never outputs an incorrect definite answer.

**Construction and probability.** The \(2n\)-coordinate construction is proved in Section 7. Divide that direction by the largest absolute entry, so each coordinate has absolute value at most one. The rescaling multiplies each moment and slice product by a nonzero scalar and preserves both generation tests and the rank. Section 4 applies for real \(t\). The grid has entries of bit length \(O(\operatorname{bitlength}(\sigma)+\log m)\), so it need not be enumerated to sample one point, or to check its first \(D_n+1\) points deterministically.

**Exact all-target decision.** Perform the same two intertwiner steps as in Section 5, using \(\mathbb Q\) or \(\mathbb Q(i)\). On failure of generation, return UNDECIDED. The real or complex solution space is obtained by extending scalars in each of the linear systems, so a rational incompatibility is an ambient incompatibility. Full generation over the coefficient field becomes full generation over the ambient field, and \(P_0^*P_0=d_a I\) and \(X^*X=d_b I\) now have \(d_a,d_b>0\). The positive real normalization roots exist. Run the last Gram and kernel comparisons entirely in the rational coefficient field as in Section 5. In the correctness proof the resulting partial isometry extends by choosing orthonormal bases of the perpendicular complements over \(\mathbb R\) or \(\mathbb C\). Consequently neither an eigenvalue routine nor a numerical square root is needed. The same reasoning also proves the simultaneous anchored claim of Section 5 for these groups.

**Bit cost.** Clear a common denominator for each input tensor, with bit length at most the sum of input denominator bit lengths. The all-moment computation takes powers of a \(c\times c\) matrix only up to \(c-1\), and each retained word in the generation test has length at most \(n^2-1\). To see the latter, increasing depth through a retained word follows a chain of distinct retained words, starting at the identity. Proposed words have length at most \(n^2\). After clearing common denominators for the generators, the exact numerator sizes of these products are bounded by the product length times the common-denominator coefficient bound plus a logarithmic-in-dimension term per multiplication. Independent-column tests, kernel computations, inversion, and the two systems can then use standard polynomial-bit rational elimination. Subsequent slice products, scaling and Gram comparisons have polynomial bit length by the same denominator and dimension bounds. All counts are polynomial in the explicit input lengths.

## 7. Exactly \(2n\) coordinates are necessary and sufficient

**Construction.** Choose \(M=\operatorname{diag}(d_1,\ldots,d_n)\) as before, with distinct nonzero squares and with \(\mu=\sum_i d_i^2\notin\{0,d_1^2\}\). The additional condition is imposed by excluding one more square when choosing the last diagonal value. In characteristic zero take \(d_i=i\). Take \(v=(1,\ldots,1)^{\mathsf T}\), put \(N=\tau e_1v^{\mathsf T}\), and use \(M,N\) as the only nonzero middle slices. For \(x=\tau^2\), the middle Gram matrix on these slices is
\[
 \begin{pmatrix}\mu&\tau d_1\\ \tau d_1&xn\end{pmatrix}.
\]
Therefore \(R_0=M^2+xvv^{\mathsf T}\) and for \(\tau\ne0\),
\[
 J(x)=x^{-1}(R_1-\mu R_0)
     =(xn-\mu)vv^{\mathsf T}+d_1^2(e_1v^{\mathsf T}+ve_1^{\mathsf T}).
\]
At the formal value \(x=0\), the displayed polynomial expression for \(J(x)\) has every off-diagonal entry nonzero by the two restrictions on \(\mu\). The same matrix-unit proof as in Section 3 shows that \(M^2,J(0)\) generate the full algebra in words of length at most \(2n-1\). Choose a basis from those words and take the determinant of the vectorized corresponding words in \(R_0,J(x)\). It is a polynomial of degree at most \((2n-1)n^2\) in \(x\), with nonzero constant term. For any nonzero \(x\) at which it does not vanish, the corresponding \(R_0,R_1\) generate in words of length at most \(2n-1\).

The second test also passes whenever \(1+x/d_1^2\ne0\), by applying the rank-one update argument of Section 3 with \(u=e_1\). The product of the two tests' witness polynomials in \(x\) has degree at most \(E_n=(2n-1)n^2+1\). If \(q>2E_n+1\), test \(2E_n+1\) distinct nonzero \(\tau\) until a passing direction is found. The product after substituting \(x=\tau^2\) has degree at most \(2E_n\), so this scan succeeds. The hypothesis \(q>D_n\) implies this field-size requirement and permits the choices of the \(d_i\). In characteristic zero use \(\tau\in\{1,\ldots,2E_n+1\}\), giving rational directions of polynomial bit length. At each trial, check the linear span of the slice products and the span of words in \(R_0,R_1\) of length at most \(2n-1\). The latter span can be built one length at a time by adjoining the left products of a current basis by each generator and retaining only an independent basis, with at most \(n^2\) matrices retained at any stage.

There are exactly \(2n\) nonzero entries. The same rank argument as before applies, since \(M^{-1}N\) is rank one with nonzero trace \(\tau/d_1\). The degree bounds along the later smoothing line are unchanged, because at the direction selected here the moments \(R_0,R_1\) still admit a basis in words of length at most \(2n-1\), and the slice products span their matrix algebra linearly.

**Lower bound.** Suppose both algebra tests pass and the tensor has at most \(2n-1\) nonzero coordinates. Every last-mode coordinate must occur, since otherwise all \(R_h\) preserve the proper subspace generated by the occurring coordinates. Every first-mode coordinate similarly must occur because of the \(Z_{k\ell}\). In the bipartite graph on first-mode rows \(i\) and last-mode columns \(k\), join \(i\) to \(k\) whenever some \(M_j(i,k)\ne0\). The matrices \(R_h\) preserve the column spans of its components. In fact, a matrix entry can couple two last-mode columns only if some first-mode row contributes to both. Hence the graph is connected. A connected graph with \(2n\) vertices needs at least \(2n-1\) edges, so the only possibility is exactly \(2n-1\) edges and exactly one nonzero tensor coordinate for each edge.

It follows that two different middle slices have disjoint entry supports, so \(S\) is diagonal. The matrices \(R_h\) can now couple two last-mode columns only if a row within **one** middle slice contributes to both. Make a new bipartite graph by splitting each first-mode row into its nonempty slice occurrences, keeping the last-mode vertices and the \(2n-1\) edges. If some row splits, this graph has at least \(2n+1\) vertices and is disconnected. Each component contains a last-mode vertex, and its column span is invariant under all \(R_h\), a contradiction. Thus every first-mode row lives entirely in a single middle slice. The \(Z_{k\ell}\) have zero entries between rows from different slices, so full generation forces every row into the same slice. But then every \(R_h\) is a scalar multiple of the single Gram matrix of that slice, and the unital algebra they generate is commutative. This contradicts \(n\ge2\). Hence any passing tensor has at least \(2n\) nonzero coordinates.

## Scope and closest prior work

The construction assumes the first and last dimensions agree and the middle dimension is at least as large. Over finite fields the field-size bound is needed for the given guarantee. An independently added marker is an additional constraint, so the marked theorem does not imply a worst-case algorithm for the original unmarked problem.

Chizewer, Everett, Mithal, and Qiao study independent sub-Gaussian inputs over \(\mathbb R,\mathbb C\), with a local smoothed analysis and a general smoothed-analysis question. Li, Li, Qiao, Tao, and Wang give a finite-field average-case result for uniform orthogonal three-tensors. A previous MathProofs note gives exact characteristic-zero smoothing through independent bounded discrete noise. The contribution here is a rank-optimal sparse perturbation along one explicit line, an exact all-target guarantee, and a search and decision procedure using only linear algebra over the coefficient field. The matrix-pencil diagonalization and univariate root count used in the proof are standard. The particular rank-optimal witness for both Problem 1.8 generation tests is the construction to compare for novelty. [Chizewer–Everett–Mithal–Qiao](https://arxiv.org/abs/2603.27128) · [Li–Li–Qiao–Tao–Wang](https://arxiv.org/abs/2604.00591v2) · [MathProofs characteristic-zero smoothing](https://github.com/Dugongue/MathProofs/blob/main/SmoothedOrthogonalUnitaryTI/Proof.md)
