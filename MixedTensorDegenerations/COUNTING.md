# Exact transporter counts for two tensor compilers

Write \(\#\operatorname{Trans}(A,B)\) for the number of isomorphisms from the first input to the second, counting distinct tuples of mode maps. The number is zero when the inputs are inequivalent. These results reduce exact counting to exact counting of ordinary 3-tensor transporters over the same field or ring.

## 14. Exact counting for balanced rank-marker erasure

**Theorem.** Over \(\mathbb F_q\), let \(\Phi_d\) be the balanced product-tree and rank-marker reduction from positive-mode \(d\)-tensor isomorphism to ordinary 3-tensor isomorphism, for \(d\ge3\). On every fixed input format, there is a positive integer \(F\), computable from the format and \(q\) in polynomial bit time, such that
\[
\#\operatorname{Trans}\bigl(\Phi_d(T),\Phi_d(T')\bigr)
 = F\,\#\operatorname{Trans}(T,T').
\]
This uses the same output dimensions \(O(d^7 n^{\lceil d/3\rceil})\) as the decision compiler. The factor is given below. In particular one ordinary 3-tensor counting call suffices. Applying the formula with \(T'=T\) gives the automorphism-group order. [Balanced compiler, §§1–3](https://github.com/Dugongue/MathProofs/tree/main/TensorUniversalityApplications) · [Grochow–Qiao, Part IV, §5](https://arxiv.org/html/2306.16317#S5)

### One erasure

Let \(A\in X\otimes Y\otimes Z\) be concise, meaning its supports in all three modes are full. Put \(X=\bigoplus_{i=1}^k X_i\) with \(k\ge2\) positive-rank ordered blocks and \(a_i=\dim X_i\). Other modes can have retained partitions. Write \(Y_0,Z_0\) for the designated blocks to which the new second- and third-mode spaces are appended, taking the whole old space if that mode has no partition. Put \(a=\dim X\), \(b=\dim Y\), \(b_0=\dim Y_0\), and \(c_0=\dim Z_0\). In the single-marker construction set \(w_i=(k+i+1)(a+b+1)\). The three new spaces are
\[
\widehat X=X\oplus\bigoplus_i(L_i\oplus R_i),\qquad
\widehat Y=Y\oplus\bigoplus_i(M_i\oplus S_i),\qquad
\widehat Z=Z\oplus\bigoplus_i K z_i ,
\]
where \(K=\mathbb F_q\), \(L_i\simeq Y^*\), \(M_i\simeq X_i^*\), and \(\dim R_i=\dim S_i=w_i\). The tensor is \(E(A)=A+\sum_i C_i\otimes z_i\). In the row and column blocks \((X,L_i,R_i)\) and \((Y,M_i,S_i)\), write its marker as
\[
C_i=\begin{pmatrix}0&\iota_i&0\\ I_b&0&0\\0&0&I_{w_i}\end{pmatrix},
\]
where \(\iota_i\) is the matrix of \(X_i\hookrightarrow X\) in the given bases. Unshown rows and columns are zero.

Recovery from a transporter of \(E(A)\) to \(E(B)\) restricts the first two mode maps to \(X,Y\) and takes the third map on the quotient by the span of the \(z_i\). For completeness, the rank of the slice at \((u,\alpha_i)\in\widehat Z^*\) is \(\sum_{\alpha_i\ne0}w_i\) plus a residual rank between zero and \(a+b\). The private identities account for the sum, and the remaining columns split into old \(Y\) columns and \(M_i\) columns that land in \(X\). The threshold \(a+b\) therefore identifies \(Z^*\). The singleton-marker bands \([w_i,w_i+a+b]\) distinguish every marker line modulo \(Z^*\), since the bands are disjoint and any two markers have weight exceeding \(w_k+a+b\). Old slices recover \(X,Y\) by conciseness. The row support of a singleton slice intersects \(X\) exactly in \(X_i\), since the old \(Y\) columns project isomorphically onto \(L_i\). Thus recovery also reads the erased partition. The mode restrictions and the quotient preserve composition. Conversely a source transporter lifts by acting on \(L_i,M_i\) through the duals of the corresponding inverse maps, and by the identity on \(R_i,S_i,Kz_i\). This respects every retained partition. These facts give a surjection of transporter sets with all nonempty fibers in bijection with the recovery kernel of the target automorphism group. Each \(E(A)\) is concise, so recovery applies at successive stages. Old slices recover the old row and column supports, singleton slices add every private row and column support, and a vanishing slice has no marker coefficient and then no old coefficient.

Compute the recovery kernel on \(E(A)\). Let an element be \((P,Q,J)\). The restrictions \(P|_X,Q|_Y\) and the induced map \(J_0\) on \(Z\) are identity maps. The marker bands force \(J(z_i)=s_i z_i\) with \(s_i\in K^\times\). There are functionals \(\beta_i:Z\to K\) vanishing on the other retained blocks such that \(J(z)=z+\sum_i\beta_i(z)z_i\). Contracting the equality of tensors with \(z_i^*\) gives
\[
C_i=A_{\beta_i}+s_i P C_i Q^{\mathsf T},
\]
where \(A_{\beta_i}\) is the old slice, supported on \(X,Y\). Contractions at old covectors already agree.

Project this equation in the row mode modulo \(X\). Since \(Q\) is invertible, the row support of the projected right-hand marker is the image under the induced \(P\) of \(L_i\oplus R_i\). It equals \(L_i\oplus R_i\) on the left. The column-mode projection modulo \(Y\) gives the corresponding constraint for \(Q\) on \(M_i\oplus S_i\). Project in both modes at once. The private identity has supports \(R_i,S_i\), so the induced maps also preserve these two spaces. Consequently there are no other private blocks in the following matrices for \(P,Q\), written on \(X\oplus L_i\oplus R_i\) and \(Y\oplus M_i\oplus S_i\):
\[
P_i=\begin{pmatrix}I&P_l&P_r\\0&A_L&0\\0&U&B_i\end{pmatrix},
\qquad
Q_i=\begin{pmatrix}I&Q_m&Q_s\\0&A_M&0\\0&V&C\end{pmatrix}.
\]
The retained second-mode partition requires the images of \(Q_m,Q_s\) to lie in \(Y_0\). It places no further constraints on these parameters. The first mode has no retained partition.

The \((L_i,Y)\), \((X,M_i)\), \((R_i,S_i)\), \((R_i,Y)\), \((X,S_i)\), and \((X,Y)\) sectors give, respectively,
\[
\begin{split}
A_L &= s_i^{-1} I_b,\qquad A_M=s_i^{-1}I_{a_i},\\
C &= s_i^{-1}B_i^{-\mathsf T},\qquad U=-B_iQ_s^{\mathsf T},\\
P_r &= -\iota_i V^{\mathsf T}(C^{\mathsf T})^{-1},\\
P_l &= -\iota_iQ_m^{\mathsf T}-P_rQ_s^{\mathsf T}-s_i^{-1}A_{\beta_i}.
\end{split}
\]
All other sectors vanish identically. For example, the \(X,Y\) block of \(P_i C_i Q_i^{\mathsf T}\) is \(P_l+\iota_iQ_m^{\mathsf T}+P_rQ_s^{\mathsf T}\). Thus the independently free parameters are \(s_i\in K^\times\), \(B_i\in\mathrm{GL}_{w_i}(K)\), \(V:M_i\to S_i\), \(Q_m:M_i\to Y_0\), \(Q_s:S_i\to Y_0\), and \(\beta_i\in Z_0^*\). Every such choice yields invertible matrices with the required partitions. The choices for different \(i\) combine because they agree on the old spaces and act on disjoint private blocks modulo those spaces.

It follows that the fiber factor for this erasure is
\[
F_E=\prod_{i=1}^k
 (q-1)\,|\mathrm{GL}_{w_i}(\mathbb F_q)|\,
 q^{\,w_i a_i+(a_i+w_i)b_0+c_0}.
\tag{1}
\]
The equations remain valid for the doubled-marker variant in §5 of the balanced compiler. There each block is recovered by intersecting the row supports of its two isolated marker slices, and \(Y\) is recovered by intersecting their column supports. These recovery statements hold for a nonconcise \(A\). After recovery, each marker still has exactly the displayed \(C_i\) form, with its own private spaces. Formula (1) then uses one factor per marker, assigning \(a_i\) the dimension of its marked block. No conciseness hypothesis is needed for that variant.

### Product trees and total factor

The partitioned product-tree tensor has one scalar line per mode. Scalar maps \(s_1,s_2,s_3\) on those lines satisfy \(s_1s_2s_3=1\). After normalizing the three mode maps by \(s_i^{-1}\), the scalar maps are fixed. The coevaluations between primal and dual copies in distinct modes then force identical primal actions on all copies and inverse transposes on the dual copies. Each product node forces the tensor product of its two child actions. Consequently each tuple of source maps has exactly one normalized lift. The scalar choices are independent of that lift and contribute \((q-1)^2\).

Use (1) for each of the three rotated single-marker erasures with their then-current formats and designated blocks. Thus \(F=(q-1)^2\prod_E F_E\). Source inputs with unequal formats can be returned as zero directly. All dimensions and weights are explicit, and
\[
|\mathrm{GL}_w(\mathbb F_q)|=\prod_{j=0}^{w-1}(q^w-q^j).
\]
The factors and their binary lengths are polynomial in the dense encoded input length, including \(\log q\). Exact division therefore finishes the one-call counting reduction.

## 15. Exact counting for presented tensors over a finite chain ring

**Theorem.** Let \(R\) be a nonzero finite commutative chain ring. Given two 3-tensors on finitely presented \(R\)-modules, with free presentations and a tensor representative in the tensor product of the three free covers, the exact number of transporting triples of \(R\)-linear isomorphisms reduces to one ordinary free 3-tensor counting call over \(R\). The presentations explicitly list generators and relation columns, and the tensor representatives are dense coefficient arrays. The output side lengths have the same bound as in the presented-module decision compiler. The reduction is polynomial in the explicit input size for every fixed \(R\). It is also uniform for \(R=\mathbb Z/p^e\mathbb Z\) with the prime \(p\) and modulus specified. More generally the same bound is uniform in chain-ring presentations providing polynomial-bit ring arithmetic, the residue cardinality, the length, valuations, and exact division by a nonzero pivot on entries divisible by it, including nonunit pivots. [Presented-module compiler](https://github.com/Dugongue/MathProofs/tree/main/TensorUniversalityApplications) · [Grochow–Qiao–Stange–Sun, Part V, §1.3](https://arxiv.org/html/2611.00735v1#S1.SS3)

### A general cover factor

Write \(\mathfrak m\) for the maximal ideal of \(R\). Let \(\pi:R^r\twoheadrightarrow M\) be any free cover and put \(m=\dim_{R/\mathfrak m}M/\mathfrak m M\), \(t=r-m\). Choose a basis of the cover whose first \(m\) images generate \(M/\mathfrak m M\). These images also generate \(M\), because the maximal ideal is nilpotent. Subtract lifts of the other images from the remaining basis vectors. This expresses the cover as the direct sum of a minimal cover \(F_0=R^m\to M\) and a free summand \(R^t\) mapping to zero. The kernel \(K_0\) of the minimal cover lies in \(\mathfrak mF_0\), since the minimal map induces an isomorphism on reduction modulo \(\mathfrak m\). Its cardinality is \(|R|^m/|M|\).

An automorphism of \(R^r\) inducing identity on \(M\) has blocks
\[
\begin{pmatrix}I+L&B\\ C&D\end{pmatrix},
\]
where all images of \(L,B\) lie in \(K_0\), the block \(C:F_0\to R^t\) is arbitrary, and \(D\in\mathrm{GL}_t(R)\). Indeed these are the conditions on the first row of blocks from composing with \(\pi\). Reducing modulo \(\mathfrak m\) makes the upper blocks \(I,0\), so invertibility is equivalent to that of \(D\) modulo \(\mathfrak m\), hence to that of \(D\) over \(R\). The kernel factor is therefore
\[
L_R(r,M)=
 \left(\frac{|R|^m}{|M|}\right)^{r}
 |R|^{tm}|\mathrm{GL}_t(R)|.
\tag{2}
\]
If two covers of the same rank cover isomorphic modules, every module isomorphism lifts to an invertible cover map. To see this, choose a lift on the two minimal covers by lifting basis images. Its reduction modulo \(\mathfrak m\) is the induced isomorphism of the modules modulo \(\mathfrak m\), and thus is invertible. Extend by any isomorphism of the redundant free summands. Composing any one lift with automorphisms in the target cover kernel shows that (2), using the target module, counts every lift fiber. The formula also applies to the zero module and to a free module with no redundant generators.

### The marked tensor and its shears

For the input pair, use the decision compiler's stabilized covers \(F_i,F'_i\) of free rank \(f_i=r_i+r'_i\), with kernels \(K_i,K'_i\) and quotient modules \(M_i,M'_i\). Explicitly use the original cover as the first summand and the other input's free cover as a summand mapping to zero. These choices make the formats on both sides agree. Use input representatives \(\widetilde t,\widetilde t'\) in the stabilized free tensor products. Put \(U_i=F_j\otimes F_k\), \(E_i=U_i^*\) for the other two indices \(j<k\), and use the primed analogues. Put \(e_i=f_jf_k\). The decision compiler forms
\[
\mathcal T=\widetilde t+\tau_1+\tau_2+\tau_3
 \quad\text{on the modes }G_i=F_i\oplus E_i,
\]
where \(\tau_i\) is the coevaluation in \(E_i\otimes U_i\), placed in its respective sector. It marks \(F_i\) and \(D_i^0=K_i\oplus E_i\). A map on the marked mode has blocks
\[
P_i=\begin{pmatrix}A_i&S_i\\0&D_i\end{pmatrix},
\qquad A_iK_i=K'_i,\qquad S_i(E_i)\subseteq K'_i .
\]
The coevaluation equation with \(E'_i\) as the only \(E'\) factor forces \(D_i=((A_j\otimes A_k)^{-1})^*\). The only remaining equation is the all-\(F'\) component.

Fix a quotient transporter \((u_i)\) of the original tensors. For each \(i\), there are \(L_R(f_i,M'_i)\) choices of \(A_i\) lifting \(u_i\). For fixed \(A_i\), write \(B_i=A_j\otimes A_k\). The possible shears \(S_i:E_i\to K'_i\) form an additive group of cardinality \(|K'_i|^{e_i}\). The one remaining equation asks their sum, under the linear map
\[
(S_i)_i\longmapsto\sum_i (S_i\otimes B_i)\tau_i ,
\]
to equal \(\widetilde t'-(\bigotimes_i A_i)\widetilde t\). The image is
\[
W'=\sum_i\operatorname{im}
 \bigl(K'_i\otimes U'_i\longrightarrow F'_1\otimes F'_2\otimes F'_3\bigr),
\]
since the vectors \(B_i e\) for the chosen basis \(e\) of \(U_i\) form a basis of \(U'_i\). The map on the \(i\)-th summand assigns arbitrary coefficients from \(K'_i\) to those basis vectors. The submodule \(W'\) is the kernel of the natural map to \(\bigotimes_i M'_i\). This follows by the universal property of the tensor product, by factoring a trilinear map through the three quotient maps precisely when it kills the three indicated images. For the chosen quotient transporter the residual belongs to \(W'\). The fiber is a coset of the additive kernel and has cardinality
\[
F_{\rm shear}=\frac{\prod_i |K'_i|^{e_i}}{|W'|},
\qquad
 |W'|=\frac{|R|^{f_1f_2f_3}}{|\bigotimes_i M'_i|}.
\tag{3}
\]
Conversely any marked tensor transporter induces a quotient transporter by this same equation.

The decision compiler expresses each mark by a specified linear map into \(G_i\). For the inclusion with image \(F_i\), the domain map is uniquely forced by \(P_i|_{F_i}\). For the second mark it uses a free generator domain \(R^{d_i}\twoheadrightarrow D_i^0\). The common rank \(d_i\) is obtained by padding with zero columns from the opposite generator list. This domain has \(L_R(d_i,(D'_i)^0)\) lifts of the restriction of each \(P_i\) to the marked image. This factor can be multiplied independently for each mark. It accounts for redundant generator columns even when some columns are zero.

### The final free tensor factor

Here is the fiber count for the triangular-algebra compiler used in the decision theorem. Its input is the fixed type of named tensors on free sorts, including the specified linear maps for the marks just described.

The compiler first makes one bilinear map \(B:X\times Y\to Z\) with ordered summand marks in \(X,Y\). Its scalar-product block and copy maps force the actions on each triple of copies to have the form \(a g_i,b g_i,ab g_i\), with arbitrary \(a,b\in R^\times\). The additional copy maps from private occurrences to reference indices force equality of their normalized \(g_i\). Evaluation forces the dual actions. The scalar sort used to pad named data is fixed by its multiplication after normalization. Therefore each typed map has exactly \(|R^\times|^2\) lifts to the marked bilinear map. These equations work over a ring because evaluations on basis pairs determine every coefficient and the scalars being cancelled are units.

The compiler realizes this marked bilinear map as the \(0\to1\to2\) multiplication in a free associative algebra \(A\). Its other corners consist of scalar arrows for the summand marks, the corresponding projection quotients, and private rank-label corners for its vertices. Denote by \(v\) the total number of vertices, by \(j\) the free rank of the off-diagonal ideal \(J\), by \(b\) the number of scalar arrows for the summand marks, and by \(h_1,\ldots,h_s\) the ranks of the private rank-label corners. These numbers are computed directly from the compiler's output format.

The off-diagonal ideal is the commutator ideal, since the diagonal quotient is commutative and every off-diagonal corner is obtained by commutating with its source idempotent. It has \(J^3=0\) and diagonal quotient \(R^v\). Since \(R\) is local, an algebra isomorphism permutes the quotient idempotents. Its action on \(J/J^2\), reduced modulo \(\mathfrak m\), forces the permutation to be the identity. Each rank-label corner survives in full, with distinct dimension larger than all ordinary corners, and its two endpoints are thereby fixed. Every vertex is an endpoint of one of these corners.

For a target system \((f_i)\) of lifted vertex idempotents congruent to the standard system \((e_i)\) modulo \(J\), the unit \(u=\sum_i f_i e_i\in 1+J\) satisfies \(f_i u=u e_i\). It is the unique such conjugating unit in \(1+J\), since any element of \(1+J\) centralizing all vertices has vanishing off-diagonal part. Thus undoing the vertex normalization contributes \(|R|^j\) choices. With vertices fixed, the marked \(X,Y\) submodules are recovered as annihilators of the scalar arrows in \(B\)'s extension. Each scalar arrow has an independent unit scale, and the multiplication with this arrow forces the action on the projection quotient. Each private rank-label corner has an independent invertible map and every action on the main corners already belongs to the marked bilinear map. These are all the corners and products. The resulting factors are \(|R^\times|^b\) and \(\prod_{\alpha=1}^s|\mathrm{GL}_{h_\alpha}(R)|\).

Taking the ordinary multiplication tensor adds two independent target unit choices. In detail, an isotopy \(H(xy)=P(x)Q(y)\) gives \(a=P(1)\), \(b'=Q(1)\), and \(H=R_{b'}P=L_aQ\). Both multiplication operators are invertible, so both elements are units. For example, if \(ac=1\), injectivity of \(L_a\) gives \(ca=1\). The map \(x\mapsto a^{-1}H(x)(b')^{-1}\) is a unital algebra isomorphism. Conversely that isomorphism and the two units reconstruct the isotopy. In the target algebra the units are exactly the elements whose image in \(R^v\) is a unit, because the kernel \(J\) is nilpotent. Thus \(|(A')^\times|=|R^\times|^v |R|^j\).

The final fiber factor from the typed system to output free tensor is therefore
\[
F_{\rm free}=|R^\times|^{\,2v+b+2}|R|^{3j}
              \prod_{\alpha=1}^s|\mathrm{GL}_{h_\alpha}(R)|.
\tag{4}
\]
This is a count for this particular compiler, using its ranks and its vertex marks. The argument uses the same idempotent and isotopy normalizations as the earlier scheme-exact associative compiler. [Scheme-exact compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorIsomorphismAndAlgebraicCrossovers/Rings.md)

### Total factor and complexity

For the specified pair of inputs, every quotient transporter has exactly
\[
 F_{\rm free}\, F_{\rm shear}
 \prod_{i=1}^3 L_R(f_i,M'_i)\,L_R(d_i,(D'_i)^0)
\tag{5}
\]
lifts to the ordinary free tensor query. The converse map follows every recovery just proved, so when the input count is zero the output count is also zero. The same formula can be applied to a pair of equal inputs to count automorphisms. Presentations with zero ranks use the unique linear map on a rank-zero free sort, and the formulas use \(|\mathrm{GL}_0(R)|=1\).

Write \(q=|R/\mathfrak m|\) and \(\ell\) for the chain length, so \(|R|=q^\ell\) and \(|\mathfrak m|=q^{\ell-1}\). Reduction modulo \(\mathfrak m\) gives
\[
 |R^\times|=q^{\ell-1}(q-1),\qquad
 |\mathrm{GL}_u(R)|=q^{(\ell-1)u^2}
                  \prod_{h=0}^{u-1}(q^u-q^h).
\]
Smith elimination over the chain ring computes the cyclic lengths of the quotient modules and kernel submodules. It uses a pivot of least valuation and row and column operations to clear its row and column by exact division by that pivot, which is permitted by the representation assumptions. Each cyclic module \(R/(\pi^a)\) has order \(q^a\) and contributes one minimal generator for \(a>0\). Tensor products of cyclic modules have length equal to the minimum of their lengths. These facts compute the module parameters in (2) and (3). For the marked image \((D'_i)^0\), use the direct sum of \(K'_i\) and a free module of rank \(e_i\). All free ranks, image matrices, and binary integer lengths are polynomial in the explicit input size. Construct the same free tensor query as the decision compiler and divide its exact count by (5).

## Verification scope

The proofs are written mathematics. The finite replay independently enumerates the local marker equations and the cover and shear fibers on small finite inputs. The algebra-label count follows from the unique idempotent normalization and the two-unit description of multiplication transporters. The two reductions use an exact counting oracle.
