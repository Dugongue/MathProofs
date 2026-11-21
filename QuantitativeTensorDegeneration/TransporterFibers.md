# Determinant-resolved transporter schemes for the degeneration compilers

For a multiplication tensor of an algebra \(A\), use the bilinear-map convention for its transporter \((P,Q,H)\):
\[
 H(xy)=P(x)Q(y).
\]
Thus the determinants in the covariant tensor convention are \((\det P^{-1},\det Q^{-1},\det H)\). In particular the identity determinant vector has the same meaning in both conventions.

The assertions below concern the existing affine-linear Peirce compiler of mixed records and the existing \(29\)-dimensional ordered-pencil algebra. Their tables are unchanged. The previously recorded field-level count for the Peirce construction had unprescribed determinants. Here the transporter description holds functorially over arbitrary commutative coefficient rings, and fixes any prescribed determinant triple.

## 1. Linear-width Peirce compiler

Use the construction and notation of *Linear-width compilation of mixed tensor degeneration*. After the balanced products and three-copy construction, a blocked bilinear map \(\mu:X\times Y\to Z\) is made into a unital split Peirce algebra \(A_\mu\). Its main corners are \(X:0\to1\), \(Y:1\to2\), \(Z:0\to2\), with product \(\mu\). A scalar arrow and the relevant quotient encode each partition projection. A private source arrow of width \(M_u\) enters each old vertex \(u\). Its width is unique among all corner dimensions, and all positive-length continuations vanish. Write \(v\) for the total number of vertices, \(j\) for the total dimension of the strict off-diagonal corners, and \(b\) for the number of scalar partition arrows. These integers and the \(M_u\)'s depend only on the format. Pick one private marker \(u_*\).

Let \(\mathcal T(x,y)\) be the original transporter functor for the mixed records of this common format. It uses the shared primal and dual actions, over the same coefficient ring. Write \(\Phi(x),\Phi(y)\) for their ordinary multiplication tensors. As schemes over the ring of record coefficients, the unrestricted transporter is isomorphic to
\[
 \mathcal T(x,y)\times
 \mathbb A^{3j}\times\mathbb G_m^{\,2v+b+2}
       \times\prod_u\mathrm{GL}_{M_u}. \tag{1}
\]
With any three prescribed invertible determinants its transporter is isomorphic to
\[
 \mathcal T(x,y)\times
 \mathbb A^{3j}\times\mathbb G_m^{\,2v+b}
       \times\mathrm{SL}_{M_{u_*}}\times
              \prod_{u\ne u_*}\mathrm{GL}_{M_u}. \tag{2}
\]
The descriptions are natural in base change of the records and the prescribed units. They are product decompositions of schemes, without requiring the group law on the unrestricted or determinant-one stabilizer to be a direct product. For either stabilizer its recovery homomorphism onto the original stabilizer splits as a group-scheme map.

### Proof of the unrestricted product

Balanced products and evaluation pairings give unique lifts of the original named-space maps. The product-space maps are forced by the product isomorphisms, and a dual-space map is forced by a perfect evaluation pairing. A scalar space carrying its multiplication has only its identity as an invertible multiplication-preserving map. If relation frames are present, include their free basis-frame sorts among the records. On split injective frames the induced frame map, when it exists, is unique.

In the three-copy block construction, the maps on the two distinguished input scalar lines are arbitrary units \(s,t\). The scalar actions on the fixed input pairs force the maps on each named or occurrence copy \(X_i,Y_i,Z_i\) to be \(s g_i,t g_i,st g_i\), respectively. Copy records force the occurrence map to equal its reference map. The private scalar lines carry the forced multiplier \(t\), and evaluation records force inverse transposes on the dual copies. The payload equation then has its original form after canceling the scalar factors. Thus the block-preserving bilinear transporters consist of the original mixed transporters and two independent units. These arguments use invertible maps and multiplication by units, so they hold over an arbitrary commutative base ring.

In \(A_\mu\) the span of commutators is precisely the full strict ideal \(J\). Every strict basis element is its commutator with its source idempotent, and the quotient \(A_\mu/J\) is commutative. Consequently \(J\) is intrinsic under all base changes. The ranks of the free Peirce corners pin the vertex labels over each residue field, using the unique widths \(M_u\). The same labels are fixed in the quotient \(R^v\) over a general commutative ring \(R\): an image coordinate of a vertex idempotent is itself idempotent, and its values in every residue field force it to be identically zero or identically one. An idempotent in every maximal ideal is zero, and the same argument applies to its complement.

For a transporter whose ordered vertex images are \(f_i\), use the unique element \(z=\sum_i e_i f_i\) in \(1+J\) to align them, since \(z f_i=e_i z\). Uniqueness follows because a difference of two such conjugators centralizes the fixed vertex idempotents and lies in \(1+J\), whose diagonal corners are zero apart from the identity. This gives \(j\) independent affine coordinates. Once the vertices are fixed, the maps on \(X,Y\) preserve the prescribed partition blocks since these are kernels of multiplication by the respective scalar arrows. Each scalar arrow has an independently chosen unit. The projection-output map is then forced by multiplying the induced quotient map by that scalar. The rank markers contribute independent maps in \(\mathrm{GL}_{M_u}\), because their continuations vanish. The only remaining product equation is the given block-preserving comparison for \(\mu\). This gives the factor \(\mathbb A^j\times\mathbb G_m^b\times\prod_u\mathrm{GL}_{M_u}\) at the algebra step.

Finally an ordinary transporter of unital associative multiplication tensors is uniquely an algebra isomorphism \(f\) together with independent target units \(a,b_0\), with
\[
 P=L_a f,\qquad Q=R_{b_0} f,\qquad H=L_a R_{b_0} f .
\]
Here \(L_a\) and \(R_{b_0}\) denote left and right multiplication. Indeed \(a=P(1)\), \(b_0=Q(1)\), and the two identities with an input equal to \(1\) make their multiplication operators invertible. In an associative unital algebra, invertibility of left or right multiplication implies the element is a unit: a one-sided inverse exists by surjectivity and the other inverse equation follows by injectivity. Then \(f(x)=a^{-1}H(x)b_0^{-1}\) preserves multiplication. Its converse follows directly by substitution. Each unit has arbitrary invertible diagonal residues and arbitrary coefficients in \(J\), because \(J\) is nilpotent. Its coordinates therefore give \(\mathbb G_m^v\times\mathbb A^j\). This proves (1).

All displayed choices and recoveries are regular in the scheme sense. Inverting a chosen scalar, unit or matrix uses only inverses on its specified unit or general-linear locus, and all marks, quotient coordinates, conjugation and normalization are defined using fixed free bases. Conversely multiplying the specified blocks gives an actual transporter for every choice. This proves the scheme isomorphism by its inverse natural transformations, including on rings with nilpotents. Recovery preserves composition. For example aligned vertex conjugations compose by multiplying their conjugators in the strict unit group and using uniqueness, and algebra recovery from isotopy composes by the two-unit description. The canonical mixed transporter lift fixes rank markers, all free scalar arrows and both isotope units. Quotient maps are its induced ones. This lift preserves composition and gives the splitting.

### Resolving all three determinants

Write \(d_f=\det f\), \(\ell=\det L_a\) and \(r=\det R_{b_0}\). The displayed formula yields \((d_f\ell,d_fr,d_f\ell r)\). For a requested triple \((d_1,d_2,d_3)\), these prescribe uniquely
\[
 d_f=d_1d_2/d_3,\qquad \ell=d_3/d_2,\qquad r=d_3/d_1 . \tag{3}
\]

A topological ordering of the Peirce vertices makes left multiplication by a strict element strictly triangular on the blocks grouped by their first endpoint, and right multiplication strictly triangular on the blocks grouped by their last endpoint. Thus a unit with diagonal residues \(\lambda_i\) has
\[
 \det L_a=\prod_i\lambda_i^{\dim e_i A_\mu},\qquad
 \det R_a=\prod_i\lambda_i^{\dim A_\mu e_i}.
\]
This holds with the indicated free ranks over all rings and needs no flatness of the radical powers. At a sink the first exponent is one, and at a source the second is one. Use \(2\) as one sink and a private marker vertex as one source. In the two independent units, these coordinates uniquely impose \(\ell,r\) in (3) and leave all their other coordinates free.

The conjugator in \(1+J\) has determinant one by the same triangularity applied to its left and right multiplications. In the aligned isomorphism every marker arrow map is an independent diagonal block. Thus \(d_f\) is an invertible factor from the remaining coordinates times \(\det\) of the chosen marker matrix. Parameterize that matrix as \(\mathrm{diag}(\delta,1,\ldots,1)B\) with \(B\in\mathrm{SL}_{M_{u_*}}\). Then a unique \(\delta\) imposes \(d_f\) in (3). These eliminated coordinates are regular functions of all the others and the prescribed units. This proves (2). For determinant-one stabilizers one can split by correcting the canonical mixed lift by its inverse determinant on this marker, with both isotope units still one. The marker correction commutes with every canonical lift, which is identity on its marker block. The resulting section is a homomorphism.

## 2. Arithmetic lifts and special-linear degeneration

Set
\[
 D_{\mathrm{free}}=3j+2v+b+2+\sum_u M_u^2,\qquad
 D_{\mathrm{fixed}}=D_{\mathrm{free}}-3 .
\]
The supplementary factors in (1) and (2) are smooth of the indicated dimensions over \(\mathbb Z\). For any surjection \(R\twoheadrightarrow S\) of finite local rings with nilpotent kernel \(I\), take a given output transporter over \(S\) and recover its mixed transporter. A lift over \(R\) exists exactly when the recovered mixed transporter lifts. Each such mixed lift has precisely \(|I|^{D_{\mathrm{free}}}\) output lifts reducing to the given transporter, or \(|I|^{D_{\mathrm{fixed}}}\) if one has fixed a determinant triple over \(R\) extending its residue. Indeed all the auxiliary coordinates lift. A general-linear matrix has \(|I|^{m^2}\) lifts, and imposing its determinant divides the number by \(|I|\), by multiplying a diagonal entry by any element of \(1+I\). The same formulas hold with arbitrary record deformations specified at level \(R\). No smoothness assumption is made on the original transporter.

For example, over a finite chain ring \(R\) of length \(a\) and residue cardinality \(q\), the count for each prescribed triple equals the mixed transporter count times
\[
 q^{3aj}\,\bigl(q^{a-1}(q-1)\bigr)^{2v+b}
       |\mathrm{SL}_{M_{u_*}}(R)|\prod_{u\ne u_*}|\mathrm{GL}_{M_u}(R)|.
\]
Here \(|\mathrm{GL}_m(R)|=q^{(a-1)m^2}\prod_{i=0}^{m-1}(q^m-q^i)\) and \(|\mathrm{SL}_m(R)|=|\mathrm{GL}_m(R)|/|R^\times|\). Thus every determinant triple has identical count, exactly the unrestricted count divided by \(|R^\times|^3\). The formulas handle empty transporter sets. The original field count without determinant restrictions is the specialization of (1).

Over any coefficient field, the encoded ordinary tensor has the same orbit under the full general-linear product and the determinant-one product, because its stabilizer realizes every determinant triple. Hence the prior directional and smooth-germ comparison of reduced orbit closures for this same compiler holds with \(\mathrm{SL}\times\mathrm{SL}\times\mathrm{SL}\) acting on its outputs. This preserves the original width \(O_\sigma(n^{\lceil d/3\rceil})\), including the affine-linearity and the linear width for low-order mixed records. It does not require the input orbit to be closed.

The product assertion is stronger than a count on fields. Over characteristic \(p\), for the one-dimensional record \(1\) in its \(p\)-fold primal tensor power the input stabilizer is the nonreduced \(\mu_p\). Over \(\mathbb F_q[t]/(t^a)\) it has \(q^{a-\lceil a/p\rceil}\) points, since each element is \(1+z\) with \(z^p=0\). Formula (2) keeps exactly that factor in every determinant-one stabilizer count. Also the record \(1+t^h\), for \(p\nmid h\), is transportable from \(1\) through precision \(h\) and fails at precision \(h+1\). The same first failure occurs in every determinant channel of the compiled comparison, using compatible prescribed determinants. This follows from \((1+z)^p=1+z^p\) and the natural product lifting assertions.

## 3. The same calculation for the existing \(29\)-dimensional pencil

Use \(A(X)\) from *Exponentially many branches in sparse ordinary tensor orbit closures*. Its vertices are \(0,1,a,b,2,w\), and the rank-three corners \(U:0\to1\), \(V:0\to2\) carry the ordered pair of maps \(X_i:U\to V\), \(i=a,b\). The seven scalar arrows are \(r:w\to1\), \(t:w\to2\), \(p_i:1\to i\), \(q_i:i\to2\), and \(\eta:a\to b\). The retained paths and products are as in that construction, with
\[
 u p_i q_i=X_i(u),\qquad r p_iq_i=t ,
\]
and all nontrivial continuations of \(\eta\) zero. Its strict ideal \(J\) has rank \(23\).

The full corner ranks pin the vertices over all residue fields, since the old row outdegrees are \(4,4,3,2,1,0\) at \(0,w,1,a,b,2\) and the two tied rows have different corner widths. Thus the quotient and vertex normalization work over arbitrary base rings as in Section 1. The aligned map has \(P\) on \(U\), \(H\) on \(V\), and units \(\rho_r,\rho_t,\alpha_i,\beta_i,\xi\) on \(r,t,p_i,q_i,\eta\). Put \(\gamma=\rho_t/\rho_r\). The scalar equations force \(\beta_i=\gamma/\alpha_i\), and the other equations say \(H X_i=\gamma Y_iP\). Consequently \((P,H_0)\) with \(H_0=\gamma^{-1}H\) is the recovered ordered-pencil transporter. All maps on length-two paths are forced by their indicated products. Conversely the five free units \((\rho_r,\rho_t,\alpha_a,\alpha_b,\xi)\) and any such original transporter give the unique aligned map. The isotope units then give the same ordinary multiplication-tensor parametrization as before.

In particular, for each pencil transporter the ordinary tensor fiber is
\[
 \mathbb A^{69}\times\mathbb G_m^{17},
\]
and with any prescribed determinant triple it is
\[
 \mathbb A^{69}\times\mathbb G_m^{14}.
\]
The scalar \(\xi\) controls the algebra determinant since \(\eta\) spans its own corner and has no positive products. More explicitly, in the standard Peirce bases the determinant of the aligned algebra map is
\[
 \xi\,\rho_t^8\rho_r^{-4}(\alpha_a\alpha_b)^4
                  (\det P)^3\,\det H_0 .
\]
To see this, the \(U,V\) blocks contribute \(\det P\) and \(\gamma^3\det H_0\); the \(u p_i\) blocks contribute \((\det P)^2(\alpha_a\alpha_b)^3\); the \(r p_i\) blocks contribute \(\rho_r^2\alpha_a\alpha_b\); the two \(p_iq_i\) paths give \(\gamma^2\); and the seven scalar arrows contribute \(\xi\rho_r\rho_t\gamma^2\). The infinitely many base changes and all finite nilpotent lifts follow from these formulas exactly as in Section 2. For determinant resolution choose \(2\) as the left-multiplication sink and \(0\) as the right-multiplication source. Thus again the existing sparse \(29\)-dimensional output has equal ordinary and determinant-one orbits, and the same directional singularity theorem applies under the determinant-one product.

### Explicit source and special stabilizers

For the actual Zwara pencil seeds
\[
 X_a=Y_a=E_{21}+E_{32},\quad X_b=E_{11}+E_{33},\quad Y_b=E_{32},
\]
solve the linear equations \(H_0X_i=X_iP\) and \(H_0Y_i=Y_iP\). In the source case all solutions are
\[
 P=\begin{pmatrix}a&0&0\\ b&d&0\\ c&0&d\end{pmatrix},\qquad
 H_0=\begin{pmatrix}a&0&0\\ 0&a&0\\ c&b&d\end{pmatrix}.
\]
Both are invertible precisely when \(a,d\) are units. In the special case all solutions are
\[
 P=\begin{pmatrix}a&0&0\\ 0&d&0\\ b&c&e\end{pmatrix},\qquad
 H_0=\begin{pmatrix}x&0&0\\ y&a&0\\ z&0&d\end{pmatrix}.
\]
Both are invertible precisely when \(a,d,e,x\) are units. These equations and invertibility tests hold over any commutative ring. Hence for any finite commutative local ring \(R\), with \(N=|R|\) and \(U_R=|R^\times|\), the ordinary stabilizer orders of the single encoded source and special tensor are
\[
 N^{71}U_R^{19},\qquad N^{73}U_R^{21}.
\]
For the tensor of the product of \(s\) identical algebras, both counts are \(s!\) times the respective \(s\)-th powers. Each single algebra has center \(R\): commuting with all vertex idempotents forces the diagonal corners, and commuting with the arrows identifies their diagonal coefficients because the graph is connected. Thus over a local base the product algebra isomorphisms permute its central factors and are otherwise independent. The isotope units also factor, and a determinant preset on the whole output can be imposed by the same three coordinates in one selected target factor, regardless of the permutation. Each prescribed determinant count for the amplified example is therefore its corresponding unrestricted count divided by \(U_R^3\), once for the whole direct product.

Over an algebraically closed field the two ordinary stabilizers have dimensions \(90s\) and \(94s\), and the two determinant-one stabilizers dimensions \(90s-3\) and \(94s-3\). Thus the orbit dimension drops by exactly \(4s\) in this existing strict degeneration, for either acting group. The known strictness comes from the rank difference of the second ordered-pencil matrices. The scheme and counting results are for exact transport within each orbit and do not assert an isomorphism of the strict source and special tensors.

## Provenance and verification

These are written proofs on the unchanged tables of *Linear-width compilation of mixed tensor degeneration* and *Exponentially many branches in sparse ordinary tensor orbit closures*. [Linear-width construction](https://github.com/Dugongue/MathProofs/blob/main/TensorDegenerationFallout/LINEAR-WIDTH.md) · [29-dimensional construction](https://github.com/Dugongue/MathProofs/blob/main/TensorDegenerationFallout/SINGULARITIES.md) The older finite-field transporter count is the unrestricted field case of (1). The new parts are the ring-valued and determinant-resolved product decompositions, their finite-lifting formulas, the determinant-one degeneration consequence and exact arithmetic for the \(29\)-dimensional seed. The isotopy normalization for unital multiplication tensors and the two-pencil degeneration come from the prior constructions. [Bläser–Lysikov, degeneration of multiplication tensors](https://arxiv.org/abs/1606.04253) · [Zwara, Theorem 1](https://www.impan.pl/shop/en/publication/transaction/download/product/87496)
