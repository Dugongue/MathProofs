# The determinant coset of a direct sum of tensors

Fix a finite field \(F=\mathbb F_q\). A determinant vector always refers to the three ordered mode maps in the given bases, without interchanging the modes. The determinant of the map of a zero-dimensional space is \(1\). For two tensors of the same format, let \(\Delta(T,S)\subseteq(F^\times)^3\) be the set of determinant vectors of their transporters.

**Theorem.** In deterministic polynomial time, the computation of \(\Delta(T,S)\) for arbitrary three-tensors reduces to determinant-vector queries on concise tensors with a local centroid. The reduction is a polynomial-time Turing reduction at fixed \(q\). More specifically, it computes the intrinsic centroid decompositions and uses determinant cosets for pairs of individual summands and for their stabilizers. There is no restriction on the number of repeated isomorphic summands. The summands can have nonreduced centroids.

There is a deterministic algorithm with runtime \(q^{k^2} L^{O(1)}\) for fixed \(q\), where \(L\) is the input length, if every centroid summand of the concise part of either tensor has some mode of dimension at most \(k\). The narrow mode may be different in different summands. This algorithm computes the entire determinant coset, the number of transporters in every determinant fiber, and one ordinary transporter when there is one. In particular \(k=O(\sqrt{\log L})\) gives polynomial time, with arbitrary global mode dimensions. The case of SL-TI follows by testing \((1,1,1)\).

## Intrinsic blocks from the centroid

First compute the three support spaces by flattening. A tensor lies in their tensor product and is concise there. If support dimensions disagree the comparison fails. Work on the concise parts for now, with support bases chosen by elimination. If the concise part is zero, the tensor is zero. Two zero tensors of the same format have all determinant vectors allowed by their mode dimensions, with counts given by independent general linear groups.

For a nonzero concise tensor \(T\in V_1\otimes V_2\otimes V_3\), write \(a_i T\) for an endomorphism acting only in mode \(i\). The centroid is the linear solution space
\[
 C(T)=\{(a_1,a_2,a_3):a_1T=a_2T=a_3T\}.
\]
For two centroid tuples \(a,b\), one may transfer either operator to a spare mode and commute it with the operator in the first mode. For example
\[
 a_1 b_1T=a_1 b_2T=b_2a_1T=b_2a_3T=a_3b_2T
     =a_3b_1T=b_1a_3T=b_1a_1T.
\]
Conciseness makes the action of each individual endomorphism on \(T\) faithful in the sense that \(u_iT=0\) implies \(u_i=0\). Thus the tuples commute componentwise. Their product belongs to the centroid, since \(a_i b_iT=a_i b_jT=b_ja_iT=b_ja_jT=a_jb_jT\). This is a finite commutative unital algebra given by linear equations and matrix multiplication.

The subalgebra fixed by \(x\mapsto x^q\) is a product of copies of \(F\). Indeed a finite commutative algebra is a product of local algebras. Each local factor has residue field a finite extension of \(F\). A fixed element reduces to an element of \(F\), while a fixed nilpotent must vanish under iteration of Frobenius. Thus the fixed subalgebra maps injectively to the corresponding product of copies of \(F\), and contains the idempotents of the local factors, so maps onto it. Compute this subalgebra as an \(F\)-linear kernel. On it, simultaneous eigenspaces of multiplication by a basis are the one-dimensional primitive ideal spaces. Split by the \(q\) eigenvalue candidates for each multiplication, and project the identity to those spaces to obtain the primitive idempotents of \(C(T)\).

For each primitive idempotent \(e\), its three projections split the \(V_i\) into blocks. The tensor lies in the sum of the matching triple blocks. To check this, apply two distinct idempotents in two distinct modes. Transfer one action to the mode of the other and use their zero product. The block tensors remain concise, and their centroids are local, since a further centroid idempotent for a block could be extended by zero to split \(e\). A tensor transporter conjugates all three centroid actions and therefore permutes primitive idempotents. This gives a bijection on blocks and actual tensor transporters between matched blocks, and conversely every such matching and list of block transporters assembles. [First–Maglione–Wilson, transverse tensor operators](https://arxiv.org/abs/1911.02518) · [Centroids of concise tensors, §4.1](https://arxiv.org/abs/2608.27434)

## Multiply determinant cosets and add the block permutation factors

Classify the source and target summands by ordinary tensor isomorphism. A nonempty local determinant coset detects this relation. A global transporter exists exactly when every isomorphism type occurs with the same multiplicity on the two sides. Fix a matching within each type and some transporter on each matched pair. Using their known local determinants and the source and target block basis-change determinants, compute the determinant vector \(d_0\) of this global reference transporter. The actual matrices of the reference transporter are unnecessary for the Turing reduction.

For each source summand \(T_i\), let \(H_i=\Delta(T_i,T_i)\). For a type \(c\) with multiplicity at least two and mode dimensions \((n_{c1},n_{c2},n_{c3})\), put
\[
 e_c=\big((-1)^{n_{c1}},\,(-1)^{n_{c2}},\,(-1)^{n_{c3}}\big).
\]
Then
\[
 \Delta(T,S)=d_0\left\langle H_i\text{ for all }i,\ e_c\text{ for types with multiplicity at least two}\right\rangle.
\]
To prove the formula, each \(H_i\) extends by identity to the other summands. A swap of two same-type summands uses a fixed local isomorphism one way and its inverse the other way. In each mode these two determinants cancel, and the block swap has determinant \((-1)^{n_{cj}^2}=(-1)^{n_{cj}}\). This is valid even for nonadjacent blocks, by decomposing the mode into the two swapped summands and their fixed complement. Conversely every stabilizer induces a permutation within each type. Remove that permutation using the constructed swaps. The remainder fixes each block and has determinant in the product of the \(H_i\). This proves exactness. In particular omitting permutation signs can change the answer. For two copies of a \(1\)-by-\(1\)-by-\(1\) nonzero tensor, blockwise stabilizers have product-one determinant vectors, while the block swap has vector \((-1,-1,-1)\) in odd characteristic.

If every local stabilizer order \(s_i\) is known, the full stabilizer order on the concise part is \(\prod_i s_i\prod_c m_c!\), where \(m_c\) is the multiplicity of type \(c\). Every permutation within one type has a lift and all such lifts differ by an independent block stabilizer. Over the original ambient spaces let the support and complement dimensions in mode \(j\) be \(r_j\) and \(a_j\). Every supported map extends by an arbitrary invertible complement map and an arbitrary \(r_j\)-by-\(a_j\) off-diagonal block. Thus multiply the group order by \(q^{r_j a_j}|\mathrm{GL}_{a_j}(F)|\) and, when \(a_j>0\), include the full determinant subgroup in that mode. Use the original basis-change determinant ratios in \(d_0\). A nonempty transporter set is a stabilizer coset, so each attainable determinant vector has the same number of transporters, the stabilizer order divided by the order of its determinant subgroup.

The subgroup computations take place in a group of order \((q-1)^3\). A query for a prescribed determinant vector on an individual block reduces to one SL-TI query on that block, by applying to its target mode \(j\) the diagonal change \(\operatorname{diag}(\lambda_j^{-1},1,\ldots,1)\). This invertible twist preserves centroid locality and conciseness. All blocks of a nonzero concise tensor have positive dimensions in each mode. Testing all vectors and all pairs thus proves the Turing-reduction assertion. It locates the hard core of the determinant problem within concise tensors with local centroid.

## Solve a summand with one narrow mode

For a pair of blocks of the same format, choose a mode of dimension \(b\le k\). Enumerate the at most \(q^{b^2}\) invertible matrices in that mode. After applying one of them to the source, the remaining condition is left-right equivalence of an ordered tuple of matrices \(M_\ell:D\to C\) and \(N_\ell:D'\to C'\), namely
\[
 P M_\ell=N_\ell Q\quad\text{for every }\ell ,
\]
with \(P,Q\) invertible. Here the two actual tensor mode maps have determinants \(\det P\) and \((\det Q)^{-1}\). This is a module isomorphism problem on \(C\oplus D\) and \(C'\oplus D'\): use two idempotents for the two summands and one off-diagonal endomorphism for each arrow \(M_\ell\) or \(N_\ell\). The constructive deterministic module isomorphism algorithm gives \(P_0,Q_0\) or rejects. [Brooksbank–Luks](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

The remaining choices are a coset of the units of the source endomorphism algebra
\[
 A=\{(P,Q):P M_\ell=M_\ell Q\text{ for every }\ell\}.
\]
This algebra is computed by a linear system. The determinant coset and stabilizer order of the tuple can be computed without finding a norm preimage or sampling invertible matrices.

Here are the details. Compute its Jacobson radical \(J\) using the finite-field matrix algebra radical algorithm, and the semisimple quotient \(B=A/J\). Compute its center by commutator equations and split that commutative algebra by its Frobenius fixed subalgebra as above. Each central factor is \(B_j\simeq M_{s_j}(E_j)\), with \(E_j\) its center. The integers \(e_j=[E_j:F]\) and \(s_j\) follow from the center dimension and \(\dim_F B_j=e_js_j^2\). No matrix units are needed. The surjection \(A^\times\to B^\times\) has kernel \(1+J\). This follows by lifting an inverse modulo \(J\) and inverting \(1+x\) for \(x\in J\) via the finite geometric series. Its kernel has size \(q^{\dim_F J}\) and determinant one on both modules by nilpotence. [Rónyai, Computing the structure of finite algebras](https://doi.org/10.1016/S0747-7171(88)80017-X)

On each of \(C,D\) use the radical filtration \(J^hC\) and \(J^hD\). The quotient layers are \(B\)-modules. Applying the central factor idempotent of \(B_j\) to each layer and dividing its dimension by \(e_js_j\) gives the multiplicity of the simple column module of that factor on the layer. Lifting the idempotent arbitrarily to \(A\) gives the same operator on each layer, since \(J\) acts there by zero. Write \(u_j,v_j\) for the sums of these multiplicities for \(C,D\). By block triangularity along the filtrations, the determinant vector on the two remaining tensor modes contributed by \(B_j^\times\) is exactly
\[
 \{(t^{u_j},t^{-v_j}):t\in F^\times\}.
\]
Indeed restriction of scalars on a column module gives the norm of the ordinary \(E_j\)-determinant, and that determinant followed by the finite-field norm is surjective. The order of \(A^\times\) is \(q^{\dim_F J}\prod_j|\mathrm{GL}_{s_j}(\mathbb F_{q^{e_j}})|\). Thus the matrices \(P_0,Q_0\) calibrate the base determinants, the displayed subgroups give all allowed determinant pairs, and division by the subgroup order gives exact fiber counts for this fixed narrow-mode matrix. Sum over the enumerated narrow-mode matrices, whose transporter triples are disjoint. Pair counts for the stabilizer yield \(s_i\) for the global calculation.

The matrix algebra and radical-filtration calculations and all the integer counts use polynomial time for fixed \(q\). Group orders and fiber counts have polynomial bit length since the total number of potential triples is at most \(q^{\sum_i(\dim V_i)^2}\). The centroid and block steps contribute a polynomial number of block comparisons. This proves the stated runtime. For instance one can take unboundedly many copies of concise \(1\)-by-\(d\)-by-\(d\) tensors with invertible matrix slices and choose different narrow axes in different types. A \(1\)-by-\(d\)-by-\(d\) invertible slice is centroid-local, since the first centroid endomorphism is scalar and forces the two others to be the same scalar. The direct sum then has no globally narrow mode, yet is handled by \(k=1\).

## Scope

The algebra and module algorithms for ordered tuples are established, and the compact prime-power-ring result already gives the corresponding globally narrow-mode bound. [Earlier prescribed-determinants proof](https://github.com/Dugongue/MathProofs/blob/main/GrochowLiteratureTransfers/PrescribedDeterminants.md) The result here combines an intrinsic decomposition of the raw tensors, exact determinant contributions from interchangeable tensor components, and complete determinant counts when each component has its own narrow mode. The assembly also works with a determinant oracle on unrestricted centroid-local blocks. It is a Turing reduction for the general hard core, and a direct polynomial-time decision algorithm for the stated narrow-block family. The general single-instance reduction of Open Question 1.9 remains open. [Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5)
