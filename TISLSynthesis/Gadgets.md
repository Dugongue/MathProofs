# Special-linear tensor isomorphism with bounded constrained dimensions

Let $K$ be any field. In ordinary three-tensor isomorphism the three mode maps are independently invertible. In literal special-linear tensor isomorphism, each of the three mode determinants must equal $1$.

**Theorem.** On a pair of dense tensors, let $k$ be the largest dimension of a mode whose flattening has full support. If no such mode exists, put $k=0$. There is an explicit deterministic many-one reduction of literal special-linear tensor isomorphism to one ordinary three-tensor isomorphism instance over the same field with output size and arithmetic cost $2^{O(k)}\operatorname{poly}(N)$, where $N$ is the input size. In particular this is a polynomial-time reduction for $k=O(\log N)$ in the usual effective coefficient models. Both directions of witness recovery use the input field. A determinant-preserving castling step can reduce $k$ before the construction, even from formats with arbitrarily large original full-support modes.

The proof treats literal determinant-one conditions in all characteristics, including characteristic two, and includes zero tensors. All verification here is informal.

## 1. Impose each necessary orientation using exterior multiplication

Use tensors as trilinear forms on based argument spaces $V_1,V_2,V_3$. This is equivalent to using coefficient tensors, by duality, and determinant-one conditions are unchanged. The radical in a mode is the space of vectors giving identically zero contractions in that argument. Compare the three radical dimensions by elimination. A mismatch gives a fixed negative ordinary instance. If a mode radical is nonzero, an automorphism of that radical, extended by the identity on a complementary space, fixes the tensor and can have any determinant in $K^\times$. The three corrections act independently. It therefore suffices to impose determinant one on the modes with zero radical. If these are absent, the original ordinary instance suffices.

For each constrained mode $V$ of dimension $d$, put $e=\lceil d/3\rceil$ and add spaces $E_j=\Lambda^j V$ for $1\le j\le e$, identifying $E_1=V$. Use the usual increasing-subset bases. All basic mode spaces are regarded as separate labels, even when two have the same dimension. The following single partitioned tensor encodes the orientation constraints.

For every named space $E$, use a separate primal copy of $E$ and dual copy of $E^*$ in each of the three modes. Use three additional one-dimensional parts $L_1,L_2,L_3$, one per mode. The entry on $(L_1,L_2,L_3)$ is the product of its coordinates. For every pair of distinct modes $i,j$, place the evaluation between the primal $E$ in mode $i$ and the dual $E^*$ in mode $j$, multiplied by the line coordinate in the remaining mode. The data block is the input tensor on the primal copies of $V_1$ in mode 1, $V_2$ in mode 2, and $V_3$ in mode 3.

A partitioned transporter acts on the three lines by $\alpha_1,\alpha_2,\alpha_3$ with $\alpha_1\alpha_2\alpha_3=1$. Divide each primal and dual map in mode $i$ by $\alpha_i$. Then all the evaluation equations say that each dual map is inverse dual to the respective primal map. The incidence graph of the three primal and three dual copies, with edges on unequal modes, is a connected six-cycle. Thus for each label $E$ the normalized primal maps are one map $H_E$, and all normalized dual maps are its inverse dual. Conversely any such $H_E$ with the specified line scalars preserves all these blocks. In particular normalization cancels all scalar factors in the data block.

For every constrained $V$ and $1\le j<e$, put an additional nonzero block on the primal $E_1$ in mode 1, primal $E_j$ in mode 2, and dual $E_{j+1}^*$ in mode 3, with entry
$$
(x,y,\eta)\longmapsto \eta(x\wedge y).
$$
Its transporter equation says $H_{E_{j+1}}(x\wedge y)=H_Vx\wedge H_{E_j}y$. Such products span $E_{j+1}$, so induction gives $H_{E_j}=\Lambda^j H_V$.

Choose three integers $a,b,c$ between $0$ and $e$ with $a+b+c=d$. The last block for this constrained $V$ is on primal copies $E_a,E_b,E_c$ in their respective modes and evaluates
$$
(x,y,z)\longmapsto \omega(x\wedge y\wedge z)
$$
for the fixed top-volume functional $\omega$ of the based space $V$. In a mode with exterior degree zero, use its line part $L_i$, with its map normalized to identity. Wedges of complementary basis subsets give a nonzero value of $\omega$. The block equation is consequently exactly $\det H_V=1$. The blocks used for evaluation, exterior products, volumes, and original data occupy distinct tuples of parts. All unspecified blocks are zero. This description uses alternating exterior products in the usual quotient definition, so it also works in characteristic two.

An ordinary partitioned transporter now gives an exact special-linear witness after normalization and the permitted corrections on mode radicals. A special-linear witness extends by its exterior powers, inverse duals, and identity line maps. No root extraction occurs. The total of the lengths before removing the partitions is $O(\sum_i\dim V_i+\sum_{V\ {\rm constrained}}\sum_{j=1}^{\lceil\dim V/3\rceil}\binom{\dim V}{j})$. There are only linearly many parts in the original total mode length.

## 2. Remove polynomially many partitions with polynomial size

Here is an exact field construction for this step. It permits polynomially many parts, so the number of exterior powers does not cause an additional exponential dependence. Use matrix slices with row space $X=\bigoplus_{i=1}^s X_i$, column space $Y$, and slice space $Z$, of dimensions $p,m,\ell$. For $s=1$ this mode needs no treatment. For $s\ge2$, add two tags for each part with indices $j=1,\ldots,2s$, rank labels $r_j=j$, and associated part $X_{i(j)}$. For tag $j$ add private copies $Y_j,I_j$ of dimensions $m,r_j$ to the row space and private copies $X'_j,J_j$ of dimensions $\dim X_{i(j)},r_j$ to the column space. The new slice $D_j$ consists only of identities on $(Y_j,Y)$, $(X_{i(j)},X'_j)$, and $(I_j,J_j)$. Old slices are embedded in the old $X,Y$ rectangle. The enlarged first mode is unpartitioned, while all additions to the other modes are placed in their last existing part.

The maximum rank of the contraction pencil $A(z)+\sum_j b_jD_j$ over the function field of its coordinates is $q=p+m+\sum_j r_j$. Every nonzero $q$-minor contains all rows and columns of the private rectangles and is divisible by $\prod_j b_j^{r_j}$, since away from those rectangles the rank is at most $p+m$. Select all private rectangles, all old rows and columns, one column copy $X'_j$ per old part, and one row copy $Y_j$. The associated determinant is a pure tag monomial, since ordering the identities leaves only an off-diagonal data block. For each prescribed tag one can take its twin's column copy and another tag's row copy, so the corresponding exponent can be exactly $r_j$. Therefore the greatest common divisor of the nonzero maximal minors is exactly $\prod_j b_j^{r_j}$ up to a field unit.

An isomorphism acts by invertible row and column matrices and an invertible linear substitution of slice covariates. The ideals of maximal minors are preserved by the row and column changes by Cauchy–Binet and their inverses. Factor uniqueness for the displayed greatest common divisor and the distinct exponents $r_j$ therefore forces the tag covariates to be fixed up to nonzero multiples. In the slice equation this means data combinations have no tags, and the source combination for target $D_j$ is $\beta_jD_j+C_j$ with $\beta_j\ne0$ and $C_j$ supported in the old rectangle.

A row shear with block $-\beta_j^{-1}C_j$ from $Y_j$ to $X$ fixes the original slices and clears all $C_j$ at once. Absorb its inverse into the row transporter. The normalized row map must preserve each column span $X_{i(j)}\oplus Y_j\oplus I_j$, and the column map must preserve each row span $Y\oplus X'_j\oplus J_j$. Intersect the two spans for the twin tags to recover each $X_i$, and intersect any two distinct row spans to recover $Y$. The surviving maps restrict invertibly to those old spaces and to the old slice coordinates, preserving all old partitions. Conversely an original partitioned witness extends by inverse-transpose maps on the paired copies and identities on the private rectangles and new slice coordinates.

One step has lengths $p+2sm+s(2s+1)$, $m+2p+s(2s+1)$, and $\ell+2s$. Repeat cyclically for the other two modes, preserving their part counts until removal. The lengths stay polynomial in the old lengths and number of parts, and all entries are copied or set to constants. Together with Section 1 this proves the stated reduction. A fixed positive or negative ordinary instance can encode the outcome of any direct preprocessing decision, including the zero case.

## 3. Determinant-preserving castling over the input field

Use coefficient tensors for this section. Suppose the flattening $F_T:U^*\to E=V\otimes W$ of $T$ is injective. Write $n=\dim U$, $m=\dim V$, $\ell=\dim W$, and $D=m\ell$. Use the ordered tensor-product basis on $E$ and its top-volume functional $\omega_E$. With ordered columns $x_1,\ldots,x_n$ of $F_T$, define
$$
\eta_T(y_1,\ldots,y_{D-n})
=\omega_E(x_1\wedge\cdots\wedge x_n\wedge y_1\wedge\cdots\wedge y_{D-n}).
$$
For $n<D$ this is a nonzero decomposable $(D-n)$-form whose underlying subspace of $E^*$ is the annihilator of $\operatorname{im}F_T$. Choose an ordered annihilator basis with wedge exactly $\eta_T$ and write it as the columns of the new flattening $F_{T^\perp}$ into $V^*\otimes W^*$. Gaussian elimination finds an initial annihilator basis. Choose new columns $y_j$ complementing $\operatorname{im}F_T$ by elimination. The pairing matrix of the initial annihilator basis against the new columns is invertible, and its determinant is the value of the initial annihilator wedge on them. The value of $\eta_T$ on them is an ordinary $D$-square determinant. Multiplying the first annihilator basis vector by their ratio gives the required normalization. No full exterior tensor needs to be materialized.

If $T'=(P,Q,R)T$, put $C=Q\otimes R$. Then $F_{T'}=CF_TP^{\mathsf T}$. The exterior-volume identity gives
$$
\eta_{T'}=(\det P)(\det C)\,(\Lambda^{D-n}C^{-\mathsf T})\eta_T,
\qquad
\det C=(\det Q)^\ell(\det R)^m .
$$
It follows that the determinant triples of transporters for the castled pair are precisely the images of the original triples under
$$
(a,b,c)\longmapsto (a b^\ell c^m,\ b^{-1},\ c^{-1}).
$$
Indeed $Q^{-\mathsf T},R^{-\mathsf T}$ take the annihilator subspaces to each other. The unique basis change on the first mode has determinant prescribed by the exact wedges in the displayed identity. Conversely, a complementary transporter determines $Q,R$ by inverse duality. Recover the original subspaces by taking annihilators again and compare the ordered column bases using elimination. The same identity determines the original determinant as $a=(a b^\ell c^m)b^{-\ell}c^{-m}$. Thus castling preserves literal special-linear equivalence in both directions, with same-field witnesses.

If $n=D$, there is no complementary mode. In this case equality of $\det F_T$ and $\det F_{T'}$ decides literal special-linear equivalence, since $Q=R=I$ and the induced first-mode basis change suffices. If an axis has size $1$, the instance is a two-sided special-linear matrix problem. Its classification is rank, plus determinant when the shape is square of full rank. For the rank statement, the canonical rank-$r$ matrix is the identity between $r$ basis vectors with zero elsewhere. Its stabilizer can change either determinant independently on unused coordinates. When only one side lacks spare coordinates, act by an arbitrary change on that full side and its inverse transpose on the support of the other side, and adjust the other determinant on an unused coordinate. This supplies independent determinant corrections except in the full square case, where the product is constrained to $1$ and equal determinants suffice.

Preprocess by repeatedly castling any injective mode of dimension strictly above half the product of the other two dimensions. Compare flattening ranks first, and handle equality with the full product as above. Each nontrivial step strictly decreases the sum of mode sizes. Thus there are polynomially many exact same-field steps and the dense instance shrinks. This bounds the number of field operations throughout the chain. For an unbounded chain over fields with variable coefficient heights, the statement is an arithmetic-operation bound. Then apply Sections 1–2 whenever the remaining constrained dimensions are within the desired range. In particular formats $(m\ell-1,m,\ell)$ with injective first flattening reduce to matrices, even when all original modes are full and grow. [Sato's castling transformations](https://rikkyo.repo.nii.ac.jp/records/10005) · [Loeser, Section 1.1](https://webusers.imj-prg.fr/~francois.loeser/nagoya.pdf) · [Venturelli](https://arxiv.org/abs/1606.07257)

## 4. Two sufficient conditions requiring no exterior spaces

### Determinant corrections from direct sums

Suppose, with decompositions of the three mode spaces as fixed blocks, a tensor is a direct sum of components of dimensions $(d_{1j},d_{2j},d_{3j})$. Scaling the three mode blocks of one component by $(u,v,(uv)^{-1})$ fixes that component and acts trivially on all the other components. The stabilizer determinant group contains the values of the multiplicative monomial map whose integer column generators are
$$
(d_{1j},0,-d_{3j}),\qquad (0,d_{2j},-d_{3j}).
$$
Include the standard vector for a mode whenever there is an unused complement in that mode. Compute the Smith invariants of this three-row integer matrix. Changing integral bases in domain and target corresponds to bijective monomial changes on products of $K^\times$. Thus the monomial map is surjective if the rank is three and taking each of the three Smith powers is surjective on $K^\times$. Over $\mathbb F_q$ the equivalent criterion is that each Smith invariant, padding with zeros if needed, be coprime to $q-1$. Over an algebraically closed field it is just rank three. Whenever this criterion holds for either input tensor, every ordinary transporter can be corrected to literal determinant one by composing with these stabilizers. Hence the identity map to the ordinary instance is an exact reduction on the certified inputs.

For example, over an algebraically closed field two direct summands with different aspect ratios suffice. Each summand's two columns span the plane with normal $(1/d_{1j},1/d_{2j},1/d_{3j})$ over $\mathbb Q$, and nonproportional triples give distinct planes. The field scope matters for the Smith exponents. For a supplied block decomposition the criterion is an exact linear algebra and integer arithmetic check.

### Detect determinant freedom by linear equations in characteristic zero

Let $K$ be algebraically closed of characteristic zero. Compute the space
$$
L_T=\left\{(X_1,X_2,X_3):
 (X_1\otimes I\otimes I+I\otimes X_2\otimes I+I\otimes I\otimes X_3)T=0
 \right\}
$$
and its image under $(X_1,X_2,X_3)\mapsto(\operatorname{tr}X_1,\operatorname{tr}X_2,\operatorname{tr}X_3)$. If this image has dimension three, literal special-linear equivalence to $T$ is just ordinary equivalence to $T$. The stabilizer is an algebraic group and smooth by Cartier's theorem. The displayed kernel is its Lie algebra, by substituting each $I+\epsilon X_i$ for $\epsilon^2=0$. The trace map is the differential of the determinant homomorphism to the three-dimensional torus. If its rank is three, the image has dimension three and is therefore the full torus. For example, the image of an algebraic group homomorphism is a closed algebraic subgroup. Every determinant triple in $K^\times$ is then available on the stabilizer, as required. This supplies a polynomial arithmetic recognition test for a sufficient condition without knowing a block decomposition. [Cartier's theorem](https://stacks.math.columbia.edu/tag/047N) · [Milne, Algebraic Groups](https://www.jmilne.org/math/CourseNotes/AGS.pdf)

## 5. Scope and primary sources

Chen, Grochow, Qiao, Tang and Zhang single out special-linear actions after establishing results for other classical groups. Joux and Narayanan's ITCS 2025 discussion asks about special-linear tensor isomorphism hardness in relation to hyperdeterminants and also discusses a uniform random input assumption. The present maps concern worst-case explicit inputs and literal determinant-one transporters. Grochow and Qiao's Part IV supplies the rank-marker and partitioning antecedent. Duplicate supports and the greatest common divisor of maximal minors allow linearly increasing marker ranks here, keeping the dependence on the number of parts polynomial. The exterior-volume constraint and the normalized determinant-preserving castling step give the proved reverse reductions on their stated families. The resulting scope leaves unrestricted same-field polynomial-time many-one reducibility open. Publication priority remains unverified. [Chen–Grochow–Qiao–Tang–Zhang, Section 1](https://arxiv.org/html/2306.03135v2#S1) · [Joux–Narayanan, Section 5](https://doi.org/10.4230/LIPIcs.ITCS.2025.62) · [Grochow–Qiao, Theorem 5.1](https://arxiv.org/html/2306.16317#S5)

The companion [Gadgets.py](Gadgets.py) checks 4,608 determinant identities for castling from shape $3\times2\times2$ over $\mathbb F_3$ and 64 split-volume identities on four-dimensional spaces over that field.
