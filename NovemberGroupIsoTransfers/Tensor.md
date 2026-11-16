# Singly exponential transport for tensors with three unrestricted modes

## Statement

Assume the degree-three subquotient transporter from [Qiao–Zhang, Theorem 8.10](https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1723.pdf).

Fix an order $r$, a finite field $k=\mathbb F_q$, and based $k$-spaces $V_i$ of dimensions $n_i$, with $n=\sum_i n_i$. Let $H\leq\prod_i\operatorname{GL}(V_i)$ be supplied by matrix generators. At most three factors have unrestricted action. Every other factor is supplied with a direct sum decomposition into nonzero spaces which $H$ permutes, and for each such block the image of its set stabilizer on the block has order at most $q^{C n}$ for a fixed $C$. In particular an auxiliary mode may carry the full monomial group, since its blocks can be coordinate lines.

For arbitrary explicitly given tensors $T,T'\in\bigotimes_i V_i$, compute the complete $H$-transporter in deterministic time $q^{O_{r,C}(n)}\operatorname{poly}(L)$, where $L$ is the input bit length. The output is empty or one transporter and generators for the source stabilizer. The same proof permits affine quotient actions on bounded-order tensor modules with at most three active positions per summand with supplied auxiliary block decompositions. An affine quotient input must explicitly provide the relevant stable numerator and denominator and the quotient-valued generator translations.

This is a conditional extension of the November manuscript. Its three-tensor theorem already covers arbitrary input subgroups, so the contribution here concerns higher order and controls the cost in the original mode dimensions.

## 1. Prime-field presentation

Write $q=p^e$ and restrict each $V_i$ to $\mathbb F_p$. The original representation is the block diagonal representation on their sum, of dimension $d=en$. The $\mathbb F_q$ tensor product is the quotient of the prime-field tensor product by balancing relations. It suffices to take a basis of scalars over $\mathbb F_p$ and impose that moving each such scalar between adjacent factors is unchanged. This relation space is invariant under $H$, since all mode maps are $k$-linear. It can be specified explicitly in polynomial size for fixed $r$. Thus all quotient relations are retained, including any linking different selected blocks of a local presentation. Under restriction of scalars the given summand-stabilizer bounds are $p^{O(d)}$.

## 2. Split the auxiliary labels and solve cubic leaves

We use the quotient-and-fiber operation from the fixed-position recursion of [Qiao–Zhang, Algorithm 7.6](https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1723.pdf). In this application the auxiliary decompositions are supplied. The following recursion keeps all active representations unchanged and uses Theorem 8.10 only at its leaves.

A recursive instance has an acting subgroup $G$ and an affine action $\alpha_g(u)=L_g u+c_g$ on the current quotient $Q=N/P$. Its ambient tensor module is expanded into coordinate blocks by the current selected labels in each auxiliary mode. The current group permutes each selected label set. It is enough to solve $\alpha_g(x)=y$ with the full coset output. The original tensor comparison is the case $N=Z$, with $P$ the balancing relations and $c_g=0$.

Choose a largest remaining auxiliary label set $I$ of size at least two and a subset $A$ of size $\lfloor |I|/2\rfloor$. Let $G_A\leq G$ be its set stabilizer. Enumerate the orbit of $A$ under the given generators, retaining an actual lifting matrix for each subset. This supplies at most $2^{|I|}$ left coset representatives $r$ for $G/G_A$ and, by Schreier's formula, generators of $G_A$. To test a coset $rG_A$, replace $y$ by $y_r=\alpha_{r^{-1}}(y)$ and work in $G_A$.

Let $\pi_A$ be projection onto the tensor coordinates whose chosen auxiliary label belongs to $A$. It commutes with the linear action of $G_A$. Use the quotient map
$$
 q_A:N/P\longrightarrow Q_A=\pi_A(N)/\pi_A(P).
$$
The induced affine $G_A$-action on $Q_A$ uses the projected translations $q_A(c_g)$. Recursively find the complete transporter from $q_A(x)$ to $q_A(y_r)$, using the shorter auxiliary label set $A$. If its answer is empty, discard this coset. Otherwise write it as $aS$ with $S=\operatorname{Stab}_{G_A}(q_A(x))$.

The exact remaining direction space is $F=\ker q_A$, presented by
$$
 F=(N\cap\ker \pi_A)/(P\cap\ker\pi_A).
$$
Indeed each $n\in N$ with $\pi_A(n)\in\pi_A(P)$ can be corrected by some $p\in P$ to belong to $\ker\pi_A$. The kernel of this corrected presentation is $P\cap\ker\pi_A$. It lives in the coordinate blocks with complementary labels $I\setminus A$, including all relations inherited from $N$ and $P$. On $F$ use the $S$-action
$$
 \beta_s(z)=L_s z+\alpha_s(x)-x
$$
with source zero and target $\alpha_{a^{-1}}(y_r)-x$. These translations and target lie in $F$ by the projected comparison. The action is affine because it is the original action on the fiber through $x$, translated by $x$. A solution $s$ is equivalent to the original witness $ras$ in that branch. Its fiber stabilizer is $\operatorname{Stab}_{G_A}(x)$, the same subgroup in every successful branch. Combine the coset outputs by taking one successful witness and adjoining to this subgroup the differences between that witness and all returned witnesses. The same calculation applies to any presentation with fixed summand labels and at most the fixed number of auxiliary label positions, using a fixed dummy label for a position absent from a summand.

At a leaf there is at most one remaining label per auxiliary position. The current subgroup $G$ fixes all these blocks setwise. Its joint image on them has order $p^{O_{r,C}(d)}$, by the assumed bound on the action of each block stabilizer. Enumerate this image with lifts and use Schreier generators to compute its kernel $K$. For each left coset of $K$, normalize the target by its representative's inverse affine action. The selected auxiliary spaces are pointwise fixed under $K$. Evaluating on their bases rewrites the ambient module as fixed copies of tensor products of at most three active factors. Keep the exact numerator, denominator, and quotient translations under this linear identification. In particular an element that is trivial on the displayed factors can still translate the quotient and stays in the input group.

Theorem 8.10 applies to the resulting $K$-action. Its original group budget is $O(d)$, since the faithful input matrices on the original direct sum have dimension $d$ and the displayed active representations can be included once. It returns a complete answer in each coset, with words in the input generators. Evaluate those words in the stored affine generator actions to recover their translations. At a split or auxiliary image enumeration the lifts likewise carry their affine actions, computed by composing the generator actions along the orbit search. Uniting the leaf answers works as in the split step, now with common subgroup $\operatorname{Stab}_K(x)$.

For the time bound, let $b$ be the total number of surviving auxiliary labels, summed over the at most $r$ positions. Each quotient and fiber child loses at least $\lfloor |I|/2\rfloor\ge b/(3r)$ labels. The branching factor is at most $2\cdot 2^{|I|}$ and the sum of all successive $b$'s along any branch is $O_r(b_{\rm start})$. Thus the number of recursive nodes is $2^{O_r(b_{\rm start})}$. At each node all quotient presentations and group matrices have size polynomial in the original input length and $d$. Generator lists may be kept of length at most the logarithm of the order of the full matrix group by retaining only generators outside the generated subgroup. The necessary membership tests are polynomial in $p^d$ by expanding the faithful matrix representation on its vectors and using permutation-group membership. This compression also applies to the Schreier lists and to unions of returned cosets.

For the original tensor, $b_{\rm start}\leq \sum_i n_i=n$. The stated affine variant uses auxiliary presentations with the same total representation budget and hence the same label bound up to a fixed multiple. Each node costs $p^{O_{r,C}(d)}\operatorname{poly}(L)$, including its leaf calls and any coset processing, so the total is $p^{O_{r,C}(d)}\operatorname{poly}(L)=q^{O_{r,C}(n)}\operatorname{poly}(L)$.
## 3. A raw-input ordinary four-tensor application

For ordered ordinary four-tensor isomorphism, suppose the first flattening $12\mid34$ is invertible. Form the crossed inverse operator $E_4$ in mode 4 as in [Almost-All Ordinary Four-Tensor Isomorphism](https://github.com/Dugongue/MathProofs). Its construction is to invert-transpose the first flattening, contract the tensor with this dual tensor over the complementary modes of a crossed pair containing mode 4, square the resulting crossed endomorphism, and trace over its other mode. Any ordinary isomorphism conjugates $E_4$ by the fourth mode map. Different first-cut invertibility, or different rational canonical forms of $E_4$, therefore rules out isomorphism.

Align the two rational canonical forms and change the fourth-mode coordinates accordingly. The remaining fourth-mode maps must lie in the common centralizer of the aligned operator $E$; conversely a tensor witness in that constrained group recovers an ordinary witness by undoing the alignment. The centralizer has a direct sum decomposition on the primary blocks. Compute the dimension $a_f$ of the full commutant on each $f$-primary block by linear equations. Its unit group has order at most $q^{a_f}$. If $\max_f a_f\leq C\sum_i n_i$, these primary blocks satisfy the hypothesis in the theorem.

The required group generators can be computed in this same singly exponential time. Enumerate the at most $q^{a_f}$ elements of every small primary commutant and retain the invertible elements, acting identically on other blocks. These lists generate the centralizer because all its elements preserve the primary blocks. Compress the generator lists as above. The remaining three mode groups have their usual elementary matrix generators with diagonal scalings from the field. Trial division by all monic polynomials of degrees at most the operator dimension suffices for primary factorization within the claimed bound. The method tests the source promise and decides, with an explicit transporter and stabilizer generators when appropriate, against every second input. This extends the inverse-operator recognition approach from a logarithmic total repeated-primary budget to a linear budget on *each* block, at the singly exponential endpoint.

## 4. Sum-rank code equivalence in the original block dimensions

For a code of dimension $k_0$ in $\bigoplus_{j=1}^{b}k^{a_j\times b_j}$, consider the linear equivalence action that uses independent invertible row and column operations in each block and a permutation of blocks of the same shape. This is the equivalence action in [D’Alconzo, Definition 5](https://doi.org/10.1007/s10623-024-01375-0), restricted to shape-preserving permutations and with the source and target block shapes aligned. Complete equivalence under this action, including a witness and generators of the automorphism group, takes
$$
 q^{O(k_0+b+\sum_j(a_j+b_j))}\operatorname{poly}(L)
$$
time, with no assumptions on the ranks of the projected codes. If independent transposes are also allowed on square blocks, the same exponent suffices.

Form the tensor of the displayed code basis in
$$
 \left(\bigoplus_j k^{a_j}\right)\otimes
 \left(\bigoplus_j k^{b_j}\right)\otimes
 k^{k_0}\otimes k^{b}.
$$
The part in the last coordinate line $j$ has its first two factors supported on the corresponding row and column blocks. The basis-change action in the third mode preserves the represented code. In the first two modes allow exactly the independent block actions and the synchronized permutations, and in the fourth mode force the same permutation on the coordinate lines. This subgroup has explicit generators: the row and column block generators, common transpositions of equal-shape blocks, and generators of the third-mode basis changes. The last mode is auxiliary, and the first three can be treated as active. Equivalence of the codes supplies exactly a transporter in the allowed group, because a map carrying one code to the other has an invertible induced change of the displayed code basis. Conversely projecting onto each fourth-mode coordinate recovers the corresponding matrix-block map, which verifies a code equivalence. On an automorphism, projecting to the row, column, and permutation actions gives all code automorphisms in this representation, since each preserving map admits the same basis lift.

Allowing individual transposes on square blocks extends the ambient transformation group by a binary choice at each such block. Enumerate all their at most $2^b$ products and run the same comparison on the resulting normalized target. Row and column operations and block permutations conjugate through this enumeration into operations of the same form. Every allowed map occurs in one branch. Combining its full coset answers gives the complete extended transporter. This uses the same linear exponent because $q\ge2$.

The earlier sum-rank construction already establishes qualitative completeness via monomial four-tensor isomorphism. The quantitative addition is a singly exponential guarantee in the original total row and column dimensions, code dimension, and block count, including the constructive coset output. The synchronized generators make the block coupling explicit rather than deciding one independent tensor comparison per block.

## 5. A separate cubic consequence in small characteristic

Theorem 8.10 gives simultaneous affine equivalence of cubic tuples and quadratic maps in every characteristic. For an affine $n$-space let $\widetilde V$ be its homogenization, with one additional coordinate, and use the matrix subgroup of $\operatorname{GL}(\widetilde V)$ preserving the final-coordinate functional. Homogenize to the indicated degree and use the symmetric-power quotient of the corresponding tensor power of $\widetilde V^*$. A change in the output space contributes one more moving factor.

- For scalar cubic polynomials or ordered tuples of cubic polynomials, the tuple index is a fixed multiplicity. Complete simultaneous affine equivalence takes $q^{O(n)}\operatorname{poly}(L)$ time for arbitrarily many supplied polynomials.
- For quadratic maps with arbitrary output changes in a space of dimension $m$, their coefficient module $W\otimes\operatorname{Sym}^2(\widetilde V^*)$ has three moving factors. Their analogous transporter takes $q^{O(n+m)}\operatorname{poly}(L)$ time. Output translations can also be allowed: encode them in the acting affine matrix group of dimension $m+1$, and send a translation vector $b$ to the constant coefficient of value $b$ in the quotient-valued cocycle. Input changes fix constant polynomials, so this is the affine action required by the theorem.

If coefficients represent functions on $\mathbb F_q^n$ instead of formal polynomial expressions, also quotient by the kernel of evaluation of the indicated degree. This kernel is intrinsic and stable under affine changes. It is computed by reducing monomials modulo $x_i^q-x_i$; the reduced monomials are independent by the elementary univariate root bound and induction on the number of variables. The kernel therefore has a polynomial-size description in these bounded degrees. For general prime powers the same prime-field balancing step applies, taking the preimage of the symmetric and evaluation relation spaces in the prime-field tensor module.

This consequence differs from the polarization route of Qiao–Zhang's Corollary 1.4, whose cubic and quadratic polynomial conclusions restrict the characteristic. It also computes the complete constrained coset. It leaves general cubic maps with independent output changes outside this conclusion, because those would use four unrestricted moving factors.

## Status

This is an informal proof dependent on the stated interfaces of the Qiao–Zhang manuscript. Those interfaces and their nontrivial local dependencies were traced to the numbered statements and appendices. The full upstream proof has not been independently validated here. Publication priority of these extensions is unestablished.
