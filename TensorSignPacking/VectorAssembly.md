# One ordinary TI query for assembling all determinant signs across arbitrary centroid blocks

Work over $\mathbb F_3$ and write $\Gamma=\mathbb F_2^3$ for the three determinant bits. Use determinant $+1$ for bit zero. The results are informal.

**Assembly theorem.** Suppose a family of concise primitive centroid blocks has a deterministic polynomial-time local compiler. It takes two raw blocks and $a\in\Gamma$ and gives one ordinary same-field TI instance deciding whether the block pair has a transporter of sign vector $a$. There is a deterministic polynomial-time many-one reduction from the prescribed determinant vector problem for arbitrary direct sums of blocks in this family to one ordinary TI instance. The source and target need no supplied matching, multiplicities, orientation frames or isotype counts. Block parities may differ and each ordinary type may occur arbitrarily often. The local compiler may depend on both input blocks.

## Optional variables controlled by ordinary TI

Use the companion optional-bit construction. For an explicit system of binary equations, allow each variable to be zero and allow it to be one if its attached ordinary TI instance is positive. A system may also contain free bits, attached to a fixed positive query. The companion construction compiles this feasibility question to one ordinary TI query.

The construction splits rows into equations of arity at most three. Attach an idempotent pair to each bit and an idempotent for each allowed local assignment to each equation. Fixed, indexed marker idempotents determine the variable pairs and the assignment sets. The source assignment sets satisfy homogeneous rows and the target sets satisfy the required right-hand sides. Three incidence maps tie each local assignment to its bit idempotents. An isomorphism may swap the two bit idempotents exactly when the ordinary tensors attached to those labels match. Its permutation of each assignment set is forced to translate by the corresponding bit swaps. This gives precisely the requested row equations. A fixed number of label algebras, incidence maps, actions and tensor components suffices, regardless of the number of rows and columns. The ordinary tensor-system compiler gives one ordinary TI pair. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

## Enforce the sum of the internal signs without choosing a matching

Compact supports and extract the intrinsic centroid blocks $U_1,\ldots,U_k$ and $V_1,\ldots,V_\ell$, using the raw decomposition algorithm of [the narrow-mode profile proof](Structure.md). Record source and target basis calibration for each physical determinant. Conjoin an independent ordinary comparison of the original tensors. On its positive branch every ordinary type is balanced between the two lists, and compatible block matches characterize ordinary transporters. The ordinary comparison is a guard throughout the proof. In particular, the binary incidence equations below alone would allow classes of unequal multiplicities of the same parity.

Introduce a bit $x_{ij,a}$ for every source-target block pair and sign vector $a$. Gate this bit by the local ordinary query for that specific sign. Require odd degree at each source and target index:
$$
 \sum_{j,a}x_{ij,a}=1\quad\text{and}\quad
 \sum_{i,a}x_{ij,a}=1
 \qquad\text{over }\mathbb F_2.
$$
These are conditions on a binary multiset of local signed edges. Define its internal sign sum to be $z=\sum_{i,j,a} a x_{ij,a}$.

The possible values of $z$ equal the internal sign profile of any fixed ordinary perfect matching. To see this, consider one ordinary type and choose conceptual isomorphisms from each source and target block to a common representative. Let their signs be $b_i$ and $c_j$. Let $H\le\Gamma$ be the sign subgroup of that representative's automorphisms. Exactly the signs in $b_i+c_j+H$ are available for a matched local edge. No actual reference isomorphisms need to be found. Summing any selected edges with odd incidence at every vertex therefore gives
$$
 \sum_i b_i+\sum_j c_j+h,\qquad h\in H.
$$
An ordinary perfect matching gives this full coset by selecting one allowed label per matching edge. Each nonempty type has at least one matched edge, so independently varying one label realizes all of $H$. The sum of these cosets over ordinary types proves both inclusions.

## Account for block permutation signs by independent inversion choices

Group the source and target block lists by their common dimension parity vector $p\in\Gamma$, using the same order of parity buckets on both sides and arbitrary orders within a bucket. Pay the known basis-calibration determinants for those orders. Matching preserves the buckets. For each crossing of two coordinate intervals of dimension $m$ and $n$ in one mode, the block permutation contributes the sign $(-1)^{mn}$. Hence within bucket $p$, the permutation contributes $p$ times its inversion parity, and there are no crossings across buckets. If bucket cardinalities differ, reject before constructing these constraints.

For a bucket of size $s$, for each source index pair $i<k$, introduce option bits $y_{ikj\ell}$ for ordered distinct target indices $j,\ell$ in that bucket. The gate for an option is
$$
 O(U_i,V_j)\ \land\ O(U_k,V_\ell),
$$
where $O$ is ordinary TI. This gate compiles to one ordinary instance by the preceding ordinary conjunction construction. Impose the row $\sum_{j\ne\ell}y_{ikj\ell}=1$. Define
$$
 t_p=\sum_{i<k}\sum_{j>\ell} y_{ikj\ell}.
$$
The formula gives the true set of possible bucket inversion parities on the positive ordinary branch.

Indeed, if there is no repeated ordinary type in the source bucket, every source has one possible target, so exactly one option is enabled in the row for each pair. The binary sum is the true inversion parity of the unique matching. If some ordinary type repeats, actual matchings give both parities by exchanging the targets of two equal-type source blocks. All choices from any actual matching satisfy the rows. Reversing just the two target options for an equal-type pair in the row for that pair changes the binary inversion sum by one and preserves the row constraints. Thus the option system also realizes both parities. These arguments include buckets of size zero or one, whose inversion parity is zero. They need no complement tests, canonical labeling, matching algorithm on unknown ordinary types or positive logical formula for parity.

The possible internal sum $z$ is exactly the same for every ordinary block matching, by the coset argument. Hence it is legitimate to choose the inversion parities using independent options. The actual global possible sign bits are precisely
$$
    c+z+\sum_{p\in\Gamma}p\,t_p+s,
$$
where $c$ is the known calibration vector and $s$ is freely supported on the modes with unused ambient coordinate complements. Include bits for these free signs and impose the three desired scalar equations on this expression. Every accepting optional-bit assignment can be realized by choosing actual matchings with its bucket parities, then local transporters in those matchings with its internal sign sum, and finally the unused complement maps. Conversely an actual transporter supplies a selected edge in each matching slot and the genuine image option for every source pair. This proves soundness and completeness.

There are at most $8k\ell$ signed edge variables and $O((k+\ell)^4)$ inversion option variables. The number of rows and all gate-query dimensions are polynomial. Apply the ordinary optional-bit compiler once, then the independent ordinary conjunction guard. This is one deterministic polynomial-size ordinary TI instance.

## Concrete application with logarithmic width over a block coefficient field

This removes the unknown-type restriction whenever each local determinant can be tested by a small linked exterior algebra. For example, let $K$ be the intrinsic coefficient field in the local centroid of a block, with $d=[K\colon\mathbb F_3]$. Suppose that **each** of its three mode dimensions over $K$ is at most $C\log(2+L)$ for fixed $C$ and global written length $L$. The field degree $d$ may be unbounded. The raw extraction and deterministic alignment of two presentations of $K$ are given in [the narrow-mode profile proof](Structure.md). A matching ordinarily isomorphic block has the same coefficient degree and width. The criterion is compatible with arbitrary repetitions and permutations among all qualifying blocks.

Include the original block tensor, its coefficient field algebra and its actions in the three modes in a tensor system. Choose a $K$-basis in each mode. At each endpoint attach the exterior algebra of each mode over $K$, its degree-one inclusion and the top wedge line. These data make the exterior action arise from the actual mode map. For a true transporter written $A_i\sigma$ in the selected mode frames, its action on the resulting $K$-line is $z\mapsto\lambda_i\sigma(z)$, where $\lambda_i=\det_K A_i$. The field isomorphism $\sigma$ is forced by the same original transporter since the coefficient action is faithful. Take tensor products of line scalars with bilinear multiplication maps and force Frobenius-conjugate copies of each line using the $\mathbb F_3$-linear maps $z\mapsto z^{3^j}$. Because $\sigma$ commutes with Frobenius, these copies have scalars $\lambda_i^{3^j}$. Multiplication of all $d$ copies and an inclusion of an $\mathbb F_3$-line into the resulting $K$-line read precisely $N_{K/\mathbb F_3}(\lambda_i)$.

The factor from the semilinear part is $(\det_{\mathbb F_3}\sigma)^{r_i}$, for $r_i$ the mode dimension over $K$. After aligning the endpoint field bases by one reference field isomorphism, this follows by composing the linear and coefficientwise semilinear maps. If $d$ is odd every Frobenius power has positive determinant in a normal basis. If $d$ is even, the Frobenius generator acts in a normal basis as a $d$-cycle, so its determinant on the full field is exactly its determinant on the intrinsic quadratic subfield. Attach the latter subfield, its inclusion into $K$, and its two-dimensional exterior algebra to read this additional scalar on the true field map. In either case multiply the factors, accounting for the determinant ratios of the selected basis changes. Pin a vector in each final $\mathbb F_3$-line with the prescribed calibrated scalar. These are exactly the requested determinant constraints on one and the same transporter.

The sum of exterior-space dimensions is at most $\sum_i d2^{r_i}$, polynomial under the width bound. The field arithmetic lines, inclusions and multiplication maps are polynomial in dimension and number. The variable number of maps is packaged in a fixed number of tensor components by role-tagged direct sums and pinned coordinate label algebras, so the ordinary tensor-system compiler yields the required exact local query. This uses the project’s earlier semilinear norm construction.

Consequently the unrestricted-multiplicity direct sums of these logarithmic-width blocks reduce to one ordinary TI instance even when primitive blocks have unbounded dimensions over the base field. If either arm of a two-input one-sign conjunction qualifies, compile that arm to one ordinary TI instance and use the existing neutral-block absorption to place it beside the unmodified signed arm in one one-sign TI comparison. The assembly theorem also applies to any stronger exact local compiler as soon as it is available. An unrestricted pointwise local determinant compiler is still missing.
