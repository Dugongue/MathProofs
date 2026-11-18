# Shared-core tensor isomorphism and determinant transport

Informal proofs. The algorithms handle marked core subspaces and, in the main recoverable class, reconstruct every bag from the tensor. The theorem also gives an exact local-to-global counting formula. Publication priority for the specific assembly below has not been established.

## 1. Model and gluing theorem

Let the input be two three-tensors over a finite field $F=\mathbb F_q$. In each source mode choose a marked subspace $C_m$ and a splitting

$$
V_m=C_m\oplus\bigoplus_{i=1}^k U_{mi},\qquad B_{mi}=C_m\oplus U_{mi}.
$$

Use primed notation at the target. The tensor lies in the sum of the spaces $E_i=B_{1i}\otimes B_{2i}\otimes B_{3i}$. Write $K=C_1\otimes C_2\otimes C_3$. Expanding by the three chosen direct sums gives

$$
\sum_i E_i=K\oplus\bigoplus_i E_i^\circ,
$$

where $E_i^\circ$ consists of the coordinate sectors of $E_i$ with at least one private factor. Write $T=T_0+\sum_i t_i$ in this decomposition, and similarly $S=S_0+\sum_j s_j$. The classes $[t_i]\in E_i/K$ are intrinsic once the bags and cores are fixed. Changing their lifts changes the equations below by predictable core translations.

Fix isomorphisms $A_m:C_m\to C'_m$. A local transporter for $i\to j$ is a triple $F_m:B_{mi}\to B'_{mj}$ of isomorphisms acting as $A_m$ on the core and carrying $[t_i]$ to $[s_j]$. Its spill is the element $\delta=F t_i-s_j\in K'$, where the product of maps on the three modes is understood. The local matrices have the form

$$
F_m=\begin{pmatrix}A_m&X_m\\0&D_m\end{pmatrix}.
$$

In particular the shears $X_m:U_{mi}\to C'_m$ are included in the local search. They can move tensor contributions from a private sector into the core.

**Gluing theorem.** A bag-preserving transporter exists with the prescribed core maps if and only if there is a bijection $\pi$ of bags and a local transporter for each $i\to\pi(i)$ with spills summing to $S_0-(A_1\otimes A_2\otimes A_3)T_0$.

**Proof.** A global map restricts to the local maps and induces the chosen bijection on quotient blocks. Comparing private sectors gives exactly the local transport equations. Comparing the core gives the sum equation. Conversely, define each global mode map on the core by $A_m$ and on the private $U_{mi}$ by its local map. Its quotient is a block permutation with invertible blocks $D_m$, and its restriction to the core is invertible, so the global map is invertible. Its action on $T$ has the prescribed private sectors, and its core coefficient is correct by the sum equation. This argument remains valid when some of the private-sector terms involve core factors in one or two modes. ∎

## 2. Arbitrary explicit local lists

This version allows additional local restrictions, even restrictions chosen separately for every pair $(i,j)$. The input to this stage consists of the finite spill sets $D_{ij}\subseteq K'$ or an explicit procedure that builds them. Each listed spill may carry one local witness. The glue theorem reduces decision to a perfect matching with given total spill $\gamma$.

**Randomized decision and checked search.** Let $E$ be a finite auxiliary field, possibly of different characteristic from $F$. Work in the commutative group algebra $E[K']$ with basis $e_x$ and multiplication $e_x e_y=e_{x+y}$. Set

$$
M_{ij}=\sum_{x\in D_{ij}}X_{ijx}e_x.
$$

The coefficient of $e_\gamma$ in $\det M$ is a scalar polynomial. The Leibniz expansion assigns a distinct degree-$k$ monomial to every labeled perfect matching. Its coefficient is $1$ or $-1$, even when these two numbers agree in the auxiliary field. Thus the polynomial is nonzero exactly when the requested matching exists. For independent uniform field evaluations, the miss probability is at most $k/|E|$ on positive instances. Division-free determinant evaluation works directly over the group algebra. With dense arrays and ordinary convolution this costs $\operatorname{poly}(k,|K'|)$ auxiliary field operations, besides building the lists. One can choose the auxiliary field to contain the roots of unity for the additive group and use its character decomposition to perform the determinant evaluations componentwise.

A nonzero coefficient gives a witness without fresh randomness. Keep the successful evaluation fixed. At a row, replace that row by each individual allowed labeled entry in turn. At least one replacement preserves the nonzero target coefficient by row multilinearity. Keep that replacement and repeat. At the end, the surviving assignments form a matching of the requested weight. Retrieve the local witnesses and verify the glued maps against the original tensors. This gives one-sided decision error, and every reported positive witness is checked.

**Deterministic one-bit algorithm.** If the spill group has order two, or all sets are nonempty cosets of the same subgroup and the quotient has order two, start with any labeled perfect matching $M_0$ found by ordinary bipartite matching. On its contracted row vertices, add an arc $i\to j$ for each possible labeled match of row $i$ to the column assigned by $M_0$ to row $j$. Tag it by the difference between its label and the baseline label at row $i$. Use parallel arcs and loops when appropriate. A matching of the opposite parity exists exactly when the digraph contains an odd-tag directed simple cycle. One direction follows by writing the relative permutation as disjoint cycles. The other follows by replacing the baseline along such a cycle. A parity-doubled reachability search finds a closed odd-tag walk if there is one, and splitting at repeated vertices recovers an odd-tag simple cycle. Lift any quotient witness to concrete spills by adding the remaining subgroup element on one edge, provided the matching is nonempty. The empty matching is checked separately. This algorithm concerns the parity of additive labels. Permutation signs in the intrinsic model below use a separate, exact formula.

**Why closure of the local maps matters.** Arbitrary explicit lists already give an NP-complete problem when $K'$ is represented by its dimension, even with a unique underlying perfect matching and with at most three labels per assigned pair. Given a graph, use $K'=(\mathbb F_2^2)^{E(G)}$. For each graph vertex, choose a nonzero color vector and place it in every edge coordinate incident to that vertex. For each graph edge, choose a nonzero auxiliary vector supported only in that edge coordinate. Use one diagonal assignment per choice variable, with its three possible labels. Total zero means $c_u+c_v+c_{uv}=0$ on every edge, so $c_{uv}\ne0$ holds exactly when endpoints differ. A valid labeling is a polynomial-size certificate. This list construction is realized by individual tensor shears: let $C'_1=K'$, let $C'_2,C'_3$ be one-dimensional, and give each diagonal pair a private vector $u_i$ in mode one and tensor contribution $u_i\otimes c_2\otimes c_3$. The three specified allowed shears send $u_i$ to $u_i+x$ for the three labels. Hardness here is for pair-specific lists of allowed maps.

The determinant method is classical exact matching machinery applied to the spill group. The one-bit argument is an elementary alternating-cycle specialization. [Mulmuley–Vazirani–Vazirani](https://doi.org/10.1145/28395.383347) · [Sato–Yamaguchi](https://arxiv.org/abs/2508.04081)

## 3. Deterministic intrinsic transport, including the three determinants

Assume all bag maps respecting $A_m$ are allowed. Transport the source cores to the target core coordinates using $A_m$ and keep the chosen private bases. An identity-core isomorphism of two fringes means an invertible local map taking one fringe class to the other. Because these maps have identities, composition and inverses, they give equivalence classes of the combined source and target fringes, including their three mode dimensions. Each class must have equally many bags of either tensor. Assemble one global map $F_0$ by matching arbitrarily within each class and choosing local transporters. This map is a transporter on the private sectors, so $S-F_0T\in K'$.

Let $G$ be the group of target automorphisms of the marked bag system that fix the cores pointwise and preserve the fringe classes. Its elements may permute bags. For a target bag $j$, let $H_j$ be its identity-core local stabilizer of $[s_j]$. Choose a representative in every target fringe class and a local identity-core map from the representative to each bag. These choices identify local stabilizers in a class and give consistent maps between bags. They split the quotient of $G$ by $\prod_j H_j$ as the product of the symmetric groups on the classes. In particular,

$$
|G|=\left(\prod_j |H_j|\right)\left(\prod_{\mathcal C}|\mathcal C|!\right).
$$

Every global map preserving the fringes and acting as $A_m$ on the cores is uniquely $gF_0$ for some $g\in G$. Define the homomorphism

$$
\eta:G\longrightarrow K'\times(F^\times)^3,
\qquad g\longmapsto(gS-S,\det g_1,\det g_2,\det g_3).
$$

Indeed $gS-S\in K'$, and $g$ acts as the identity on $K'$, so spills add under composition. Determinants multiply in the original ambient bases. Since $S-F_0T$ is also in $K'$, one has $gF_0T=F_0T+(gS-S)$. Thus, for prescribed nonzero determinants $d_1,d_2,d_3$, the existence of a full transporter is equivalent to

$$
\left(S-F_0T,\frac{d_1}{\det (F_0)_1},\frac{d_2}{\det (F_0)_2},\frac{d_3}{\det (F_0)_3}\right)\in\operatorname{im}\eta.
$$

This proves the three-determinant result as soon as the local fringe routines give representatives and generators. It also gives an exact count, $|G|/|\operatorname{im}\eta|$, on each nonempty fiber, and zero on an empty fiber. For ordinary TI omit the determinant coordinates of $\eta$.

Generators of $\operatorname{im}\eta$ have two explicit sources. A local stabilizer contributes its spill and the three determinants of its quotient maps on the private factors. Extend it by the identity on all other bags. A transposition within a fringe class uses a selected local map $h$ on the first bag and $h^{-1}$ on the other. If $h$ spills $x$, then $h^{-1}$ spills $-x$. The global contribution is therefore

$$
\bigl(0,(-1)^{\dim U'_{1j}},(-1)^{\dim U'_{2j}},(-1)^{\dim U'_{3j}}\bigr).
$$

Each sign is the sign of transposing two equally sized coordinate blocks. The determinants of $h$ and $h^{-1}$ on the two quotient blocks cancel. One transposition per class with at least two members suffices for the image, even though the whole group generally contains additional transpositions. This is why the determinant correction can be assembled independently of the choice of support matching.

Write $p=\operatorname{char} F$. The additive factor has exponent $p$, and the determinant factor has exponent dividing $q-1$. These are coprime. For each image generator $(x,d)$, its $(q-1)$-st power isolates $x$ up to a nonzero scalar in $\mathbb F_p$, and its $p$-th power isolates $d$ up to an invertible power. This gives both projections with explicitly known exponent words in the original generators. The image therefore splits as $W\times D$, with $W$ a linear subspace over the prime field and $D$ a subgroup of $(F^\times)^3$. Gaussian elimination and a subgroup scan through at most $(q-1)^3$ vertices decide membership and produce a word in the generators. Using that word gives the full transporter. The count is $|G|/(p^{\dim_{\mathbb F_p}W}|D|)$ on a nonempty fiber. At fixed $q$ this assembly is polynomial in the tensor encoding and the local routine outputs, even when $K'$ has large cardinality.

## 4. Recovering the bags from the marked tensors

The bags in Section 3 can be obtained from the input whenever the following conditions hold. In all three modes project out the marked cores and let $\bar T$ be the resulting tensor. Require a concise quotient, meaning full support in each quotient mode. Recover its finest direct-sum decomposition, and take the preimages of its blocks in the original modes to be the bags. Require $T\in\sum_i B_{1i}\otimes B_{2i}\otimes B_{3i}$. Treat $S$ the same way.

To perform the recovery, compute the centroid of $\bar T$ by solving the linear equations in triples $(a_1,a_2,a_3)$ that require the actions of $a_m$ on their respective tensor modes to coincide. For a concise three-tensor, each action on the tensor determines the corresponding endomorphism. Operators on distinct modes commute. For centroid triples $a,b$, this gives

$$
a_1b_1\bar T=a_1b_2\bar T=b_2a_1\bar T=b_2a_3\bar T=a_3b_2\bar T=a_3b_1\bar T=b_1a_3\bar T=b_1a_1\bar T.
$$

The other modes have the same property. This proves commutativity by conciseness, and the same movement across modes gives closure under multiplying centroid triples. The unit is the triple of identity maps. Orthogonal centroid idempotents split the three modes, and each tensor component with different idempotents in distinct modes vanishes. Conversely, the projections of a direct-sum decomposition are orthogonal centroid idempotents. Thus the centroid's primitive idempotents give precisely the finest decomposition, canonically up to permutation. In particular any marked TI transporter has to preserve these bags. The support condition can then be tested directly in adapted bases, and it is invariant under marked isomorphism.

For completeness, computing the primitive idempotents is deterministic polynomial time at fixed $q$. In a finite commutative $F$-algebra $R$, compute the kernel $R_0$ of the $F$-linear map $x\mapsto x^q-x$. The product decomposition of the Artinian ring into local rings shows $R_0\cong F^s$. In each local factor a root must reduce to a scalar in the residue field. If it reduces to $\lambda\in F$, then $x-\lambda$ is nilpotent and fixed by the Frobenius map, so it is zero. Each scalar supplies a root. Given a basis of $R_0$, refine the unit idempotent by intersecting its current pieces with $1-(b-\lambda)^{q-1}$ for every basis element $b$ and scalar $\lambda\in F$. Its coordinates are precisely the indicators of $b=\lambda$. The resulting nonzero pieces are the primitive idempotents, since the basis separates all coordinates of $F^s$.

This uses published centroid decomposition machinery. The assembly acts on the overlap data of the original tensor after decomposition of its quotient. [Huang–Lu–Ye–Zhang](https://arxiv.org/abs/2110.07915) · [Brooksbank–Maglione–Wilson](https://arxiv.org/abs/2005.04046)

**Algorithm from marked tensor coordinates.** Let $c_m=\dim C_m$, and let $u_{mi}=\dim U_{mi}$, taking the maximum below across both inputs. For fixed $q$, the marked class admits deterministic recognition and decision, search and counting of ordinary or prescribed-determinant transporters in time

$$
q^{\sum_m c_m^2+\max_i\sum_m(u_{mi}^2+c_m u_{mi})}\operatorname{poly}(L).
$$

Here $L$ is the input length. Recover the bags, iterate all core isomorphisms if none are prescribed, and enumerate the local shear maps and invertible quotient matrices. This gives actual local transporters, stabilizer generators by listing the stabilizer, and stabilizer orders. Complexity follows by charging all choices of core maps and, for each choice, all pairs of bags with the indicated worst local enumeration charge. The deterministic assembly gives decision and checked search. The counts sum over disjoint core-map choices. If the core maps are prescribed, omit the first exponent. In particular this is polynomial when the displayed exponent is $O(\log L)$. With stronger local transporter and stabilizer routines the gluing still costs polynomial time at fixed $q$. The empty quotient can be handled as the core-only case by testing core maps directly.

**A class the full centroid does not split.** For any $k\ge2$, in every mode take a core vector $e_0$ and private vectors $e_1,\ldots,e_k$. Consider

$$
T=e_0^{\otimes3}+\sum_{i=1}^k
\left(e_i^{\otimes3}+e_i\otimes e_0\otimes e_0+e_0\otimes e_i\otimes e_0+e_0\otimes e_0\otimes e_i\right).
$$

The marked quotient has $k$ one-dimensional blocks, so the algorithm has polynomial cost. The full centroid is scalar. To see this, comparing actions in modes one and two on slice $i>0$ uses the matrix $E_{00}+E_{ii}$. Both endomorphisms preserve each plane spanned by $e_0,e_i$ and hence preserve their common line. Comparing the off-diagonal entries of the same equation removes all possible $e_i\to e_0$ shears, and the diagonal entries identify the two modes' diagonal values. The slice at zero has nonzero entries connecting every $e_i$ to $e_0$, so all those values agree. Tensor conciseness forces the third mode to have the same scalar. This family witnesses a genuine enlargement over splitting the full tensor into centroid blocks.

## 5. Canonical core recovery on an unmarked family

The following construction computes the core lines from tensor coordinates in every fixed finite field. It applies to the preceding example and to its weighted versions with arbitrary nonzero private weights and nonzero two-core weights. More precisely, let $k\ge3$ and suppose that in some bases the tensor is

$$
a e_0^{\otimes3}+\sum_{i=1}^k\left(d_i e_i^{\otimes3}+x_i e_i\otimes e_0\otimes e_0+y_i e_0\otimes e_i\otimes e_0+z_i e_0\otimes e_0\otimes e_i\right),
$$

where each $d_i,x_i,y_i,z_i$ is nonzero and $a$ is arbitrary. The bases in different modes may be chosen independently. The theorem gives ordinary and prescribed-determinant decision, search and counting directly on raw coordinate tensors in this family.

Work in one mode and write $\alpha,\beta_1,\ldots,\beta_k$ for the linear functions of a contraction covector given by evaluation at the corresponding basis vectors. The slice matrix has the form

$$
\begin{pmatrix}
a\alpha+\sum_i\lambda_i\beta_i & \alpha u^{\mathsf T}\\
\alpha v&\operatorname{diag}(d_i\beta_i)
\end{pmatrix},
$$

with every $\lambda_i,u_i,v_i$ nonzero. In actual input coordinates, form the linear span of all $3\times3$ slice minors multiplied by all polynomials of degree at most $q-2$. Use the ring of polynomial functions on the contraction space, with unique reduced representatives of coordinate exponents less than $q$. Intersect this span with the functions of degree at most two, and denote the resulting space by $Q$. Gaussian elimination computes the intersection in polynomial time for fixed $q$: all products have degree at most $q+1$, and reduction by $t^q=t$ preserves this bound. Left and right changes of the slice bases mix minors by invertible compound matrices, and linear substitutions in the contraction coordinates preserve each function-degree filtration. The resulting space $Q$ is therefore equivariant under TI.

We claim that in the hidden basis $Q$ is exactly $\operatorname{span}\{\alpha\beta_1,\ldots,\alpha\beta_k\}$. Every function of $Q$ vanishes on slices of rank at most two. Those include the full $\alpha$-axis, every $\beta_i$-axis at $\alpha=0$, and, for every $i\ne j$, the line at $\alpha=0$ with only $\beta_i,\beta_j$ possibly nonzero and $\lambda_i\beta_i+\lambda_j\beta_j=0$. On the axes a polynomial of degree at most two vanishing as a function has zero constant, linear and pure-square coefficients, using reduced representatives also when $q=2$. The two-coordinate lines then force all $\beta_i\beta_j$ coefficients to vanish. This proves one inclusion. For the other, fix $i$ and choose distinct $j,\ell$ outside $\{i\}$, possible since $k\ge3$. The submatrix with rows $0,i,j$ and columns $0,i,\ell$ has determinant $-u_\ell v_j d_i\alpha^2\beta_i$. Multiplication by $\alpha^{q-2}$, followed by function reduction, gives a nonzero scalar times $\alpha\beta_i$, since $\alpha^q=\alpha$ as a function. This proves the claim.

For $q>2$, $Q$ consists of homogeneous quadratics. Their common linear divisor is the unique line $F\alpha$. Find the two linear factors of a first nonzero member and test which factor divides every basis member of $Q$. This step is polynomial at fixed $q$: the span of the formal partial derivatives of the first quadratic is the plane of its two independent factors, so scan the projective lines of that plane and check divisibility by substitution. For $q=2$, leading quadratic classes of reduced Boolean functions identify with exterior two-forms. A linear coordinate change may add linear terms to a product, and its action on the leading class is the exterior action. The linear equations $\ell\wedge u=0$ for all leading classes $u$ of $Q$ recover $F\alpha$, since $\bigcap_i\operatorname{span}(\alpha,\beta_i)=F\alpha$. The line $F\alpha$ is a subspace of tensor mode space, as the linear functions are evaluated on covectors. Repeat in all three modes. This yields the marked cores of Section 4. Its quotient block sizes are one, so the resulting exact ordinary and prescribed-determinant algorithms have polynomial cost for these raw tensors.

The algorithm also gives a checkable invariant domain that can include other tensors. In each mode require the quadratic recovery to give a unique line, and then test conciseness, the bag support condition and the quotient size bound from Section 4. For $q>2$, take leading homogeneous quadratics and require a unique common linear factor up to nonzero scalar. Compute candidates from a first nonzero quadratic, using its derivative space and testing divisibility. A derivative space of dimension larger than two rules out any factorization into two linear forms. A nonzero square in characteristic two has zero derivative and its unique candidate is read from its square root. For $q=2$, require a one-dimensional solution to the exterior equations. These tests are equivariant, so a failed test and a successful test certify nonisomorphism across the two inputs. When both fail, this method makes no decision. When both pass, every transporter necessarily matches the computed cores, so the marked solver decides unrestricted transport between them. The tests work without recognizing the displayed hidden normal form.

## 6. Implications and concrete questions

- **Tensor and group algorithms.** The method composes local isomorphisms with a shared center or coefficient space while retaining actual witnesses and determinant constraints. For groups or algebras encoded into tensors, it is applicable when their identified characteristic layers induce the marked cores and the quotient blocks of Section 4. Grochow–Qiao's encoding and coloring tools motivate testing this interface. Their reductions alone do not supply such a layer for arbitrary tensors. [Grochow–Qiao](https://arxiv.org/abs/1907.00309) · [Brooksbank–Grochow–Li–Qiao–Wilson](https://arxiv.org/abs/1905.02518)
- **Larger unmarked recovery question.** On all changes of bases of inputs satisfying Section 4 with constant core dimensions and constant quotient block dimensions, seek a polynomial algorithm that outputs a polynomial-sized equivariant list of core triples containing a valid one. A positive result gives unmarked TI and SL-TI on that family by comparing the two lists and using the exact marked solver. Equivariance is sufficient. Alternatively it suffices that every isomorphic pair have at least one compatible pair of core triples in the lists. Section 5 gives one solved explicit family and a basis-independent test for additional inputs.
- **Local compression question.** For a fixed-size core and unrestricted local bag dimensions, seek a direct computation of the image of a fringe stabilizer in $K\times(F^\times)^3$, possibly using smaller local decision instances. Section 3 requires only the image generators and a transporter for each used image generator to solve search. Stabilizer orders are needed for exact counting. The arbitrary-list hardness example explains the value of keeping the actual stabilizer group action in view.
- **Multiple overlaps.** An explicit test for extending Section 3 is whether every overlap acts through a common fixed subspace and whether the kernel of the block-permutation map acts on the overlap corrections by translations. Under these two hypotheses with a supplied local generating set for that kernel and lifts of permutation generators, the same homomorphism argument handles the product of correction spaces. Recovering those generators in meaningful decompositions with more than one overlap remains open here.

The results give determinant-aware deterministic gluing and a polynomial-time core recovery test for the unmarked family above. The arbitrary restricted-list theorem handles cases where the local maps lack group closure. The unrestricted SL-TI reduction remains open in this work.
