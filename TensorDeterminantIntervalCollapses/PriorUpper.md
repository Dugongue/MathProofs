# Ten candidate degrees from two-sign TI through SL-TI

Work over $F=\mathbb F_3$. Each named class is the deterministic polynomial-time many-one downward closure of the displayed decision problem. Write $A$ for one-sign TI, $B$ for two-sign TI, and $S$ for SL-TI on explicit dense three-tensors. All claims here are informal. The ten are distinct definitions. Pairwise inequality of their many-one degrees is open.

For an ordinary tensor pair $X=(T,T')$, let $D(X)\subseteq \Gamma=\mathbb F_2^3$ be the relative determinant sign set, with zero denoting determinant one. The set is empty when there is no ordinary transporter. Otherwise it is a coset of the stabilizer sign subgroup, since every transporter is a translate of the source stabilizer. Set $P(X)=\pi D(X)$ for the projection $\pi:\Gamma\to\mathbb F_2^2$ to the first two coordinates. Thus $B(X)$ asks if $0\in P(X)$.

## The ten definitions

The first decision couples three independent raw comparisons. The second couples one relative comparison to a source automorphism.

| Local ID | Candidate | Acceptance rule |
|---|---|---|
| U1 | Tilted-line determinant balance | Couple one rank-two sign profile to two rank-one profiles on different lines transverse to its plane. |
| U2 | Cross-mode stabilizer correction | Permit a source automorphism with an odd first determinant to correct the third sign of a relative transporter. |
| U3 | Two-plane determinant balance | Use two distinct normal directions. |
| U4 | Three-plane balance with dependent normals | Use $\{a,b,a+b\}$. |
| U5 | Three-plane balance with independent normals | Use $\{a,b,c\}$. |
| U6 | Four-plane balance complementary to a dependent triple | Use $\Gamma^{*\times}\setminus\{a,b,a+b\}$. |
| U7 | Four-plane balance complementary to an independent triple | Use $\Gamma^{*\times}\setminus\{a,b,c\}$. |
| U8 | Five-plane determinant balance | Use $\Gamma^{*\times}\setminus\{a,b\}$. |
| U9 | Six-plane determinant balance | Use $\Gamma^{*\times}\setminus\{a\}$. |
| U10 | Seven-plane determinant balance | Use all of $\Gamma^{*\times}$. |


For U1, take independent pairs $X_0,X_1,X_2$. If $(x,y)$ is a choice from $P(X_0)$ and $a,b$ are choices of the first sign from $D(X_1),D(X_2)$, require
$$
(x,y,0)+a e_3+b(e_1+e_3)=0.
$$
Thus the two one-sign slots must agree on the selected bit, and that common bit is also the first sign in the two-sign slot, whose second sign must be zero. Here $e_1,e_2,e_3$ are the standard basis of $\Gamma$.

For U2, take one raw pair $X=(T,T')$. Let $H(T)=D(T,T)$ be its source stabilizer sign subgroup and set $Qh=h_1e_3$. Require
$$
0\in D(X)+QH(T).
$$
If every source automorphism has even first determinant, all three signs must be zero on a relative transporter. If an odd first determinant is available on a source automorphism, the third relative sign can be corrected and only two signs remain constrained.
For U3–U10, let $E$ be the displayed set of nonzero normals, collected from the nonzero portion $\Gamma^{*\times}$ of the dual space. Fix a dual basis $a,b,c$ and choose once a linear isomorphism $\iota_\lambda:\mathbb F_2^2\to\ker\lambda$ for each normal direction $\lambda$. An instance has one separate raw tensor pair $X_\lambda$ for each $\lambda\in E$. It accepts precisely when
$$
0\in \sum_{\lambda\in E}\iota_\lambda P(X_\lambda).
$$
The sum is a Minkowski sum of sets. Equivalently each slot chooses a transporter independently, with its two signs inserted into a designated plane, and the signed contributions must sum to zero in the common three-dimensional space. One empty sign set makes the comparison fail. Distinct input tensors in different slots need not have the same shape.

The eight arrangement definitions give exactly the eight orbits of subsets of at least two normals under invertible changes of the common three coordinates. Every pair of distinct normals is independent. A triple is either the nonzero part of a two-dimensional subspace or a basis. These two possibilities are both transitive under $\mathrm{GL}_3(\mathbb F_2)$. Complementation is equivariant, so it gives exactly two four-normal types, one five-normal type and one six-normal type. The full set gives one seven-normal type. This establishes the count without giving any computational separation between those types.

## A compiler for sum constraints

The earlier MathProofs sign-projection theorem gives, from any ordinary tensor pair $X$ and any specified linear endomorphism $L$ of $\Gamma$, an explicit polynomial-size tensor pair whose sign set is exactly $L D(X)$. It preserves emptiness. The determinant-preserving scalar-centroid construction can then make the output absolutely indecomposable, while leaving the exact sign set intact and allowing a sufficiently large marker size to distinguish its ordered format from finitely many other outputs.

Consequently, a fixed list of ordinary raw pairs $X_i$ and linear maps $L_i$ can be compiled to a single $S$ instance testing
$$
0\in \sum_i L_i D(X_i).
$$
First apply the exact projection to each pair. Use the scalar-centroid construction with successively oversized marker dimensions, and form the direct sum in the same fixed order at both endpoints. In a concise tensor the primitive centroid idempotents recover the direct-sum factors. Each marked factor is absolutely indecomposable, and its format differs from all the others, so any transporter must match it to the intended factor. Every list of individual transporters conversely extends by block-diagonal maps. The full sign on each mode is the sum of the individual bits, because the determinant of a block-diagonal map is the product of its diagonal determinants. Thus the compiled instance has exactly the claimed sum of sign sets. The supports, basis calibrations, tags and direct sum have polynomial size. There are at most seven slots in the present uses, and their formats can be fixed without deciding isomorphism. Malformed inputs go immediately to a fixed negative pair.

This lemma proves the upper reduction for U3–U10 by setting $L_\lambda=\iota_\lambda\pi$. It proves the upper reduction for U1 by using the three indicated slot maps, and for U2 by using the relative pair with the identity sign map and the self-pair $(T,T)$ with the map $Q$.

## Lower reductions and the arrangement order

For comparison with known degrees, let $J$ ask for an independent $B$ and $A$ conjunction, and let $K$ ask for three independent $A$ comparisons. These are benchmarks, separate from the ten new definitions. One $B$ instance yields three $A$ instances by testing the three nonzero linear functionals on the projected sign pair. Use the exact sign maps to present each as a first-coordinate test. An affine set omitting zero admits a separating functional constantly one on it, while an affine set containing zero passes all three tests. The empty set fails all three. Thus $B\le_m^p K$. Also $K\le_m^p J$ because two independent $A$ comparisons pack into one $B$ comparison by assigning their signs to separate axes of the sum compiler. The same compiler gives $J\le_m^p S$ by assigning the separate $A$ sign to the third axis.

For U1 a reduction from $J$ uses the given $B$ and $A$ pairs in the first two slots and a fixed sign-zero pair in the last slot. The sum vanishes exactly when the $B$ and $A$ requirements both hold. Conversely U1 reduces to U3. Keep the first pair in a rank-two plane slot, and aggregate the two one-sign pairs into one pair in the other plane slot. Use the sum compiler followed by a change of coordinates so its rank-two projected sign set equals the sum of the two designated transverse line contributions. The two lines span a plane different from the first slot's plane. A common change of coordinates and independent basis changes on the planes gives the standard U3 layout.

For U2 first project an arbitrary $B$ pair to the plane $P_0=\mathrm{span}(e_1,e_2)$, retaining exact projected sign profiles. If the output pair has no ordinary transporter, the answer is no. Otherwise its stabilizer sign subgroup equals the direction of the relative sign coset and is contained in $P_0$. The correction term lies in the line spanned by $e_3$, complementary to $P_0$. Hence the correction cannot cancel a nonzero relative sign in $P_0$, and the resulting U2 instance has the original $B$ verdict.

For each U3–U10, the lower reduction starts from $J$. Choose two different normal directions $\lambda,\mu\in E$, so the two planes are different. Put the projected sign set of the $B$ instance into the $\lambda$ slot. Choose a nonzero vector $v\in\ker\mu$ outside $\ker\lambda$. Encode the sign of the $A$ instance in the rank-one contribution $d_1 v$ of the $\mu$ slot, using a preliminary exact sign map into the preimage of its designated line. Use a fixed pair with sign set $\{0\}$ in every other slot. Then an element of $\ker\lambda$ cancels a multiple of $v$ only if both terms vanish. This gives exactly $B(X_1)\land A(X_2)$.

A fixed pair with sign set $\{0\}$ is the multiplication tensor of $\operatorname{Mat}_2(\mathbb F_3)$ compared with itself. An isotopy $\alpha(x)\beta(y)=\gamma(xy)$ factors as an algebra automorphism followed by left and right multiplication by units. To see this, put $u=\alpha(1)$ and $v=\beta(1)$, so $\gamma(x)=\alpha(x)v=u\beta(x)$. Surjectivity makes both $u$ and $v$ units. Then $u^{-1}\alpha(x)=\beta(x)v^{-1}$ is a unital algebra automorphism by the isotopy equation. An algebra automorphism of a full matrix algebra is inner, as is seen by changing basis to make the images of the matrix units standard. Left and right multiplication each act on two copies of a column or row space, so their determinants are squares. A conjugation has determinant one as well. Thus every stabilizer has all three determinant signs zero, and identity realizes zero.

If $E$ can be sent into $E'$ by an invertible change of the common sign coordinates, its balance language reduces to that of $E'$. The same coordinate change sends the associated planes to the target planes after taking the inverse dual on their normals. Reencode each input slot by a rank-two sign map so the two bits are in the target plane's basis, and fill new slots with the fixed neutral pair. The joint sum is zero in the new coordinates precisely when the old sum is zero. Thus U3 reduces to both U4 and U5, U5 reduces to both U6 and U7, and U4 reduces to U7. Both four-plane types reduce to U8, which in turn reduces to U9 and then U10. For the two four-to-five embeddings, the two omitted normals can be extended either to a dependent triple or to a basis. The complementary dependent-triple four-set contains no dependent triple, while the complementary independent-triple four-set contains both triple types. These facts prove the listed inclusions and do not exclude other many-one comparisons.

In particular, all ten candidates are in the requested inclusive interval $B\le_m^p C\le_m^p S$. There is also a conditional strictness statement for nine of them. The previous conjunction theorem gives $J\le_m^p B$ if and only if $S\le_m^p B$. In one direction use $J\le_m^p S$ just proved. In the other, if a $B$ query absorbs an independent $A$ query, it absorbs three by iteration. Since $B$ reduces to three independent $A$ queries, $B$ then absorbs a second $B$. Since $S$ reduces to three independent $B$ queries, another two absorptions give $S\le_m^p B$. The reductions have fixed arity throughout. Therefore if the upper gap is strict, U1 and U3–U10 are all strictly above $B$, because they contain $J$. This does not decide whether they are strictly below $S$. No analogous conditional strictness is claimed for U2. If $B$ and $S$ already have the same many-one degree, every candidate here has that degree too.

## Dependencies

The two reused MathProofs constructions are the exact determinant sign projection for all binary linear maps in *Determinant Sign Projections and Conjunctions in Tensor Isomorphism* and the marker pencil in *A determinant-preserving scalar-centroid embedding*. The ordinary distinction between object reductions and general comparison reductions is discussed by [Fortnow and Grochow](https://arxiv.org/abs/0907.4775). The original TI versus SL-TI comparison is [Open Question 1.9 of Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5).
