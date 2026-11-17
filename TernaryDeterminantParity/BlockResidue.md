# A parity compiler for small permutable tensor blocks

## Theorem

Fix $C>0$. Let $T,S$ be dense three-tensors over $\mathbb F_3$, with total input length $L$. In each of the three mode spaces of each tensor, supply an unordered direct-sum decomposition into nonzero blocks of dimension at most $C\log L$. For any three prescribed determinant signs, there is a deterministic polynomial-time construction of **one ordinary 3-tensor isomorphism instance over $\mathbb F_2$**. Its answer is yes exactly when a transporter has the prescribed signs and takes each supplied block to a block in the corresponding mode. There is no bound on how many blocks of the same dimension may be permuted. If the decompositions are recovered equivariantly from the raw pair, the construction tests the full transporter coset.

## Recover the exact linear transporter from finite relations

For mode $i$ use the dual blocks $D_{ij}$ which annihilate the sum of the primal blocks other than $j$. Their sum is $V_i^*$. For tensor $T$ make a finite set $\Omega_i(T)$ with the following elements.

- All vectors of every $D_{ij}$, tagged with their block. The zero vectors of distinct blocks are distinct points.
- One extra point for each even-dimensional block.

Make the corresponding sets for $S$. Use a separate block-label set in each mode. Record membership of each point in its block, and use a unary relation to distinguish the extra points from the vector points. Record the ternary same-block addition relation on the vector points. Finally use three ternary relations on vector points of the three modes, one for each possible value of $T(x_1,x_2,x_3)$ under evaluation by the three covectors. Each relation is supplied as a table.

A sort-preserving relational isomorphism gives a bijection of blocks and an additive isomorphism on each dual block. Such a map is $\mathbb F_3$-linear, and its source and target block dimensions agree. Each extra point must follow its associated block. The three resulting linear maps $\beta_i\colon V_i(T)^*\to V_i(S)^*$ satisfy
$$
 S(\beta_1 x_1,\beta_2 x_2,\beta_3 x_3)=T(x_1,x_2,x_3)
$$
on the tagged block vectors, thus everywhere by trilinearity. Setting $g_i=\beta_i^{-\mathsf T}$ yields exactly a block-preserving original transporter from $T$ to $S$. Every such transporter gives the corresponding relational isomorphism.

## Compute the three signs from those permutations

Order blocks by dimension, breaking ties in any deterministic way within each input. Choose an ordered basis of each dual block and enumerate its vectors in the common lexicographic coordinate order. In $\Omega_i$, list the vector points first, in block order, and then the extra points in the induced block order. Write $B_T,B_S$ for the change-of-basis matrices from the resulting ordered block bases of the two dual mode spaces to the original dual coordinate bases.

In dimension $d$, the sign of the permutation of all $3^d$ vectors induced by an invertible linear map equals its determinant, identified with a sign. Transvections have cycles of length $1$ or $3$ and generate the determinant-one subgroup. Negating one basis coordinate makes $3^{d-1}$ transpositions, an odd number. This proves the claim also in dimension one.

A swap of two blocks of equal dimension $d$ contributes $(-1)^d$ to the dual determinant and $-1$ to the permutation of the vector points since each block has odd cardinality. The permutation of the extra points contributes one more $-1$ exactly for swaps of even-dimensional blocks. Different dimensions never cross the corresponding dimension runs. Hence for the induced point permutation $\pi_i$ the determinant in original coordinates is
$$
 \det g_i=\det\beta_i=(\det B_S/\det B_T)\operatorname{sgn}(\pi_i).
$$
This identity calibrates the prescribed determinant sign independently in each mode.

## Compile the parity tests over the binary field

For an ordered point set $\Omega$, let $W$ have basis $e_{xy}$ for ordered distinct pairs. Let $E$ have basis $e_{xy}+e_{yx}$, one for each unordered pair, and let $E_0\subset E$ be the kernel of summing the coefficients in that basis. These two subspaces are intrinsic to the action of the full permutation group. Over $\mathbb F_2$, use the marker
$$
 v=\left[\sum_{x<y}e_{xy}\right]\in W/E_0.
$$
On sending one ordered point set to another, the image of the source marker differs from the target marker by the sum of one pair-sum per inversion, taken modulo $E_0$. For an even permutation this is zero. For an odd permutation it is the class of any one pair-sum. Thus either parity is imposed by a single point mark on the target quotient. A point set of size less than two has only the even possibility and is handled directly.

To realize this as a linear tensor system, attach to each named point or label set $X$ the algebra with coordinatewise multiplication $\mathbb F_2^X$. Its primitive idempotents are the coordinate vectors, so preserving the algebra is exactly permuting $X$. Encode a relation $R\subset X\times Y\times Z$ by the tensor whose coefficient on a triple is its membership bit, and use the analogous rank-one and rank-two markings for unary and binary relations. Link the point algebra to $W$ by the bilinear map that sends a pair of distinct coordinate vectors to $e_{xy}$ and sends equal pairs to zero. Surjectivity forces the induced action on $W$. The quotient map forces the action on $W/E_0$; its kernel is preserved under every permutation. Mark the required vector via a fixed scalar line with its basis pinned. Repeat independently in all three modes.

There are a fixed number of named spaces and maps, each of order at most three after dualizing as needed. The tensor-system compiler gives one ordinary binary 3TI instance. Each $\Omega_i$ has at most $\sum_j (3^{d_{ij}}+1)$ points, polynomial in $L$ because $d_{ij}\le C\log L$. Both the relation tables and the ordered-pair spaces have polynomial size, as do their dense tensor encodings. [Tensor-system compilation](https://arxiv.org/abs/1810.09219), [reduction framework](https://arxiv.org/html/2306.03135v2).

## One source of decompositions from raw tensors

For concise tensors the centroid consists of the triples $(a_1,a_2,a_3)$ whose three separate actions on the tensor coincide. Solve these linear equations. The centroid is a commutative algebra and each projection is faithful. In detail, for two triples $a,b$ and three distinct modes, the action $a_i b_i$ on $T$ can be moved to $a_i b_j$ on $T$, which equals $b_j a_k$ on $T$, and then $a_k b_k$ on $T$. The same moves with $j,k$ exchanged establish equality in all modes. Moving the last $b_k$ to $i$ gives $b_i a_i$ on $T$. Conciseness converts equality on $T$ to equality of endomorphisms in each mode. This proves closure, commutativity and faithfulness.

The primitive idempotents give a covariant direct-sum decomposition in every mode. To recover them in polynomial time, solve $x^3=x$ in the centroid, a linear equation over $\mathbb F_3$. In every local factor a solution reduces to an element of $\mathbb F_3$, and it equals that element because a nilpotent $u$ with $u^3=u$ is zero. The solution subalgebra is therefore a product of copies of $\mathbb F_3$. Starting from the identity, refine its idempotents using the three indicators $1-(x-\lambda)^2$ for each basis element $x$ of this subalgebra and $\lambda\in\mathbb F_3$. The basis separates all coordinates of the product, so the resulting nonzero pieces are exactly the primitive idempotents. Their images in the three modes are the required blocks. When all three recovered maximum dimensions meet the logarithmic bound, the binary compiler applies directly to the raw tensors. A transporter preserves the centroid by conjugation, so a pair with a mismatch of recovered block sizes can be rejected during preprocessing.

This example gives a testable family. The theorem with supplied block decompositions also permits arbitrary cross-block terms of the tensor. Its binary output field matters for the parity quotient, which uses $e_{xy}-e_{yx}=e_{xy}+e_{yx}$.
