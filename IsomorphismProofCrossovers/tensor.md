# Balanced order reduction for orthogonal and unitary tensor isomorphism

**Status.** Informal proof. The quantitative reduction and its field-uniform scope below are the claims presented for review. The fixed-order qualitative reduction for real orthogonal and complex unitary groups was already established by Chen, Grochow, Qiao, Tang and Zhang.

## Theorem

Let $K$ have an involution $x\mapsto\bar x$, allowing the identity, and let $G_m(K)=\{g\in\mathrm{GL}_m(K):\bar g^Tg=I\}$. Consider ordinary ordered $d$-tensor isomorphism for $d\ge3$ under independent copies of $G_{n_i}(K)$, on input dimensions $n_1,\ldots,n_d>0$. For any split of the modes into three nonempty groups, there is a uniform constant-free coordinate projection into ordinary 3-tensor isomorphism for these same form groups. It preserves and reflects isomorphism for every pair of input tensors of the given format. If $n_i\le n$ for $n\ge2$, the balanced split gives total output dimension at most $C n^{\lceil d/3\rceil}$, with an absolute constant independent of $K$, $d$, and $n$. For a three-way split with every $n_i\ge2$, the more precise bound is $O(N_1+N_2+N_3)$, where $N_j$ is the product of the dimensions in group $j$.

The formula for each output coordinate is zero, one, or a copy of one input coordinate. The layout is computable in deterministic polynomial time in the explicit dense input size, even when $d$ varies. The result includes standard bilinear orthogonal groups in characteristic two, standard unitary groups over finite fields, and compact complex unitary and real orthogonal groups.

In particular equal dimensions and $3\mid d$ give $O(n^d)$ output coordinates. For fixed local dimension, including qubits, the bound is also $O(n^d)$ for all $d$. In the complex case unit vectors can be sent to unit vectors by a single normalization factor depending only on the format. This gives an exact reduction of many-party local-unitary equivalence to tripartite local-unitary equivalence with the same coordinate bound.

## 1. Linear size removal of a constant number of blocks

First consider three spaces as orthogonal direct sums of named standard coordinate blocks. The restricted action uses one independent form isometry on each block. Let $N$ be the total dimension and $b$ twice the number of named blocks. Introduce two marker slices per block, consecutively numbered $j=1,\ldots,b$. Put $M=N+b+1$ and $s_j=M+N+j$. To mark a block $B$ in mode $i$, create a private row block $R_j$ of dimension $s_j-\dim B$ in mode $i$, a partner block $D_j$ of dimension $s_j$ in mode $i+1$, and a tag line $Kz_j$ in mode $i+2$, with mode indices cyclic. These are standard coordinate blocks and all new blocks are disjoint. Add the identity tensor between $B\oplus R_j$ and $D_j$, tensored with $z_j$.

For each mode, the covectors annihilating that mode's tag space are precisely the covectors whose contraction has rank less than $M$. In fact the core tensor contributes rank at most $N$, and every marker that survives such a contraction has a tag in an uncontracted mode and contributes rank at most one. In the other direction, any nonzero tag coefficient gives a private submatrix scalar times the identity of size $s_j-\dim B\ge M$. Other slices vanish there. The dual form isometry therefore preserves the tag annihilator and its orthogonal complement, the covectors supported on the tags. This uses nondegenerate coordinate summands and is valid for isotropic ambient forms.

Within the tag-supported covectors a single tag's rank is $s_j<2M$. Two or more nonzero tag coefficients give rank at least $2M$ on two disjoint private row and column blocks. The cross blocks there are zero. Thus each tag line is intrinsic, and the distinct ranks $s_j$ distinguish its label. The image support in the marked mode of the slice at tag $j$ is exactly $B\oplus R_j$. Intersecting the supports of the two markers for $B$ recovers $B$. Every isomorphism of the enlarged tensors preserves all the named blocks, and projection to the original core spaces recovers a restricted isomorphism. This projection commutes with a form isometry preserving the named blocks, since it also preserves their orthogonal complements.

Conversely, extend a restricted isomorphism by the identity on all $R_j$ and tag lines, and by $\overline{g_B\oplus I_{R_j}}$ on $D_j$, where $g_B$ is the action on the marked block. The marker is fixed since $g\bar g^T=I$ for a form isometry. This proves exact equivalence. The total added dimension is $O(b(N+b))$, which is $O(N)$ when the number of blocks is a fixed constant. All marker entries are zero or one. This is the rank-based block removal from the previous linear-length classical-actions construction, given here in full.

## 2. A small collection of block-structured tensors

For each of the three groups of modes, list its leaf spaces $U_1,\ldots,U_r$ in the chosen order. Define $P_k=U_1\otimes\cdots\otimes U_k$ with the standard product basis. Use the same named summand for $P_1=U_1$, and separate named summands for later prefixes. All names in distinct groups are separate. Let $V$ be the standard orthogonal direct sum of the leaf spaces and the prefixes $P_k$ for $k\ge2$ across all three groups. Enumerate its named summands as $V_a$ for $a=1,\ldots,s$. Let $L$ be the standard coordinate space with basis $\ell_1,\ldots,\ell_s$. The superscript $\flat$ below denotes a standard coordinate copy of a space, eventually forced to carry the conjugate action. The copies are initially independent named blocks.

Use the following layout:

| Mode | Named blocks |
| --- | --- |
| 1 | $V_1^{\rm role}$, $L_1$, $Ka_1$ |
| 2 | $V_2^{\rm role}$, $V_2^{\flat}$, $L_2^{\flat}$, $Ka_2$ |
| 3 | $V_3^{\rm role}$, $V_3^{\flat}$, $L_3$, $Ka_3$, $Kb_3$ |

The superscript $\rm role$ distinguishes a full copy of $V$ from the individually named summands $V_a$. All source-dependent and fixed tensors below occupy distinct triples of these twelve named blocks.

Include $a_1\otimes a_2\otimes a_3$ and $a_1\otimes a_2\otimes b_3$. An isomorphism scales the three $a_i$ by norm-one elements $t_i$ with $t_1t_2t_3=1$. The $b_3$ scale is $t_3$. Divide every block action in mode $i$ by $t_i$. Isometry is preserved, and the transformed full tensor is unchanged because the product of the three factors is one. After this normalization the four pin lines have action one.

To connect two equal-dimensional blocks in distinct modes, put the identity tensor between them times the pin $a_i$ of the remaining mode. The normalized action fixes this wire exactly when the two block maps $X,Y$ satisfy $XY^T=I$, or $Y=\bar X$. Use wires for the pairs

$$
(V_1^{\rm role},V_2^\flat),\quad
(V_3^{\rm role},V_2^\flat),\quad
(V_2^{\rm role},V_3^\flat),\quad
(V_1^{\rm role},V_3^\flat),
$$

and for $(L_1,L_2^\flat)$ and $(L_3,L_2^\flat)$. Therefore the three $V^{\rm role}$ actions agree at a single $g\in G(V)$, and both flat copies have action $\bar g$. Likewise $L_1,L_3$ have a common action $h\in G(L)$ and $L_2^\flat$ has $\bar h$.

Let $J\ell_a=\ell_{a+1}$ for $a<s$ and $J\ell_s=0$. Encode the matrix $J$ in $L_1\otimes L_2^\flat$, times $b_3$. Encode $\ell_1$ in $Ka_1\otimes Ka_2\otimes L_3$. These entries impose $hJh^{-1}=J$ and $h\ell_1=\ell_1$. Since the $J^j\ell_1$ form the prescribed basis, $h=I$. The shift uses no distinct field elements.

Use the block triple $V_1^{\rm role}\otimes V_2^\flat\otimes L_3$ for the tensor $\sum_a E_a\otimes \ell_a$, where $E_a$ is the coordinate projection matrix onto the summand $V_a\subseteq V$. It forces $gE_ag^{-1}=E_a$ for every $a$. Thus $g$ acts separately on each named leaf and prefix, even though the block remover in Section 1 only needed a constant number of blocks.

## 3. Product actions and the input tensor

In $V_1^{\rm role}\otimes V_2^{\rm role}\otimes V_3^\flat$, sum the tensors of the canonical identifications

$$
P_k\longrightarrow P_{k-1}\otimes U_k
$$

for every $k\ge2$ in all three groups. The third slot is dual under the normalized action, because $\bar g=g^{-T}$. Different identifications are on distinct named summand triples. Once preservation of $V_a$ is established, each summand equation is independent and reads

$$
g_{P_k}=g_{P_{k-1}}\otimes g_{U_k}
$$

using the product basis. Consequently the action on each of the three terminal prefix spaces is precisely the product of its independent leaf actions.

Reshape the input tensor to the product of the three terminal prefixes and put it in the triple of $V^{\rm role}$ blocks, with zeros elsewhere. This is the only input-dependent block triple. All fixed triples are disjoint from it and from one another. Hence a normalized restricted isomorphism of the core gives a source isomorphism. Conversely any source isomorphism extends to the prescribed prefix maps, which are form isometries because the forms on the prefixes are tensor products. Take $g$ to be the direct sum of these maps, use $\bar g$ on the flat copies, and let $h$ and the pins act identically. Every fixed tensor is preserved and the input-dependent tensor is carried correctly. Section 1 removes the partition and produces an ordinary 3-tensor.

## 4. Exact transporter recovery

The proof also lists all the freedoms introduced by the reduction. Each marker recovers both $B\oplus R_j$ and $D_j$ from its two slice supports. Once $B$ is recovered, its orthogonal complement inside $B\oplus R_j$ recovers $R_j$. For a chosen source transporter, the normalized core transporter is uniquely determined by the prefix actions, wires and rigid labels. Undo the normalization with arbitrary $t_1,t_2\in G_1(K)$ and $t_3=(t_1t_2)^{-1}$. For marker $j$, choose its tag-line scalar $u_j\in G_1(K)$ and any $r_j\in G_{\dim R_j}(K)$. If $g_B$ is the normalized map of its marked block in mode $i$, the identity pairing and tag scalar uniquely force the partner map on $D_j$ to be

$$
u_j^{-1}\overline{(t_i g_B)\oplus r_j}.
$$

Every choice gives a transporter and every transporter is given uniquely by these choices. Composition multiplies the parameters componentwise. In particular, for the output of a tensor $T$, its automorphism group is isomorphic to

$$
\operatorname{Aut}(T)\times G_1(K)^{b+2}\times\prod_j G_{\dim R_j}(K).
$$

The extra factor is determined solely by the format. This gives explicit recovery of a source transporter from any target transporter and a section given by setting all new parameters to the identity. Over finite fields the number of transporters therefore changes by the same known factor for every pair of the format.

## 5. Size, input model and prior work

In a group of at most $r=\lceil d/3\rceil$ leaves, their total dimension is at most $rn\le n^r$ for $n\ge2$, and the successive prefix dimensions sum to at most $2n^r$. All summands have positive dimension, so $\dim L\le\dim V$. Thus twelve blocks have total dimension at most a fixed multiple of $n^r$, independently of $d$. If each dimension is at least two, the prefixes in each group form a reverse geometric bound with final product $N_j$, and the sum of the leaf dimensions is at most their product for two or more leaves (and equals it for one). This gives the rectangular bound. Even for dimension-one leaves all named dimensions are at most the dense input coordinate count $P=\prod_i n_i$, so the total output dimension is $O(dP)$. Enumerating and filling the dense output takes polynomial time. The normalized complex quantum-state claim follows from the disjoint support of input entries and fixed entries and their common squared norm on unit inputs.

For a fixed finite field of cardinality $q$ and fixed $d\ge3$, the number of source orbits on equal sides $n$ is at least $q^{n^d-dn^2}$, since each local group has size at most $q^{n^2}$. Any object-wise kernel map into one fixed 3-tensor format of total dimension $s$ must distinguish these orbits, while its codomain contains at most $q^{s^3}$ tensors. This gives $s=\Omega(n^{d/3})$ as $n$ grows. Our upper bound attains this exponent when $3\mid d$.

Theorem 1.7 of Chen–Grochow–Qiao–Tang–Zhang gives the qualitative transport from fixed-order orthogonal and unitary TI to order three over the reals and complexes. Their proof in Section 6 reports $O(d^2 n^d)$ for its intermediate path-algebra quotient dimension, rather than as a final three-tensor side bound. This construction gives a direct side bound with an absolute constant and works for arbitrary involutive fields in the standard-form input model. It combines the named projections and prefix products of the balanced ordinary reduction with the earlier rank markers and pin wires for form groups. The bound at fixed $d$ uses $\lceil d/3\rceil$. A targeted search did not establish publication priority.

An exact finite check used a 4-tensor of shape $3\times2\times2\times2$ over $\mathbb F_4$, with the first two factors grouped. It checked the twelve distinct fixed block triples under the product actions, including a nonmonomial unitary Fourier matrix on the first factor and nontrivial pin phases. Replacing the required product action on the first prefix by the identity failed the product constraint. The data block and the marker extension with a nontrivial tag scalar agreed with their formulas. This check tests specific identities; the all-input proof is above.

- [Chen–Grochow–Qiao–Tang–Zhang, classical groups, Theorem 1.7 and Section 6](https://arxiv.org/html/2306.03135v2)
- [Grochow–Qiao, linear-length general-linear reductions](https://arxiv.org/abs/2306.16317)
- [Balanced ordinary reduction](https://github.com/Dugongue/MathProofs/blob/main/BalancedOrdinaryReduction.lean)
