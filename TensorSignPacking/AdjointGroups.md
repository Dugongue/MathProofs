# Packing adjoint determinants over many small intrinsic groups

This extends the [represented adjoint width reduction](Swaps.md). Keep its notation $E(T)$, $B=\prod_j M_{d_j}(K_j)$, $D$, $U$, $W$, and $R_j$. For each radical grade $i$, compute the multiplicity $M_{j,i}$ of the natural simple module of factor $j$ on $J^iV/J^{i+1}V$. Use the tuple
$$
b_j=(k_j,d_j,(M_{j,i})_{i\ge0})
$$
as a key. The vector stops at the last nonzero grade of the whole represented module. These integer keys and their lexicographic order are preserved by every raw transporter. For each distinct key $b$, put $R_b=\bigoplus_{j:b_j=b} R_j$. Let $w_{\max}$ be the maximum ground-field dimension of one $R_b$, or zero if all these spaces vanish.

**Theorem.** The signed comparison reduces to one ordinary TI instance when $w_{\max}=O(\log L)$, with no bound on $\sum_b\dim R_b$ other than the polynomial input bound. The reduction is deterministic. It does not assume that factors with the same key can individually be matched. One such comparison and one arbitrary one-sign comparison therefore pack into one one-sign instance.

Sort the factors by key on each side, with arbitrary deterministic order inside each key. Use that order for the determinant frames on $D$ and on the $R_b$, and for the calibration matrices $C_T,C_{T'}$ of the adjoint proof. If the two lists of key multiplicities differ, ordinary isomorphism is impossible. The determinant calculation in that proof holds on each group, including the block permutations inside the group. Hence every ordinary transporter and every compatible choice of lifts induces maps $r_b$ satisfying
$$
\det_{\mathrm{raw}}(a)
   =\det(C_{T'})\det(C_T)^{-1}\prod_b \det(r_b).
$$
The multiplication below uses exactly these factor-first frames. No permutation crosses keys.

## Local volumes and a single scalar condition

Build the graded-algebra diagram of the adjoint proof up to the stage containing $R=\bigoplus_bR_b$. Retain the group projections on $R$, and order the nonzero groups $b_1,\ldots,b_m$ by their keys. These projections can be constructed from the central idempotents of $B$: they are induced by the sums of those idempotents of each key on the $U$, $W$ and $Z(B)$ portions of $R$. Since the underlying diagrams force the actual algebra isomorphism and its graded map, the projections covary with the same original transporter.

For each $b_g$ construct $\Lambda R_{b_g}$ with its top line $H_g=\bigwedge^{\dim R_{b_g}}R_{b_g}$, and use the local wedge basis to choose the coordinate vector $h_g$. Across the two endpoint diagrams, $h_g$ maps to $\det(r_{b_g})h'_g$. The total dimension of these exterior algebras is at most $m2^{w_{\max}}$. Pack them in their product algebra, linking each degree-one inclusion and each top-line inclusion with group labels. Use the split ordered label algebra $F^m$ with directed successor shift on its coordinate idempotents, as in the adjoint proof. This fixes the group labels and the exterior factors. Any unital map on an exterior factor is determined by its action on the included degree-one generators.

Give $L_g$ for $0\le g\le m$ dimension one with chosen bases $e_g$. Take the bilinear maps $L_{g-1}\times H_g\to L_g$ sending $(e_{g-1},h_g)$ to $e_g$. They pack as one bilinear map on the indicated direct sums, with all other components zero. To prevent permutations in the first variable, output and inputs, attach the actions of the split ordered label algebra $F^{m+1}$ to these spaces and to the exterior factors, matching $H_g$ with label $g$. If an isomorphism sends $e_g$ to $\lambda_g e'_g$, preservation of the bilinear map is equivalent to
$$
\lambda_g=\lambda_{g-1}\det(r_{b_g}).
$$
Mark $e_0$ and $(\det C_T)^{-1}e_m$ and the analogously scaled terminal vector in the target. The first forces $\lambda_0=1$; the last then holds exactly when the raw tested determinant is one. If $m=0$, simply use the ordinary comparison when the frame signs match and a fixed negative instance otherwise.

These diagrams have a fixed number of sorts and linear or bilinear maps. Orthogonal projections for group and grade labels are each stored once as an action map, with the shift fixing the associated label idempotents. Two endpoint volume marks supply the only extra scalars. The ordinary bounded-order tensor-system compiler gives one instance, and its size and construction time are polynomial in $L+\sum_g 2^{\dim R_{b_g}}$. A true positive transporter extends by the unique required prefix scalars. In the reverse direction the diagram forces the original transporter and its raw sign. This reduction uses neither a matching oracle nor the sign of a supplied transporter. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

## Example separating the two size tests

For $t\ge2$, take pairwise labeled summands $K_i^{1\times2}$ over $K_i=\mathbb F_{3^i}$ for $1\le i\le t$, and take an extra summand $\mathbb F_3^{2\times h}$ for even $h=2^t$. On their direct sum $V$ use the slice algebra comprising all independent right multiplications by $M_2(K_i)$ on the former summands and by $M_h(\mathbb F_3)$ on the extra summand. The slice projections to the summands force the fixed-label adjoint projection to be block diagonal. Commuting with the central $K_i$ and the matrix units shows it is $\prod_i K_i\times M_2(\mathbb F_3)$ acting on the left. There is only one module grade. On $K_i$ the natural simple has multiplicity two, so its carrier has dimension $2i$. They have distinct keys. The extra summand supplies a factor with matrix degree two and even multiplicity $h$, so its carrier vanishes. Thus $w_{\max}=2t$ but the total width is $t(t+1)$. The dense input length has logarithm $\Theta(t)$ since its mode dimensions are polynomial in $h+\sum_i i$ and at least one is at least $h$. This example separates the width criteria themselves. The theorem also applies with nonzero radicals, as the keys and determinant products use the transported radical grades.

The unrestricted binary signed conjunction is outside the theorem. A scalar represented algebra on one large tested mode can give one group with full width. These are informal proofs.
