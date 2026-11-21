# The original FGS rank markers do not admit a bounded-degree PC reverse simulation in fixed positive characteristic

**Theorem.** Over any field of fixed characteristic \(p>0\), exact partition erasure in Futorny–Grochow–Sergeichuk, Lemma 2.2, can turn a constant-degree ordinary Polynomial Calculus nonisomorphism refutation into an instance requiring linear degree in the matrix side length. This holds with just two one-dimensional third-axis blocks and with the other two axes unpartitioned. Thus the original block-tensor-to-tensor compiler is not reversible by a constant-degree PC simulation in that characteristic. This answers the general small-characteristic original-gadget question left open in the earlier proof-transfer note. [FGS, Lemma 2.2 and Section 2.4](https://arxiv.org/pdf/1810.09219#page=17) · [Prior good-characteristic simulation](https://github.com/Dugongue/MathProofs/blob/main/MixedTensorDegenerations/PC-TRANSFER.md)

### Two partitioned pencils with a degree-six separation

Take \(q=p^k\) with \(k\ge1\), and set \(L=2q-1\). For \(0\le d\le L\) write \(P_d=\operatorname{diag}(I_d,0_{L-d})\). Use the two data pencils
\[
 A=(P_{q-1},I_L-P_{q-1}),\qquad B=(P_q,I_L-P_q).
\]
The third-axis transporter in the partitioned instance is diagonal, with nonzero scalars and witnessed inverses. Its first-slice equation is \(\lambda X P_{q-1}Y^{\mathsf T}=P_q\). Apply Galesi–Grochow–Pitassi–She Proposition 3.1 to this first slice, regarding \(\lambda Y\) as the right witness. The two ranks differ by \(1\). In the degree-three matrix-equivalence refutation, substitute \(\lambda Y\) and \(\lambda'Y'\) for that witness and its inverse. The matrix inverse axioms for these substitutions follow from the original inverse identities by
\[
 \lambda\lambda' YY' - I=\lambda\lambda'(YY'-I)+(\lambda\lambda'-1)I,
\]
and likewise in the other order. The substitution uses monomials of degree at most two, so the resulting PC refutation has degree at most six. [GGPS, Proposition 3.1](https://arxiv.org/html/2305.19320#S3.SS1)

### The original augmentation has a hard slice swap

The FGS augmentation uses \(r=\min(L,L)+1=2q\), with identity marker blocks of sizes \(r\) and \(2r\) in the first and second slices respectively. This is the specialization of their displayed augmentation to one slice in each block. Both augmented pencils consist of two complementary diagonal projections after a fixed simultaneous reordering of their row and column coordinates. The ranks of the source projections are
\[
 (3q-1,5q),
\]
and those of the target projections are
\[
 (3q,5q-1).
\]
The common matrix side is \(8q-1\). The first two axes have only one block already, so there is no additional partition to erase in the full block-tensor reduction.

Put \(a=5q-1,\ b=3q-1\), and start with \(UV=I_a,\ VU=I_b\), where \(U\) is \(a\)-by-\(b\) and \(V\) is \(b\)-by-\(a\). Order the source spaces by its first and then second projections, and the target spaces by its second and then first projections. Define
\[
 F=\operatorname{diag}(U,V\oplus[1]),\qquad
 G=\operatorname{diag}(V,U\oplus[1]).
\]
Thus \(F\) goes from the source to the target and \(G\) from target to source, with the two complementary projection spaces matched in the swapped order. Every entry of \(FG-I\) and \(GF-I\) is zero or an entry of one of the original rectangular inverse defects. For source projection \(\widetilde A_i\) and target projection \(\widetilde B_{\sigma(i)}\), with \(\sigma=(1\;2)\), the block supports give the polynomial identity \(F\widetilde A_i=\widetilde B_{\sigma(i)}F\), independently of the inverse equations.

In ordinary tensor variables use \(F\) and \(G^{\mathsf T}\) as the first two witnesses, \(G\) and \(F^{\mathsf T}\) as their witnessed inverses, and the swap permutation matrix as both the third witness and its inverse. In the slice convention \(\sum_i Z_{ji}X\widetilde A_i Y^{\mathsf T}=\widetilde B_j\), the resulting action defect in slice \(\sigma(i)\) is exactly
\[
 F\widetilde A_i G-\widetilde B_{\sigma(i)}
 =\widetilde B_{\sigma(i)}(FG-I).
\]
Thus every image axiom has a derivation of degree at most two from the rectangular inverse axioms. All substitutions are coordinate variables or constants.

The gap \(a-b=2q\) is divisible by \(q\) and \(2(q-1)\le b\). The rectangular reduction to Riis's Boolean bijection system gives degree at least \(q\) for the rectangular inverse equations, as proved in the companion matrix-conjugacy note. Equivalently, substitute \(U_{ij}=V_{ji}=z_{ij}\) in the same display and apply Riis's Lemma 14.1 with \(D=q-1\). A degree below two is already impossible for the rectangular system, so \(q=2\) causes no edge-case exception. Any refutation for the ordinary augmented tensor system gives a rectangular refutation by the displayed substitutions, with the degree bound preserved once it is at least two. Hence the augmented refutation degree is at least \(q=\Omega(8q-1)\). [Riis, Lemma 14.1](https://arxiv.org/pdf/2611.07280#page=62)

This contradicts the consequence of any uniform constant-degree reverse PC simulation, since such a simulation would transfer the degree-six refutations of the partitioned systems to bounded-degree refutations of their ordinary outputs. For a fixed finite field, the lower bound also survives adding field equations to the ordinary output. After the complete substitution to Boolean \(z_{ij}\), each field axiom is derivable from \(z_{ij}^2-z_{ij}\) in degree at most the fixed field cardinality, and for all sufficiently large \(q\) this cost is at most \(q-1\).

This is a paper proof. The example concerns the exact partition-erasure gadget on arbitrary partitioned instances. The GP159 comparison asks about the images of two specific graph reductions, which are outside this example.
