# Exact orientation transfer to the dual relation bimap

Over \(F=\mathbb F_3\) let \(\beta:X\times X\to Z\) be symmetric, spanning and radical-free. Write \(K=\ker(\operatorname{Sym}^2 X\to Z)\). In the cube-zero case \(n=\dim X\) is even, \(\dim Z\) odd, and the rectangular cubic has transporter sign \(\det g\det h\). [Exact cubic bridge](ExactCubicOrientationSeed.md) · [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

**Theorems.** Orientation transfers exactly to the output determinant of the dual relation bimap. Its centroid gives a one-instance compiler on the previously proved local-factor domains even if the original centroid is scalar. Conversely all ternary cube-zero comparisons reduce with exact signs to inputs where both bimaps have scalar centroid and the relations have full support.

## Relation duality

The perfect pairing of symmetric squares takes \(xy,\lambda\mu\) to \((\lambda(x)\mu(y)+\lambda(y)\mu(x))/2\). Restrict it to \(K\) to obtain \(\kappa:X^*\times X^*\to K^*\). Its output spans. If \(N\) is the common radical, put \(S=N^\perp\subseteq X\). Testing coefficients in an adapted basis gives \(K\subseteq\operatorname{Sym}^2 S\): every coefficient involving a direction outside \(S\) is detected by its covector in \(N\) and a second basis covector. Crop \(\kappa\) to \(S^*=X^*/N\).

A transporter \((g,h)\) induces \((g_S^{-T},k_g^{-T})\) on cropped \(\kappa\), where \(k_g=\operatorname{Sym}^2 g|_K\). Conversely a cropped transporter \((p,q)\) gives \(g_S=p^{-T}\) carrying \(K\) onto \(K'\) with restriction \(q^{-T}\), by the perfect pairing. Extend \(g_S\) on complements of matching dimension to obtain \(g\), and take the induced quotient map \(h\). This includes \(K=0\).

Frame calibration uses an adapted basis of \(\operatorname{Sym}^2X\) consisting of the displayed \(K\)-basis followed by lifts of the displayed \(Z\)-basis. Denote its determinant in the monomial basis by \(c_X\). Block triangularity gives \(\det h=(c_X/c_{X'})(\det g)^{n+1}/\det k_g\), using \(\det(\operatorname{Sym}^2g)=(\det g)^{n+1}\). The latter holds on diagonal maps, transvections and swaps, which generate GL. In even dimension the combined sign is therefore \((c_X/c_{X'})\det q\). For a general \((a,b)\) character the transformed weights are \((a+(n+1)b,b)\) modulo two and the frame factor to power \(b\). If support is proper and the transformed input weight is odd, a reflection on the complement fixes \(K\) and corrects the sign.

Apply the preceding centroid determinant theorem to the cropped relation bimap with weights \((0,1)\). Its local tests, including logarithmic output rank over the coefficient field, apply to its own primitive factors. Its signed assembly permits unlimited repeated types. If factors are intrinsically ordered, the product of their determinant lines also gives an exact record on each transporter. [Local criteria and signed assembly](CentroidDeterminantDescentSeed.md)


For an infinite sign-rigid example take \(X=\bigoplus_{i=1}^s X_i\), where \(\dim X_i=3\), \(s\ge6\), \(s\equiv2\bmod4\), and take \(K=\bigoplus_i\operatorname{Sym}^2X_i\). The quotient is the sum of universal cross products \(X_i\otimes X_j\), \(i<j\). Here \(n=3s\) is even, \(\dim Z=9\binom{s}{2}\) is odd, and \(\dim K=6s\). The common radical is zero by the cross products. Centroid balance on independent vectors in one block kills the off-block projections, and balance on cross products forces one common scalar. On the relation side there are \(s\) primitive universal symmetric-square factors: their centroids are scalar by the identity \((P x)y=x(P y)\) tested on basis vectors. Every local determinant is one by the exponent-four formula. Permuting the six-dimensional outputs is also even, so all original automorphisms have positive sign. A target output basis reflection gives ordinary YES and positive-sign NO. All three original dimensions grow.

## Simultaneously scalar centroids

Take four auxiliary spaces \(V_1,\ldots,V_4\) of distinct dimensions divisible by four and strictly larger than \(n\), at most \(n+16\). Set \(V_0=X\) and \(Y=\bigoplus_{i=0}^4 V_i\). Use the relation space
\[
 K^+=K\oplus\!\bigoplus_{\{i,j\}\in C_5} V_i\otimes V_j
\]
in \(\operatorname{Sym}^2Y\), where \(C_5\) is the five-cycle on the labels. The quotient uses the given \(Z\)-basis at label zero and all added natural tensor or symmetric-square bases in label order. The new input dimension is even and the new output dimension is odd: all added mixed dimensions and all auxiliary symmetric-square dimensions are even.

For a bimap with a relation space, the endomorphisms \(D\) of its input whose symmetric-square derivatives \(xy\mapsto(Dx)y+x(Dy)\) preserve its relations are a linear space conjugated by every transporter. For \(K^+\) these are block diagonal. For distinct \(i,j\) there is \(k\notin\{i,j\}\) adjacent to \(i\) and not \(j\) in \(C_5\). Apply a derivative to \(xy\), \(x\in V_i,y\in V_k\), and project to \(V_j\otimes V_k\), where there are no relations. This gives \((Dx)_j\otimes y=0\), hence kills every off-diagonal block. The same argument applies to the complementary cycle.


The derivative algebra contains the label-zero projector and the full endomorphism algebra on each auxiliary label. It is the product of the old derivative algebra and the four auxiliary matrix algebras. The auxiliary primitive central projectors have distinct ranks greater than \(n\), while those supported at zero have rank at most \(n\). Thus every transporter pins these labels and \(X\). Its quotient map restricts to the original map on label-zero products. Conversely every old transporter extends by auxiliary identities and the induced maps on the new outputs.

Both bimaps are radical-free by independent universal cross products along their respective cycles. For the relation bimap the mixed kernel blocks are exactly the complementary cycle. Consequently its derivative space is block diagonal too. In either bimap a centroid operator is a projected derivative, since its two actions add to twice its output action. Being block diagonal it must act by equal scalars at the endpoints of each universal cross product. Connectedness forces one scalar. This gives scalar centroids on both sides and full relation support.

Every new mixed output contributes each endpoint determinant to the even power given by the other endpoint's dimension. Each auxiliary input and internal symmetric-square output together give exponent \(1+\dim V_i+1\), also even. Thus the sign is exactly the original sign. The padding is polynomial and an ordinary compiler for simultaneous scalar centroids would settle the ternary question by the prior square-zero normal form. [Earlier scalar-centroid reduction](https://github.com/Dugongue/MathProofs/blob/main/TISLSquareZeroDirect/ScalarCentroid.md)
