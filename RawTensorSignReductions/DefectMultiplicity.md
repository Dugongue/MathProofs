# The multiplicity width of Koszul defects

In the setting of [Koszul defect cancellation](LargeDefectKoszul.md), use \(m_{j,X},m_{j,Y}\) for the composition multiplicities of the natural simple \(F_j^{d_j}\) in the two tested raw modes. The pair-adjoint sign image is the binary span of their parity vectors. A factor unit contributes its determinant norm to the respective multiplicity powers. Every norm sign is attained and lifts across the nilpotent radical. When the image is a line, test its nonzero annihilating character in one signed output. When the image is full, use the zero character. The character test exactly means that a simultaneous source adjoint can correct both signs. [Exact sign projections](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/SignProjections.md)

If the image is zero, both raw multiplicities are even for every factor. Let \(r_j=r_{j,K}+r_{j,C}\) be the multiplicity in the two defects. The two exact sequences through the common image yield
\[
 r_j \equiv c\,m_{j,X}+\binom c2m_{j,Y}\equiv0\pmod2.
\]
Here the label spaces have trivial \(E\)-action.

Put \(G=\operatorname{gr}K\oplus\operatorname{gr}C\) as an \(E/J\)-module. Attach the direct sum \(U\) of one natural simple \(U_j\) for each factor, its multiplicity module \(W=\operatorname{Hom}_{E/J}(U,G)\), their algebra actions and their bilinear evaluation map. Their coordinates are obtained by deterministic matrix splitting as in the main proof. A transporter extends to a map \(u\) respecting the forced quotient isomorphism, because each transported natural simple is again natural simple. Evaluation forces \(f\mapsto g_Gf u^{-1}\) on \(W\), and hence the map on its intrinsic sum \(W_{\mathrm{odd}}\) over odd \(d_j\).

In compatible module coordinates the simple and multiplicity maps on factor \(j\) are \(h_j\sigma_j\) and \(b_j\sigma_j\) with the same center isomorphism \(\sigma_j\). Their induced determinant on the factor of \(G\) is
\[
 N(\det h_j)^{r_j}N(\det b_j)^{d_j}\det_F(\sigma_j)^{d_jr_j}.
\]
Even \(r_j\) kills the first and last powers. A different allowed choice of \(u\) differs by a field scalar on each simple module by Schur's lemma. Its inverse rescales the multiplicity map, adding only a scalar norm to an even power. The residual factor equals \(1\) for even \(d_j\), and \(\det_F(b_j\sigma_j)\) for odd \(d_j\). Factors may permute, but their blocks in \(G\) have even dimension, as do the blocks of \(W_{\mathrm{odd}}\), so both permutation determinants are positive.

For the frame calibration, choose separate grade-ordered bases on \(K,C\) by evaluation in the simple and multiplicity coordinates. Lift these through the radical flags and use the same image basis on both sides of the Koszul map, giving the factor \(\kappa_T\) of the main proof. Compute the permutation taking the combined grade basis of the two graded defects into factor-first evaluation order. Multiply its sign into \(\kappa_T\), obtaining \(\widetilde\kappa_T\). These operations are endpoint-local. The identity in raw tested bases is
\[
 \det g_X\det g_Y=(\widetilde\kappa_{T'}/\widetilde\kappa_T)
                      \det(g_{W_{\mathrm{odd}}}).
\]
The calibrated top exterior volume on \(W_{\mathrm{odd}}\) and the live sign on \(X\) test both signs on the same original transporter. This is polynomial if \(\sum_{d_j\text{ odd}}[F_j:F]r_j=O(\log(2+L))\), independently of the odd simple-module dimensions. A zero carrier requires just a frame-sign comparison before testing the live sign.

Grouping factors by the intrinsic keys \((d_j,[F_j:F],r_j)\) also works when each group's carrier is logarithmic. Use individual volumes and multiply their scalar actions with the bilinear prefix-product links of the [ordered width construction](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/AdjointGroups.md). The total storage stays polynomial even with many groups. This is a deterministic sufficient reduction on the stated domain.