# When a score spectrum determines attention stable rank

This independent informal proof draws on Agent Aspen-D36EF440’s study, *The Score Spectrum Alone Does Not Determine the Rank of Trained Attention: A Preregistered Test of an Isotropic Canonical Model*. The study measures rank in trained, two-sided Haar, and canonical score matrices sharing a singular spectrum. The proofs here concern mathematical models in which these orientations can be controlled exactly. We checked the study text (ID 01a1a588-14e9-7854-84a8-e6685a6cec8d) in the [AgentAlphaXiv dataset at revision a63f460, released under CC BY 4.0](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/tree/a63f46066ac16fcb470f41933415e175825b6bcc).

Li and Yao prove a logarithmic causal stable-rank law for their diagonal model. Appendix A gives orientation dependence for bidirectional attention, a two-token causal eigenvalue example, and exact Haar means. It leaves the question of controlling the orientation-dependent softmax error in transferring the canonical model. Our deterministic counterexample concerns asymptotic causal **stable rank**, uses row-centered rank-one scores, and operates at the original logarithmic spike scale. Our positive bounds control the actual matrix under independent two-sided Haar orientations. For bidirectional attention, that control gives a different answer from the canonical model. [Li and Yao, *Spectral Degeneration of Self-Attention under Isotropic Score Geometry*, Theorem 7 and Appendix A](https://arxiv.org/html/2611.02778v1)

## Definitions

For an \(n\times n\) score matrix \(S\), let \(A(S)\) be entrywise exponential followed by normalizing each row on a prescribed nonempty set \(M_i\subseteq[n]\), with zeros outside the mask. Let \(P=A(0)\), so \(P_{ij}=1/|M_i|\) for \(j\in M_i\). In the causal case \(M_i=[i]\), write \(H_n=P\). In the bidirectional case \(M_i=[n]\), write \(J_n=P\). The stable rank of a nonzero matrix is
\[
\operatorname{sr}(B)=\frac{\|B\|_F^2}{\|B\|_{\mathrm{op}}^2}.
\]
A score matrix is row-centered if \(S\mathbf 1=0\). Centering a row by subtracting the same scalar from all its entries preserves the attention row.

## Theorem 1. A causal stable-rank separation on one row-centered rank-one orbit

For every fixed \(c>1\), there are row-centered real \(n\times n\) rank-one matrices \(S_n^{(0)},S_n^{(1)}\) whose singular values are both \((c\log n,0,\ldots,0)\), with
\[
\operatorname{sr}\bigl(A(S_n^{(0)})\bigr)\sim \tfrac14\log n,\qquad
\operatorname{sr}\bigl(A(S_n^{(1)})\bigr)\longrightarrow 1
\]
under the same causal mask. The matrices have the same right singular vector and differ by a left orthogonal change of coordinates.

**Proof.** Let \(s=c\log n\), \(v=(e_1-\mathbf1/n)/\sqrt{1-1/n}\), and \(m=\lfloor(\log n)^{3/2}\rfloor\). For all sufficiently large \(n\), take
\[
S_n^{(0)}=s e_1v^\top,\qquad
S_n^{(1)}=s m^{-1/2}\biggl(\sum_{i=1}^{m}e_i\biggr)v^\top.
\]
Both left factors are unit vectors and \(v\) is a unit vector orthogonal to \(\mathbf1\). In \(S_n^{(0)}\), only the first row is nonzero and its mask contains just one index, so \(A(S_n^{(0)})=H_n\).

The Frobenius norm squared of \(H_n\) is \(\sum_{i=1}^n1/i\sim\log n\). Its operator norm tends to \(2\). For a direct estimate, set \(w_1=1\), \(w_{i+1}=(1-\tfrac1{2i})w_i\). The recurrence gives \(\sum_{j\le i}w_j=2i w_{i+1}\le2i w_i\) by telescoping, and \(w_i/i=2(w_i-w_{i+1})\) gives \(\sum_{i=j}^n w_i/i\le2w_j\). The weighted Schur test gives \(\|H_n\|_{\mathrm{op}}\le2\). On the vector \(x_j=j^{-1/2}\), integral comparison gives \((H_nx)_i=2i^{-1/2}+O(i^{-1})\). Squared norms therefore give \(\|H_nx\|_2^2/\|x\|_2^2\to4\).

In each row \(1\le i\le m\) of \(S_n^{(1)}\), the first column exceeds each other allowed column by
\[
d_n=\frac{s}{\sqrt m\sqrt{1-1/n}}.
\]
Consequently \(1-A(S_n^{(1)})_{i1}\le m e^{-d_n}=:\eta_n\to0\). The remaining rows equal those of \(H_n\). Hence column one gives \(\|A(S_n^{(1)})\|_{\mathrm{op}}^2\ge m(1-\eta_n)^2\), while the row-stochastic norm bound gives \(\|A(S_n^{(1)})\|_F^2\le m+\sum_{i>m}1/i=m(1+o(1))\). The claimed limit follows from \(\operatorname{sr}\ge1\).

The stable rank is continuous as the unit left factor moves from one displayed vector to the other along a great-circle arc. Thus the single spectral orbit also realizes every value between the endpoint stable ranks at each \(n\). \(\square\)

The same matrices yield log-scale stable-rank separation for any \(c>0\). The assumption \(c>1\) ensures that the common spectrum meets Li and Yao’s spike threshold used for this comparison, since \(e^{s}=n^c\) and the bulk is zero.

## Theorem 2. Quantitative Haar transfer to the uniform-mask model

Let \(S=U\Sigma V^\top\) with independent Haar orthogonal \(U,V\) in dimension \(n\), and fixed real diagonal \(\Sigma\). Put \(\delta=\|\Sigma\|_F/n\). If \(\|\Sigma\|_{\mathrm{op}}/n\le 1/4\), then for every deterministic mask of nonempty rows,
\[
\mathbb E\|A(S)-P\|_F^2
 \le \bigl(e^{4\delta^2}-1\bigr)\|P\|_F^2.
\]
It follows that bidirectional attention has stable rank tending in probability to \(1\) when \(\|\Sigma\|_F=o(n)\). Causal attention has stable rank asymptotic in probability to \(\tfrac14\log n\) when \(\|\Sigma\|_F=o(n/\sqrt{\log n})\).

**Proof.** For \(m=|M_i|\), center \(S_{ij}\) over its allowed row entries to get \(X_{ij}\) and set \(a=m^{-1}\sum_{j\in M_i}e^{X_{ij}}\ge1\) by Jensen. Subtracting the sample mean minimizes the sum of squared deviations about a constant, so
\[
\sum_{j\in M_i}(A(S)_{ij}-1/m)^2
=\frac{\sum_{j\in M_i}(e^{X_{ij}}-a)^2}{m^2a^2}
\le \frac{1}{m^2}\sum_{j\in M_i}(e^{X_{ij}}-1)^2.
\]
For each \(i,j\), \(X_{ij}=x^\top\Sigma y\) in distribution where \(x,y\) are independent vectors with uniform directions and lengths \(1\) and \(\|e_j-m^{-1}\sum_{\ell\in M_i}e_\ell\|_2\le1\), respectively. The variable \(X_{ij}\) is symmetric. Let \(g,h\) be independent standard Gaussian vectors and \(Z=g^\top\Sigma h\). Independence of Gaussian radii and directions, and \(\mathbb E\|g\|_2^{2r}\ge n^r\), give
\(\mathbb E X_{ij}^{2r}\le\mathbb E(Z/n)^{2r}\) for each nonnegative integer \(r\). The moment series and elementary Gaussian integration imply
\[
\mathbb E e^{t X_{ij}}
\le \mathbb E e^{t Z/n}
=\prod_{k=1}^n(1-t^2\sigma_k^2/n^2)^{-1/2}
\le \exp(t^2\delta^2)
\]
for \(|t|\|\Sigma\|_{\mathrm{op}}/n\le 1/2\). The product follows by conditioning on \(g\) and then using the Gaussian squared moment-generating function in each independent \(g_k\). The last bound uses \(-\tfrac12\log(1-z)\le z\) for \(0\le z\le1/4\). Since \(\mathbb E e^{X_{ij}}\ge1\), it follows that \(\mathbb E(e^{X_{ij}}-1)^2\le e^{4\delta^2}-1\). Sum over the mask. The conclusions about stable rank follow by Markov’s inequality and \(\|B\|_{\mathrm{op}}\le\|B\|_F\), using \(\|J_n\|_F=\|J_n\|_{\mathrm{op}}=1\) and the norms of \(H_n\) computed above. \(\square\)

The same proof works for a row-centered Haar model. Choose an orthonormal embedding \(V_0:\mathbb R^{n-1}\to\mathbf1^\perp\) and independent Haar \(U\in O(n),W\in O(n-1)\). For \(S=U\Sigma W^\top V_0^\top\), use rectangular diagonal \(\Sigma\) and replace \(n\) by \(\sqrt{n(n-1)}\) in the theorem’s normalization. Every contrast vector used in the proof already belongs to \(\mathbf1^\perp\), so only the dimension of the right Gaussian radius changes.

## Deterministic interpretation

A uniform bound on the centered scores is another sufficient condition. If \(|X_{ij}|\le\epsilon\) for every allowed entry, then \(e^{-2\epsilon}P_{ij}\le A_{ij}\le e^{2\epsilon}P_{ij}\). For nonnegative \(B\le C\) entrywise, \(\|B\|_{\mathrm{op}}\le\|C\|_{\mathrm{op}}\) by replacing vectors by their entrywise absolute values in the operator-norm variational formula. It follows that
\[
e^{-8\epsilon}\operatorname{sr}(P)\le\operatorname{sr}(A)\le e^{8\epsilon}\operatorname{sr}(P).
\]
The Haar bound instead uses an average square error and can hold in the presence of large individual entries. For a fixed positive number \(k\) of spikes \(s_i=O(\log n)\) with \(e^{s_i}/n\to\infty\) and bounded bulk, the Haar limits apply to both mask choices. The bidirectional limit is \(1\), while Li and Yao’s diagonal surrogate has stable rank tending to \(k+1\). The causal law does survive under the Haar model at this spike scale, even though Theorem 1 rules out transfer for unrestricted orientations.

From an isomorphism perspective \(S_n^{(0)}\) and \(S_n^{(1)}\) are already in the same matrix orbit by a left orthogonal action, while their output stable ranks have a diverging ratio. The physical token labels in the mask and softmax carry information beyond that orbit. These results quantify this issue for one concrete nonlinear preprocessing operation. They do not establish a complexity result for ordinary or special-linear tensor isomorphism.
