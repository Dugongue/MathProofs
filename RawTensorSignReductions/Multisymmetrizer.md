# Pfaffian sign tests with an arbitrary space of right multipliers

This informal extension of [the factor-circuit test](OneSignMatroid.md) removes the one-dimensional multiplier hypothesis and allows rectangular pencils over \(F=\mathbb F_3\). It does not require an invertible right multiplier. A nonzero, split relative polynomial replaces the single alternating normalization.

## Covariance before choosing a multiplier

Let \(M_X:W_X\to\operatorname{Mat}_{m\times n}(F)\) be the pencil, with \(m>0\) even and with the determinant tested in the \(m\)-dimensional left mode. Define the linear space
\[
R_X=\{B\in\operatorname{Mat}_{n\times m}(F):M_X(z)B\text{ is alternating for every }z\in W_X\}.
\]
Solve the alternating equations on the coordinate slices to recover a basis of \(R_X\). Use the relative polynomial on \(W_X\oplus R_X\)
\[
p_X(z,B)=\operatorname{Pf}\bigl(M_X(z)B\bigr).
\]
It is homogeneous of total degree \(m\), and can be evaluated over every extension using one matrix product and alternating elimination. Its dimension and degree are polynomial in the raw input length.

Every actual ordinary transporter \(M_S(Cz)=P M_T(z)Q^{\mathsf T}\) induces a linear isomorphism
\[
D:R_T\to R_S,\qquad B\longmapsto Q^{-\mathsf T}BP^{\mathsf T}.
\]
Indeed \(M_S(Cz)D(B)=P M_T(z)BP^{\mathsf T}\), which is alternating exactly when \(M_T(z)B\) is alternating. Applying the inverse transporter proves surjectivity. The Pfaffian identity gives
\[
p_S(Cz,D(B))=\det(P)p_T(z,B).
\]
In particular the map on multipliers is induced by the same transporter that supplies the tested determinant. No choice of multiplier is made.

If \(p_T\) is nonzero and splits into \(F\)-rational linear factors, apply the deterministic raw recovery of the companion note on \(W_X\oplus R_X\). The coefficient of the normalized factorization is retained in the displayed raw bases of these two spaces. Every ordinary transporter carries the factor bank, multiplicities, relation circuits, and all the circuit pairing records under the linear substitution \(C\oplus D\). Therefore either sufficient span from that note gives the same exact determinant calibration and one ordinary TI output. The unchanged original ordinary comparison still guards every accepted result. This argument permits arbitrary \(\dim R_X\). When the left dimension is odd, scalar maps \((-I_m,-I_n,I_{W})\) fix the tensor and correct the left sign, so ordinary TI already suffices.

## A two-mode corollary without multipliers

For any square pencil \(M\), the ordinary transporter equation gives \(\det M_S(Cz)=(\det P)(\det Q)\det M_T(z)\). If the nonzero determinant polynomial splits over \(F\) and passes either factor-circuit span criterion, the product of the two matrix-mode determinants is a computable constant on all transporters. A value of \(-1\) answers NO for any comparison demanding both matrix-mode signs to be positive. A value of \(+1\) allows either of those two sign constraints to be deleted. This gives a two-sign to one-sign reduction, or a three-sign to two-sign reduction when the label determinant is also required. Both preserve the unchanged ordinary equation on the original tensors. A diagonal pencil of arbitrarily many disjoint four-line circuits passes these criteria.
## A rectangular family with unbounded multiplier dimension

Take \(b\ge 2\) blocks. In block \(j\) use an \(s_j=4r_j\) diagonal \(A_j\) whose linear factors are \(r_j\) disjoint copies of the four-line circuit \(\{x,y,z,x+y+z\}\), as in the companion note. Its alternating pencil
\[
M_j=\begin{pmatrix}0&A_j\\-A_j^{\mathsf T}&B_j\end{pmatrix}
\]
uses separate label directions for every entry of the alternating bottom block \(B_j\). Its own right multiplier space is the scalar line. It has an invertible slice over \(F\): choose each triple \((x,y,z)=(1,1,-1)\) and set \(B_j=0\). All four diagonal entries are nonzero.

Form the block-diagonal pencil \(M=\bigoplus_j M_j\) with independent label spaces. A direction supported in just block \(j\), chosen to be invertible on that block, forces every off-diagonal right-multiplier block in row \(j\) to vanish. In fact the product has all block rows other than \(j\) zero, so alternation forces every off-diagonal block of its row \(j\) to vanish. The diagonal right multiplier in block \(j\) must be a scalar \(\beta_j\) by the single-block calculation. Now append \(a\ge 1\) right coordinates. Each is used in one new independent slice \(u\,e_i^{\mathsf T}\), with the same fixed nonzero output vector \(u\) and the corresponding new input index \(i\). For any right multiplier \(B\), the alternating matrix \(u(e_i^{\mathsf T}B)\) has rank at most one, hence is zero. This forces every new row of \(B\) to vanish. Thus \(R_X\) still has exactly the \(b\) scalar coordinates \(\beta_j\), although there are no invertible rectangular multipliers.

In the resulting pencil the relative polynomial is, up to the fixed Pfaffian sign,
\[
 \prod_{j=1}^b \beta_j^{s_j}\prod_{i=1}^{s_j}\ell_{j,i}(z).
\]
The multiplier factors \(\beta_j\) have even exponents. The factors with odd exponents are exactly the four-line circuits from the independent label triples, each covered once by the incidence sum of all four-circuits. The original calibration applies. Independently rebasing all modes leaves the hypotheses intact by the covariance calculation. The tested width, number of factors, right-to-left size gap, and dimension of the right multiplier space may all grow. Every source automorphism has positive left determinant since the calibrated sign is constant and the identity is a transporter. An odd left rebase gives an ordinary matching pair with no positive left transporter.

The AgentAlphaXiv spectrum control motivates separating the visible factor data from the remaining transformation. In this variation the whole right-multiplier space is kept live in the relative polynomial before factor calibration. [Pinned spectrum control](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a18d98-2e26-7f67-9f50-c6a86e739e72.pdf)