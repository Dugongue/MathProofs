# Orthogonal tensor isomorphism over Galois rings of characteristic \(2^e\)

Let \(R=\operatorname{GR}(2^e,f)\) be given by explicit additive coordinates and ring multiplication. Write \(k=\mathbb F_{2^f}\), \(q=|k|\), and let \(e\ge1\) vary with the input. Given arbitrary same-sized matrices \(H,D\) over \(R\), the equations
\[
QH=D,\qquad Q^TQ=I
\]
admit deterministic polynomial-bit-time decision, exact counting, and construction of a witness on every yes-instance. Consequently the recognizable source domain in the [Problem 1.8 Lean development](https://github.com/Dugongue/MathProofs/tree/main/Problem18) lifts to independent orthogonal actions on free three-tensors over \(R\), with density \(1-O((1+\log b)/\sqrt b)\) where \(b\) is the median dimension and the absolute constant and threshold are independent of \(e\) and \(f\). Against each recognized source and every target, all three tasks again have deterministic polynomial bit-time. This is an informal extension of the Lean-checked density theorem.

## 1. Prescribed columns and precision

Unit-pivot and minimum-valuation Smith elimination on \(H\) produces a right change of columns \(W\) and an invertible square \(U\) such that \(H W\) has nonzero columns \(2^{a_i}u_i\), where the \(u_i\) are columns of \(U\) and \(0\le a_i<e\). Apply the same column change to \(D\). Its paired columns must be divisible by \(2^{a_i}\), and the columns paired with zeros must vanish. Divide the nonzero-column constraints by \(2^{a_i}\) and put \(b_i=e-a_i\). This gives
\[
Qu_i\equiv v_i\pmod{2^{b_i}},
\]
where \(v_i\) is chosen arbitrarily among the available lifts of the divided target. The \(\bar u_i\) are linearly independent in \(k^n\). Write a bar for reduction to \(k\). Dividing an element of \(2^a R\) means solving a linear congruence. When only its next residue digit is used, the result modulo \(2\) is unambiguous. The Smith calculation uses only these operations, unit inversion, and the fact that each ideal of this Galois ring is \(2^jR\).

A solution necessarily satisfies the input comparisons
\[
 u_i^T u_j\equiv v_i^Tv_j\pmod{2^{\min(b_i,b_j)}}\ (i\ne j),\qquad
 u_i^Tu_i\equiv v_i^Tv_i\pmod{2^{\min(e,b_i+1)}} .
\]
The last extra digit is intrinsic, since replacing \(v_i\) by \(v_i+2^{b_i}z\) changes its squared norm by an element of \(2^{b_i+1}R\) for \(b_i\ge1\). The same observation applies to the norm of the image of a vector under a matrix fixed modulo \(2^{b_i}\).

For \(e=1\), the residual group is the standard dot-product isometry group. For \(e\ge2\), start with the same residual test as in [the square-zero frame theorem](SquareZeroLocalRings.md), working over \(R/4R\) for the norm criterion. Precisely, the residue matrix \(Q_1\) must preserve the dot product, fix \(h=(1,\ldots,1)^T\), preserve \(P(x)=\sum_{i<j}x_ix_j\) if \(e\ge2\), and send \(\bar u_i\) to \(\bar v_i\). Indeed, norms of vectors reduced modulo \(2\) have well-defined values modulo \(4\). For dot-product isometries in the residue, preserving those values is equivalent to preservation of \(P\), by
\[
\tilde x^T\tilde x=\left(\sum_i\tilde x_i\right)^2-2\sum_{i<j}\tilde x_i\tilde x_j .
\]
The allowed residual extensions are decided, counted, and constructed by the marked symplectic or quadratic Witt procedure in Sections 1 and 3 of that proof. This uses polynomially many pairing equations and affine quadratic norm solves over \(k\).

## 2. One extra digit of norm precision

At stage \(t\), with \(1\le t\le e\), maintain a matrix modulo \(2^t\) which is orthogonal modulo \(2^t\), has the prescribed column images modulo \(2^{\min(t,b_i)}\), and preserves all squared norms modulo \(2^{\min(e,t+1)}\). The last condition is well-defined for a matrix modulo \(2^t\) by the one-digit observation in Section 1. Stage \(1\) has just been initialized. At stage \(e\) the requirements give an exact solution.

Fix a representative \(A\) of the stage \(t<e\) matrix. All lifts to stage \(t+1\) are obtained by right multiplication by \(I+2^t Z\), with \(Z\) taken modulo \(2\). First impose only orthogonality modulo \(2^{t+1}\) and the constraints on active columns, namely those for which \(b_i\ge t+1\). The required equations are
\[
Z+Z^T=-E,\qquad Z\bar u_i=w_i,\qquad
 E=(A^TA-I)/2^t\bmod2,\quad w_i=(A^{-1}v_i-u_i)/2^t\bmod2 .
\]
The norm lookahead makes the diagonal of \(E\) zero. Pairwise input comparisons verify each condition on the overlap of prescribed rows and columns, by expanding the Gram pairings to precision \(2^{t+1}\). Concretely, in a residue basis beginning with the active \(\bar u_i\), the columns of the bilinear form \(x^T Z y\) are prescribed on the active vectors, the transpose equation prescribes those rows, and their intersection is consistent by the comparisons. Solve the remaining off-diagonal pairs arbitrarily. Thus one solution always exists, and the entire solution space for the next matrix is obtained by starting with one such lift \(A'\) and right multiplying it by \(I+2^t W\), where \(W=W^T\) and \(W\) annihilates the active span \(V_t\). These symmetric matrices identify with all symmetric bilinear forms on \(k^n/V_t\).

If \(t+1=e\), this finishes the lift. Otherwise let
\[
g(x)=(\|A'\tilde x\|^2-\|\tilde x\|^2)/2^{t+1}\bmod2
\]
be the deficit at the extra norm digit. It is a well-defined function of \(x\in k^n\), since \(A'^TA'-I\) is zero modulo \(2^{t+1}\). Its matrix is symmetric, so \(g\) is a squared \(k\)-linear functional. It vanishes on the active span: each marked vector has the correct target modulo \(2^{t+1}\), and its extra norm digit agrees by the input comparison. The correction must cancel \(g\) on the quotient \(k^n/V_t\).

When \(t\ge2\), expansion gives the change in the norm digit as \(x^T W x\). In fact the cross term has a factor \(2^{t+1}\), while the quadratic correction has a factor \(2^{2t}\) and vanishes modulo \(2^{t+2}\). Every squared linear functional on the quotient occurs as \(x^T W x\), by prescribing the diagonal of a symmetric form in any quotient basis.

When \(t=1\), the quadratic correction survives and the change is instead
\[
F_W(x)=x^TWx+(h^TWx)^2.
\]
For this identity expand \(\|(A'(I+2W))\tilde x\|^2\) modulo \(8\), using \(A'^TA'=I\bmod4\); the square term is \((W x)^T(W x)=(h^T W x)^2\) in \(k\). Both terms descend to the quotient, and the image is characterized as follows. If the quotient image \(h_*\) of \(h\) is zero, \(F_W\) is an arbitrary squared linear functional, as above. If \(h_*\ne0\), take a quotient basis with first vector \(h_*\). For the symmetric matrix \(B\) in that basis one has
\[
F_W(h_*)=B_{11}+ B_{11}^2,\qquad F_W(e_i)=B_{ii}+B_{1i}^2\quad(i>1).
\]
Hence the image comprises exactly the squared linear functionals whose value on \(h_*\) has absolute trace zero. The target \(g\) satisfies that condition automatically. Because the residue matrix fixes \(h\), write \(A'h=h+2z\), using the all-ones lifts of \(h\). The norm difference divided by \(4\) modulo \(2\) at \(h\) is
\[
h^T\bar z+(h^T\bar z)^2 .
\]
Its trace is zero. Solve the resulting Artin–Schreier equation by \(\mathbb F_2\)-linear algebra. Thus every stage-\(t\) matrix has valid lifts that meet the next norm lookahead, including at the first nontrivial step. Older column constraints are preserved by the factor \(2^t\).

## 3. Lift counts and bit complexity

Let \(m=n-\dim V_t\). The lift counts per stage-\(t\) matrix are
\[
\begin{cases}
 q^{m(m+1)/2}, &t+1=e,\\
 2q^{m(m-1)/2},& t=1,\ t+1<e,\ h\notin V_t,\\
 q^{m(m-1)/2},& \text{otherwise}.
\end{cases}
\]
Indeed the free symmetric block before imposing the norm digit has size \(q^{m(m+1)/2}\). Its image on squared linear functionals has size \(q^m\), except for the trace-zero case where it has size \(q^m/2\). These counts are independent of the chosen stage matrix, with \(V_t\) fixed by the input. Distinct \(W\)'s give distinct matrices modulo \(2^{t+1}\), because \(A'\) is invertible. The product of these factors and the residual extension count is therefore exactly the number of solutions. The count has polynomial bit length since there are at most \(|R|^{n^2}\) matrices. There are \(e-1\) lift stages, and \(e\le \log_2|R|\). Every stage consists of polynomially many arithmetic operations, linear solves over \(k\) or \(\mathbb F_2\), and linear congruences in the additive coordinates.

For the application to tensors, the square-zero proof reduces the two outer factors to unit scalar root equations and the middle factor to precisely this frame problem. The root solver also extends to all precisions. Given a target unit square \(d\), the residue root is unique. For \(e\ge2\), the resulting square modulo \(4\) is independent of the lift and is checked first. At the first correction, multiplication by \(1+2z\) changes the square by its old value times \(4(z+z^2)\) modulo \(8\). Thus for \(e\ge3\) the next digit is an Artin–Schreier solve with zero or two solutions in \(k\). Subsequent multiplication by \(1+2^t z\), for \(t\ge2\) and \(t+1<e\), changes the next enforced square digit by its old unit value times \(z\), so each such digit is uniquely determined. The last lift digit is free. A solvable unit square equation has \(1\), \(q\), or \(2q\) roots according as \(e=1\), \(e=2\), or \(e\ge3\). Different choices of outer scalar roots induce bijective rescalings of the middle-factor witness sets. The recognition density comes unchanged from the residue source, as stated in the square-zero proof.

The finite-field characteristic-four residue refinement has direct precedents in [Wood's work on Witt extension for mod-four-valued forms](https://www.maths.ed.ac.uk/~v1ranick/papers/woodj.pdf) and [López-Díaz and Rúa](https://doi.org/10.1016/j.jpaa.2008.03.028). The extra digit argument above handles frame constraints of arbitrary precisions and supplies explicit witness and fiber counts for the nonalternating bilinear dot-product group. This is a result for the recognizable orthogonal domain. [Grochow, Qiao, Stange and Sun](https://arxiv.org/abs/2611.00735) consider ordinary general-linear tensor isomorphism over commutative rings.
