# A finite-probe symplectic-preserver theorem: a CEOC 2.0 application

**Research date:** November 11, 2026

**Problem addressed:** Ivo D. Dinov, *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*, arXiv:2607.07851v1 (July 2026), **Problem 4.8**, https://arxiv.org/html/2607.07851v1 .

**Status:** A self-contained informal proof of the precise linear-matrix converse in Problem 4.8, with an additional explicit finite-probe strengthening. It is **not independently peer-reviewed or historically priority-verified**, and the cited source is a public *preprint*, not a journal publication. It does not resolve the broader foundational questions of the paper or TI versus TI_SL.

## 1. Problem and result

Let \(J=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}\) on \(\mathbb R^{2n}\). For every symmetric positive-definite \(\Sigma\), define its symplectic eigenvalues \(\nu_1(\Sigma),\dots,\nu_n(\Sigma)>0\) by the eigenvalues \(\pm i\nu_j(\Sigma)\) of \(J\Sigma\).

**Problem 4.8 (as stated in the source):** If an invertible real linear map \(S\) preserves the full symplectic spectrum of \(S\Sigma S^T\) for *every* \(\Sigma\succ0\), must \(S\) be symplectic or antisymplectic (up to an overall positive scaling in the scale-covariant formulation)?

**Theorem A (complete affirmative converse).** For every \(n\ge1\) and every \(S\in GL_{2n}(\mathbb R)\), the following statements are equivalent:

1. \(\nu(S\Sigma S^T)=\nu(\Sigma)\), as multisets, for all \(\Sigma\succ0\).
2. \(Q(S\Sigma S^T)=Q(\Sigma)\) for all \(\Sigma\succ0\), where \(Q(\Sigma)=\sum_{j=1}^n\nu_j(\Sigma)^2\).
3. \(S^TJS=J\) or \(S^TJS=-J\).

**Theorem B (finite probes; stronger).** It is enough in statement 2 to check \(Q\) at **at most \(4n^2-1\) explicit integer-entry positive-definite covariance matrices**, independent of \(S\). The construction and exact proof are below.

**Scale-covariant form.** For any prescribed \(c>0\), replacing equality in (1) by \(\nu(S\Sigma S^T)=c\nu(\Sigma)\), or equality in (2) by \(Q(S\Sigma S^T)=c^2Q(\Sigma)\), is equivalent to \(S^TJS=\pm cJ\). The same finite probe family suffices.

## 2. The quadratic trace statistic

The eigenvalues of \(J\Sigma\) occur in pairs \(\pm i\nu_j(\Sigma)\), hence

\[
Q(\Sigma)=-\tfrac12\operatorname{tr}\bigl[(J\Sigma)^2\bigr].\tag{1}
\]

Put \(K=S^TJS\). By cyclic invariance of trace,

\[
Q(S\Sigma S^T)=-\tfrac12\operatorname{tr}(K\Sigma K\Sigma).\tag{2}
\]

Both sides are *homogeneous quadratic polynomials in the entries of* \(\Sigma\). This is essential: we can recover what happens on singular rank-two matrices from tests restricted entirely to positive-definite matrices.

**Rank-two identity.** If \(R=uu^T+vv^T\), and \(K\) is any real skew-symmetric matrix, then

\[
-\tfrac12\operatorname{tr}(KRKR)=(u^TKv)^2.\tag{3}
\]

Indeed, with \(L=[u\ v]\) and \(R=LL^T\), cyclicity gives \(\operatorname{tr}(KRKR)=\operatorname{tr}[(L^TKL)^2]\), while \(L^TKL=\begin{pmatrix}0&t\\-t&0\end{pmatrix}\) for \(t=u^TKv\), so the trace equals \(-2t^2\).

## 3. Proof of Theorem A

Assume statement 2. The two quadratic expressions (1) and (2) agree on the nonempty open cone of positive-definite symmetric matrices, hence agree as polynomials on **all** symmetric matrices. By (3), for every \(u,v\in\mathbb R^{2n}\),

\[
(u^TKv)^2=(u^TJv)^2.\tag{4}
\]

Both sides are polynomials in the independent coordinates of \(u,v\). Factoring gives

\[
\bigl(u^T(K-J)v\bigr)\bigl(u^T(K+J)v\bigr)=0
\]

as an identity in the polynomial ring \(\mathbb R[u_1,\dots,u_{2n},v_1,\dots,v_{2n}]\), which is an integral domain. Hence one entire factor vanishes identically. Therefore \(K=J\) or \(K=-J\): statement 3.

Conversely, if \(S^TJS=\epsilon J\), \(\epsilon\in\{\pm1\}\), then \(JS\Sigma S^T=\epsilon S^{-T}(J\Sigma)S^T\), which is similar to \(\epsilon J\Sigma\). Multiplication by \(\epsilon\) merely interchanges the eigenvalue pairs \(\pm i\nu_j\). Thus the full symplectic spectrum is preserved, proving statement 1. Statement 1 plainly implies statement 2. QED.

For the scaled version, apply the same argument with (4) replaced by \((u^TKv)^2=c^2(u^TJv)^2\), yielding \(K=\pm cJ\), and reverse the eigenvalue argument.

## 4. Proof of Theorem B: only 4n²−1 covariances

Let \(d=2n\) and \(e_1,\dots,e_d\) be the standard basis. Define a collection \(\mathcal R\) of rank-two positive-semidefinite matrices \(R=uu^T+vv^T\) as follows.

**Entry probes:** For all \(1\le r<s\le2n\), take

\[ R_{rs}=e_re_r^T+e_se_s^T. \]

**Synchronization probes:** For each \(i=2,\dots,n\), take

\[
R_i^{\mathrm{sync}}=(e_1+e_i)(e_1+e_i)^T
 +(e_{n+1}+e_{n+i})(e_{n+1}+e_{n+i})^T.
\]

The total is

\[|\mathcal R|=\binom{2n}{2}+(n-1)=2n^2-1.\]

Test only the **strictly positive-definite** matrices

\[
\mathcal P_n=\{I_d\}\cup\{I_d+R,I_d+2R:R\in\mathcal R\}.
\]

Every element has integer entries, and

\[|\mathcal P_n|=1+2(2n^2-1)=4n^2-1.\]

Suppose \(Q(S\Sigma S^T)=Q(\Sigma)\) for every \(\Sigma\in\mathcal P_n\). For each \(R\in\mathcal R\), the expression

\[
P_R(t)=Q(S(I+tR)S^T)-Q(I+tR)
\]

is a polynomial of degree at most 2 that vanishes at \(t=0,1,2\). Thus \(P_R\equiv0\), and its \(t^2\) coefficient vanishes:

\[
Q_K(R)=Q_J(R),\qquad Q_H(R):=-\tfrac12\operatorname{tr}(HRHR).
\]

By (3), if \(R=uu^T+vv^T\), then

\[(u^TKv)^2=(u^TJv)^2.\tag{5}\]

Taking the entry probes gives \(K_{rs}^2=J_{rs}^2\) for all \(r<s\). As \(J\) has only the canonical nonzero entries \(J_{i,n+i}=1\), this forces

\[
K=\begin{pmatrix}0&D\\-D&0\end{pmatrix},\qquad D=\operatorname{diag}(\epsilon_1,\dots,\epsilon_n),\ \epsilon_i\in\{\pm1\}.
\]

Next, the \(i\)-th synchronization probe gives

\[
(\epsilon_1+\epsilon_i)^2=\bigl((e_1+e_i)^TJ(e_{n+1}+e_{n+i})\bigr)^2=4.
\]

Since both signs are \(\pm1\), this forces \(\epsilon_i=\epsilon_1\) for every \(i\). Hence \(K=\epsilon_1 J\), finishing the proof. The case \(n=1\) has no synchronization probes and is included. The scaled case substitutes \(c\epsilon_i\) throughout. QED.

## 5. CEOC 2.0: exact character loss and synchronized repairs

The preceding proof is more than an application of a generic spectrum identity. It explicitly instantiates the *synchronized-character* idea of Character-Exact Orbit Calculus 2.0.

After the entry probes the matrix \(K\) may have an arbitrary sign \(\epsilon_i\) on each canonical two-plane. These signs form a group

\[A=(\mathbb Z/2\mathbb Z)^n.\]

The acceptable global transformations correspond to the diagonal subgroup

\[K_{\mathrm{global}}=\{(+1,\ldots,+1),(-1,\ldots,-1)\}\le A.\]

If one takes each local test separately and wrongly assumes its \(\pm\) witness can be chosen consistently, the missing correlation information has cardinality

\[|A/K_{\mathrm{global}}|=2^{n-1}.\]

For \(i\ge2\), the synchronization probe enforces the character equation

\[\chi_i(\epsilon)=\epsilon_1\epsilon_i=+1.\]

The common kernel is exactly

\[\bigcap_{i=2}^n\ker\chi_i=K_{\mathrm{global}}.\]

Thus the "parallel character checks" are applied to the **same matrix \(S\)**, their kernels intersect, and their joint erasure is precisely the allowed global sign. In CEOC terms, this is a *realized* (not hypothetical) synchronization protocol. We do **not** claim it supplies a new ordinary-tensor-isomorphism reduction.

**Sharp obstruction:** For \(n\ge2\), take \(S=\operatorname{diag}(I_n,D)\) with \(D=\operatorname{diag}(\epsilon_i)\) of mixed signs. Every entry probe passes, yet the synchronization probe connecting oppositely signed blocks fails. Independent two-plane tests therefore genuinely lose up to \(2^{n-1}\) sign classes.

## 6. Determinant-character correspondence

The scale-covariant characterization is \(S^TJS=\mu J\) for some \(\mu\in\mathbb R^*\). Taking Pfaffians gives

\[\det S=\mu^n.\]

The corresponding symplectic-eigenvalue scale factor is \(c=|\mu|\). Thus the exact character relation is

\[\boxed{(\mu,\det S,c)=(\mu,\mu^n,|\mu|).}\]

In particular, when \(n\) is even, the determinant does not distinguish symplectic from antisymplectic transformations. CEOC-style character bookkeeping shows exactly why a determinant-only test is insufficient, and the synchronization probes provide the missing information.

## 7. Verification and scope

An accompanying exact-arithmetic Python/SymPy checker constructs the finite probe family, evaluates the quadratic trace statistic, exhaustively checks all local sign patterns for small \(n\), and tests a nonorthogonal symplectic shear. These computations are not used as proof of the general theorem.

**What is proved:** The full linear-algebraic converse as explicitly posed in Problem 4.8, a stronger single-scalar characterization, a finite \(4n^2-1\)-probe certificate, and a precise connection to CEOC synchronized characters.

**What is not proved:** Full nonlinear statistical identifiability, the remaining Problems 4.9–4.11 in all of their formulations, peer-reviewed priority, or any new TI-versus-TI_SL reduction.

**Historical caution:** This statement might also follow from established linear preserver theory. A targeted literature check did not identify the exact finite-probe argument, but this is **not** a certification of novelty. The preprint describes Problem 4.8 as open as of July 2026; external review is needed before calling this a new discovery.

## References

- Ivo D. Dinov, *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*, arXiv:2607.07851v1 (2026), Problem 4.8. https://arxiv.org/html/2607.07851v1
- Williamson's theorem and the characterization of symplectic eigenvalues via eigenvalues of \(J\Sigma\). See the cited preprint, Proposition 4.7 and the references therein.
- CEOC v2 internal research note (November 11, 2026), `CEOC_v2_Correspondence_and_Synchronization_2026-11-11.md` (the synchronization-defect and common-kernel calculus).
