# Small injection failure suffices for relative Frobenius error

Fix \(0\le\varepsilon\le1/2\), \(0\le\delta\le1\), and \(\alpha=1-\varepsilon\). Let \(\Omega\) be an \((r,\alpha,\delta)\) oblivious subspace injection in the sense of Workshop Definition 5.1. Write \(M=\Omega\Omega^{\mathsf T}\). Thus \(\mathbb E M=I\), and on any fixed \(r\)-dimensional subspace the compression of \(M\) is at least \(\alpha I\) with probability at least \(1-\delta\). Assume \(r\ge1\).

**Least squares and low-rank approximation.** In each of the following two settings, writing \(E_*\) for the optimal Frobenius error and \(\widehat E\) for the achieved error, the same estimate holds for every \(u>0\):
$$
\Pr\{\widehat E^2>(1+u)E_*^2\}\le \delta+\frac{58(\varepsilon+\delta)}{u}.
$$

1. For every full-column-rank least-squares matrix with \(r\) columns and any fixed matrix of right-hand sides, use the usual sketch-and-solve minimizer.
2. For every fixed matrix and target rank \(r\), use the randomized range finder followed by the orthogonal projection onto its sampled range. The bound also holds for the best rank-\(r\) approximation whose column space lies in that range.

For any fixed target failure probability \(\eta>0\), if \(\delta\le\eta/2\) we obtain squared distortion at most \(1+116(\varepsilon+\delta)/\eta\) with probability at least \(1-\eta\). In particular \(\delta=O(\varepsilon)\) suffices for \(1+O(\varepsilon)\) relative error at every fixed confidence. This answers the small-failure follow-up to Workshop Problems 5.1 and 5.2, with arbitrary numbers of right-hand sides and arbitrary target rank. It uses the original \(r\)-dimensional injection assumption. Townsend–Wang Proposition 8 gives a low-rank guarantee under simultaneous injection on augmented spaces. The proof controls expected one-dimensional extension deficits and sums them with the spectral weights. [Workshop Definition 5.1 and Problems 5.1–5.2](https://arxiv.org/html/2602.05394v3#S5.SS1) · [Townsend–Wang, §4.2](https://arxiv.org/html/2604.10215v2#S4.SS2)

## Expected deficit after adjoining one direction

For any fixed \((r+1)\)-space \(W\) write \(M_W\) for the compression and let \(D=(\alpha-\lambda_{\min}(M_W))_+\). Then \(X=\mathbb E D\) satisfies
$$
X^3\ \le\ 64\delta^2(2X+2\varepsilon+\delta),\qquad
X\ \le\ 14(\varepsilon+\delta).
$$
Moreover the worst possible expected deficit, with \(r\) and the ambient dimension allowed to vary, is of order \(\delta+(\delta^2\varepsilon)^{1/3}\), with absolute constants.

To prove the upper bounds, fix a realization of \(M_W\). Let \(p=p(M_W)\) be the fraction of hyperplanes in \(W\) on which the compression is below \(\alpha I\) in some direction, using uniform spherical measure on the normal. By fixed-subspace injectivity and Fubini, \(\mathbb E p\le\delta\). If \(D>0\), let \(e\) be a unit eigenvector for the least eigenvalue. In the orthogonal complement of \(e\) in \(W\), set
$$
\mu=\frac1r\sum_{j=2}^{r+1}(\lambda_j-\alpha)_+,
$$
where the eigenvalues are ordered increasingly. This definition also applies when \(D=0\).

Let \(n\) be a uniform unit normal and \(t=|\langle n,e\rangle|^2\). The normalized projection of \(e\) onto the hyperplane has components of lengths \(\sqrt{1-t}\) along \(e\) and \(\sqrt t\) along a unit vector \(f\) in \(e^\perp\). The direction \(f\), up to a sign irrelevant for its quadratic form, is uniform and independent of \(t\). Its quadratic form in the positive part of \(M_W-\alpha I\) has mean \(\mu\), so with probability at least \(1/2\) it is at most \(2\mu\). On this event the projected vector has shifted quadratic form at most \(-D+t(D+2\mu)\). Thus the hyperplane fails whenever also \(t\le D/[2(D+2\mu)]\).

For \(0\le z\le1\), \(\Pr(t\le z)\ge 2\arcsin(\sqrt z)/\pi\ge 2\sqrt z/\pi\). To see the first inequality, couple normals using independent standard Gaussians: the ratio \(g_0^2/(g_0^2+\cdots+g_r^2)\) is pointwise at most \(g_0^2/(g_0^2+g_1^2)\), whose two-dimensional angle is uniform. Consequently \(p\ge\frac18\sqrt{D/(D+\mu)}\) for \(D>0\). Since \(D\le\alpha\le1\), this gives \(D^3\le64p^2(D+\mu)\), including \(D=0\). Hölder gives
$$
X^3\le64(\mathbb E p)^2\mathbb E(D+\mu).
$$

If \(\lambda_2<\alpha\), every hyperplane intersects a two-dimensional strictly deficient eigenspace, so \(p=1\) and the probability of this event is at most \(\delta\). When \(\lambda_2\ge\alpha\), only the first eigenvalue can contribute a deficit, and the sum of the other eigenvalues' positive excesses is at most \(\operatorname{tr}(M_W-\alpha I)+D\). In general it is at most this trace plus \(D+r\alpha\mathbf 1_{\{\lambda_2<\alpha\}}\). Taking expectations and using isotropy yields
$$
\mathbb E\mu\le\frac{r+1}{r}\varepsilon+\frac{X}{r}+\alpha\delta
\le2\varepsilon+X+\delta .
$$
This proves the cubic estimate. If \(X>2\varepsilon+\delta\), then \(X^3\le192\delta^2X\), giving \(X\le14\delta\). In the other case \(X\le2\varepsilon+\delta\). For the sharper scaling in this other case, the cubic bound gives \(X^3\le192\delta^2(2\varepsilon+\delta)\). Taking cube roots gives \(X\le8(\delta^2\varepsilon)^{1/3}+6\delta\).

**Matching example.** Take \(r=1\) in the plane and choose \(\Omega=M^{1/2}\). With probability \(1-q\) use \(M=\alpha I\). Otherwise use \(M=Lww^{\mathsf T}\) for a uniformly random unit vector \(w\), with \(L=2\alpha+2\varepsilon/q\). Then \(\mathbb E M=I\) and \(\mathbb E D=\alpha q\). A fixed line fails with probability \(q(2/\pi)\arcsin\sqrt{\alpha/L}\). For \(0<\delta\le\varepsilon\), take \(q=(\delta^2\varepsilon)^{1/3}/2\). By the secant bound \((2/\pi)\arcsin z\le z\) on \([0,1]\), the failure is at most \(q^{3/2}/\sqrt{2\varepsilon}\le\delta\). For \(0<\delta\) and \(\delta>\varepsilon\), take \(q=\delta/2\), for which failure is at most \(q\). These give the claimed lower bound up to a constant. When \(\delta=0\) the expected deficit is zero by the upper bound.

## A directionwise bound for mixing into the leading space

Fix an \(r\)-space \(S\) and a unit vector \(v\perp S\). Let \(G\) be the event \(M_S\succeq\alpha I\). On \(G\) put \(h=M_S^{-1}P_S Mv\), using \(P_S\) for orthogonal projection onto \(S\). Set \(h=0\) outside \(G\). With \(D\) for \(W=S+\mathbb Rv\) as above and \(P=(v^{\mathsf T}Mv-\alpha)_+\), we have
$$
\|h\|^2\ \le\ \frac{P+2D}{\alpha}\quad\text{on }G.
$$
Indeed, if \(D\le\alpha/2\), write \(\beta=\alpha-D>0\) and \(B=M_W-\beta I\succeq0\). The defining equation gives \(\beta\|h\|^2+h^{\mathsf T}Bh=h^{\mathsf T}Bv\). When \(h^{\mathsf T}Bh=0\), positive semidefinite Cauchy–Schwarz forces \(h=0\). Otherwise Cauchy–Schwarz, followed by the arithmetic–geometric mean inequality, yields \(4\beta\|h\|^2\le v^{\mathsf T}Mv-\beta\le P+D\). When \(D>\alpha/2\), use the unshifted positive semidefinite Cauchy–Schwarz inequality to obtain \(h^{\mathsf T}Mh=h^{\mathsf T}Mv\le\sqrt{h^{\mathsf T}Mh}\sqrt{v^{\mathsf T}Mv}\). On \(G\) this gives \(\|h\|^2\le(v^{\mathsf T}Mv)/\alpha\le(P+2D)/\alpha\).

A fixed \(r\)-space containing \(v\) gives \(\Pr(v^{\mathsf T}Mv<\alpha)\le\delta\). Isotropy therefore gives \(\mathbb E P=\varepsilon+\mathbb E(\alpha-v^{\mathsf T}Mv)_+\le\varepsilon+\alpha\delta\). Taking expectations in the last bound, using \(\alpha\ge1/2\) and \(X\le14(\varepsilon+\delta)\), gives
$$
\mathbb E\|h\|^2\le58(\varepsilon+\delta).
$$
This estimate applies separately to every fixed \(v\). All the directions below use the same event \(G\), and the bounds are summed in expectation.

## Application to multiple-response least squares

Let \(S\) be the column space of the design \(A\). For each right-hand side \(b_j\), its optimal residual \(z_j=(I-P_S)b_j\) is perpendicular to \(S\). On \(G\), the normal equations give the sketched residual \(z_j-\|z_j\|h_j\), where \(h_j\) is the directionwise vector above with \(v=z_j/\|z_j\|\). When \(z_j=0\) the fit is exact on \(G\). Pythagoras makes the excess squared Frobenius error on \(G\) exactly \(\sum_j\|z_j\|^2\|h_j\|^2\). Its expectation, set to zero outside \(G\), is at most \(58(\varepsilon+\delta)\sum_j\|z_j\|^2\). Markov's inequality and \(\Pr(G^c)\le\delta\) prove the stated bound. When the optimal error is zero the asserted failure probability is at most \(\delta\).

## Application to randomized low-rank approximation

Take a reduced SVD \(A=U_1\Sigma_1V_1^{\mathsf T}+U_2\Sigma_2V_2^{\mathsf T}\), with leading right singular space \(S=\operatorname{im}V_1\) of dimension \(r\), and abbreviate \(\Omega_i=V_i^{\mathsf T}\Omega\), \(Y=A\Omega\). On \(G\), \(\Omega_1\) has full row rank. The candidate \(Y\Omega_1^+ V_1^{\mathsf T}\) has rank at most \(r\) and columns in \(\operatorname{im}Y\). Orthogonality of the right singular subspaces gives its squared error as
$$
\|\Sigma_2\|_F^2+\|\Sigma_2\Omega_2\Omega_1^+\|_F^2
=\|\Sigma_2\|_F^2+\sum_{j>r}\sigma_j^2\|h_j\|^2 ,
$$
where \(h_j\) uses \(v_j\), the corresponding right singular vector. In fact \(h_j\) has leading coordinates \((\Omega_1\Omega_1^{\mathsf T})^{-1}\Omega_1\Omega^{\mathsf T}v_j\). Both the orthogonal projection of \(A\) onto the sampled range and the best rank-\(r\) approximation in that range have error at most this candidate's. Apply the expectation estimate to the weighted sum, then Markov's inequality and \(\Pr(G^c)\le\delta\). If \(\operatorname{rank}(A)\le r\), pad its right singular space to dimension \(r\); on \(G\) the sampled range already contains the column space of \(A\). We assume \(r\) does not exceed the dimension of the sketch domain.

## The least-squares failure scale is optimal

For \(0\le\delta<1\), set \(\alpha'=(1-\delta)\alpha\) and \(\varepsilon'=1-\alpha'\). For each \(u>0\) and \(\varepsilon'>0\), the supremum of the least-squares failure probability over admissible inputs and dimensions is at least
$$
\min\left\{1,\ \delta+\frac{\varepsilon'}{4\alpha u}\right\}.
$$
Thus for vanishing \(\delta,\varepsilon\), a uniform \(1+O(\varepsilon)\) bound at any fixed positive success probability requires \(\delta=O(\varepsilon)\).

Here is an isotropic construction. First build \(M_0=\alpha'I+B\) with \(\mathbb E B=\varepsilon'I\), on a signal \(d\)-space with coordinates \(e_1,\ldots,e_d\) and a unit residual vector \(v\). For \(0<q<1\), take \(d\ge q\alpha'/\varepsilon'\). With probability \(q\), choose \(j\) uniformly, choose an independent uniform sign \(s\), and set \(B=ww^{\mathsf T}\) for \(w=\sqrt{\alpha'}e_j+s\sqrt{\varepsilon'/q}\,v\). Otherwise set \(B=((\varepsilon'-q\alpha'/d)/(1-q))P_S\). The two pieces are positive semidefinite and their expectation is the stated scalar matrix. With response \(b=A x+v\) and orthonormal columns of \(A\) spanning \(S\), the squared excess on the first piece is \(\varepsilon'/(4\alpha' q)\) by the single contaminated coordinate's normal equation. It is zero on the second piece.

Now use \(M=0\) with probability \(\delta\), and \(M=M_0/(1-\delta)\) otherwise, with sketch \(M^{1/2}\). The mean is \(I\), and on the second event \(M\succeq\alpha I\). The sketched least-squares solution on the second event is unchanged by the scaling. On the zero event the pseudoinverse gives the zero solution, so choosing \(\|x\|^2>u\) forces failure. We can take \(q\) arbitrarily close to \(\min(1,\varepsilon'/(4\alpha'u))\) from below. Substitution gives the displayed lower bound for the strict tail. For any fixed \(C>0\), put \(u=(1+C\varepsilon)^2-1\). If \(\delta/\varepsilon\) tends to infinity, the lower bound then tends to one.
