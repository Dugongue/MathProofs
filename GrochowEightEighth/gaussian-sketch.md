# A sharp near-relative accuracy law for rank-one Gaussian mixtures

Fix \(0<\delta<1/4\), \(0\le\varepsilon\le1/4\), and let \(\rho=\delta/2\). In the zero-inflated Gaussian model use \(\Omega=0\) with probability \(\rho\) and otherwise use a matrix of independent standard Gaussians multiplied by \(1/\sqrt{k(1-\rho)}\), where \(k\) is the sketch width. This distribution is isotropic. Let \(\beta=1-(1-\varepsilon)(1-\rho)\). For sufficiently small absolute \(\delta>0\), the least width at which this is a dimension-one oblivious subspace injection with injectivity \(1-\varepsilon\) and failure at most \(\delta\) is
\[
 k_{\min}=\Theta\!\left(\beta^{-2}\log(1/\delta)\right).
\]
At this width, the worst-case positive squared relative Frobenius excess of the ordinary randomized range finder at target rank one is of order
\[
\frac{1}{k_{\min}}
=\Theta\!\left(\frac{(\varepsilon+\delta)^2}{\log(1/\delta)}\right)
\]
at fixed confidence. The upper bound holds for every input matrix at fixed confidence. An explicit spiked diagonal family attains the scale with probability tending to one. Consequently the general small-failure implication in Workshop Problem 5.2 fails for every \(\delta=\varepsilon^\gamma\) with \(0<\gamma<1/2\). The upper and lower statements here give the sharp scale in the specified Gaussian mixture model. [Workshop Definition 5.1 and Problem 5.2](https://arxiv.org/html/2602.05394v3#S5.SS1)

## Width for injection

For any fixed unit vector the nonzero component of the sketched squared norm has distribution \(\chi_k^2/[k(1-\rho)]\). Thus the failure probability is exactly
\[
 \rho+(1-\rho)\Pr\{\chi_k^2<k(1-\beta)\}.
\]
For \(0<\beta\le1/2\) there are absolute constants \(c_0,C_0>0\) such that
\[
 c_0\exp(-C_0 k\beta^2)\le
 \Pr\{\chi_k^2<k(1-\beta)\}\le\exp(-k\beta^2/4).
\]
For the upper bound use the Laplace transform \(\mathbb E e^{-t\chi_k^2}=(1+2t)^{-k/2}\), optimize at \(t=\beta/[2(1-\beta)]\), and use \(-\beta-\log(1-\beta)\ge\beta^2/2\). For the lower bound when \(k\ge16\), integrate the chi-square density on the interval from \(k(1-\beta)-\sqrt k/2\) to \(k(1-\beta)\). At \(x=ks\) in this interval, \(3/8\le s\le1\), and Stirling's bound gives density at least \(c k^{-1/2}\exp[-(k/2)(s-1-\log s)]\) for an absolute \(c>0\). On this fixed interval of \(s\), \(s-1-\log s\le C(1-s)^2\) by Taylor's theorem with bounded second derivative. Also \(\lvert1-s\rvert\le\beta+1/(2\sqrt k)\). Integration proves the lower bound, with the finitely many smaller \(k\) covered by decreasing \(c_0\). The exact probability formula now proves the two-sided bound on \(k_{\min}\).

## A uniform upper bound and an exact spiked calculation

Conditional on a nonzero sketch, scalar normalization does not change its range. Take a singular-value decomposition of a fixed input \(A\), and let \(g\) be the leading right singular row of the standard Gaussian sketch and \(W\) its remaining right singular rows. Orthogonal Gaussian invariance gives independent standard Gaussian rows for \(g,W\). On this event, a rank-one candidate in the sampled column space is \((A\Omega)g^+v_1^{\mathsf T}\) after disregarding the scalar normalization of \(\Omega\). Its squared Frobenius excess over the optimal rank-one error is \(\|\Sigma_2 Wg^+\|_2^2\). Conditional on \(g\) its expectation is \(\|\Sigma_2\|_F^2/\|g\|^2\). The inverse chi-square expectation is \(1/(k-2)\) for \(k>2\), directly by integrating the density. Since the sampled orthogonal projection minimizes the approximation error in that range, Markov gives, for every \(u>0\),
\[
 \Pr\{\|A-\widetilde A\|_F^2>(1+u)\|A-A_1\|_F^2\}
 \le \rho+\frac{1}{u(k-2)} .
\]
A rank-at-most-one input is recovered on the nonzero event almost surely. The same estimate applies to the best rank-one fit in the sampled range.

For a matching example take \(A=\operatorname{diag}(L,1,\ldots,1)\) with \(m\) unit entries, \(m\ge128k^2\), and \(L=m\). The best rank-one squared error is \(m\). Rotate the \(k\) sketch columns so that the leading Gaussian row has support on the first column only. Conditional on that row, the tail Gaussian matrix has the original distribution by orthogonal invariance. Its last \(k-1\) columns span a pure tail subspace of dimension \(k-1\). Project the first tail column orthogonally off that subspace, giving a vector \(w\). Put \(q=\|g\|^2\) and \(v=\|w\|^2\), with independent distributions \(\chi_k^2,\chi_{m-k+1}^2\).

In the two-dimensional plane spanned by the leading direction and \(w\), the sampled line has coordinates \((L\sqrt q,\sqrt v)\). The orthogonal complement line has a direction vector \((\sqrt v,-L\sqrt q)\). Evaluating the residual on that line and on the \(m-k\) orthogonal uncaptured tail dimensions gives the exact conditional squared Frobenius error
\[
 m-k+\frac{L^2(q+v)}{L^2 q+v}.
\]
The mean and variance of a chi-square variable with \(h\) degrees of freedom are \(h,2h\). With probability at least \(1-8/k-8/(m-k+1)\), both \(q\) and \(v\) are within a factor two of their respective degrees of freedom. On this event, for \(z=v/q\) and \(a=1+z/L^2\), we have \(m/(8k)\le z\le4m/k\) and \(1\le a\le2\). The squared relative excess is
\[
 \frac{(1+z)/a-k}{m}.
\]
It lies between \(1/(32k)\) and \(5/k\). For the lower bound use \((1+z)/a\ge z/2\ge m/(16k)\) and \(k\le m/(128k)\). For the upper bound discard the subtraction and bound \(1+z\le1+4m/k\). This supplies the matching high-probability family already for the untruncated projection specified in the workshop. The zero-sketch atom has error ratio squared \(1+L^2/m\) on this example.

The lower bound at the minimum feasible width yields the claim for \(\delta=\varepsilon^\gamma\), since \(1/k_{\min}\) then dominates \(\varepsilon\) as \(\varepsilon\) tends to zero. Larger widths can reduce the excess. The scaling assertion is the worst-case guarantee when only the smallest feasible widths in this model are required.
