# Sharp least-squares accuracy from zero-failure subspace injection

[Simons Workshop, §5.1](https://arxiv.org/html/2602.05394v3#S5.SS1) asks whether sufficiently small injection failure suffices for near-relative accuracy. For least squares the answer is negative even for zero injection failure. The fixed-confidence conclusion, and its exact dependence on the confidence over unrestricted dimensions, are as follows. This strengthens the zero-injection-failure example of [Townsend–Wang, Theorem 5](https://arxiv.org/html/2604.10215v2#S3.SS1), which gives a constant-factor error on an event of probability of order ε.

For 0<ε<1 let α=1−ε. Assume that \(\mathbb E[\Omega\Omega^{\mathsf T}]=I\) and that for each fixed s-dimensional subspace, with s≥1, every vector in it satisfies the injection lower bound α almost surely. Fix any full-column-rank least-squares problem with nonzero optimal residual. If R is the ratio of the sketched solution's full residual norm to the optimal residual norm, then for every t>0
$$
\Pr\{R^2-1\ge t\}\le\min\left\{1,\frac{\varepsilon}{4\alpha t}\right\}.
$$
This is sharp as a supremum over dimensions, inputs, and such isotropic sketches. In particular, for each proposed constant C, a failure probability bounded below by a constant depending on C persists at the accuracy factor 1+Cε as ε tends to zero. Taking the injection failure arbitrarily small cannot remove this obstruction.

## Upper bound

Write \(M=\Omega\Omega^{\mathsf T}\). The zero-failure lower bound gives \(M\succeq\alpha I\) almost surely by a countable dense set of directions, each lying in a fixed s-space, and continuity. Put \(B=M-\alpha I\), so \(B\succeq0\) and \(\mathbb E B=\varepsilon I\). Write the optimal residual as \(v\), perpendicular to the column space S, and the sketched residual as \(v-h\), where \(h\in S\). The normal equation along h gives
$$
\alpha\|h\|^2+h^{\mathsf T}Bh=h^{\mathsf T}Bv.
$$
Positive semidefiniteness gives \(|h^{\mathsf T}Bv|^2\le(h^{\mathsf T}Bh)(v^{\mathsf T}Bv)\). If \(h^{\mathsf T}Bh=0\) then \(h=0\). Otherwise square the normal equation and apply \((u+w)^2\ge4uw\) for nonnegative u,w. This gives \(4\alpha\|h\|^2\le v^{\mathsf T}Bv\). Pythagoras shows \(R^2-1=\|h\|^2/\|v\|^2\). Markov's inequality proves the result.

## Exact sharpness and arbitrarily small injection failure

Let S have dimension d, with unit coordinate vectors \(e_1,\ldots,e_d\), and let \(v=e_0\) be a unit vector perpendicular to S. Take A with these d orthonormal columns and right-hand side v. Fix any bad-event probability \(0<q<1\), with \(d\ge q\alpha/\varepsilon\). On the bad event choose j uniformly and an independent uniform sign σ, and let
$$
B=(\sqrt\alpha\,e_j+\sigma\sqrt{\varepsilon/q}\,v)
  (\sqrt\alpha\,e_j+\sigma\sqrt{\varepsilon/q}\,v)^{\mathsf T}.
$$
On the remaining event let B be \((\varepsilon-q\alpha/d)/(1-q)\) times the orthogonal projector onto S. Both choices are positive semidefinite, and direct averaging gives \(\mathbb E B=\varepsilon I\), because the sign cancels cross terms. Take \(\Omega=(\alpha I+B)^{1/2}\) on each outcome. It satisfies injection on the entire ambient space for every outcome and is isotropic.

On the bad event, the normal equations in S give \(h=\sigma\sqrt{\alpha\varepsilon/q}\,e_j/(2\alpha)\), so \(R^2-1=\varepsilon/(4\alpha q)\). On the other event h=0. For t with \(\varepsilon/(4\alpha t)<1\), choose q equal to that ratio to attain the displayed upper bound for the weak inequality. For smaller t take q tending to one. For the claimed obstruction at accuracy 1+Cε, take a fixed sufficiently small q depending only on C. For all sufficiently small ε, the bad-event excess is strictly greater than \((1+C\varepsilon)^2-1\). The dimension may grow as ε decreases, which is allowed by the workshop question. The construction uses square sketches, allowed in its OSI definition, and settles the least-squares follow-up.
