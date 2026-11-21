# Near-extremal eigenvalues from matrix-vector products

[Simons Workshop Problem 3.9](https://arxiv.org/html/2602.05394v3#S3.SS5) and its rightmost variant have randomized solutions in the exact matrix-vector model. Let A=VΛV⁻¹ be diagonalizable and supply K≥‖V‖₂‖V⁻¹‖₂. Write ρ=max_i|λ_i|. For 0<ε,δ<1/2, with probability at least 1−δ there are algorithms with the following guarantees.

- With O(ε⁻² log(nK/δ)) products, return z within ερ of some λ′ with |λ′|≥(1−ε)ρ.
- With O(ε⁻⁴ log(nK/δ)) products, return z within ερ of some λ′ with Re λ′≥max_i Re λ_i−ερ.

These are products with A only. The guarantees concern one extremal eigenvalue in each objective.

Draw a vector b of independent standard circular complex Gaussians, normalized to have second moment one per coordinate. For M(p)=max_i|p(λ_i)|, with probability at least 1−δ we have simultaneously for every polynomial p
$$
\frac{\delta}{2nK}M(p)\le\frac{\|p(A)b\|_2}{\|b\|_2}\le K M(p).
$$
The upper bound is immediate in the eigenbasis. Each coordinate of V⁻¹b is a circular Gaussian with standard deviation at least 1/‖V‖₂, as its row sends the matching column of V to one. The squared magnitude of a unit circular Gaussian is exponential of mean one. A union bound gives min_i|(V⁻¹b)_i|≥√(δ/(2n))/‖V‖₂ with failure at most δ/2. Markov gives ‖b‖₂≤√(2n/δ) with failure at most δ/2. Apply the least singular value of V to get the lower bound. The event depends on b and V only, so it also covers data-dependent polynomials.

The list b,Ab,…,A^m b evaluates any degree-m polynomial on b without further products. For m≥τ⁻¹ log(2nK/δ), taking the m-th root of the measured ratio for p(z)=f(z)^m estimates max_i|f(λ_i)| within factors e^(-τ) and e^τ for every affine f.

## Largest modulus

Choose τ=ε²/100. With f(z)=z obtain R estimating ρ. If R=0 return zero, which on the good event means ρ=0. Otherwise take a unit-circle net of chord radius √τ. For each net point u estimate the maximum with f(z)=R+conj(u)z. Select the largest estimate and return z=Ru. One Krylov list serves all net points.

At a point nearest the direction of a maximum-modulus eigenvalue the squared deficit from (R+ρ)² is at most τRρ, so the unestimated shifted radius is at least (1−τ)(R+ρ). Maximizing the estimates therefore gives a λ′ with |R+conj(u)λ′|≥e^(-2τ)(1−τ)(R+ρ)≥(1−3τ)(R+ρ). The triangle inequality gives ρ−|λ′|≤3τ(R+ρ)≤7τρ. Also,
$$
(R+\rho)^2-|R+\bar u\lambda'|^2
=(\rho^2-|\lambda'|^2)+2R(\rho-\operatorname{Re}(\bar u\lambda')) .
$$
Both terms are nonnegative, and |ρu−λ′|²≤2ρ(ρ−Re(conj(u)λ′)). Thus |ρu−λ′|²≤6τ(ρ/R)(R+ρ)²≤30τρ². With |R−ρ|≤2τρ this gives both promised bounds.

## Rightmost real part

Obtain a constant-accuracy radius estimate ρ/2≤R≤2ρ on the same event and set T=16R/ε. Apply the preceding algorithm to B=A+TI with relative tolerance ε²/200, returning z_B, and output z=z_B−T. The binomial expansion evaluates every shifted power from the original Krylov list. The shift keeps the eigenbasis; ρ(B)≤(32/ε+1)ρ, so the relative tolerance gives additive error less than ερ/5 for both position and deficit from the largest shifted modulus. For every |λ|≤ρ,
$$
0\le |T+\lambda|-T-\operatorname{Re}\lambda
=\frac{(\operatorname{Im}\lambda)^2}{|T+\lambda|+T+\operatorname{Re}\lambda}
\le \frac{\rho^2}{2(T-\rho)}\le\frac{\varepsilon\rho}{15}.
$$
Compare λ′ with a truly rightmost eigenvalue. If ρ=0 return zero.

## Deterministic case

Fewer than n deterministic products cannot solve either problem in general, even for normal matrices. On a zero transcript choose a unit vector v perpendicular to all queries. For largest modulus the two normal inputs vv* and −vv* give the same transcript and disjoint answer disks. For rightmost real part use zero and vv*, whose permitted outputs are also disjoint.
