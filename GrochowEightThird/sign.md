# Two workshop questions about polynomial sign approximation

The questions and the cost model are from [Sections 6.1–6.3 of the Simons Workshop problem list](https://arxiv.org/html/2602.05394v3). The circuit starts from 1 and x, scalar linear combinations are free, and a product of two available polynomials costs one multiplication. Put Kδ = [−1,−δ] ∪ [δ,1] for 0 < δ < 1.

## 1. Workshop Problem 6.4 has a negative answer

In continuous L² with ordinary Lebesgue measure, take δ = 1/2 and a budget of two multiplications. The feasible set is the entire degree-at-most-four space. Every feasible polynomial has degree at most four, and every member of that space can be computed by using x² as the first product, x²(c₄x²+c₃x) as the second, and adding free lower terms. Reflection symmetry and strict convexity imply that the unique least-squares approximation to sign(x) is an odd cubic ax+bx³.

Let I_j = ∫_(1/2)^1 x^j dx. The normal equations are I₂a + I₄b = I₁ and I₄a + I₆b = I₃. They give a = 8325/4088 and b = −165/146 = −4620/4088. On [1/2,1] the residual r = ax+bx³−1 has endpoint values −503/4088 and −383/4088. Its unique stationary point is a maximum at x* = √(185/308), lying strictly between 1/2 and 4/5. Its value equals 2ax*/3−1 < 352/4088. It follows that the absolute residual has its unique maximum on the positive interval at 1/2. By oddness precisely two points, ±1/2, attain maximal modulus on Kδ. Thus there is no Chebyshev equioscillation of the least-squares residual.


### Discrete ℓ² gives the same negative answer

Use the eight samples ±1/2, ±2/3, ±5/6, ±1 with equal weights. Evaluation on these distinct nodes is injective on quartics, so the unique least-squares polynomial is again odd. The two normal equations with sums in place of integrals give a = 19371/9341 and b = −10476/9341. At the positive nodes in increasing order the residual numerators over the common denominator 9341 are −965, 469, 739, −446. The maximum magnitude occurs only at ±1/2.

## 2. Workshop Problem 6.5 has an asymptotic separation

**Theorem.** After T odd cubic stages the best uniform error is
$$
E_T^{\rm cub}=\frac{1-\Phi^{\circ T}(\delta)}{1+\Phi^{\circ T}(\delta)},\qquad
\Phi(a)=\frac{a(1+a)}{2((1+a+a^2)/3)^{3/2}}.
$$
For fixed δ, log(1/E_T^cub) = Θδ(2^T). By contrast, if E_m is the infimum over unrestricted computations of budget m, then
$$
c_\delta 5^{\lfloor m/4\rfloor}\le \log(1/E_m)\le C_\delta 2^m
$$
for positive δ-dependent constants and sufficiently large m. At the same budget 2T the unrestricted error is strictly smaller for all sufficiently large T. The smallest number of cubic stages that matches E_m is between (log₂5)m/4−Oδ(1) and m+Oδ(1).

**The best cubic stage.** On [a,1], q(x)=x(1+a+a²−x²) has equal endpoint minima a(1+a) and maximum 2((1+a+a²)/3)^(3/2) at its sole interior critical point. Scale q so its maximum and minimum have equal displacement above and below 1. Any odd cubic with smaller uniform error would differ from the scaled q in signs +,−,+ at these three points. Dividing the difference by x gives an affine function of x², making two distinct roots impossible. Equivalently, among odd cubic maps with positive image, q maximizes the output minimum-to-maximum ratio. Indeed the minimal uniform error attainable by scaling any positive image of ratio r is (1−r)/(1+r). The optimal ratio Φ is nondecreasing since shortening the input interval cannot worsen optimal uniform error.

For any successful composition of error below 1, each intermediate image of [δ,1] is an interval missing zero. An intermediate zero would persist to the output by oddness. Sign and scale changes can be absorbed into the following odd cubic to orient each intermediate interval as [a,1]. Its output ratio is at most Φ(a). Monotonicity gives the iterative upper bound on the ratio, and picking the maximizing stage at each step attains it. The final scaling yields the displayed error formula.

For 0 < a < 1, Φ(a)>a because (1+a+a²)/3 ≤ (1+a)/2 < 1. The iterates increase to 1. Taylor expansion gives 1−Φ(1−u) = 3u²/8 + O(u³). Once the iterates are close to 1, the negative log of their distance from 1 obeys z_(j+1) = 2z_j + O(1). Taking a starting iterate with z_j larger than the error constant proves the claimed Θδ(2^T) rate.

**Unrestricted products.** Let c_j = binom(2j,j)/4^j and P(x) = x Σ_(j=0)^4 c_j(1−x²)^j. Compute x², then u² for u = 1−x², then u²(c₄u²+c₃u), and finally x times the completed sum. This costs four products. The truncated inverse-square-root series shows x < P(x) < 1 on (0,1). The coefficient recurrence gives P′(x) = 9c₄(1−x²)^4, so P is increasing on [0,1] and 1−P(x) is comparable to (1−x)^5 near 1. Iterating P from δ yields E_m ≤ exp(−cδ 5^floor(m/4)) by the same negative-log recurrence with multiplier 5. Oddness gives the bound on the negative interval.

For the other direction, every circuit of budget m has degree ≤ D = 2^m. Odd symmetrization preserves that degree bound and cannot increase uniform error against sign. If q is the odd part, 1−q is a polynomial of degree at most D whose value at 0 is 1. The external-point Chebyshev inequality on [δ,1] therefore gives error at least
$$
|T_D(-(1+\delta)/(1-\delta))|^{-1}\ge \exp(-C_\delta D).
$$
At budget 2T the ratio of the logarithmic accuracies grows at least as a positive constant times (√5/2)^T. Combining both degree and construction bounds with the exact cubic-stage rate gives the displayed two-sided stage-count estimate.
