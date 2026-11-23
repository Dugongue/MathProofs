# Finite observations and adaptive phase tests

## 1. Exact finite verdicts and stable linear reconstruction

Let $\Omega$ be a finite state set, let $p$ be a probability on it, and let the exact observations range over $Mp=\tau$. Include normalization as a row of $M$. For a feasible $\tau$, write $P_\tau=\{p\ge0:Mp=\tau\}$. Let a finite set of affine response inequalities be the law, written $Bp\ge0$ by absorbing constants in normalization. For a row $b_j$ of $B$, use its column transpose in coordinatewise comparisons.

**Theorem 1.** The trace forces the law exactly when for each $j$ there is a vector $y_j$ with $M^{\mathsf T}y_j\le b_j^{\mathsf T}$ and $y_j^{\mathsf T}\tau\ge0$. It rules out the law exactly when there are $z\ge0,y$ with
$$
M^{\mathsf T}y\ge B^{\mathsf T}z,\qquad y^{\mathsf T}\tau<0.
$$
Otherwise there are one satisfying and one violating completion. A violating completion can be chosen on at most $\operatorname{rank}M$ states. A satisfying completion can be chosen on at most $\operatorname{rank}M+\operatorname{rank}B$ states. If the law is ruled out, some certificate has $z$ supported on at most $\dim(\operatorname{aff}P_\tau)+1$ clauses. This last bound is sharp.

Minimize each $b_jp$ over $P_\tau$. Linear programming duality gives the first alternatives and an optimal vertex when a clause is violated. At a vertex, the columns of the equality matrix on the positive support must be independent, because a dependency can be perturbed in both directions. For a satisfying completion, take a vertex of the further constrained polytope and use the same argument including active inequalities. Farkas's lemma, with nonnegative slack variables for the law clauses, gives the stated infeasibility certificate. Helly's theorem on the sets $P_\tau\cap\{b_jp\ge0\}$ cuts the number of clauses to the stated bound. Apply Farkas to that subsystem. Sharpness is witnessed by the probability simplex on $d+1$ states and the clauses $-p_i\ge0$, any $d$ of which are satisfiable. [Multistochastic transport and observation duality](https://arxiv.org/abs/2008.07926).

**Theorem 2.** Let $A$ be a linear observation map, $S\subseteq\Omega$ a known support, and $\|\cdot\|$ a norm on observation space. The least constant $L\in[0,\infty]$ making
$$
|c^{\mathsf T}(p-q)|\le L\|A(p-q)\|
$$
hold for all probabilities supported on $S$ is
$$
\inf\bigl\{\|a\|_*:c|_S=A_S^{\mathsf T}a+b\mathbf1,\;b\in\mathbb R\bigr\}.
$$
Here an empty infimum is infinite. A finite value is attained and gives an affine reconstruction whose error is at most $L\eta$ when the observation error is at most $\eta$. On an individual feasible trace, replace $S$ by the union of positive supports of compatible completions to test exact identifiability of a linear response on that fiber.

Every sum-zero vector on $S$ is, after scaling, the difference of two probabilities near the uniform point there. Consequently the exact modulus is the dual norm of the induced functional on $A\{v: \operatorname{supp}v\subseteq S,\ \sum v=0\}$, or infinite if it is not defined. Hahn–Banach extends it with exactly that norm. On a feasible trace there is a completion positive on the union of compatible supports, obtained by averaging finitely many completions. The same two-sided perturbation argument applies to the kernel of the observation matrix on that support.

There is also an exact noisy dual, without assuming that the observation ball meets an interior point. If $Q=\{p\in\mathcal P(\Omega): \|Mp-\hat\tau\|\le\eta\}$ is nonempty, then
$$
\inf_{p\in Q}c^{\mathsf T}p
=\sup_y\left\{\hat\tau^{\mathsf T}y-\eta\|y\|_*+
        \min_{x\in\Omega}\bigl(c_x-(M^{\mathsf T}y)_x\bigr)\right\}.
$$
Indeed the supremum of $y^{\mathsf T}(\hat\tau-Mp)-\eta\|y\|_*$ is zero inside the ball and infinite outside. Sion's minimax theorem exchanges the simplex minimum and dual supremum. This dual need not attain its supremum for a general norm. At $\eta=0$ the finite linear-programming certificates of Theorem 1 apply. [Sion's minimax theorem](https://doi.org/10.2140/pjm.1958.8.171).

## 2. Which additional observations determine a law

Let $K$ be a polytope of responses in its affine hull and $L\subseteq K$ the subpolytope satisfying the law. An exact observation map $A$ decides the law on $K$ if points with equal observation always have the same membership in $L$. Suppose $L$ is nonempty and full-dimensional in $\operatorname{aff}K$. Write $\mathcal F$ for the facet normals of $L$ whose facets meet $\operatorname{relint}K$, considered as linear functionals on the translation space of $K$.

**Theorem 3.** The map $A$ decides the law on $K$ if and only if its row span contains $\operatorname{span}\mathcal F$, on that translation space. In particular the minimum number of unrestricted nonadaptive scalar linear observations is $\dim\operatorname{span}\mathcal F$. For arbitrary $L$, including lower-dimensional cases, the exact criterion is
$$
\ker A\cap T_K(p)\subseteq T_L(p)\qquad(p\in L),
$$
where the tangent cones are the feasible-ray cones of the polytopes.

For the first necessity choose a point in the relative interior of a cutting facet and in the relative interior of $K$. If its normal does not annihilate the kernel, a small two-sided perturbation in a kernel direction changes whether the point lies in the law. For sufficiency, the facets of $L$ lying wholly in the boundary of $K$ have supporting halfspaces already satisfied throughout $K$, since both polytopes are full-dimensional. All other facet inequalities are determined by the measurements. For the tangent criterion, any violating kernel direction at $p\in L$ has a small feasible step in $K$ leaving $L$. Conversely if $p\in L,q\in K\setminus L$ are in the same fiber, the segment direction is feasible in $K$. If it is in $T_L(p)$, proceed along the segment to its last point in $L$, where it ceases to be feasible in $L$. Signs and equalities of active inequalities make the cone criterion finite, since there are only finitely many relevant active sets.

Adaptivity can give an arbitrarily large gap. For $D\ge2$, let $K$ be the convex hull of $(0,0),(D+1,0)$ and $(i,\pm e_i)$ for $i=1,\ldots,D$. The coordinates are $(t,z)$. For each $i$, the maximum feasible $z_i$ at fixed $t$ is $\min(t/i,(D+1-t)/(D+1-i))$. The upper bound follows by looking at the mass at $(i,e_i)$ in a convex combination, and the formula is attained by mixing that point with an endpoint. Choose $0<\rho_i<1$ close enough to 1 that the open intervals where those maxima exceed $\rho_i$ are disjoint. Set the law to $z_i\le\rho_i$ for all $i$. Each facet $z_i=\rho_i$ cuts the interior of $K$, as seen on the segment between an interior point with $z=0$ and $(i,e_i)$. Thus every fixed sensor system needs at least $D$ scalar observations. An adaptive system reads $t$, then reads the unique $z_i$ whose constraint might fail, if such an index exists. This finite experiment is realized by allowing arbitrary mixtures of the displayed vertices as states.

## 3. Exact phase probes are covering designs

Use the phase law on $\mathbb T^n$ with product-Haar marginals through size $2m-1$. The response is
$$
F_\mu(x)=F_0(x)+\sum_{J\in\mathcal J} c_J G_J(x),\qquad
G_J(x)=\prod_{j\in J}x_j^{1/(2m)},\quad
\mathcal J=\binom{[n]}{2m}.
$$
Write $D=|\mathcal J|$. Its concavity is equivalent to all $c_J\ge0$, and its minimal nonconcave coordinate faces are the $c_J<0$.

**Theorem 4.** A set of exact marginal probes determines all the coefficients, and decides concavity for all completions, precisely if every $J\in\mathcal J$ is contained in some probed set. The same covering condition is necessary on the product-Haar transcript of every exact deterministic adaptive decision procedure. Hence for maximum block size $b\ge2m$, both optimal nonadaptive and worst-case exact adaptive probe counts equal the covering number $C(n,b,2m)$. With additive probe costs, the corresponding answer is the minimum cost cover. With arbitrary exact scalar linear measurements of $c$, at least $D$ measurements are necessary on the product-Haar transcript even adaptively, and $D$ suffice.

A marginal containing $J$ directly gives the Fourier expectations in its coefficient. If $J$ is uncovered, choose a balanced charge $v_J$ on $J$ and the density $1-\epsilon\cos(v_J\cdot\theta)$ relative to Haar, for $0<\epsilon<1$. Its projection to any probe omitting at least one coordinate of $J$ is Haar. Its only changed coefficient is $c_J=-(m!)^2\epsilon$. It therefore matches the product-Haar transcript but has a different verdict. For adaptive probes the same argument applies pathwise to the Haar transcript because a replicate oracle produces its identical history. Finally the perturbations $1+\sum_J s_J\cos(v_J\cdot\theta)$ realize an open neighborhood of $c=0$ in coefficient space. If fewer than $D$ scalar linear measurements are asked on the zero path, a nonzero vector in their common kernel can be signed and scaled to have a negative coordinate in that neighborhood. It gives the same transcript. [Schönheim's covering designs](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-s.pdf).

## 4. Statistical probes and an exact adaptivity gap

In this section each query $B$ receives a fresh independent draw from the $B$-coordinate marginal of the same unknown law. Let $\mu_0$ be product Haar and let $\mu_J$ have density $1-\epsilon\cos(v_J\cdot\theta)$ for the fixed balanced charge on $J$. The hypotheses are $\mu_0$ versus any one $\mu_J$. Write $N_J$ for the number of queries that contain $J$, possibly at a stopping time, and suppose $0<\epsilon\le1/2$.

**Theorem 5.** For an adaptive procedure with error at most $\delta<1/2$ under the null and every alternative,
$$
\mathbb E_0 N_J\ge
 \frac{\mathrm{kl}(1-\delta,\delta)}{\kappa(\epsilon)}
 \quad\text{for every }J,\qquad
 \kappa(\epsilon)=\log\frac{2}{1+\sqrt{1-\epsilon^2}}.
$$
Here $\mathrm{kl}(p,q)$ is Bernoulli relative entropy. For any allowed probes with positive prices $a_B$, define
$$
\tau_*=\min\left\{\sum_B a_Bx_B:x_B\ge0,\quad
                   \sum_{B\supseteq J}x_B\ge1\ \forall J\right\}.
$$
Then expected price under the null is at least $\tau_*\mathrm{kl}(1-\delta,\delta)/\kappa(\epsilon)$. With all $b$-subsets at unit price, $\tau_*=D/\binom b{2m}$, by counting incidences and taking uniform fractional weights. Without a separation gap in $\epsilon$, there is no procedure with bounded expected cost on the null and a fixed uniform risk below $1/2$.

When $B$ contains $J$, its likelihood ratio against Haar is $1-\epsilon\cos(v_J\cdot\theta)$. Otherwise it is 1. Under Haar the charge angle is uniform. Its one-sample relative entropy is $-\int\log(1-\epsilon\cos\theta)\,d\theta/(2\pi)=\kappa(\epsilon)$. To evaluate it, write $1-\epsilon\cos\theta=A|1-r e^{i\theta}|^2$ with $A=(1+\sqrt{1-\epsilon^2})/2$ and $r=\epsilon/(2A)<1$. The logarithm of the second factor has zero integral by its convergent Fourier expansion. The log likelihood of the stopped transcript is the sum of the log likelihood increments. Decisions and randomization used to choose actions contribute the same conditional factors under both laws. If the expected count is finite, bounded increments and conditional expectation give transcript relative entropy exactly $\kappa(\epsilon)\mathbb E_0N_J$. One may also apply the chain rule through finite truncations and pass to a limit. The final binary decision has relative entropy at least $\mathrm{kl}(1-\delta,\delta)$ by data processing. The fractional cover bound follows by scaling the expected probe counts to a feasible cover. At fixed risk the per-query information tends quadratically to zero with $\epsilon$. [Adaptive change of measure](https://www.jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf).

For comparison, for general phase laws, if every nonzero $|c_J|$ is at least $\gamma>0$, the entire minimal failure hypergraph can be recovered with probability $1-\delta$ by a nonadaptive design of expected cost $O_m(\tau_*\gamma^{-2}\log(D/\delta))$. Constants can absorb the maximum possible $\gamma$, which is bounded in terms of $m$. On every query containing $J$, evaluate
$$
(m!)^2\sum_{\substack{I\subset J\\ |I|=m}}
 \cos\left(\sum_{i\in I}\theta_i-\sum_{j\in J\setminus I}\theta_j\right).
$$
This score has expectation $c_J$ and an absolute bound depending only on $m$. Independently draw a Poisson number of samples of each allowed probe with mean $R x_B$, for an optimal cover and $R=O_m(\gamma^{-2}\log(D/\delta))$. Each score receives at least $R/2$ samples except with probability $e^{-R/8}$. Hoeffding's inequality conditionally on the schedule and a union bound estimate all signs away from zero. Using threshold $-\gamma/2$ recovers exactly the negative coefficients.

**Theorem 6.** When allowed probes are exactly the $2m$-subsets, the adaptive minimax expected number of samples for the null versus one changed edge is
$$
\Theta\bigl(D\epsilon^{-2}\log(1/\delta)\bigr)
\qquad (0<\delta\le1/4).
$$
At fixed risk $\delta\le1/4$ and $D\ge2$, nonadaptive fixed-budget sampling requires $\Theta(D\epsilon^{-2}\log D)$ samples, including randomized nonadaptive schedules.

The lower bound for adaptive sampling is Theorem 5. For the upper bound, test edges in any order. At a given edge stop its cumulative log likelihood at the upper boundary $\log(D/\delta)$ or the lower boundary $-\log(1/\delta)$. Declare failure on an upper crossing, and continue to the next edge on a lower crossing. Likelihood ratios and reciprocals are nonnegative martingales under the corresponding reference laws. Under the null the chance of an upper crossing on any edge is at most $\delta/D$. Under $\mu_J$, the chance of a lower crossing at the true edge is at most $\delta$. Stop the local expectations at a deterministic horizon first. The bounded increments imply overshoot at most $2\epsilon$, and the drift is $-\kappa(\epsilon)$ under Haar and $D(\mu_J\Vert\mu_0)$ on the changed marginal. Both drift magnitudes are bounded below by a universal multiple of $\epsilon^2$. For the latter use the second derivative of $s\log s$ on $[1/2,3/2]$ and the Haar mean of $\cos^2$. Thus expected local cost is $O(\epsilon^{-2}\log(1/\delta))$ on a null edge and $O(\epsilon^{-2}\log(D/\delta))$ on the changed edge. This gives the stated worst expected bound. [Wald–Wolfowitz sequential likelihood ratio tests](https://doi.org/10.1214/aoms/1177730197).

A more general nonadaptive lower bound holds for any fixed maximum block size $b$, with $K_b=\binom b{2m}$. Condition on a full nonadaptive schedule, including its random seed. Let $k_J$ be the number of samples covering $J$. The likelihood $L_J$ of the alternative edge has Haar mean 1 and Haar second moment $(1+\epsilon^2/2)^{k_J}$. For distinct $J,J'$, its product with $L_{J'}$ has Haar mean 1. In a sample containing both edges this follows from orthogonality of the two different Fourier characters, and across fresh samples it follows from independence. Since $\sum_J k_J\le NK_b$, at least $D/2$ edges have $k_J\le2NK_b/D$. Mix uniformly over this low-count set conditionally on the schedule. Its chi-squared divergence from Haar, including the random seed in both laws, is at most
$$
\frac2D\left[(1+\epsilon^2/2)^{2NK_b/D}-1\right].
$$
Although this mixture depends on the seed, its type-II risk is at most $2\delta$ because its weight on any edge is at most twice the uniform weight. Its type-I risk is at most $\delta$. The total variation bound by half the square root of chi-squared divergence now implies
$$
N=\Omega\left(\frac{D}{K_b}\epsilon^{-2}\log D\right)
$$
for $D\ge2,\ \delta\le1/4$. For all $b$-subsets, sampling them uniformly and applying a union bound gives the matching fixed-budget upper bound at fixed risk. Indeed each edge is covered with probability $K_b/D$ per trial, and conditional score concentration gives the upper bound. Taking $K_b=1$ proves the claimed adaptive versus nonadaptive gap.

## 5. From moment gaps to Jensen gaps

For $f$ on $[0,1]^n$, put
$$
J_f=f((1-\lambda)x+\lambda y)-(1-\lambda)f(x)-\lambda f(y),
\quad
\operatorname{Def}(f)=\sup_{x,y,\lambda}(-J_f)_+ .
$$
Write $a_J=(-c_J)_+$. A nonnegative phase representation has all $a_J=0$.

**Theorem 7.** For every law in the phase model of §3,
$$
c_m\|a\|_\infty^2\ \le\ \operatorname{Def}(F_\mu)\
\le\ \frac18\inf_{\omega}\sum_{J:a_J>0}\frac{a_J^2}{\omega_J},
$$
for a positive constant $c_m$ depending only on $m$. The infimum uses positive weights on the negative supports with $\sum_{J\supset\{i,j\}}\omega_J\le1$ for every coordinate pair. If the negative support is empty the upper sum is zero. In particular the upper bound is at most $\|a\|_1^2/8$, and at most $\Delta_2\|a\|_2^2/8$ when $\Delta_2$ is the maximum number of negative supports containing a coordinate pair. For a single negative edge the Jensen defect is quadratic in its coefficient, uniformly in $n$.

Put $\gamma=1/(2m)$. For a geometric mean $g=x^p$ with $\sum_i p_i=1$, its negative directional Hessian is
$$
-D^2 g(x)[h,h]=g(x)\sum_{i<j}p_i p_j(h_i/x_i-h_j/x_j)^2 .
$$
The independent response is a sum of such monomials with $p=\alpha/m$, $|\alpha|=m$, each coefficient at least one. For a pair $i,j\in J$, select a monomial using one count each at $i,j$, and the remaining $m-2$ counts at a maximal coordinate in $J$. Its value on the cube is at least $G_J(x)^2$, since the other $2m-2$ coordinates are at most that maximum and the maximum is at most 1. Its pair weight $p_i p_j$ is at least $1/m^2=4\gamma^2$. Thus by the pair-capacity condition on $\omega$, the Hessian of $F_0$ satisfies
$$
-D^2F_0(x)[h,h]\ge
4\sum_J\omega_J G_J(x)\bigl(-D^2G_J(x)[h,h]\bigr).
$$
Indeed the coefficient of a fixed pair on the left dominates $4\gamma^2$ times each individual $G_J^2$ containing that pair, hence also their weighted sum.

On a line segment inside the positive cube let $K_\lambda(s)=\min\{(1-\lambda)s,\lambda(1-s)\}$. A twice differentiable function on the segment has Jensen gap $\int_0^1 K_\lambda(s)(-g''(s))\,ds$. For a nonnegative concave $g$, let $u=g-$ its endpoint chord. Then $0\le u\le g$, $u''=g''$, and integrating the second derivative of $u^2$ gives
$$
2\int_0^1K_\lambda u(-u'')=u(\lambda)^2+
2\int_0^1K_\lambda(u')^2\ge J_g^2 .
$$
Apply this to each $G_J$ in the Hessian bound. It gives $J_{F_0}\ge2\sum_J\omega_J J_{G_J}^2$, also on boundary segments by continuity. Complete the square in $\sum_J(a_JJ_{G_J}-2\omega_J J_{G_J}^2)$. Positive $c_J$ only improve the gap. This proves the weighted upper bound. Weights proportional to $a_J$ give the $\ell_1$ version, and weights $1/\Delta_2$ give the $\ell_2$ version.

For the lower bound restrict to the face of a largest negative edge, set $2m-1$ entries to one, and vary the last entry from 0 to $t$. At the midpoint the $G_J$ gap is $(2^{-\gamma}-1/2)t^\gamma$. The other phase monomials vanish on this face. The $F_0$ gap is at most $C_m t^{2\gamma}$, since constant and linear terms contribute zero and all remaining exponents are at least $2\gamma$. Choose $t^\gamma$ to be a small constant times $a_J$, keeping $t\le1$ by the uniform Fourier bound on $a_J$. This gives a negative response gap of magnitude at least $c_m a_J^2$. Under the one-edge statistical promise, the adaptive and nonadaptive rates therefore scale with the inverse Jensen defect.

## 6. Open problems suggested by the exact rates

- For unit-price $b$-coordinate fresh-sample queries, the one-negative-edge problem has adaptive expected sample cost between $\Omega((D/K_b)\epsilon^{-2})$ and $O((D/K_b)\epsilon^{-2}\log D)$ at fixed confidence. With $b=n$ it also needs $\Omega(\epsilon^{-2}\log D)$: stop any expected-cost algorithm at a constant multiple of its worst expected count, use Markov's inequality to bound the added risk, and apply the full-observation nonadaptive second-moment bound. A concrete conjecture is the interpolating rate $\Theta((D/K_b)\epsilon^{-2}\log(K_b+1))$ uniformly in $n,b$ at fixed $m$. The endpoint rates above agree with it.
- The weighted-pair upper estimate for Jensen defect may lose information when several overlapping negative supports compete on the same face. Determine whether the pair-packing bound is comparable to the actual worst Jensen defect for all sign-realizable, bounded-degree families, or exhibit a separating sequence. The single-edge bound and the dimension-free weighted inequality provide two test cases.
- For general finite response polytopes, a transcript through a point in the relative interior of the ambient polytope must measure the linear span of every law facet incident to that point. Determine whether the maximum of these local ranks bounds the adaptive depth up to an absolute additive constant under unrestricted scalar linear probes. The example in §2 separates this local question from the static facet span.

The results here are written proofs. The construction of the phase coefficient family is the given starting result. The covering-design identification, the statistical distinction between exact and fresh-sample probes, and the Jensen-gap estimates are derived from it above.
