# Arithmetic witnesses in one partially observed phase model

A single arithmetic sampling rule converts polynomial solutions over each probe ring into hidden violations of concavity. All lower coordinate marginals and all lower even phase responses remain exactly independent. The resulting law is uniformly computable and real analytic even when its exact concavity profile is an arbitrary linked family of computably enumerable languages. Over finite fields the same rule recovers full point counts and admits an exact classification of possible failure profiles.

## 1. The arithmetic phase compiler

Fix $n\ge2m\ge4$. Let $\mathcal J$ be a finite collection of $2m$-subsets of $[n]$. Give each $J$ a balanced charge $v_J\in\{0,1,-1\}^n$, supported on $J$, with $m$ entries of each sign. Write $\gamma_J(z)=\prod_i z_i^{(v_J)_i}$ on $\mathbb T^n$. Fix positive rational mixing weights $w_J$ of sum at most one and a rational noise parameter $0<\eta<1/2$. These parameters do not change with the arithmetic probe.

For each $J$, the input is a finite polynomial system $f_J=(f_{J1},\ldots,f_{Js_J})$ in $r_J$ variables over a common base ring. Test it in probe rings $R$ whose additive groups are finitely generated. The probes here are finite fields with their usual arithmetic, or rings of integers with effective integral bases. Let a random $X_J\in R^{r_J}$ be uniform for a finite ring. For an infinite ring of integers choose a computable bijection $x_0,x_1,\ldots$ from the nonnegative integers to $R^{r_J}$ and use
$$
     \Pr(X_J=x_h)=2\cdot3^{-h-1}.
 \tag{1}
$$
For zero variables use the single empty tuple with probability one. The probabilities have full support in both cases. Put
$$
      P_J(R)=\Pr(f_J(X_J)=0).
$$
This is a definition for the proof. The sampling rule below only evaluates the polynomial vector at its sampled candidate and never searches for any root.

**Theorem 1.** There is one phase sampler, given the polynomial systems, that works over all the probes. Its unconditional law $\mu_R$ has density
$$
 \frac{d\mu_R}{d\operatorname{Haar}^{n}}(z)
   =1-2\eta\sum_{J\in\mathcal J}w_J P_J(R)\operatorname{Re}\gamma_J(z).
 \tag{2}
$$
It is strictly positive and real analytic, with total variation distance from independent Haar at most $\eta$. Its $(2m-1)$-coordinate marginals and lower even phase responses equal those of independent Haar. Its inclusion-minimal concavity failures for the response
$$
 F_R(x)=\mathbb E_{\mu_R}\left|\sum_i x_i^{1/(2m)}Z_i\right|^{2m}
$$
are exactly the faces $J$ for which $f_J$ has a solution over $R$.

There is also a natural bijection of witness sets. A witness in the sampling format is a latent candidate $x\in R^{r_J}$ for which the conditional phase law, given the channel $J$ and candidate $x$, has the fixed density $1-2\eta\operatorname{Re}\gamma_J$. The bijection to the polynomial witnesses is the identity on $x$. Conditional laws are preserved under arithmetic embeddings on all candidates, including those which are not witnesses.

*Proof.* Randomly select channel $J$ with probability $w_J$. The leftover probability uses the independent reference law. For the selected channel draw $x=X_J$, and independently draw a Haar character $\chi$ of the discrete additive group $R^{s_J}$. Its value $C=\chi(f_J(x))$ has mean
$$
       \int\chi(f_J(x))\,d\chi=\mathbf 1_{f_J(x)=0}.
 \tag{3}
$$
If the argument is nonzero, some character does not take value one on it, and translation of Haar measure by that character forces the integral to vanish. Characters separate points because the group is a finite sum of cyclic and infinite cyclic groups. Over a finite field the rule is especially explicit: independently sample $y\in R^{s_J}$ uniformly and set
$$
 C=\exp\left(\frac{2\pi i}{p}\operatorname{Tr}_{R/\mathbb F_p}
                   \sum_j y_j f_{Jj}(x)\right),
 \qquad p=\operatorname{char}R.
$$
The field expression inside the character is a polynomial of degree at most one more than the degree bound of the supplied equations. Over an integer ring the rule instead samples circle angles dual to the integer coordinate vector of $f_J(x)$. Both are instances of (3).

Draw independently a circle phase $U$ with density $1+2\eta\operatorname{Re}U$ and put $B=-UC$. Generate Haar phases in all but one coordinate of $J$, then set the omitted coordinate so that $\gamma_J(Z)=B$. Generate all coordinates outside $J$ independently by Haar. For a given $C$, the resulting density on $\mathbb T^n$ is $1-2\eta\operatorname{Re}(\gamma_J(z)\bar C)$. This follows by changing the omitted coordinate to the resulting value of $\gamma_J$, which preserves Haar for every fixed choice of the other coordinates. Averaging over $\chi$ gives exactly $1-2\eta\operatorname{Re}\gamma_J$ when $f_J(x)=0$ and exactly independent Haar otherwise. The conditional formula is independent of the additive coordinates used to sample the character. For the integer-ring probes the unconditional weights use the fixed candidate enumeration. It also proves the natural witness statement because polynomial evaluation commutes with embeddings and an embedding preserves nonzero values. Averaging over $x$ and the channel gives (2). The absolute value of the deviation of (2) from one is at most $2\eta$, giving the positivity and total variation claims.

Every missing coordinate of $J$ kills its corresponding Fourier term on marginalization. In the even moment expansion, all nonconstant charges below order $2m$ involve fewer than $2m$ coordinates. At order $2m$, the non-independent terms occur only at $\pm v_J$. Each has multinomial coefficient $(m!)^2$, and the paired contribution is a scalar times the geometric mean on $J$. Thus
$$
 F_R(x)=F_0(x)-\sum_{J\in\mathcal J}D_J(R)\prod_{i\in J}x_i^{1/(2m)},\qquad
 D_J(R)=2(m!)^2\eta w_JP_J(R),
 \tag{4}
$$
where $F_0$ is the independent response. The independent expansion is a nonnegative combination of weighted geometric means and is concave. The next argument gives an explicit failure on each face with $D_J>0$. Every face with no such subface has the independent response, proving minimality. $\square$ [Original phase-moment law and definitions](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md)

### Stochastic transport of the conditional experiment

For an embedding $R\hookrightarrow S$, fix a channel $J$ and candidate $x$ in $R^{r_J}$. Its whole conditional experiment admits a stochastic lift to candidate $\iota(x)$ in $S^{r_J}$, preserving its sampled phases pointwise. The lifts respect identities and compose as Markov kernels.

Indeed the additive character restriction map $\widehat{(S,+)^{s_J}}\to\widehat{(R,+)^{s_J}}$ is surjective. An elementary extension argument adds one generator $b$ at a time to the subgroup on which the character is given. If there is a least positive $d$ with $db$ in that subgroup, choose a $d$-th root on the circle of the given character's value on $db$, and use it as the value on $b$. If there is no such $d$, the value on $b$ is unconstrained. This defines the extended character using additivity and proves surjectivity.

For each source character, choose the unique probability law on its restriction fiber invariant under the compact kernel, by translating Haar measure. It is a Borel probability kernel. On each continuous test function, averaging over the kernel is continuous on the larger dual group and constant on its restriction fibers, and hence descends continuously to the smaller dual group. The iterated lift through an intermediate dual is invariant under the full restriction kernel and supported on its fiber, so equals the direct lift. An identity restriction has singleton fibers. In particular a Haar source character lifts to a Haar character on the larger group, by translation invariance there.

For each sample the lifted character agrees with the original one on $f_J(x)$. Use the same smoothing phase and Haar coordinate masks. All output phases then agree in the two probes. This statement is conditional on the chosen candidate and channel. The unconditioned candidate distributions use the appropriate weighting for their own probes, so can differ under the embedding.

### Exact failure scale and rational certificates

On a fixed face $J$, set all but one of its coordinates to one and write the remaining coordinate as $s=t^{2m}$, $t>0$. Let $g(s)$ be this slice. Set $A_j$ to be the independent coefficient of $s^{j/m}$, for $0\le j\le m$. Every $A_j>0$, as follows by choosing exponent $j$ on the varied coordinate in the diagonal expansion and distributing the rest elsewhere. By (4),
$$
 \frac{g(s)-\tfrac12(g(0)+g(2s))}{t}
 =
 \sum_{j=1}^{m-1}A_j(1-2^{j/m-1})t^{2j-1}
   -D_J(R)(1-2^{1/(2m)-1}).
 \tag{5}
$$
The polynomial sum is strictly increasing from zero to infinity. Thus if $D_J>0$ there is a unique positive threshold $t_*$, with a strict midpoint violation exactly for $0<t<t_*$. For $0<t\le1$ the sum is bounded above and below by positive constants depending only on $m$ times $t$. In particular $t_*=\Theta_m(D_J)$ as $D_J\downarrow0$, and the resolution in the original coordinate $s$ is of order $D_J^{2m}$.

A single arithmetic witness gives a certificate without calculating $P_J$. Its regime supplies a rational lower bound $d$ on $D_J$, by taking the weight of that witness and multiplying by $2(m!)^2\eta w_J$. Choose
$$
        t=\min\big(1/2,\ d/(8(2m)^{2m})\big).
$$
Indeed $\sum_j A_j=F_0(1,\ldots,1)\le(2m)^{2m}$, and $1-2^{1/(2m)-1}>1/4$. Equation (5) then makes the midpoint gap strictly negative. The three input vectors have rational entries. Over a finite probe their bit lengths are $O_m(r_J\log |R|+\operatorname{bits}(\eta,w_J)+1)$. For a witness at index $h$ in (1) the bit length is $O_m(h+\operatorname{bits}(\eta,w_J)+1)$. Transporting the latent witness and then applying the same canonical input formula gives compatible certificates under successive embeddings.

## 2. Finite-poset c.e. universality with analytic densities

**Corollary 2.** Fix a number field and a finite poset $P$. For each $J\in\mathcal J$ and $p\in P$, prescribe a computably enumerable language $S_{J,p}$, monotone in $p$. There are common probes $\mathcal O_{E_p}$ representing $P$ by field embeddings, and one computable family of the phase-sampler inputs above, with one input $e$ used over every probe, for which
$$
 J\text{ is an inclusion-minimal failure at }p
       \quad\Longleftrightarrow\quad e\in S_{J,p}.
$$
Every law in the entire family has the same $(2m-1)$-coordinate marginals and the same lower even phase responses. Its density and phase response coefficients have uniform computable names with an explicit geometric approximation error. The hidden arithmetic systems can have the fixed dimension and degree bounds, smooth geometrically integral generic fibers, and local solubility of the simultaneous arithmetic realization theorem.

*Proof.* Apply the finite-poset arithmetic realization theorem separately to each $J$, using the same construction of the probe fields since that construction depends only on $P$ and the base field. Then apply Theorem 1 to this tuple of systems for each input $e$. To approximate $P_J$, check the first $L$ entries of the effective enumeration over the given ring, using its multiplication table. The remaining mass is exactly $3^{-L}$; this gives uniformly computable real coefficients for a fixed finite trigonometric polynomial. Real analyticity and all observation claims follow from (2) and (4). $\square$ [Simultaneous computability, finite-poset theorem](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/SimultaneousComputability.md) · [Koymans–Pagano, integral Diophantine definability](https://arxiv.org/html/2412.01768v3#S1.SS2)

For each fixed finite-poset format, use the fixed integral bases and enumerate coefficient tuples by expanding integer cubes. The first $O(b)$ candidates have coordinates with $O(\log(b+1))$ bits and give $b$ bits of accuracy. Their fixed-degree polynomial evaluations take time polynomial in $b$ and the bit length of the explicitly supplied equations.

The ternary weighting retains more than nonemptiness. From a Cauchy name of the normalized coefficient $P_J$, one can recover the witness bit at every index $h$. After subtracting earlier bits, a zero bit leaves residual at most $3^{-(h+1)}$, whereas a one bit leaves residual at least $2\cdot3^{-(h+1)}$. Precision $O(h)$ bits suffices to distinguish the intervals, with the earlier bits recovered by the same procedure. If there is a first witness at index $h$, the whole mass lies from $(2/3)3^{-h}$ to $3^{-h}$. For fixed $m,\eta,w_J$, the threshold in the varied coordinate of (5) is consequently of order $3^{-2mh}$.

For a nonrecursive c.e. language at a specified probe, there is no computable positive lower bound depending on the input for the nonzero coefficient magnitudes on its positive instances. Such a bound, together with the computable approximation error, would decide whether the coefficient is zero. Equivalently there is no total computable bound for the first witness index on its positive instances. Formula (5) also rules out a computable positive lower bound on the spatial threshold of these canonical midpoint violations. The obstruction concerns exact concavity with fixed observed marginals. It persists even though the laws themselves have fixed Fourier support and effectively approximable densities. [Computable real zero-testing context](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2016.58)

## 3. Which finite-field failure profiles occur

For a fixed finite base field $\mathbb F_q$ and one edge, let $B$ be the set of extension degrees over which that edge is a minimal failure in the sampler. Call a set of positive integers upward closed for divisibility if membership of $d$ implies membership of each positive multiple of $d$.

**Theorem 3.** A set $B$ occurs exactly when it is upward closed for divisibility and, outside a finite range, is a finite union of sets of multiples. The converse can be realized by a smooth affine scheme with at most three ambient field variables and four equations. Any finite collection of such profiles can occur independently on the designated faces in one phase model.

*Proof of necessity.* The phase compiler gives the nonemptiness profile of one affine finite-type scheme $X$. The profile is upward closed by field extension. For the eventual description, pass to the reduced geometric scheme. Decompose it into its irreducible components, take their disjoint relatively open parts off the intersections, and iterate on the closed complement of smaller dimension. This gives a finite partition into geometrically irreducible locally closed strata permuted by Frobenius. For a stratum whose orbit has length $d$, an $\mathbb F_{q^e}$-point in it is possible only if $d\mid e$, since a fixed point must be in a fixed stratum. The stratum descends to $\mathbb F_{q^d}$. Lang–Weil gives such a point for all sufficiently large $e$ divisible by $d$ when its dimension is positive. In dimension zero the stratum is a geometric point with that residue field, giving points for every multiple of $d$. The finite list of orbit lengths gives the eventual description. [Lang–Weil, number of points of varieties over finite fields](https://doi.org/10.2307/2372655)

*Proof of sufficiency.* Take a finite list $D$ so that the sets of multiples of its elements describe $B$ eventually. For $d\in D$, over $\mathbb F_{q^d}$ take the affine line with every closed point removed whose relative degree divides some $j$ with $dj\notin B$. Only finitely many such $j$ occur. The resulting affine open, viewed over $\mathbb F_q$, has no points over degrees not divisible by $d$, and has no points over $dj$ if $dj\notin B$. If $dj\in B$, a primitive element for $\mathbb F_{q^{dj}}/\mathbb F_{q^d}$ gives a closed point of relative degree $j$. This degree does not divide any of the excluded integers, by upward closure of $B$. The corresponding open therefore has a point. Add one finite closed point of degree $e$ for each $e\in B$ outside the union of the sets of multiples from $D$. Only finitely many are added, and their multiples already belong to $B$. The disjoint union realizes $B$, including the empty case.

For the bounded ambient format, use a primitive-element variable $t$ for all the finitely many distinct base degrees, with one square-free polynomial $g(t)$ obtained by multiplying one irreducible polynomial per degree. Each open line is an equation $uF_d(x)=1$ over its own field, where $F_d$ is a product of the irreducible polynomials for the removed points. Use the Chinese remainder theorem to put these in one $F(t,x)$ modulo $g(t)$, and choose $\sigma(t)$ with residue one on open-line components and zero on the extra finite components. The equations are
$$
  g(t)=0,\qquad
  \sigma(t)(uF(t,x)-1)=0,\qquad
  (1-\sigma(t))x=(1-\sigma(t))u=0.
$$
After the Chinese-remainder decomposition these are exactly the chosen smooth components. The empty case is the equation $1=0$. Applying the compiler to the individual schemes realizes the requested profiles simultaneously. $\square$

For example $x^q-x$ vanishes at exactly the base-field elements over every finite extension. The scheme $(x^q-x)u=1$ therefore accepts precisely $e\ge2$. In uniform sampling over the two ambient variables, the coefficient in (4) is proportional to $(q^e-q)/q^{2e}$, a fully explicit profile. The set $\{e\ge2\}$ is no finite union of sets of multiples, since it contains all primes but excludes one. Thus it cannot be the scalar-extension existence profile of an ordinary finite-field tensor pair, whose transporter components give a finite union of such cones. This is an exact difference between the present geometric observable and a finite-field ordinary tensor transporter. [Earlier ordinary finite-field tensor profile classification](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/SimultaneousComputabilityAndGrochow/FiniteFieldProfiles.md)

More generally the observable gives the full sequence $\#X(\mathbb F_{q^e})$ through $q^{er}P(\mathbb F_{q^e})$. Its formal exponential expression $\exp(\sum_{e\ge1}\#X(\mathbb F_{q^e})T^e/e)$ is the arithmetic zeta function, which is rational by Dwork. Möbius inversion recovers the number of closed points of each degree. The model therefore retains much more than the support of the failure profile. The analogue over rings of integers is the weighted witness-set reconstruction following Corollary 2. [Dwork, rationality of the zeta function](https://www.mathnet.ru/php/archive.phtml?jrnid=mat&option_lang=eng&paperid=201&wshow=paper)

The new claims are the uniform sampler, natural conditional witnesses, exact observation and precision laws, and the constructive characterization of its finite-field failure profiles. The work uses established character orthogonality, Lang–Weil, and the earlier arithmetic realization theorem. These are written proofs.
