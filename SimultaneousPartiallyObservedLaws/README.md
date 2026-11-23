# Simultaneous computability of partially observed laws

These four proofs use one mathematical input across a family of experiments. Each experiment has a specified observation model and a phase-moment law. A change of environment may reveal different Fourier modes, allow new field-valued parameters, change the arithmetic used in a sampler, or permit different exact sample sizes. The conclusions specify what is shared across experiments and give explicit witness transport where it exists.

The common response is an even phase moment, $F(x)=\mathbb E|\sum_i x_i^{1/(2m)}\xi_i|^{2m}$. If lower marginals are fixed and a negative Fourier term first appears on a coordinate face, the response can fail concavity there. The hybrid results use this phenomenon to carry entire linked families of observations and witnesses. [Partially observed laws](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md) · [Simultaneous computability](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/SimultaneousComputability.md)

## Four results

| Experiment and its environments | Hybrid theorem |
| --- | --- |
| [One analytic phase law under cyclic averaging and moment-order probes](Phase.md) | A uniformly computable family of positive analytic densities on exactly four phase coordinates realizes **every uniformly c.e. monotone concavity-failure profile** on the specified infinite probe grid. Per input, one density works on the entire grid. Triple marginals and all proper-coordinate-face responses agree with independence. A finite witness code produces a rational Jensen violation and transports along the refinement arrows. The minimum bit depth is logarithmic in the inverse visible coefficient. A separate fixed-order theorem realizes arbitrary signed strength tables on any finite poset. |
| [One observed experiment over totally real fields](Certification.md) | For any affine polynomial system, its actual field-point witnesses are in natural computable bijection with nonconcave completions of a single fixed fourth-moment response. All observations are rational expected scores on at most **three independent coins** at a time. Every world has a concave completion. Two-coin observations in the same model can only acquire nonconcave witnesses that already exist over a multiquadratic subfield. Three coins realize a first witness over a cyclic cubic extension. The harmonic flag gives a quantitative Jensen violation that stays bounded away from zero when the arithmetic wire values stay bounded. |
| [One arithmetic sampler under changes of base ring](Models.md) | Each phase coefficient is an exact weighted mass of arithmetic solutions. Over finite fields it recovers the **entire point count**, and hence the zeta function, across extension degrees. Possible finite-field support profiles are exactly the divisibility-upward sets that eventually agree with finite unions of sets of multiples. Over integer rings a computable analytic density can carry arbitrary linked c.e. failure languages on common finite-poset probes, with canonical witness transport and effective coefficient precision. |
| [One fair binary experiment under sample replication](Empirical.md) | Every additive submonoid of the nonnegative integers is an exact attainable sample-size spectrum after multiplication by two, using only fair one-coordinate marginals on a listed finite binary support. The construction is logarithmic in the generator values and gives an exact bijection of empirical witnesses that commutes with replication and addition. Arbitrary homogeneous rational tests on the witnesses become regional phase concavity tests. The resulting joint verdicts eventually stabilize periodically. |

## How the witness claims differ

- Cyclic averaging transports which Fourier mode certifies failure. Its code stays the same, while its computed violating amplitudes may depend on the new moment order.
- The three-coin construction transports each complete arithmetic solution as a specific complete vector of coin biases. Its bijection holds for actual field-valued completions of the trace.
- The arithmetic sampler transports a latent candidate and its conditional phase law. Its unconditional phase coefficient records the weighted mass of all candidates solving the equations in that ring.
- The sample-size construction transports integer multiplicities. Its real response set is an entire simplex, while the empirical worlds retain only the points representable with the permitted numbers of samples.

## Two concrete consequences

Over a fixed finite field, the equation $(x^q-x)u=1$ yields a phase law whose concavity fails over exactly the extensions of degree $e\ge2$. The Fourier coefficient counts $q^e-q$ solutions after multiplying by the explicit normalization. This profile includes every prime degree and excludes degree one, so it cannot be a finite union of sets of multiples. The general classification explains why finite initial exceptions are essential. [Arithmetic proof](Models.md)

In the fair binary experiment with generators $2,3$, choose the regional law that only the first generator is used. At sample size four the law is forced, at sample size six it is excluded, and at sample size twelve it is undetermined. Each sample size refers to the same structural input and the same fair marginal readings. [Empirical proof](Empirical.md)

## Verification

All four principal results are manuscript proofs. Lean independently checked the [integer balance identity](FairBalance.lean) used in the fair-probe compiler. The finite controls include 8,192 generator compressions, 5,048 Fourier charges and 26,705 divisibility gates, and 1,039 arithmetic character and decoding checks. The arguments use standard facts from Galois theory, Fourier analysis, and finite-field point counting, with the cited literature in the individual chapters. Publication priority and external review remain pending.
