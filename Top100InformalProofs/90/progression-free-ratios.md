# Ratio and dyadic-scale results for progression-free sets

The ratio inputs are the named progression-free upper and lower bounds. The asymptotic in Erdős Problem 142 remains open.

## 1. Prior art for general k (verified against the sources)

| k | upper bound | source / status |
|---|---|---|
| 3 | N exp(−c(log N)^{1/12}) | Kelley–Meka 2023, published |
| 3 | N exp(−c(log N)^{1/9}) | Bloom–Sisask 2023 |
| 3 | N exp(−c(log N)^{1/6}(log log N)^{−1}) | Raghavan arXiv:2603.27045v3 (May 2026), preprint |
| 4 | N (log N)^{−c} | Green–Tao 2017 |
| ≥5 | N exp(−(log log N)^{c_k}) | Leng–Sah–Sawhney arXiv:2402.17995 |
| **all ≥3** | **C_k N exp(−c_k (log N)^{γ_k})**, γ_k > 0 not explicit | **OpenAI, "Quasipolynomial Bounds for Arithmetic Progressions", 23 Sep 2026** (github.com/openai/math preprints). It is cited on erdosproblems #3 ("companion PDF claims"). AI-written, about 190 pp, not refereed. Inputs: the LSS quasipolynomial inverse theorem and Schoen–Sisask almost-periodicity. It claims no improvement for k = 3. |

So for k = 4 and k ≥ 5, Green–Tao and LSS are **superseded** (conditional on the OpenAI paper) by a bound of the same shape as Kelley–Meka.

**Lower bounds.** O'Bryant (EJC 18 (2011), arXiv:0811.3057, Cor. 1), refining Rankin (1961) and correcting Łaba–Lacey: with n = ⌈log₂ k⌉ and log = log₂,

  r_k(N) ≥ C_k N · 2^{−n 2^{(n−1)/2} (log N)^{1/n}} · (log N)^{1/(2n)}  for all N ≥ 1.

The exponent is 1/2 for k = 3, 4; 1/3 for k = 5..8; 1/4 for k = 9..16; and 1/n for 2^{n−1} < k ≤ 2^n. Elsholtz–Hunter–Proske–Sauermann and Hunter (2024) improve the constant only: for k = 3, and for all k by a factor (1−δ) per Hunter §5.2. Hunter's "Improved lower bounds for Szemerédi's theorem" is still listed as in preparation, and no arXiv version was found. The *exponent* 1/⌈log₂ k⌉ has been unchanged since 1961. Fox–Hunter 2606.02541 (van der Waerden numbers) does not touch r_k(N).

## 2. Exact target ladder for general k

Write L_k(N) := log(N / r_k(N)). The known range is (log N)^{γ_k} ≪ L_k(N) ≪ (log N)^{1/⌈log₂ k⌉}.

- r_k(N) ~ f(N) means L_k(N) = log(N/f(N)) + o(1). This is **additive o(1) precision** on a quantity that tends to infinity like a power of log N. It is hopeless with current methods.
- "log r_k(N) ~ g(N)" is **trivial**: log r_k(N) = log N − L_k(N) and L_k = o(log N), so log r_k(N) ~ log N. Any meaningful "log-asymptotic" target has to be about L_k itself.
- Meaningful weaker targets, in increasing strength: (a) the existence of the exponent lim log L_k(N)/log log N; (b) L_k(N) ≍ (log N)^{θ_k}; (c) L_k(N) ~ c_k(log N)^{θ_k}. **None is known for any k.** Even (a) is open, since the exponent gap is [1/6, 1/2] for k = 3 and [γ_k, 1/⌈log₂ k⌉] in general.

## 3. Results

### Theorem A (proved; elementary given the cited bounds; confidence 0.95 that it is correct, 0.6 that it is not already folklore)

**r_3(N) = o(r_K(N)) for K = 4097** (from Kelley–Meka alone), **for K = 513** (Bloom–Sisask), and **for K = 65** (Raghavan, preprint). More precisely, with K = 65,

  r_3(N)/r_65(N) ≤ exp(−c(log N)^{1/6}(log log N)^{−1} + C(log N)^{1/7}) → 0.

*Proof.* For K = 65 we have n = ⌈log₂ 65⌉ = 7, so O'Bryant gives r_65(N) ≥ C N exp(−C'(log N)^{1/7}). Raghavan gives r_3(N) ≤ N exp(−c(log N)^{1/6}/log log N). Since 1/6 > 1/7, the ratio tends to 0. For K = 513 we have n = 10 and 1/9 > 1/10. For K = 4097 we have n = 13 and 1/12 > 1/13. ∎

K = 64 does not work with Raghavan's bound: n = 6, and the lower exponent 1/6 is not beaten by an upper exponent of 1/6 − o(1).

**Corollary A1 (partial answer to Erdős's [Er80] remark; proved).** There is j ∈ {3, …, 64} with liminf_{N→∞} r_j(N)/r_{j+1}(N) = 0. Quantitatively, there is such a j for which r_{j+1}(N) ≥ r_j(N)·exp((log N)^{1/6−o(1)}/62) holds for a set of N of upper density ≥ 1/62.
*Proof.* Monotonicity gives r_3 ≤ r_4 ≤ … ≤ r_65, so ∏_{j=3}^{64} r_j(N)/r_{j+1}(N) = r_3(N)/r_65(N). This product is ≤ exp(−(log N)^{1/6−o(1)}), so for each N some factor is ≤ exp(−(log N)^{1/6−o(1)}/62). Apply pigeonhole over the 62 indices. If every j had a positive liminf, the product would stay bounded below. ∎ Using only peer-reviewed inputs (KM), the same holds with j ∈ {3, …, 4096}.

**Corollary A2 (conditional on OpenAI 2026-09-23; proved modulo that).** For every k ≥ 3 there is K(k) with r_k(N) = o(r_{K(k)}(N)): take ⌈log₂ K⌉ > 1/γ_k. Hence **there are infinitely many j with liminf_N r_j(N)/r_{j+1}(N) = 0.** K(k) is not explicit because γ_k is not explicit. Gowers, Green–Tao and LSS alone give nothing here, since their savings are weaker than any Rankin bound.

**Meaning for #142.** Any asymptotic formula f(k, N) must genuinely separate k = 3 from k = 65. The r_k are not all of one asymptotic class, and Erdős's "we do not even know" remark is now false in the averaged/liminf form. The consecutive question with a full limit, r_k/r_{k+1} → 0 for a *specific* k (e.g. k = 3), stays open: it needs an upper exponent for r_3 above 1/2, i.e. beating Behrend-type lower bounds for r_4, which is impossible while r_4 ≥ r_3 ≥ Behrend. In fact, for k = 3 the question r_3/r_4 → 0 cannot be settled by exponent comparison at all, because the lower bounds for r_3 and r_4 have the same exponent. It would need either a 4-AP-free construction better than every 3-AP-free one, or a structural argument.

### Proposition B (proved; elementary; confidence 0.97; almost certainly folklore in spirit)

Fix k ≥ 3, N₀ ≥ 1 and ε ∈ (0, 1). Then

  #{0 ≤ j < n : r_k(2^{j+1}N₀) < (2−ε) r_k(2^j N₀)} ≤ (2/ε)·L_k(2^n N₀) ≤ (2C_k/ε)(n + log₂N₀)^{1/⌈log₂ k⌉}.

*Proof.* Subadditivity (split [M+N] into two intervals and use translation invariance) gives r_k(2M) ≤ 2r_k(M). So δ(M) := r_k(M)/M satisfies δ(2M) ≤ δ(M), and log δ(N₀) − log δ(2^n N₀) = Σ_{j<n} log(δ(2^j N₀)/δ(2^{j+1}N₀)) is a sum of non-negative terms. A bad j contributes > log(2/(2−ε)) ≥ ε/2. The total is ≤ L_k(2^n N₀), which is bounded via O'Bryant. ∎

So r_k(2N) ~ 2 r_k(N) holds on all but O(n^{1/⌈log₂ k⌉}) = o(n) of the first n dyadic scales. This partly answers the jleng01 forum question: r_k is regularly varying at index 1 on a density-one set of scales. An asymptotic N·exp(−L(N)) with L(λN) − L(N) → 0, which is what every conjectured shape gives, needs this on *all* scales. Ruling out sparse "density cliffs" (r_k(2N) ≤ (2−ε) r_k(N) infinitely often) is, as far as we found, **open**. I tried and failed to prove r_k(2N)/r_k(N) → 2. A gapped union A ∪ (A + N + g) only gives r_k((2 + 2/(k−2))N) ≥ 2 r_k(N), and more copies create the periodic AP a, a+(N+g), …. The product construction r_k(2MN) ≥ r_k(M) r_k(N) loses a constant factor.

### Lemma C (proved, standard) used above
r_k(2MN) ≥ r_k(M) r_k(N) via A + 2M·B. Each consecutive triple of a k-AP forces digit-wise 3-APs, because |a₁ + a₃ − 2a₂| < 2M. Hence L_k(2MN) ≤ L_k(M) + L_k(N) + log 2, i.e. L_k(e^x) is subadditive up to a constant. This yields nothing new on exponents; it is recorded only as a no-go.
