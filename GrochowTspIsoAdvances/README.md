# Four candidates for the Grochow top 30

These four results build on the previous isomorphism and TSP rounds. The proposed placements compare with the previous 30-result briefing. They are editorial estimates based on proximity to Grochow's work, strength of the new conclusion, and breadth of the assumptions.

| Proposed band | Result | Reason for the placement |
|---|---|---|
| **15–20** | [Tensor isomorphism via semisimple cycle holonomy](EtaleHolonomyGI.md) | Strengthens the earlier finite-field tensor-block reduction from bounded blocks and forest supports to arbitrarily large blocks with nontrivial, possibly nonsplit holonomy. The result gives a polynomial-size GI reduction and explicit transporters, placing it beside the portfolio's structured isomorphism algorithms. The graph reduction assumes commuting semisimple holonomy and short cycle generators. The aligned-support test works without the short-cycle condition. |
| **22–26** | [Accuracy–aspect-ratio tradeoff for Hamming TSP formulations](MetricAspectRank.md) | Extends the Newton-polytope and guarded-assignment line already represented by #26. A shared LP at factor $1+\varepsilon$ can require $2^{\Omega(\varepsilon^{-1}\log(1+\min\{N\varepsilon,A\}))}$ inequalities, even for Hamming distances of aspect at most $A\ge5$ as $\varepsilon\to0$. For error $1/\log N$ and polynomial aspect ratio, the rank bound is quasipolynomial where the earlier transfer gave a polynomial lower-bound rate. The new result uses a shared projected relaxation and a vanishing-error guarantee. |
| **25–28** | [Exact WL width of edited TSP terminal profiles](EditedTerminalProfiles.md) | A direct follow-up to the Grochow–Urisman entry at #25. The full joint distribution of edited distances on $r$ terminals is determined by $(r-1)$-WL. Explicit connected diameter-two witnesses prove sharpness for unedited TSP histograms, and even for the minimum-cost bin when $r$ is an odd prime. The circuit exponent is $n^{\Theta(r)}$ for the stated numerical task. |
| **27–30** | [Rank-parameterized Rural Postman with binary holonomy](VoltagePostmanFPT.md) | Replaces the earlier boundary-dependent enumeration by randomized time $2^{r+\rho}\operatorname{poly}(\text{input},C)$ for integer budget $C$. Here $r$ is the number of required components and $\rho$ is the rank of cycle voltages. For rational weights it gives a randomized parameterized $(1+\varepsilon)$ scheme with polynomial dependence on $1/\varepsilon$. The ordinary postman sieve and its approximation precedents are credited in the proof. |

The strongest lead for Grochow is the tensor reduction. It directly advances a recurring question in the briefing: when can a tensor problem be reduced to a discrete isomorphism problem at polynomial size? The Hamming lower bound is the strongest result to foreground for complexity and optimization readers. The terminal-profile result gives a sharp expressivity counterpart. The postman theorem gives the clearest algorithmic improvement over the previous TSP round.

## Verification

The four main arguments have informal proofs. Each proof describes its primary sources and controls. The tensor test checked all 12 support alignments and all 11,232 root maps per alignment in the stated field example. The Hamming route checked 26 exact optima and 74 matching-tour costs. The postman test compared direct tour multiplicities with symbolic matching-sieve outputs.

Run the reproducible terminal-profile controls with Python 3.10 or later.

    python -B check_terminal_profiles.py

The script compares 240 anchored distance tables with a full-host shortest-path calculation and enumerates the sharp TSP bins on explicit diameter-two witnesses. The [Lean file](ArithmeticOr.lean) passed an independent kernel and transitive-axiom audit for the elementary arithmetic OR identity, using propext, Classical.choice and Quot.sound. Publication priority for the combined results remains unverified.
