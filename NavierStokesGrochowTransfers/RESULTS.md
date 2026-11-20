# Four Navier–Stokes technique transfers to Grochow problems

These four theorems adapt specific finite parts of the Alpöge–Buckmaster Lean development at revision `ad53419de079eb8f95f60313473374624a348546`. The results are ordered here by the reach of the proved statements. [Navier–Stokes source](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546/lean)

| Rank | Grochow target | What is proved | Navier–Stokes construction |
| --- | --- | --- | --- |
| 1 | AP20 · Grochow–Mulmuley–Qiao, Question 4.5 | Degree-eight sparse forms whose canonical Kempf subgroups have exponentially large eigenweights. The exact primitive weight multiset is explicit. This strengthens the previous growing-degree answer. [Proof](KempfWeights.md) | Character averaging from the harmonic split compresses the moment and forces a coordinate optimal flag. |
| 2 | AP01 and AP04 · Galesi–Grochow–Pitassi–She, Questions 7.1 and 7.4 | Geometric tensor nonisomorphism has a raw-equation Polynomial Calculus degree bound $(2+m+n+k)^{O(k^2+1)}$ for mode ranks bounded by $m,n,k$. Fixed $k$ gives polynomial degree in rank and border rank, including all matrix pencils. [Proof](BoundedModeTensorPC.md) | Coordinate restriction and its graph lift eliminate the big transporter matrices before applying an effective Nullstellensatz. |
| 3 | T10 · Grochow–Qiao–Stange–Sun, Part V §1.4 | For ordered tuples over $\mathbb Z/2^\tau$, small radical lifting obstruction dimension gives deterministic decision, witnesses, and exact counts. The alternating split case also gives full isometry group generators. [Proof](AlternatingTupleLifting.md) · [Nonsplit and arbitrary-form extensions](NonsplitResidueAppendix.md) | The held adjoint correction isolates the trace correction from the obstruction. A finite orbit supplies the remaining coordinates. |
| 4 | G08 · Grochow–Srivastava–Thakkar, Open Question 3(5) | A paired-cut algorithm decides, constructs, and exactly counts epimorphisms for central elementary abelian radicals and products of simple quotient factors when the proved paired-width parameter is small. Both widths can grow. [Proof](PairedGroupEpimorphism.md) · [Arbitrary-source corollary](ArbitrarySourceCorollary.md) | Exact child-to-parent cancellation assembles the linear descent equations at the root. |

## Verification

The four manuscripts contain complete written arguments for their stated scopes. The Lean files cover the integer weight bound, the pivot lift, square-zero correction, and the exact tree cancellation. The [verification receipt](Verification.json) records the particular kernel-checked statements and their axiom dependencies. The finite checking scripts exercise the indicated constructions on exact examples.

The unrestricted tensor proof-complexity, characteristic-two isometry, and group-epimorphism questions remain open here. The Kempf result proves the fixed-degree strengthening of Question 4.5. It leaves the separate Stable-VP versus VP question open.
