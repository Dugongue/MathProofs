# Arithmetic decision problems for abelian phase data

The statements are in the supplied K-matrix and label-inference models. This written argument remains independently unaudited.

## 2. Thm K: number-theoretic tier for abelian topological order (proved, 85%)
**Problem K-GB.** Input: an even symmetric integer matrix K, entries in binary. Question: does the bosonic abelian TO of K admit a gapped boundary? By Levin this holds iff signature(K) = 0 and the discriminant form (A_K = ℤⁿ/Kℤⁿ, q(x) = ½ xᵀK⁻¹x mod 1) is metabolic, i.e. Witt-trivial.

**Problem K-SAME.** Given K and K′, are their TOs the same up to stacking invertible E₈ states? This holds iff the discriminant forms are isomorphic and the signatures agree mod 8.

**Thm K.**
- (a) K-GB and K-SAME are in NP ∩ coNP and in P^FACTOR.
  - YES certificate for K-GB: generators of a Lagrangian subgroup.
  - NO certificate: the prime factorisation of det K (checked by AKS) plus the p-adic Jordan data of the offending p-part.
  - Given the factorisation, the p-primary parts come from Smith normal form, and their Witt / isomorphism classes come from Jordan decomposition over ℤ_p, with Conway–Sloane 2-adic symbols. All of this is polynomial.
- (b) QR ≤ K-GB and QR ≤ K-SAME under randomised poly-time many-one reductions, with 4×4 diagonal K.

**Reduction.** Take a QR instance (N = pq, t) with Jacobi symbol (t|N) = 1.
1. Random self-reduce: replace t by t·r² mod N until it is a prime ℓ ∤ 2N. This takes expected O(log N) tries.
2. Pick a prime N′ ≡ N (mod 8ℓ) by sampling.
3. Put K = diag(2N, −2ℓN, −2N′, 2ℓN′), which has signature (2,2).

Discriminant pieces (for ⟨2m⟩ the p-part generator has q = (m/p)/p):
- **p | N:** Z_p² with form (N/p)(x² − ℓy²)/p. It is metabolic iff ℓ is a square mod p. Because (ℓ|N) = 1, the two primes agree, so the N-part is metabolic iff ℓ is a QR mod N, iff t is a QR mod N.
- **N′-part:** (−x² + ℓy²)/N′. It is metabolic because (ℓ|N′) = (ℓ|N) = 1: (ℓ|·) is a character mod 4ℓ and N′ ≡ N mod 8ℓ.
- **2-parts:** ⟨2N⟩ ⊕ ⟨−2N′⟩ has q = (N x² − N′ y²)/4 with (1,1) isotropic, since N ≡ N′ mod 4. Likewise ⟨−2ℓN⟩ ⊕ ⟨2ℓN′⟩.
- **ℓ-parts:** (−N x² + N′ y²)/ℓ has (1,1) isotropic, since N ≡ N′ mod ℓ.

So K has a gapped boundary iff t is a QR mod N. For K-SAME, compare with K′ = the same matrix with ℓ replaced by 1 (hyperbolic N-part). On Z_p², the metabolic forms are exactly the hyperbolic ones.

**Consequences.**
- Unless QR ∈ BPP, there is no efficient algorithm for "gapped boundary?", "is this a twisted quantum double Z(Vec_A^ω)?" or "same abelian TO?", even at rank 4.
- Since the problem is in NP ∩ coNP, it is not NP-hard unless NP = coNP. **This is the crisp intermediate tier the brief asked for.**
- It fits the thesis exactly. The classification layer (the Witt group of finite quadratic forms, an abelian group, Taylor-collapse territory) is P *given the p-local decomposition*. All hardness is in realising the anyon group from succinct data, which needs the factorisation.
- With A given explicitly as a list, the same problems are in P.

**Self-audit.**
- Levin's criterion needs a *bosonic* Lagrangian subgroup. K is even, so all anyons are bosonic-consistent: fine.
- "Witt-trivial ⟺ metabolic" holds for nondegenerate finite quadratic forms, since the anisotropic representative is unique. Fine.
- The p-parts split orthogonally. This needs gcd(N, 2ℓN′) = 1, which holds generically and is checked in the reduction.
- Is K-GB perhaps in P by a factoring-free route? The reduction shows any such route decides QR. Kill: none.
- Weakest link: whether fermionic or other variants behave the same. Not needed.
- Cogentic (memory: L[1/3] factoring) gives a subexponential *upper bound* for K-GB. This does not contradict the claim.

## 3. Thm A / A_Z: anyon-label inference (proved, 85% / 80%)
**Problem ANYON-ID(C).** Fix an abelian anyon theory C = (A, θ) with braiding B(a, b) = θ(a+b)/θ(a)θ(b) ≢ 1, and fixed reference anyons. Input: unknown quasiparticles u_1..u_r and v_1..v_s, and a list of measured mutual-statistics phases between clusters. Each record has the form Σε B(u_i, v_j) + Σ B(u_i, β) + Σ B(α, v_j) = c, with clusters fused and ε ∈ ℤ. Question: is there a consistent labelling u_i, v_j ∈ A?

**Thm A.** ANYON-ID(C) is NP-complete for every such C.
- The instances are exactly BSP(B) of Lemma S (R-L2 §2): B is bilinear and nonzero with finite image, and Rad has finite index because A is finite. Lemma S gives NP-hardness with a fixed finite set of reference anyons.
- Membership: guess the labels.
- Toric code (B(e, m) = −1) is already NP-complete.

**Thm A_Z.** Replace A by a dyon charge lattice ℤ^{2k} with the integer Dirac–Schwinger–Zwanziger pairing ⟨(q,g), (q′,g′)⟩ = q·g′ − g·q′, and take integer cluster data. The problem is then exactly QBLIN(DSZ), which is undecidable and Σ⁰₁-complete (thm:manin, cor:sigma1; c.e. membership).

**Self-audit.**
- Is the measurement model natural? Interferometry yields braiding of clusters, and a cluster's charge is the sum of its members' labels, so the bilinear form is genuine.
- Kill-check: the "same-cluster" terms B(u_i, u_j) are not needed. Lemma S's bipartite form suffices.
- Non-abelian C: monodromy scalars are not bilinear. Lemma C needs an abelian target, so this case is open (conjecture NP-c, 60%).
