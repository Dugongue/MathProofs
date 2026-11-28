# Selected consequences of the depth and split-section results

The corollaries below use their stated depth and split-section inputs. Conditional average-case and ETH claims are outside this selection.

## Theorem 5 (CGQTZ Q7.5 for forms that are neither symmetric nor skew). COROLLARY

Let (Ω_n) be any poly-time family of nondegenerate forms that contains an explicit block [[0, αI_m], [βI_m, 0]] with m ≥ n^ε. With α ≠ ±β this includes B_a(n) for a ≠ ±1, which is neither symmetric nor skew. It also includes O(p,q) with min(p,q) ≥ n^ε. Then all five Isom(Ω)-actions are TI-complete and pairwise polynomial-time equivalent.

**Proof.**
- Hardness: Theorem S with P = diag(g, g^{−t}, I), which preserves the block for any α, β.
- Membership: CGQTZ Theorem 1.10, which covers every poly-time bilinear form family.

**Why it matters.** Q7.5 asks explicitly about forms that are neither symmetric nor skew. FormTI (Lean, 09-16) covered action (i). This covers all five.

## Theorem 6 (universal real-rank barrier). COROLLARY of the depth bound

For any family of real reductive groups G_m acting on 3-tensors, by any of the five action patterns and in any representation, let r_m be the real rank and L_m the number of restricted weights. If D(r_m, L_m) ≤ n, there is no continuous kernel reduction from TI_n to G_m-isomorphism. This covers every real form, the exceptional groups included:
- compact groups (r = 0) admit no continuous reduction at all;
- for Sp(p,q) (quaternionic unitary, real rank min(p,q)), SU(p,q) and SO(p,q), bounded min(p,q) forbids reductions for n ≥ f(min(p,q)), independently of p + q.

**Why it matters.** It turns CGQTZ's Question 7.1 intuition, that compact groups should be easier, into a quantitative statement over all real forms. In the continuous model, real rank is the exact currency.

## Theorem 7 (dimension-free degeneration depth in Lorentzian algebraic classification). COROLLARY

Let O(1, N−1) act on any tensor representation whose boost weights lie in {−b, …, b}. Every strict chain of orbit closures has length ≤ 2b + 2, **in every spacetime dimension N**.
- For the Weyl tensor (b = 2) the bound is 6. That is the number of Coley–Milson–Pravda–Pravdová alignment types G, I, II, III, N, O.

**Proof.** The real rank is 1, and the restricted weights are the boost weights, so L ≤ 2b + 1. Then D(1, L) = 1 + L. The bound is independent of the dimension because Theorem 1 of the depth bound is independent of the compact multiplicities. ∎

**Why it matters.** The higher-dimensional CMPP classification is organized by boost weights, and Hervik and coauthors already use real GIT (Richardson–Slodowy) for it. This gives a uniform, dimension-free depth bound.
- **Caveat 1:** strict chains live inside one fibre, so the true depth may be smaller than 6.
- **Caveat 2:** compare with Hervik before claiming it as new.

## Theorem 8 (SLOCC needs unboundedly many split directions). COROLLARY

Tripartite SLOCC classification over ℂ is GL³-TI (`MineSLOCC.slocc_eq_gl3ti`).
- **(a)** For local pseudo-unitary groups U(p, q)³ with q bounded, there is no continuous reduction from SLOCC classification once n ≥ f(q), by BD_q. Unitary LU (q = 0) is the known endpoint (Lane B).
- **(b)** For U(n, n)³ or Sp(2n, ℝ)³ (real rank n), SLOCC reduces linearly into local equivalence, by Theorem S over ℂ or ℝ.

So hardness of local-equivalence classification is governed by the number of split (non-compact) directions.

**Caveat:** the physical identification of U(p,q) and Sp(2n, ℝ) with Bogoliubov or Gaussian operations is first-quantized and should be stated carefully. The mathematical statement stands.

## Theorem 9 (arity reduction for every Levi-section form group). COROLLARY

For any form family as in Theorem 5 (and Sp), d-tensor G-isomorphism reduces to 3-tensor G-isomorphism for every fixed d.

**Proof.** The chain is d-G ≤ d-TI ≤ 3-TI ≤ 3-G:
- d-G ≤ d-TI: FGS form compilation, the d-ary analogue of CGQTZ 1.10.
- d-TI ≤ 3-TI: Grochow–Qiao Theorem B, which is near-optimal at n^{⌈d/3⌉} in Lean (`BalancedOrdinaryReduction`).
- 3-TI ≤ 3-G: Theorem S, linear.

**Why it matters.** It extends CGQTZ Theorem 1.13, proved there for O(ℝ) and U(ℂ) only, to all Levi-section form groups.
