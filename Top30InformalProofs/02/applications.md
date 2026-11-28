# Three applications of the noncommutative lower bound

The applications inherit the unrefereed lower-bound inputs. For the coefficient-ring consequence, use Raz’s matching-size condition on the coefficient generators and inputs.

## 2. Theorem T3-A (multiquadratic sum of squares / PT-rank of the identity, every field)

Notation. I_{n^d} is the n^d × n^d identity, viewed as a 2d-leg tensor Π_k [i_k = j_k]. PT-rank is as in RZ Def 1.4: the least number of matrices each of rank 1 under some partial transpose Γ_τ (τ ⊆ [d]). q_{n,d} = Π_{k≤d}(Σ_i (X_i^{(k)})²), and SoS_K is the least number of d-multilinear squares summing to it.

**Statement.** Let K be any field, d ≥ 1, r ≥ 1 and n ≥ 2^r. Then

  log₂ PT-rank_K(I_{n^d}) ≥ √d·r − d·√(2(d−1)r) − 1,

and the same holds for border PT-rank (Zariski closure over K̄). If char K ≠ 2, then SoS_K(q_{n,d}) ≥ 2^{−d}·PT-rank_K(I_{n^d}). Hence, for fixed d:

  PT-rank_K(I_{n^d}), SoS_K(q_{n,d}) ≥ n^{√d − o(1)},

which is nontrivial once log n ≳ 2d².

Known bounds to compare:
- trivial upper bound n^d over every field;
- over ℂ (and any algebraically closed field of char ≠ 2), RZ Prop 6.2 gives n^{1.62^{⌈log₂d⌉}+o(1)} = n^{O(d^{0.696})};
- **so over ℂ the exponent lies in [√d, d^{0.696}]**;
- over GF(2) it lies in [√d, d], which answers RZ's remark only on the lower side.

**Proof.**
1. **Cut classes.** Group the s PT-basic terms by the cut they are rank-1 across. Γ_τ and Γ_{[d]∖τ} give the same cut S_τ = {i_k : k∉τ} ∪ {j_k : k∈τ}. So I = Σ_{τ∈𝒯} T_τ with |𝒯| = A ≤ 2^{d−1} and rank_{S_τ|S_τ^c} T_τ ≤ s.
2. **Placement** [ours]. Use the OAI price system P on ℝ^d. Lean `HasSpectralFlat K d` comes from `UnboundedPrimeFieldFlats.all_dimensions prime_flats K d` [OAI]. Put i_k at e_k and j_k at −e_k, with r bits per leg. Each EPR has length 2, so price(I; sites) = 2dr (multiplicativity + `wire` + `group`).
3. **Two-hub layouts** [Liu Lemma 2.1 / OAI Lemma A.3]. v_τ = r·Σ_k ±e_k, so ‖v_τ‖ = r√d for **every** τ: orthonormality makes all sign patterns equal. T_τ is a restriction of the network with hubs ±t·v_τ/‖v_τ‖ and an h = ⌈log₂s⌉-bit cable. Using ‖u − ta‖ ≤ 1 − t⟨u,a⟩ + t²/2 (valid for all t), cost ≤ 2dr − 2t·r√d + d r t² + 2th.
4. **Glue** [ours, audit-L2-glue: price ≤ cost on arbitrary sites + sum rule]. 2dr ≤ max_τ cost_τ + c·log₂A. Here c = price(diag) ≤ Σ_l ‖x_l − 0‖ = 2d (star bound from `transport` + `collapsed`). This gives h ≥ r√d − drt/2 − d(d−1)/t. Take t = √(2(d−1)/r).
5. **Border.** Liu's closure-to-exact tensor-power step applies unchanged, since the layout set depends only on (d, s).
6. **SoS ⇒ PT-rank (char ≠ 2)** [ours; the converse half of RZ Prop 3.16].
   - If q = Σ_{i≤s} g_i², let G = Σ g_i g_iᵀ. Then Q_G = q = Q_I.
   - The symmetrisation Sym(G) = 2^{−d}·Σ_τ Γ_τ(G) is fully symmetric with Q_{Sym G} = Q_I. By the RZ bijection (char ≠ 2), Sym G = I.
   - Each Γ_τ(g gᵀ) is PT-basic, so PT-rank(I) ≤ 2^d·s. ∎

**Optimality of the method (K3).** [local reference omitted] computes the asymptotic per-bit value sup_placement min_τ sup_{hubs p,q} [P − Σ_S|x−p| − Σ_{S^c}|x−q|]/|p−q|. This uses exact distances, free sites and free hubs, in D = d and D = d+1. Hill-climbing from random starts converges to 1.4137 (d=2), 1.7291 (d=3, D=3) and 1.7245 (d=3, D=4), never above √d. In D = 2, d = 3 the value is ≈ 1, so high dimension, and therefore `prime_flats`, is essential for d ≥ 3. First-order reason: for antipodal unit placements E_τ‖v_τ‖² = d·r², so min_τ ‖v_τ‖ ≤ √d·r. **√d is the ceiling of the two-hub method on I_{n^d}.**

**Consistency / conditional sharpness.**
- Iterating any composition of exponent e (RZ Prop 6.2's recursion) gives n^{e^{log₂d}} = n^{d^{log₂e}}.
- Our lower bound forces e^{log₂d} ≥ √d, i.e. e ≥ √2. That is exactly C3's d = 2 bound, so there is no contradiction (H24's 1.62 > √2).
- **If** SoS compositions of exponent √2+o(1) exist (the shape of Khoruzhii's unverified claim and of oaG Cor 6.2's sharpness), then for d = 2^j fixed, PT-rank(I_{n^d}) = n^{√d±o(1)} over ℂ. The lower bound would then be tight.
- **External refutation test:** any construction with PT-rank(I_{n^d}) ≤ n^{(1−ε)√d} at a single fixed d would refute `prime_flats` over ℂ.

**Inputs.** [OAI] `HasSpectralFlat K d` for d ≥ 3, i.e. `prime_flats` itself (the deep theorem; the `plane` route covers only d = 2). [theirs: Liu] layouts and closure-to-exact. [theirs: RZ] the PT-rank definition and the char ≠ 2 bijection. [ours] the glue, the orthonormal placement and step 6.

**Weakest link.** `prime_flats` (unbuilt, assumed by directive). In our part, the d-dimensional glue is the audited glue verbatim, since positions are unconstrained. It is not formalised.

**Rank.** This is the first superpolynomial-in-d, superlinear explicit PT-rank/multiquadratic SoS lower bound over every field, with a matching conditional upper bound. It is a clean generalisation of C3 (d = 2) but gives no VNC¹ consequence. **Rank ~15–20; merge into item #3 as "d-fold: n^{√d}".**

## 3. Theorem T3-B (the lifted identity polynomial; answers SW §1.3 future work)

**Statement.** Over every field, for all n ≥ 2 and d ≥ 2, with r = ⌊log₂n⌋:

  log₂(1 + C̲(LID_{n,d})) ≥ λ_d·r − O(√(d·r·log d)),  where λ_d ≥ √3·ρ_d ≥ (√3/π)·d.

C̲ is border nc circuit size. λ_d is C4's exact descent value on the regular 2d-gon (λ₂ = √2, λ₃ = √3, λ₄ = 1+√2, λ₁₆ ≈ 9.0). So LID_{n,d} needs n^{0.551d − o(d)} gates, uniformly in n and d. The upper bound is n^d·poly (ABP), and the descent method is capped at (2/3)·d·log n.

**Proof.** LID's coefficient tensor, restricted to 2^r letters per position, is Π_{k≤d} EPR_{2^r}(k, d+k): d mutually crossing chords. This is C1 Thm B with m = d and r bits per position (C4 (iii) gives the exact λ_d), with c_S < 2π and A ≤ (2d+1)². Circle placement, Liu's descent, two-hub layouts, glue, closure-to-exact. ∎

**Measure separating Pal and LID** (SW's request): val*(matching), i.e. the Euclidean price versus best descent stop. It is O(1) for nested chords (Pal) and ≥ (√3/π)·#chords for crossing chords (LID). This is C1 Thm B stated as a dichotomy, so the attribution is C1+C4. Our addition is the identification with SW's and HWY's named target and the uniform-in-(n,d) form.

**Rank.** A corollary, but it settles a polynomial named in a 2026 paper as the next target ("conjectured hard [HWY11]"). **Rank ~20, merge into item #3.**

## 4. Corollary T3-C (circuits over the ring F⟨Z⟩; Raz Thm 2 + bridge)

Over every field F, with R = F⟨Z⟩ the free algebra (also R = F⟨z₁, z₂, …⟩): any arithmetic circuit over R that computes Perm_n or Det_n (row-ordered) as a function R^{n²} → R has size ≥ 2^{(√3/π)n − O(√(n log n))}. Likewise LID_{n,d} needs n^{0.551d−o(d)} and ID_k needs k^{√2−o(1)}.

**Proof.** Raz Thm 2 converts the circuit into a symbolic nc circuit of the same size (constant terms of the ring constants). Then apply C1 Thm A, T3-B, or C4 S1, using their exact (non-border) versions. ∎

This is exponential against Raz's own n^{1.5}, which he describes as the first bound beyond n log d for circuits over any ring. It is one line. **Rank ~30, merge.**
