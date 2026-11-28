# The circle-placement improvement

Conditional on the stated unrefereed flat and planar inequalities. The text incorporates the audit’s correction for degree larger than the number of matched pairs.

## 1. Statements

Notation:
- K is any field. C̲ is Liu's border circuit size: ordered products, unrestricted intermediate degree, Zariski closure over K̄.
- D_n = Σ_{w∈{0,1}^n} z_w z_w. Its coefficient tensor is W_n = Π_{k=1}^n [a_k = a_{k+n}] ∈ (K²)^{⊗2n}, the diameter pairing.

**Theorem A (improved constant).** Over every field K, for n ≥ 2,

  log₂(1 + C̲(D_n)) ≥ √3·ρ_n − √(4π n log₂(2n+1)) − O(log n) ≥ (√3/π)·n − O(√(n log n)).

Hence, by Liu Lemma 3.1 (C̲(D_n)+1 ≤ n^{O(1)}(C̲(P_n)+1) for P_n = Perm_n or Det_n, row-ordered):

  log₂(1 + C̲(Perm_n)), log₂(1 + C̲(Det_n)) ≥ (√3/π)·n − O(√(n log n)),  with √3/π = 0.55133… > 1/2.

**Theorem B (general crossing form).** Let P be homogeneous noncommutative of degree d over any finite alphabet. Suppose that, after position-local linear maps (a different map at each position is allowed), its coefficient tensor restricts to Π_{k≤m} EPR₂(i_k, j_k) on 2m positions i_1 < … < i_m < j_1 < … < j_m, i.e. m mutually crossing chords, with every other position mapped to a fixed vector. Then

  log₂(1 + C̲(P)) ≥ (√3/π)·m − O(√(m log d) + log d).

More generally, for any matching pattern M on the positions:
- the bound is val*(M) − O(√(d log d)), where val*(M) is the sup over placements with partners antipodal of the descent-game value (§3);
- the palindrome pattern has val* = O(1), consistent with its linear-size circuits;
- the copy pattern has (√3/π)m ≤ val* ≤ (2/3)m + 1.

**Corollary C (cut-restricted partition rank, every field).** Call S ⊂ [N] a half-arc if it is ⌈N/2⌉ cyclically consecutive legs. The half-arc partition rank prk_½(T) of an N-tensor is the least A with T = Σ_{a≤A} f_a(legs in S_a)·g_a(legs outside S_a), each S_a a half-arc. Then:
- prk_½(W_m) ≥ 2^{2m/π³} = 2^{0.0645m}, and prk_½(W_m) ≤ 2^m;
- for even n and det_n, perm_n viewed as n-tensors in their columns: 2^{n/π³} ≤ prk_½ ≤ C(n, n/2) = 2^{Θ(n)};
- by contrast, prk(det_n) ≤ n and prk(perm_n) ≤ n (vp-collapse R-X1), and prk_½ of the unit tensor ⟨n⟩ is at most n.

So restricting partition rank to arc cuts turns the format-capped invariant of item 9 into an exponential one. It still does not see VP vs VNP: det and perm are both 2^{Θ(n)}, including in char 2.

## 2. Inputs

| input | owner | status |
|---|---|---|
| `HasSpectralFlat K 2`: a `SpectralPlacementPrices K ℝ²` exists, for every field. Two Lean routes: `HasSpectralFlat.plane` (Flat.lean:33) or `prime_flats` + `all_dimensions` | **OpenAI** (treated as proved; not built by us) | Lean statement read; structure fields checked: `group`, `wire`, `collapsed`, `normalized` |
| Chord descent (circuit ⇒ Σ over long intervals of rank-≤H pieces), closure-to-exact by tensor powers, Lemma 3.1 (D_n ≤ Perm_n, Det_n) | **Liu** 2611.00994 §2–3 | audited PASS (audit-L2-glue §6) |
| Glue: price ≤ network cost on arbitrary sites; sum rule φ(ΣN_a) ≤ A·max φ(N_a); price of a product of wires | **ours** (audit-L2-glue §2–3) | PASS; positions unconstrained |
| Multi-site placement on the 2n-gon; c_S ≤ path length < 2π; the game formulation; the √3ρ triangle constant; the 2/3 ceiling; Corollary C | **ours, new here** | §3–5 |

## 3. Proof of Theorem A

Fix the field K and a price system P (OpenAI). Put d = 2n, let u_k = (cos(π(k−1)/n), sin(π(k−1)/n)) for k = 1..2n, and use u_k as the **site** of position k. The sites are 2n distinct points of the unit circle, and u_{k+n} = −u_k. Let p_j = Σ_{k≤j} u_k. These are the vertices of a regular 2n-gon Π with unit sides, p_0 = p_{2n}, centre O and circumradius ρ_n.

**Step 1 (price of W_n = 2n).** W_n is the per-site product of the n wires EPR(k, k+n). Write price = c_S·log₂φ with c_S = price(diag_S) > 0.
- φ is multiplicative, so price(W_n; u) = Σ_k price(EPR(k, k+n); u).
- `group` (trivial slots) and `wire` turn each term into ‖u_k − u_{k+n}‖ = 2.
- The total is 2n.

**Step 2 (normalisation c_S < 2π).** GHZ on S is a restriction of the path of 1-bit wires u_1u_2, u_2u_3, …, u_{2n−1}u_{2n}: at each site, apply the copy map K²⊗K² → K², |ab⟩ ↦ δ_ab|a⟩. By glue step 3, c_S ≤ Σ‖u_{k+1} − u_k‖ = (2n−1)·2 sin(π/2n) < 2π. (This replaces the star bound c ≤ 4, which here would only give c ≤ 2n.)

**Step 3 (Liu's descent with stopping chord L = √3ρ_n).**
- Take a size-s circuit and homogenise it, giving H = O((d+1)²(s+1)) gates. Expand the degree-d output exactly as in Liu Lemma 2.1, stopping a term at the first interval (i, j] with ‖p_j − p_i‖ ≥ L.
- *Triangle fact.* A triangle with vertices among the p's that contains O has an edge ≥ √3ρ_n. Its three arcs sum to 2n steps and each is ≤ n, otherwise O is outside. So the longest arc m satisfies 2n/3 ≤ m ≤ n, and its chord is 2ρ_n sin(πm/2n) ≥ 2ρ_n sin(π/3).
- *Descent.* Liu's invariant O ∈ Q_ij = conv{p_i..p_j} passes to a child, because Q_ij = Q_ik ∪ △p_ip_kp_j ∪ Q_kj (points in convex position, in cyclic order).
  - The root hull contains O.
  - A leaf hull is a vertex or a unit side, at distance ≥ apothem > 0 from O, so it does not contain O. Hence every descent stops.
- *Result.* W_n = Σ_{I∈F} T_I, where F is the set of intervals with chord ≥ L, |F| ≤ A = (d+1)², and rank_{I|I^c} T_I ≤ H.
- *Alphabets.* For a larger alphabet, or for Theorem B, first apply the position-local maps (⊗M_k) to every T_I. Rank across I|I^c does not increase.

**Step 4 (hub layouts).**
- Write v_I = p_j − p_i and a = v_I/‖v_I‖. By the hub lemma (OpenAI Lemma A.3; Liu Fig. 1), T_I is a restriction of the network N_I with:
  - a 1-bit cable from each position k ∈ I to a hub at t·a, and from each k ∉ I to a hub at −t·a;
  - an h = ⌈log₂H⌉-bit cable between the hubs.
- Since Σ_{k∈I} u_k = v_I and Σ_{k∉I} u_k = −v_I, and ‖u − ta‖ ≤ 1 − t⟨u, a⟩ + t²/2 for unit u, a:
  cost(N_I) ≤ 2n − 2t‖v_I‖ + n t² + 2th ≤ 2n − 2tL + nt² + 2th.

**Step 5 (glue).**
- Price ≤ cost on arbitrary sites, plus the sum rule at S, give 2n ≤ max_I cost(N_I) + c_S·log₂A.
- Hence L − h ≤ nt/2 + c_S·log₂A/(2t).
- Take t = √(c_S·log₂A/n), which is < 1 for large n. Then h ≥ L − √(c_S n log₂A) ≥ √3ρ_n − √(4π n log₂(2n+1)).
- With h ≤ log₂H + 1 and H = O(n²(s+1)), this gives the first display of Theorem A.

**Step 6 (border).** Liu's closure-to-exact argument applies unchanged.
- The layout set {N_I : I ∈ F} depends only on (n, s).
- If W_n is in the closure of sums of restrictions of these layouts, then W_n^{⊗q} (on the same 2n sites, with q bits per site, price 2nq) is a sum of poly(q)·A^q networks of cost ≤ q·max cost.
- So 2nq ≤ q·max cost + c_S·log₂(poly(q)A^q). Divide by q and let q → ∞.

**Step 7 (transfer).** Liu Lemma 3.1 (a matrix simulation that preserves closure, overhead n^{O(1)}) moves the bound to Perm_n and Det_n at the same n, over every field. ∎

**Theorem B.**
- Sites of the unused positions carry 0 bits, so they cost nothing and contribute nothing to the prefix sums.
- The 2m used positions take the 2m-gon directions in their own order. i_l gets the angle π(l−1)/m, and its partner j_l gets π(l−1)/m + π. The direction sequence along the word is then exactly the circle's.
- The rest is Steps 1–7 with n replaced by m.
- For a general matching M the descent needs no convexity. The game DP of §4 certifies the stopping family directly, because Liu's Chooser strategy depends only on the current interval. ∎

## 4. The descent game, the 2/3 ceiling, and numerics (K3)

- **Game.** The Builder (the circuit) splits an interval at k, and the Chooser follows a child. Chooser wins on reaching a chord ≥ L. Its value is val(I) = max(chord(I), min_k max(val(i,k), val(k,j))). This is exactly what Liu's descent uses, and val(root) is the admissible L.
- **Ceiling.** For every antipodal unit placement, in every dimension, with interval two-hub layouts (prime_flats gives `HasSpectralFlat K D` for all D), val ≤ 2n/3 + 1.
  - The Builder splits the root at 2n/3 and then the long child at 4n/3.
  - Every interval reached afterwards has ≤ 2n/3 + 1 steps, so its chord is at most that.
  - So this method can never reach the trivial upper bound log C̲(D_n) ≤ n + O(log n).
- **C++ results.**
  - game.exe confirms val/n = 0.55136 at n = 90 for the circle (√3/π = 0.55133) and exactly 0.5 for Liu's square.
  - Three- and four-dimensional antipodal perturbations of the circle only lower val.
  - climb.exe hill-climbs over antipodal curves. The best excess over the circle is +0.0070 at n = 24 and +0.0028 at n = 48, in both 2D and 3D. It shrinks like 1/n, so it reads as discretisation.
  - Conjecture: √3/π is optimal for interval two-hub descents.
- **Triangle stops.** Stopping at triangles with a three-hub Steiner layout gives h ≥ (Σ‖v_m‖)/Steiner(a). At the Builder's equilateral split this is again √3ρ, so there is no gain (killed, §6).

## 5. Proof of Corollary C

- **Setup.** Use the circle placement on N = 2m legs. A term f(S)g(S^c) with S a half-arc is a restriction of the two-hub network with **no** hub cable (h = 0).
- **Cost.** ‖v_S‖ = 2ρ_m (a diameter of the polygon), so cost ≤ 2m − 4tρ_m + mt².
- **Glue.** 2m ≤ 2m − 4tρ_m + mt² + c_S·log₂A. At t = 2ρ_m/m this gives log₂A ≥ 4ρ_m²/(m·c_S) ≥ 4(m/π)²/(2πm) = 2m/π³.
- **Upper bound.** Across one half-arc, W_m has rank 2^m.
- **det_n, perm_n (n even).** Restrict columns k and k + n/2 to a private pair of rows, and send the other rows' unit vectors nowhere. This gives a product of n/2 copies of det₂ or perm₂, each ≅ EPR₂ by a local sign. Restriction of each term keeps it split across the same half-arc, so prk_½ ≥ 2^{(n/2)·2/π³}.
- **Upper bound via Laplace.** Laplace expansion across the half-arc gives C(n, n/2) terms.
- **Unit tensor.** ⟨n⟩ = Σ_c e_c^{⊗n} has n terms, each split across every cut.
- **Why flattening alone fails.**
  - Averaging rank_S over random half-arcs S (Raz-style) only gives A ≥ Ω(m): a term on a shifted half-arc has rank ≤ 2^{2 min(sh, m−sh)} across S.
  - The Euclidean spectral point is what makes it exponential. ∎
