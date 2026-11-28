# Self-conjugate immanants and hook families in characteristic two

The Valiant-class hardness and the conditional separations have different dependencies.

## Definitions
- Imm_λ(X) = Σ_{σ∈S_N} χ^λ(σ) Π_i x_{i,σ(i)}, read over F through Z → F.
- b(λ) := the number of boxes to the right of the first column.
- For a self-conjugate λ = λ' with r diagonal cells, D(λ) = (d_1 > ... > d_r) are the diagonal hook lengths, d_i = 2(λ_i − i) + 1. These are distinct and odd, d_1 = 2λ_1 − 1, and Σ d_i = N.
- For a partition μ ⊢ N: C_μ(X) := Σ_{σ of cycle type μ} Π x_{i,σ(i)}.
- Hook (a, 1^b) ⊢ N = a + b. Its conjugate is (b+1, 1^{a−1}).

## Theorem S (every field of char 2)
For every self-conjugate λ: **χ^λ(μ) ≡ [μ = D(λ)] (mod 2).** Hence over char 2,
  Imm_λ(X) = C_{D(λ)}(X).

*Proof.*
1. By Murnaghan–Nakayama, with the parts of μ removed in a fixed order, χ^λ(μ) = Σ_T (−1)^{ht T} over rim-hook tableaux T (chains λ = λ^0 ⊃ λ^1 ⊃ ... ⊃ ∅ with λ^{i−1}∖λ^i a rim hook of length μ_i). Mod 2 this is #T.
2. Since λ' = λ, transposing every shape is an involution on these tableaux, because transposition maps rim hooks to rim hooks. So #T ≡ #(fixed tableaux), the chains of self-conjugate shapes.
3. Maya diagram. Let S(λ) = {λ_i − i + ½} ⊂ Z + ½. Conjugation is S ↦ −(Z+½ ∖ S). Removing an ℓ-rim hook moves one bead x ∈ S to x − ℓ ∉ S. In conjugate coordinates the same removal moves ℓ − x to −x.
4. A removal between two self-conjugate shapes is its own transpose, so x = ℓ − x, i.e. x = ℓ/2. This forces ℓ odd and ℓ/2 ∈ S, and −ℓ/2 ∉ S is then automatic. For λ self-conjugate, the positive beads are exactly the d_i/2.
5. So a symmetric ℓ-removal exists iff ℓ ∈ D(λ). It is unique, and the result has diagonal hook set D ∖ {ℓ}.
6. A fixed tableau of content μ therefore exists iff μ (as a multiset) equals D(λ), and then there is exactly one. ∎

**Machine check:** [local reference omitted] (Murnaghan–Nakayama on β-numbers) gives the mod-2 support = {D(λ)} for every self-conjugate λ ⊢ N ≤ 14, 22 shapes in all.

**Corollary S (completeness).** Let (λ_N) be any family of self-conjugate shapes (N ranging over an infinite set). Over every field of char 2 it is VNP-complete under p-projections with constants {0, 1}.
- Hardness. Let P be the permutation matrix of disjoint cycles of lengths d_2, ..., d_r. Then C_D(A ⊕ P) = HC_{d_1}(A): the cycle type splits uniquely because the parts are distinct. So HC_{2λ_1 − 1} ≤_p Imm_{λ_N}, and λ_1 ≥ √N (since N ≤ λ_1·λ'_1 = λ_1²). This is a p-family reduction. For VNP-completeness in Valiant's sense on a sparse index set, pad HC_n ≤ HC_{n'} for n ≤ n' (C9's routing trick).
- Membership. Immanants are in VNP over any field (GapP characters, Valiant's criterion).
- Examples: staircases δ_k ↦ HC_{2k−1}; squares (k^k) ↦ HC_{2k−1}; self-conjugate hooks (h+1, 1^h) give Imm = HC_{2h+1} **identically** (a second proof: the palindromic half-sum Σ_{k≤h} P_k = P(1)/2 = 2^{#cycles − 1}).

## Theorem H (hook dichotomy, every field of char 2)
Let λ_N = (a_N, 1^{b_N}) and μ_N := min(a_N, b_N + 1). Since Imm_λ = Imm_{λ'} in char 2, the roles of a and b+1 are symmetric.
1. If μ_N = O(1), then Imm_{λ_N} ∈ VP (the b(λ) or b(λ') bounded algorithm works over any ring, see below).
2. If μ_N ≥ N^ε, then Imm_{λ_N} is VNP-complete under p-projections with constants {0, 1}. The hardness size is ≥ c·min(μ_N, N^ε).

### Padding calculus (an integer identity, every characteristic)
Let A be n×n and B be m×m. Then
  Imm_{(a,1^b)}(A ⊕ B) = Σ_{s=0}^{n−1} [y^{b−s}] Q_B(y) · Imm_{hook_s}(A),   where   Q_B(y) := Σ_{σ∈S_m} B^σ Π_{cycles C}(1 − (−y)^{|C|}).
- *Proof.* Restrict χ^λ to S_n × S_m. The Littlewood–Richardson rule for hooks gives c^{(a,1^b)}_{hook_s, hook_t} = [b ∈ {s+t, s+t+1}]. So the coefficient is Imm_{hook_{b−s}}(B) + Imm_{hook_{b−s−1}}(B) = [y^{b−s}](1+y)H_B(y). By Murnaghan–Nakayama, Σ_t χ^{hook_t}(σ) y^t = Π(1 − (−y)^{μ_i})/(1+y).
- Q is multiplicative over ⊕.
- Gadgets: I_1 ↦ 1+y; a c-cycle P_c ↦ 1 − (−y)^c; S_3 := I_3 + P_{(123)} ↦ 2 + 3y + 3y² + 2y³ ≡ y(1+y) (mod 2). In odd characteristic use S_2 := [[1,1],[−1,1]] ↦ 2y(1+y).
- Machine-checked over Z: the identity holds in 660/660 random cases (n ≤ 4, m ≤ 5), and the gadget Q-polynomials are as stated ([local reference omitted]).
- In char 2: HC_n = n^{-1} Σ_s Imm_{hook_s}(A) for n odd (C9 identity 3). For n odd, Imm_{hook_{(n−1)/2}}(A) = HC_n(A) by Theorem S, and Imm_{hook_s} = Imm_{hook_{n−1−s}}.

So it suffices to find B whose Q-window w_s := [y^{b−s}]Q_B, s = 0..n−1, has one of two shapes:
- **(HC)** n is odd and w_s ≡ 1 for all s;
- **(SC)** n is odd, w_{(n−1)/2} ≡ 1, and w_s ≡ w_{n−1−s} for all s. Conjugate pairs then cancel mod 2, leaving Imm_{hook_{(n−1)/2}}(A) = HC_n(A).

Throughout, B = S_3^{⊕t} ⊕ I_u ⊕ (optional P_c), with m = 3t + u + c and n = N − m.

**Route 1 (top run, any parity of N).** Take Q = y^t(1+y)^{2^g−1}(1+y^c) with t + u = 2^g − 1 and c ≥ 2^g, and put the window in the upper copy. The conditions reduce to: a − 2^g ≤ t ≤ min(a − n, 2^g − 1), n ≤ 2^g, and c = b − a − n + 2^g + 1 ≥ 2^g (with t = a − 2^g). Taking 2^g ∈ [(a+1)/2, a], window (HC) holds for every odd n ≤ min(2^g, b − a + 1). **Hardness: n ≈ min(a/2, b − a + 1).** Applied to the conjugate it gives n ≈ min((b+1)/2, a − b − 1). This settles |a − b| ≥ N^ε.

**Route 2 (bottom run, N even).** Take Q = y^t(1+y)^{w}, w = 2^G − 1, m = 2t + w, t = (N − n − w)/2, with the window inside [t, t + w]. The conditions are w ≥ |a − b| + n, (N − n)/3 ≤ w ≤ N − n, and n odd (parity is fine since N is even and w is odd). For |a − b| ≤ N/8, n ≈ N/8, a 2^G ∈ (N/4 + 2, 7N/8] exists. **Hardness Ω(N).**

**Route 3 (step-2^k run, N odd, the near-central band).** Take k := v_2(b − a + 1) (k ≥ 1 for N odd, a ≠ b + 1) and Q = y^t(1+y)^{2^G − 2^k} = y^t Σ_{j ≡ 0 (2^k), j < 2^G} y^j, with m = 2t + 2^G − 2^k even, so n = N − m is odd.
- The window centre j_0 = b − (n−1)/2 satisfies j_0 − t = (b − a + 1 + 2^G − 2^k)/2 ≡ 0 (mod 2^k) exactly because v_2(b − a + 1) = k. So the window is palindromic about a support point, and (SC) holds provided its residue-t positions lie in the run.
- That holds when 2^G + 2^k ≥ max(b − a + n + 2, a − b + n) and 2^G − 2^k ≤ N − n ≤ 3(2^G − 2^k).
- For |a − b| ≤ N/16 and n ≈ N/8 such a G exists. **Hardness Ω(N).**
- The single remaining point a = b + 1 is Theorem S: Imm = HC_N.
- Brute-force checks over S_N: (a,b,n,t,u) = (5,2,3,1,1), (6,3,3,2,0), (3,6,5,0,4) all give Imm = HC_n mod 2 (4/4 each). The control (4,5) with the wrong k fails as predicted ([local reference omitted]).

**Coverage scan.** [local reference omitted] searches all (t, u, c) for every hook with N ≤ 80. With μ_N ≥ 8, the only shapes without a size-≥8 reduction are exactly a = b+1, which is Theorem S. All three routes are therefore needed, and together they suffice.

**VP side.** For λ with b(λ) = k bounded: χ^{λ'} = Σ_{π∈S_{ℓ}} sgn(π) Ind_{S_α(π)}^{S_N} 1 (Jacobi–Trudi), with at most k+1 parts of which all but one are ≤ k. So Imm_{λ'}(X) = Σ_π ± Σ_{ordered set partitions} Π per(X[B_i]) and Imm_λ = the same with det. That is n^{O(k)} products of determinants, an integer formula valid over every ring. In char 2 apply it to whichever of λ, λ' has b bounded.

**No-go (explains why Route 3 is needed).** For N odd, a pure (HC) window with n odd must be disjoint from its mirror under the palindromy of Q_B (y^m Q_B(1/y) = Q_B(y) in char 2, and Q_B(1) = 0). Hence n ≤ |a − b − 1| + O(1). So near-central odd hooks are unreachable by HC-windows, and the self-conjugate route is what closes the band.

## Separation corollaries (Hexagon: HC ∉ VP, ∉ VP-bar over every field)
Over every field of char 2, including F_2:
- every self-conjugate immanant family, including staircases and squares, is ∉ VP and ∉ VP-bar;
- every hook family with min(a, b+1) ≥ N^ε is ∉ VP and ∉ VP-bar;
- hooks with min(a, b+1) = O(1) are in VP.
This is the first complete char-p analogue of the Bürgisser / Curticapean characteristic-0 hook classification. The char-2 answer has a genuinely different VP side: the long-row hooks, which contain per = det.

## Novelty / priority (5-minute check)
- C9 covered only (p^e, 1^{n−1}). Curticapean 2102.04340 §8 lists modular immanants as open. The web search found nothing on char-2 immanant hardness.
- The mod-2 support statement of Theorem S was not found stated. Known nearby facts: self-conjugate characters vanish on odd classes, and |χ^λ(D(λ))| = 1 (the A_n splitting). It is a one-paragraph involution argument and may be known to specialists. Its complexity consequence, all self-conjugate families VNP-complete in char 2, and the hook dichotomy are new.
- **Not FOLKLORE:** the dichotomy needs three distinct constructions plus the no-go.
