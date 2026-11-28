# Hook families in odd characteristic and characteristic zero

The scope is the stated uniform families and reductions.

## Setting
- λ = (a, 1^b) ⊢ N = a + b, with b(λ) = a − 1 boxes right of the first column.
- A is n×n. P_c is a c-cycle permutation matrix, J_k is the k×k all-ones matrix, and S_2 = [[1,1],[−1,1]].
- Padding calculus (proved and machine-checked in R-A2-immanants-char2.md):
  Imm_{(a,1^b)}(A ⊕ B) = Σ_{s<n} [y^{b−s}]Q_B · Imm_{hook_s}(A),   with Q_B(y) = Σ_σ B^σ Π_C (1 − (−y)^{|C|}),
  and Q multiplicative over ⊕.
- Gadget values: Q_{P_c} = 1 + (−1)^{c+1} y^c; Q_{J_k} = k!(1+y) (only |W| ≤ 1 principal minors of J are nonzero); Q_{S_2} = 2y(1+y).
- Since Imm_{hook_0} = per: if Q_b ≠ 0 and Q vanishes on [b−n+1, b−1], then Imm_{(a,1^b)}(A ⊕ B) = Q_b · per_n(A).

## Theorem (char F = 0 or odd p)
Let a ≥ 2. The family is hard as follows.
1. **b ≥ a.** B = P_b, Q = 1 ± y^b, n = a. So Imm = (−1)^{b−1} per_a(A).
2. **a > b, J-route.** Write d := a − b − 1 ≥ 0. Choose k_1, …, k_r ∈ [2, p−1] (any k_i ≥ 2 in char 0) with Σ(k_i − 1) ≥ d + 1, which is possible with r = ⌈(d+1)/(p−2)⌉. Put B = J_{k_1} ⊕ … ⊕ J_{k_r} ⊕ P_b. Then Q = Π k_i! · (1+y)^r (1 ± y^b), whose support is [0, r] ∪ [b, b+r]. So for n := a − Σk_i ≤ b − r we get
   **Imm_{(a,1^b)}(A ⊕ B) = (−1)^{b−1} Π k_i! · per_{a−Σk_i}(A),** and the hardness size is b − r with minimal choices.
3. **a > b, shift route.** B = S_2^{⊕b}, Q = 2^b y^b (1+y)^b, n = a − b. So Imm = 2^b per_{a−b}(A).

Combined: for a > b the hardness is max(a − b, b − ⌈(a−b)/(p−2)⌉).
- If a − b ≥ a/3, route 3 gives size ≥ a/3.
- Otherwise b > 2a/3 and r ≤ a − b < a/3, so route 2 gives size b − r > a/3.
In every case the hardness size is > a/3.

### Dichotomy
Over every field of characteristic 0 or odd p:
- **a_N = O(1):** VP (b(λ) bounded; the Jacobi–Trudi det-product formula, valid over every ring, see R-A2-immanants-char2.md).
- **a_N ≥ N^ε:** VNP-complete under p-projections, by reduction from per_{Ω(a)}, which is VNP-complete in char ≠ 2. Membership: immanants are in VNP.

**Corollary (Hexagon).** Over every field of odd characteristic, every hook family with arm a ≥ N^ε is ∉ VP and ∉ VP-bar. Together with R-A2-immanants-char2.md, hook immanants are now classified in **every characteristic**:
- char ≠ 2: VP iff the arm is bounded;
- char 2: VP iff the arm or the leg is bounded.

## Checks
- **Brute force over S_N** ([local reference omitted]): the J-route gives Imm = (−1)^{b−1} Π k! per_n(A) mod p for (p,a,b,ks) = (3,4,3,{2}), (3,6,4,{2,2}), (5,5,4,{2}), (5,6,4,{3}), (5,7,5,{3,2}), 3/3 each. Q_{J_3} = 6(1+y) is confirmed.
- **Shift route** (hooks.cpp): 4/4 on five (p,n,t,u) cases.
- **Coverage scan** (bandscan.cpp, with J-blocks): for p = 3 and 5, every hook with 40 ≤ b ≤ 79 and 0 ≤ a − b − 1 ≤ 8 has a reduction of size ≥ b − O(d). The near-square band a ≈ b, the only place the cycle and shift routes are weak, is exactly where the J-route is strongest.

## Novelty / priority
- Char 0: Bürgisser (SIAM J. Comput. 2000) and Curticapean (2102.04340) via interpolation and division.
- Char p: only C9 (ours, sparse sizes (p^e, 1^{n−1})). Curticapean §8 lists modular immanants as open. The 5-minute check found nothing on char-p hook hardness.
- Each route is a one-block padding (FOLKLORE-level gadget). The J_k "(1+y) at cost k" block is what closes the near-square band. The complete char-p hook dichotomy is new.
