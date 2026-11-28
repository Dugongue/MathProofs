# Point counting and point finding for fixed straight-line complexity

Conditional on the deterministic counting subroutine named in the proof. This is a written, independently unaudited transfer.

## 3. Theorem D3-P (new): point counting and point finding on fixed-complexity varieties

**Setup.** Let p be a prime, b = ⌈log₂ p⌉. Let Γ be a division-free straight-line program of size C over Z[x_1,…,x_v]. Its gates are a variable x_i, a constant in [0,p), g_a ± g_b, or g_a·g_b. Designated output gates compute F_1,…,F_k, with v + k ≤ C. Put V = {x ∈ F_p^v : F_j(x) = 0 ∀j}.

**Theorem D3-P.** Assume [OpenAI ETH paper, Thm D.1] (equivalently, the paper's Thm 2.2).
1. #V(F_p) is computable deterministically in poly(C, b)·2^{O(Cb/√log(Cb))} bit operations and poly(C, b) space, with an absolute implied constant.
2. With vb further calls of the same size, the lexicographically least point of V(F_p) is found (or V(F_p) = ∅ is certified).
3. For fixed C the time is p^{O(C/√log log p)} = p^{o(1)}. It stays p^{o(1)} whenever C = o(√log b).
4. The same holds over F_{p^k}, with Cb replaced by C·k(b + log k). This needs a monic irreducible h ∈ F_p[X] of degree k as part of the input.

**Proof (complete, modulo D.1 and Lemmas 2.3–2.4).**
1. *Words.* Each variable x_i is a b-bit word w_i. Range-check w_i < p with a Lemma 2.4 comparator: O(b) edges, degree ≤ 6.
2. *Gates.* Each ± or × gate is a Lemma 2.4 gadget on canonical residues with its own output word: O(b) edges, maximum degree O(b^{3/4}).
   - Constants are hard-coded inside the gadget tensors.
   - Each output word of an F_j is pinned to 0 by unary tensors.
3. *Fan-out.* A gate word used t times gets the equality trees of (2.1). The total number of occurrences is ≤ 2C + k, so the trees add O(Cb) edges. Subdividing every edge makes the network bipartite.
   - So e_net = O(Cb), Δ_net = O(b^{3/4}), and by (2.2) s_BTN = O(Cb), because Δ^{10/9} = O(b^{5/6}) ≤ e_net.
   - There are poly(Cb) vertices, and every entry evaluates in poly(b) time.
4. *Parsimony.* Every x ∈ [0,p)^v determines every gate word uniquely, by the parsimony of each Lemma 2.4 gadget (canonical residues; quotient witnesses unique by Euclidean division). The resulting assignment has weight 1 iff every F_j(x) ≡ 0, and every other assignment has weight 0.
   - So Contract = #V(F_p).
   - Take ι = 1 and P₀ = e_net + 1 > vb ≥ log₂ #V. The least nonnegative residue is then the exact count.
5. *Time.* Thm D.1 contracts in (s+L)^{O(1)}·2^{O(s/√log s)}, where L = poly(C,b) is the description length. This proves (1).
6. *Search.* Pin the bits of w_1,…,w_v from most significant to least. Pins are unary tensors on subdivided word wires, which adds O(1) degree. Keep the 0-branch whenever its count is positive. That is vb further contractions, proving (2).
   - (3) is arithmetic: Cb/√log(Cb) = b·O(C/√log b).
7. *(4), F_{p^k} arithmetic.* An element is k words. For the product c = a·a′:
   - Pack the coefficients into integers with spacing 2b + ⌈log₂ k⌉ + 1 bits. One Lemma 2.3 product computes all coefficients exactly as nonnegative integers (spacing prevents carries).
   - Introduce witness polynomials q (degree < k−1) and r (degree < k) with canonical F_p coefficients.
   - Compute q·h by a second Kronecker product. Check (q·h)_i + r_i ≡ c_i (mod p) coefficientwise with Lemma 2.4.
   - Division by a monic h is unique, so this is parsimonious.
   - Edges O(k(b + log k)), degree O((kb)^{3/4}). ∎

**Corollary D3-P1 (deterministic point finding on curves).** Assume D.1. For any plane curve F(x,y) = 0 over F_p of fixed degree d, a point of C(F_p) can be found deterministically, or nonexistence certified, in p^{O(d²/√log log p)} = p^{o(1)}.
- More generally, the number of points in any box [0,X] × [0,Y] can be counted. A comparator adds O(b) edges.
- Previous deterministic bound: p^{1/2+o(1)}. Even with poly-time factoring one must search for x with F(x,Y) having an F_p-root, and incomplete Chebotarev/Weil bounds only guarantee such an x below ~d²√p log p.
- Elliptic curves were already polynomial (K4). The gain is for every other curve family, including hyperelliptic curves of fixed genus, where no SvdW-type map exists in general.
- Status: PROVED mod D.1, 90%. Novelty: ~70%, because the prior-art search was one web query plus a local grep.

**Corollary D3-P2 (zeta functions of fixed varieties).** Assume D.1 and OpenAI Oct-4 factoring (used only to construct irreducible polynomials of degree k, via Shoup's 1990 deterministic reduction to factoring). For X of fixed complexity (dimension, number of equations, degrees), Z(X/F_p, T) is computable deterministically in p^{o(1)}.
- By Bombieri–Katz, Z is rational of total degree ≤ B(X), a bound depending only on the complexity. So the counts #X(F_{p^k}) for k ≤ 2B determine Z by Padé. Each count is D3-P(4) with k = O(1).
- For curves and abelian varieties this is dominated by Pila / Adleman–Huang (poly(log p)).
- It matters from dimension 2 up: K3 surfaces, general surfaces, singular varieties. There the best known single-prime deterministic bound is (from memory) p^{1/2+o(1)}.
- Status: PROVED modulo D.1, OpenAI factoring and the cited Bombieri–Katz bound, 85%.

**What D3-P is not.**
- It is not a consequence of the DLOG algorithm. It uses neither Theorem 4.3 nor Cauchy–Hermite beyond D.1 itself.
- It needs D.1's tolerance of degree-b^{3/4} vertices. The #k-SAT route (the Lean-checked n(log log n)²/√log n exponent) does **not** suffice. Tseitin-encoded F_p multiplication costs ≥ b log b variables, which is outside the N·o(√log N) budget of eth-fallout W1 Thm 0. So D3-P genuinely depends on the BTN engine with high-degree arithmetic gadgets.

---
