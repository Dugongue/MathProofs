# Lucas-modular arithmetic and equations in Sol lattices

The proofs give the displayed translations and the exact reduction to one relation.

## 1. Setting

Take A = [[2,1],[1,1]], ε = φ², O = Z[φ] = M, G = M ⋊ ⟨t⟩ with t v t⁻¹ = εv. (The general Sol lattice is treated in Remark 2.3.) By Prop F of r2 (audited PASS), D(G) is the existential theory of the two-sorted structure (Z, +; O, +; (k, v) ↦ ε^k v; constants), and every such existential statement is a system over G. In particular these are all expressible: linear equations among exponents; "k odd" (T = S²t); "k ≡ 0 mod N" (T = S^N); and multiplication of M-elements by any fixed element of O = Z[ε].

Notation:
- δ_c := ε^c − 1.
- For c ≠ 0, e(c) := the positive generator of δ_c O ∩ Z.
- For q ∈ Z and μ ∈ O^×, [q]_μ := (μ^q − 1)/(μ − 1) ∈ Z[μ^{±1}].

Facts used, all proved in r2 Part II / audit-sol.md:

- (F1) For c ≠ 0: δ_c | δ_m in O ⟺ c | m.
- (F2) e(c) = 5F_|c| for c even and L_|c| for c odd. Hence e(c) ≥ F_|c| ≥ φ^{|c|−2}.
- (F3) [q]_μ ≡ q (mod μ − 1) for all q ∈ Z. For negative q: [q]_μ = −μ^{q}[−q]_μ ≡ q.

## 2. Theorem M: multiplication of virtual integers

**Definition.** A *virtual integer with denominator c* (c ≠ 0) is an exponent m with c | m. It represents q = m/c. Put D(c, m) := [m/c]_{ε^c} = (ε^m − 1)/δ_c ∈ O. This is the unique solution of δ_c D = ε^m − 1, and a solution exists iff c | m, by F1.

**Theorem M.** The relation

Mul(c, m₁, m₂, m₃) :⟺ c | m₁, m₂, m₃ and m₃/c ≡ (m₁/c)(m₂/c) (mod e(c))

is defined, for all odd c, by the system

∃ D₁, D₂, D₃, X, Y ∈ O: δ_c D_i = ε^{m_i} − 1 (i = 1, 2, 3), δ_c X = (ε^{m₁} − 1) D₂, D₃ − X = δ_c Y.

*Proof.*
- c is odd, so c ≠ 0, δ_c ≠ 0, and O is a domain. The first three equations hold iff c | m_i, and they force D_i = D(c, m_i).
- The fourth equation reads δ_c X = δ_c D₁ D₂, so X = D₁D₂.
- By F3, D_i ≡ q_i := m_i/c (mod δ_c). The last equation therefore says q₃ − q₁q₂ ∈ δ_c O ∩ Z = e(c)Z.
- Every coefficient is an integer Laurent polynomial in ε^c and ε^{m_i}, so this is a system over G by Prop F. ∎

The same argument gives the additive structure, and residues of constants: D(c, m) ≡ k (mod δ_c) is witnessed by m' = kc. So for each odd c, the virtual integers with denominator c, reduced mod e(c), form an e-interpreted copy of the ring Z/e(c), uniformly in c. Linear relations among the numerators m_i are exact.

**Remark 2.1 (why odd c).** For c = 0 the system degenerates: m_i = 0 and D_i, X are arbitrary, so it is trivially satisfiable. Forcing c odd, or c ∈ (2Z+1) ∩ NZ, excludes 0 by an equation. It is not clear that "c ≠ 0" is expressible in general (§5).

**Remark 2.2 (relation to r2).**
- Prop G of r2 is the special case "q ≡ 0 mod e(c)".
- Prop H is the additive residue map.
- Theorem M adds the multiplicative structure. It is not visible in (Z, +, |, R): there each instance fixes an exponent n and sees only the ideal n·e(n)Z, never a product of two quotients.

**Remark 2.3 (general Sol lattice).** For hyperbolic A ∈ SL₂(Z), M is a lattice in K = Q(ε) and a module over an order O' ∋ ε. The proof is unchanged with residues taken in M/δ_c M:
- fix c₀ ∈ M ∖ {0};
- compare D_i c₀, which is definable as (ε^{m_i} − 1)c₀/δ_c;
- multiply via δ_c X = (ε^{m₁} − 1) D₂c₀.

The modulus becomes the positive generator of {k ∈ Z : k c₀ ∈ δ_c M}. This is ≥ |N(δ_c)|^{1/2}/C_M, which still grows like |ε|^{|c|/2}.

## 3. Corollary L: Lucas-modular solvability reduces to D(G)

**Corollary L.** Given P ∈ Z[X₁, …, X_k] and a Presburger-definable set C ⊆ 2Z + 1, one can effectively write a system Σ_{P,C} over G. It is solvable iff ∃ c ∈ C, q ∈ Z^k with P(q) ≡ 0 (mod e(c)).

*Proof.*
- **Straight-line form.** Write P as a straight-line program: q_l = q_i + q_j, q_l = a (a constant), q_l = q_i q_j, ending in a value q_out.
- **Encoding.** Introduce a common odd denominator c ∈ C and numerators m_l:
  - additions: m_l = m_i + m_j (exact);
  - constants: m_l = a·c;
  - products: Mul(c, m_i, m_j, m_l);
  - the output: δ_c | D(c, m_out). This is the existence of Y with δ_c Y = D(c, m_out), which says q_out ≡ 0 mod e(c).
- **Correctness.**
  - If P(q) ≡ 0 mod e(c), take every intermediate value exactly (m_l = c·value). Every constraint holds.
  - Conversely, additions are exact and products hold mod e(c). So q_out ≡ P(q) (mod e(c)), and hence P(q) ≡ 0. ∎

So any decision procedure for D(G) must in particular decide questions of the form "∃ c ≡ r (mod N): x² − d (or any norm form, any curve) has a point modulo L_c". These turn on the prime factorisation of Lucas numbers through Chebotarev/primitive-divisor phenomena. This does not prove undecidability, since this family is quite possibly decidable. But it is a concrete strengthening of r2's "Artin-type phenomena" remark.

## 4. Theorem C: the exact reduction to one relation

**Definition.** W_div(c, x, w) :⟺ c odd, x | c, and w − x·1 ∈ δ_c O. In words: w is the integer x reduced modulo the Lucas ideal of a multiple c of x.

**Theorem C.** The following are equivalent:
- (i) the graph of multiplication {(x, y, z) ∈ Z³ : z = xy} on the exponent sort is e-definable in G (with constants);
- (ii) the relation W(c, x, w) :⟺ (c odd, w ≡ x mod δ_c) is e-definable;
- (iii) W_div is e-definable.

If they hold, D(G) is undecidable.

*Proof.*

**(i) ⇒ (ii).** For c odd, w ≡ x (mod δ_c) iff ∃ m, D: m = cx (by (i)), δ_c D = ε^m − 1, and w − D ∈ δ_c O. This works because D = [x]_{ε^c} ≡ x by F3.

**(ii) ⇒ (iii).** Add the conjunct x | c, which is ∃v: δ_x v = δ_c, valid by F1 since x ≠ 0 whenever x | c with c odd.

**(iii) ⇒ (i).** First define multiplication on odd integers. Let ψ(c, x, w) define W_div. For odd x, y, z let Φ(x, y, z) be:

∃ c, s, m₁, m₂, m₃ ∈ Z, ∃ w₁, w₂, w₃, D₁, D₂, D₃, Y₁, Y₂, Y₃ ∈ O:
- c = 945(2s + 1);
- ψ(c, x, w₁), ψ(c, y, w₂), ψ(c, z, w₃);
- δ_c D_i = ε^{m_i} − 1 and D_i − w_i = δ_c Y_i (i = 1, 2, 3);
- Mul(c, m₁, m₂, m₃).

*Soundness.*
- c is odd and |c| ≥ 945, and ψ gives x, y, z | c, so |x|, |y|, |z| ≤ |c|.
- From D_i ≡ w_i ≡ (x, y, z)_i (mod δ_c), q_i := m_i/c is congruent mod e(c) to x, y, z respectively.
- Theorem M then gives z ≡ xy (mod e(c)).
- |z − xy| ≤ |c| + c² < φ^{|c|−2} ≤ e(c) for |c| ≥ 945 (F2). Hence z = xy.

*Completeness.* If z = xy with x, y, z odd, take c = 945xyz (odd, a common multiple, of the required form), m₁ = cx, m₂ = cy, m₃ = cz, and w_i from ψ.

*From odd integers to Z.* For a, b, r ∈ Z: r = ab ⟺ ∃p: Φ(2a+1, 2b+1, p) ∧ p − 2a − 2b − 1 = 4r. All of this is linear in exponents together with Φ.

*Undecidability.* By DPRM (Matiyasevich 1970), solvability of polynomial equations over Z is undecidable. Each such equation becomes a system over G through straight-line form, exact additions, and the definable multiplication. ∎

**Remark 4.1 (the reduction is tight within the exponent route).** By (i) ⇒ (iii), W_div is necessary for any interpretation of (Z, +, ×) on exponents. Undecidability could still come from elsewhere, for example from the M-sort, but that would need an essentially different idea.

## 6. Citations (checked this session unless noted)

- R. D. Gray, A. Levine, *Decidability of equations and first-order theory in Seifert 3-manifold groups*, arXiv 2512.07690 (Dec 2025). §6.1 states that D(G) for Sol-manifold groups is unknown, and Prop 6.1 gives first-order undecidability. Fetched.
- R. Dong, arXiv 2406.08480 (SODA 2025), and Kharlampovich–López–Myasnikov, Math. Comp. 89 (2020). Abelian-by-cyclic context; cited via audit-sol.md. Neither covers Sol D(G).
- L. Lipshitz, *The Diophantine problem for addition and divisibility*, Trans. AMS 235 (1978). ∃Th(Z, +, |) is decidable, with a local–global principle as described in Defossez–Haase–Mansutti–Pérez, arXiv 2308.13609 (checked). Smallest solutions of ∃(Z, +, <, |) can have exponential bit length, and polynomial bounds are known only for fragments. So a small-model proof that R is not ∃-definable in (Z, +, <, |), audit fix 4, is **not available** from the literature I could verify.
- Matiyasevich (1970), DPRM: H10 is undecidable.
