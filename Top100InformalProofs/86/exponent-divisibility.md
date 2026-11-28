# Divisibility of exponents in three groups

The obstruction concerns methods that represent exponent projections by Presburger or Büchi formulas. The decision problem for systems with constants remains open.

## Theorem D (divisibility interpretation)  [proved, 92%]
Let G = M ⋊ ⟨t⟩ be one of:
- (a) A≀ℤ = A[t^±] ⋊ ℤ, with A ≠ 0 a f.g. abelian group;
- (b) BS(1,k) = ℤ[1/k] ⋊ ℤ, t acting as ×k, k ≥ 2;
- (c) O⁺ ⋊ O^×, with O an order in a real quadratic field.

Let ψ: G → ℤ be the exponent of t. In case (c), ψ(b,u) = j where u = ±ε^j and ε is the fundamental unit. Then, with constants, the following are existentially definable in G:
1. M (as a centraliser);
2. the congruence g ≡ h mod M;
3. the relation R(g,h) ⟺ ψ(g) | ψ(h). In case (c), g and h range over squares, and R reads ψ(g)/2 | ψ(h)/2. The convention is 0 | m ⟺ m = 0.

Hence the structure (ℤ, +, |) is e-interpretable in G, with domain G/M (case c: {x²}/M), addition the group product, and equality ≡ mod M.

**Proof.**
- **M is pp-definable.** Fix c = (c₀, 0) ∈ M with c₀ ≠ 0. For (a,b): take c₀ = a nonzero element of A placed at position 0. For (c): c = (1,1). For x = (b,n), the product xc = (b + t^n c₀, n) and cx = (c₀ + b, n). So x commutes with c ⟺ t^n c₀ = c₀ ⟺ n = 0, since t^n acts as a shift, as ×k^n, or as ×u with u ≠ 1. So C(c) = M. Then g ≡ h ⟺ gh⁻¹ ∈ C(c), which is pp.
- **Commutators with M.** For g = (b,n) and y ∈ M, gyg⁻¹ = t^n·y, so [g,y] = (t^n − 1)y, where t^n means ε^{n} in case (c). Also [h,c] = (t^m − 1)c₀ with m = ψ(h). The pp formula is Φ(g,h) := ∃y (yc = cy ∧ [g,y] = [h,c]). It states (t^n − 1)·y = (t^m − 1)·c₀ for some y ∈ M.
- **Case (a).** Put R₀ = ℤ[t^±]. M = A ⊗ R₀. Let n ≠ 0, and multiply by a unit t^N to get honest polynomials. t^{|n|} − 1 is monic, so division by it with remainder is unique in A[t] for any abelian A. Also t^m − 1 ≡ t^r − 1 mod (t^{|n|} − 1), with r = m mod |n|, 0 ≤ r < |n|. So (t^n−1) | (t^m−1)c₀ in A[t^±] ⟺ the remainder (t^r − 1)c₀ vanishes ⟺ r = 0 ⟺ n | m. If n = 0 the left side is 0, so the formula forces (t^m − 1)c₀ = 0 ⟺ m = 0.
- **Case (b).** k^n − 1 is prime to k, so divisibility in ℤ[1/k] of (k^m−1) by (k^n−1) is divisibility in ℤ. gcd(k^n−1, k^m−1) = k^{gcd(n,m)} − 1, and k^d − 1 = k^{|n|} − 1 forces d = |n|. Negative exponents change things only by units −k^{−n}. So the relation is n | m. n = 0 works as in (a).
- **Case (c).** Restrict g, h to squares g = x², h = z². Their unit parts are ε^{2n} and ε^{2m}, and squaring is pp. In any commutative ring and for a unit E, the ideal (E^a − 1, E^b − 1) equals (E^{gcd(a,b)} − 1) (Euclid with units). So (ε^{2n}−1) | (ε^{2m}−1) ⟺ (ε^{2n}−1) and (ε^{2d}−1) are associates, with d = gcd(n,m). Since d | n, the quotient (ε^{2n}−1)/(ε^{2d}−1) lies in O. Its norm is f(2n)/f(2d), where f(2j) = |N(ε^{2j} − 1)| = (ε^{j} − ε^{−j})². This is strictly increasing in j ≥ 1. A non-zero algebraic integer has |norm| ≥ 1, with equality iff it is a unit. So the quotient is a unit ⟺ |n| = d ⟺ n | m. Squares are needed: for O = ℤ[φ], φ² − 1 = φ is a unit and odd exponents break the equivalence (C++ run below). ∎

**Corollary D1 (gcd).** gcd is also e-definable. For d = gcd(n,m), the ideal (t^n−1, t^m−1) equals (t^d−1), so ∃u,v ∈ M with [g_n,u][g_m,v] = [g_d,c]. Together with d | n and d | m, this pins d up to sign, the convention for gcd over the signed divisibility structure. So the existential theory of (ℤ, +, |, gcd) reduces to DP_c(G). [proved, 90%]

**Corollary D2 (no automatic/semilinear method).** [proved, 90%] The relation {(ψ(g), ψ(h)) : G ⊨ Φ(g,h)} = {(n,m) : n | m} is the projection of the solution set of a 3-variable system (variables g, h, y, plus a constraint pinning y into M). It is not semilinear. It is also not k-automatic for any k ≥ 2.
- Suppose D = {(n,m) ∈ ℕ² : n | m} were k-automatic.
- Then (ℕ, +, D) would be an automatic structure, and so would every FO-definable set (Khoussainov–Nerode / Hodgson).
- In particular the primes {m : m > 1 ∧ ∀n (D(n,m) → n = 1 ∨ n = m)} would be k-automatic. Here < and 1 are +-definable on ℕ.
- That is false: the primes are not recognisable in any base (Minsky–Papert 1966 [mem]).

So any procedure that represents solution sets of systems by Presburger formulas, or by Büchi-(ℤ,+,V_k) formulas, fails on systems with constants. This is exactly the form of KLM's Lemma 2 (systems Σ ±k^{y_j} + C = 0 ⟹ disjunction of linear systems, via Semenov). It explains why the KLM v1 argument could not have been completed in that form. The one-variable case (Ushakov–Wang) escapes, since D needs three variables.

**What D does not give.** The existential theory of (ℤ, +, |) is decidable (Lipshitz 1978; NP by Lechner–Ouaknine–Worrell 2015 [mem]). With gcd it is still decidable (Chistikov–Mansutti–Starchak, IP with GCD constraints, SODA 2024 [mem]). So D gives no undecidability. Dong's ℤ≀ℤ undecidability uses (X−1)²- and (X−1)³-divisibility, which reads off quadratic information in the exponents through derivatives at 1. In characteristic p that channel only sees base-p digits (Lucas), so it is Büchi-type. The open question is whether variable-divisor divisibility (D) plus Frobenius (in C_p≀ℤ) or plus the integer values (in BS(1,k)) e-defines multiplication on exponents.

**Conjecture Z2-L.** DP_c(C_p≀ℤ) ≡ an existential theory of (ℤ, +, |, V_p-type predicates). [conjecture, 35%] Whether that theory is decidable is a pure logic question. No decision either way here.
