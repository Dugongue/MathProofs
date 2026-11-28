# Descent of sign twists in group rings

Gauge equivalence is the specific diagonal group-basis change defined below. The historical frontier has since changed. [O’Neill and Astra’s independent preprint](https://charlesponeill.com/maths-releases/promislow-units/) gives a nontrivial integral unit on the same torsion-free group by a different construction.

## Setup

Let G be a group, K a field with char K ≠ 2, and alpha a normalised 2-cocycle G×G → {±1}. The twisted group ring K^alpha[G] has basis {ĝ} and product ĝ ĥ = alpha(g,h) (gh)^. A unit of K^alpha[G] is *trivial* if it equals λ ĝ.

**Gauge maps.** If f : G → K^× satisfies alpha = δf, i.e. alpha(g,h) = f(g)f(h)/f(gh), then Φ_f : K^alpha[G] → K[G], ĝ ↦ f(g) g, is a ring isomorphism. It preserves support and sends trivial units to trivial units.

## Proposition 1 (proved, conf 0.9). Descent criterion

Let alpha represent [alpha] ∈ H^2(G;{±1}). Then K^alpha[G] ≅ K[G] by a gauge map iff [alpha] ∈ ker(H^2(G;±1) → H^2(G;K^×)). This kernel is δ(Hom(G, K^×/{±1})), where δ is the connecting map of 1 → ±1 → K^× → K^×/±1 → 1.

*Proof.* The long exact sequence in group cohomology gives the kernel as the image of the connecting map. If alpha = δf with f : G → K^×, then Φ_f is the isomorphism. Conversely, a gauge isomorphism ĝ ↦ f(g)g gives alpha = δf. ∎

**Corollary 1a: real fields.** If K^× = {±1} × T with T torsion-free, every hom G → K^×/±1 = T lifts, so the kernel is 0. This covers K = Q (Q^× = ±1 × free abelian group on the primes), R, and every subfield of R. **So a nontrivial unit of K^alpha[G] with [alpha] ≠ 0 never gauges to a unit of K[G] when K is real.**

**Corollary 1b: general number fields.** Only the 2-primary part of μ(K) matters. If μ(K)_2 = μ_{2^m}, the kernel is spanned by Bocksteins β(χ) of characters χ : G → Z/2^{m-1} that do not lift to Z/2^m. For example:
- K = Q(i) (m=2): Z/2-characters not lifting to Z/4.
- K = Q(zeta_8) (m=3): Z/4-characters not lifting to Z/8.

**Corollary 1c: Promislow group P.** H_1(P) = Z/4 × Z/4 and every Z/2-character of P lifts to Z/4. So the kernel is nonzero iff K has a primitive 8th root of unity, or, over any field, an element λ with λ^4 = -1. Gardam's C-unit has coefficient of g in ±ψ(g), with ψ : P → R^×/±1, a ↦ s, b ↦ t (2312.05240 Remark 2). It is therefore Φ_f of an integral unit c ∈ Z^alpha[P] with all coefficients ±1, where alpha = δψ is the nonzero class from μ ≅ Z/8 × Z/4 → Z/4 × Z/4. **Hence: any field over which a gauge-twisted copy of c (or of any ±1-twisted unit of P) becomes an honest unit must contain a root of x^4+1.** This is exactly Gardam's corollary ("F_{p^2} for all p, F_p iff p = 2 or p ≡ 1 mod 8"), now explained for every twisted unit on P, not only his support. Novelty: low to moderate; it formalises Gardam's Remark 2.

## Proposition 2 (proved, conf 0.85; uses char-0 I). Q[G] cannot simulate zeta_8

Let G be torsion-free and K of char 0, and assume the idempotent conjecture over the splitting field L. This is now claimed for every torsion-free G by the OpenAI Bass-trace preprint, and is classical under Baum–Connes or Farrell–Jones. If θ ∈ K[G] is a root of a separable polynomial f ∈ K[x], then θ ∈ K.

*Proof.* Let m be the minimal polynomial of θ. It divides f, so it is separable. Over L it splits into distinct linear factors. The Lagrange idempotents e_r = Π_{r'≠r}(θ - r')/(r - r') lie in L[G], are orthogonal, and sum to 1. By I each is 0 or 1, so exactly one equals 1 and θ = r ∈ L. Since θ ∈ K[G] ∩ L = K, done. ∎

**Kill.** No unital ring homomorphism from Z[zeta_8][H], or from any ring containing a root of x^4+1, into Q[G] or R[G] with G torsion-free exists. So "transport Gardam's unit into a rational group ring" is impossible by any homomorphism. Also, a monomial-image realisation of the twisted ring Z^alpha[P] in Q[G]^× (â ↦ λ g) needs λ^4 = -1. Any realisation needs units A, B ∈ Q[G] with B^{-1}A^2B = -A^{-2}, and for trivial units that forces λ^4 = -1. So the route is **circular**: it needs a nontrivial Q-unit to begin with.
