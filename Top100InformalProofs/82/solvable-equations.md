# Two decision results for equations in polycyclic groups and Sol lattices

This selection concerns Theorems B and E and keeps the assumptions of each statement.

## 2. Main theorem

**Notation.** For ρ: Z^d → GL_n(Z) and w ∈ Z^d, let E_w ⊆ Q^n be the generalized eigenspace of ρ(w) for eigenvalue 1, that is, ker(ρ(w) − 1)^n. Call ρ **1-semisimple** if ρ(w) restricted to E_w is the identity for every w. Equivalently, no ρ(w) has a nontrivial Jordan block at eigenvalue 1. Applying this to powers of w shows that no ρ(w) has a nontrivial Jordan block at any root of unity either. H₃ = H₃(Z) is the integral Heisenberg group.

**Definition.** R is the class of f.g. virtually polycyclic groups G satisfying the equivalent conditions of Theorem B.

**Theorem B.** For a f.g. virtually polycyclic group G the following are equivalent:

- (a) every nilpotent subgroup of G is virtually abelian;
- (b) G has no subgroup isomorphic to H₃(Z);
- (c) G has a finite-index subgroup isomorphic to Z^n ⋊_ρ Z^d with ρ 1-semisimple.

If these hold, then also:

- (d) every nilpotent subgroup of the subgroup in (c) is abelian;
- (e) G/γ_i(G) is virtually abelian for every i.

**Corollary C (classification modulo R).** Let G be a f.g. virtually polycyclic group.

1. If G ∉ R, then D(G) is undecidable.
2. If G ∈ R, then neither GMO criterion applies. There is no non-virtually-abelian nilpotent subgroup (needed for Thm 4.16), and no non-virtually-abelian quotient G/γ_i(G) (needed for Thms 4.13/4.31).
3. If G ∈ R and G is virtually abelian, then D(G) is decidable.

So "D(G) is undecidable for every non-virtually-abelian virtually polycyclic G" is equivalent to the same statement for the non-virtually-abelian members of R. Sol lattices and O⁺ ⋊ O^× are the simplest such members.

*Proof of C from B.* For part 1: by (a), G has a non-virtually-abelian nilpotent subgroup. Virtually polycyclic groups lie in N_max (GMO Example 4.23 and the remark after Thm 4.16 that N_max is closed under finite extensions). So GMO Thm 4.16 makes a ring of algebraic integers O e-interpretable in G, which gives D(O) ≤_P D(G). D(O) is undecidable by KP Thm 1.1, since O is an infinite f.g. commutative ring. Part 2 is (a) together with (e). Part 3 is GMO Lemma 4.1. ∎

### Examples that delimit R

- **In R, not virtually abelian:** Z² ⋊_A Z with A ∈ GL₂(Z) hyperbolic, and Sol 3-manifold groups. Also O⁺ ⋊ O^× for any number field with unit rank ≥ 1, where the action is diagonalizable and the trivial eigenvalue occurs only on the torsion part. Also Z^n ⋊_ρ Z^d with ρ(Z^d) diagonalizable.
- **In R although the action is not semisimple:** Z⁴ ⋊_M Z with M = [[A, I],[0, A]] and A hyperbolic. M has no eigenvalue 1, so E_w = 0 for w ≠ 0. This shows that "1-semisimple" and not "semisimple" is the correct condition.
- **Not in R although Fit(G) is virtually abelian and the action on Fit is 1-semisimple:** take generators e₁, e₂, f₁, f₂, z, s, t. Let s act on Z⁵ = ⟨e,f,z⟩ by B ⊕ 1 ⊕ 1 and t by 1 ⊕ B ⊕ 1, with B hyperbolic, and impose [s,t] = z. The extension class is the coinvariant class of z, which has infinite order, so the group exists. Fit(G) = Z⁵, yet ⟨s,t⟩ ≅ H₃. This shows that the **splitting** in (c) is essential: the condition "Fit virtually abelian" is strictly weaker than R. GMO 4.16 applies to this group, so D(G) is undecidable.

---

## 3. Proof of Theorem B

Write group laws of A ⋊ W additively in A: (a,w)(b,w') = (a + ρ(w)b, w + w'). The commutator [x,y] = xyx⁻¹y⁻¹ satisfies the following identities.

- **(Comm-1)** For v ∈ A and g = (a,w): [g, v] = (ρ(w) − 1)v.
- **(Comm-2)** If g_i = (a_i, w_i), then [g₁, g₂] = (ρ(w₁) − 1)a₂ − (ρ(w₂) − 1)a₁.

More generally, in any extension 1 → A → K → W → 1 with A abelian and W abelian, write c = [g₁, g₂] ∈ A. Then [a₁g₁, a₂g₂] = c + (ρ(w₁) − 1)a₂ − (ρ(w₂) − 1)a₁ for a_i ∈ A. This is checked directly: a₁g₁a₂g₂ = (a₁ + ρ₁a₂)·c·g₂g₁ and a₂g₂a₁g₁ = (a₂ + ρ₂a₁)·g₂g₁.

**Lemma 1 (Heisenberg recognition).** Let x, y be elements of a group with z = [x,y] commuting with x and with y, and with z of infinite order. Then ⟨x,y⟩ ≅ H₃.

*Proof.* ⟨x,y⟩ is a quotient H₃/K, with the central generator of H₃ mapping to z. If K ≠ 1, then K meets Z(H₃) = ⟨ζ⟩ nontrivially, because H₃ is nilpotent. So some z^j = 1 with j ≠ 0, a contradiction. ∎

**(a) ⇒ (b).** Trivial.

**(b) ⇒ (a).** Let N ≤ G be nilpotent and not virtually abelian. N is f.g., because subgroups of virtually polycyclic groups are f.g. Pass to a torsion-free finite-index N₁; it is non-abelian of some class c ≥ 2. Since γ_c(N₁) = [γ_{c−1}(N₁), N₁] ≠ 1, there are x ∈ N₁ and y ∈ γ_{c−1}(N₁) with z = [x,y] ≠ 1. This z lies in γ_c(N₁) ≤ Z(N₁) and has infinite order. Lemma 1 gives ⟨x,y⟩ ≅ H₃. ∎

**(c) ⇒ (d) ⇒ (a).** Let G₂ = A ⋊_ρ Z^d with A = Z^n and ρ 1-semisimple, and let N ≤ G₂ be nilpotent of class c. Put V = N ∩ A and W = π(N) ≤ Z^d.

For g = (a,w) ∈ N and v ∈ V, the c-fold commutator [g,[g,…,[g,v]]] equals (ρ(w) − 1)^c v and vanishes. So V ⊆ E_w, where ρ(w) is the identity. Hence V ⊆ U := (Q^n)^W.

Decompose Q̄^n into joint generalized eigenspaces V_χ of the commuting family ρ(W). By 1-semisimplicity, V₁ = U ⊗ Q̄. Let U' be the Q-form of ⊕_{χ≠1} V_χ; it is Galois-stable, hence defined over Q. Each ρ(w) − 1 kills U, again by 1-semisimplicity, and preserves U'. So im(ρ(w) − 1) ⊆ U'.

Now take g₁, g₂ ∈ N. By (Comm-2), [g₁,g₂] ∈ U'. But [g₁,g₂] ∈ A ∩ N = V ⊆ U, and U ∩ U' = 0. So N is abelian. Since every nilpotent subgroup of G meets G₂ in a subgroup of finite index, (a) follows. ∎

**(a) ⇒ (c).**

*Step 1 (an abelian-by-free-abelian finite-index subgroup).* Let P ⊴ G be polycyclic of finite index and F = Fit(P). F is nilpotent and characteristic in P, so normal in G. P/F is virtually abelian (Mal'cev; see Segal, *Polycyclic Groups*, Ch. 1), so G/F is virtually abelian.

By (a), F is virtually abelian. Since F is f.g., the intersection of its finitely many subgroups of index at most [F : abelian] is characteristic, abelian and of finite index. Its subgroup of k-th powers, with k the exponent of its torsion, is characteristic and free abelian: A ≅ Z^n, normal in G, with F/A finite.

Choose B/F ≤ G/F abelian of finite index. Then B/A is f.g. and finite-by-abelian. The centralizer C of the finite normal subgroup F/A has finite index, and C has class ≤ 2 with finite derived subgroup. Each map x ↦ [x, y] is then a homomorphism into a finite group, so Z(C) has finite index and B/A is virtually abelian. Taking a torsion-free abelian finite-index subgroup and its normal core gives G₁ ⊴ G of finite index with A ≤ G₁ and G₁/A ≅ Z^d. Let ρ: Z^d → GL(A) be the conjugation action. Since G₁ ⊴ G, Fit(G₁) ≤ F, so A has finite index in Fit(G₁).

*Step 2 (ρ is 1-semisimple).* Suppose ρ(w) is not the identity on E_w. Then ρ(w) − 1 is nonzero nilpotent on E_w, so there is v ∈ A ∩ E_w (after scaling) with z := (ρ(w) − 1)v ≠ 0 and (ρ(w) − 1)z = 0. Let g ∈ G₁ lift w. By (Comm-1), [g,v] = z. z is fixed by ρ(w), so it commutes with g. It commutes with v since both lie in A. It has infinite order since A is torsion-free. Lemma 1 gives ⟨g,v⟩ ≅ H₃, contradicting (a).

*Step 3 (decomposition).* With respect to all of Z^d, write Q^n = U ⊕ U' as in the proof of (c) ⇒ (d). Here U = (Q^n)^{Z^d} by Step 2, U' is the Q-form of ⊕_{χ≠1} V_χ, and both are ρ-invariant.

H*(Z^d, U'⊗Q̄) = 0. To see this on each V_χ, pick w with χ(w) ≠ 1, so ρ(w) − 1 is invertible on V_χ. The map that conjugation by w induces on H*(Z^d, V_χ) is the identity, because inner automorphisms act trivially. Since conjugation by w is trivial on Z^d, that map is just ρ(w)_*. So (ρ(w) − 1)_* is both 0 and invertible, and the cohomology vanishes. By flat base change, H*(Z^d, U') = 0. Hence H²(Z^d, L') is torsion for every Z^d-lattice L' ⊂ U'.

*Step 4 (killing the U'-part of the extension class).* Choose m with mA ⊆ (A∩U) ⊕ (A∩U'), and set L := (1/m)(A∩U) and L' := (1/m)(A∩U'). Then A ⊆ L ⊕ L' with finite index.

Pushing the extension G₁ along A ↪ L ⊕ L' gives an extension G' ⊇ G₁ of finite index [L⊕L' : A]. Its class is (e_L, e_{L'}) ∈ H²(Z^d, L) ⊕ H²(Z^d, L'). By Step 3, r·e_{L'} = 0 for some r ≥ 1. Pushing further along L ⊕ L' ↪ L ⊕ (1/r)L' (identity on L) replaces the class by (e_L, 0). The new group G'' contains G₁ with finite index.

An extension with class (e_L, 0) is the fibre product over Z^d of the extension E_L of Z^d by L with class e_L and the split extension (1/r)L' ⋊ Z^d. In particular E_L embeds in G'' as a subgroup.

*Step 5 (e_L = 0).* Z^d acts trivially on L ⊂ U by Step 2. So E_L is a central extension, and H²(Z^d, L) ≅ Hom(Λ²Z^d, L) via the commutator pairing β, because Ext(Z^d, L) = 0.

Suppose β(w₁,w₂) ≠ 0. Lifts x, y ∈ E_L have [x,y] = β(w₁,w₂), which is central and of infinite order, so ⟨x,y⟩ ≅ H₃ by Lemma 1. This H₃ lies in G''. Since [G'' : G₁] < ∞, the group H₃ ∩ G₁ is a finite-index subgroup of H₃. It is therefore a nilpotent subgroup of G that is not virtually abelian, contradicting (a). So β = 0, hence e_L = 0, and G'' = (L ⊕ (1/r)L') ⋊ Z^d is split.

*Step 6 (descending the splitting).* Let s: Z^d → G'' be the splitting homomorphism. W₀ := s⁻¹(G₁) is a subgroup of finite index in Z^d, because [G'' : G₁] < ∞. Then G₂ := A ⋊ s(W₀) ≤ G₁ has finite index, and G₂ ≅ Z^n ⋊_{ρ|W₀} W₀ with W₀ ≅ Z^d. The restriction of ρ to W₀ is still 1-semisimple. ∎

**(c) ⇒ (e).** Take G₂ = A ⋊ Z^d as in (c), with normal core taken so that G₂ ⊴ G. Write Q^n = U ⊕ U' for the whole of Z^d as above.

Let T := Σ_w (ρ(w) − 1). On each V_χ with χ ≠ 1, some ρ(w) − 1 is invertible. So for any lattice L ⊂ U', the lattice T(L) := Σ_w (ρ(w) − 1)L has full rank in U', i.e. finite index in L.

Set L₁ := T(A ∩ U') and L_{i+1} := T(L_i). By (Comm-1), L_i ⊆ γ_{i+1}(G₂), and each L_i has finite index in A ∩ U'. The quotient G₂/(A∩U') is abelian: Z^d acts trivially on A/(A∩U'), which is a lattice in U, and A/(A∩U') is central. Hence G₂/L_i is finite-by-abelian and f.g., so virtually abelian, as in Step 1. Thus G₂/γ_{i+1}(G₂) is virtually abelian.

Then G/γ_{i+1}(G₂) is virtually abelian, and G/γ_{i+1}(G) is a quotient of it, so it is virtually abelian too. ∎

This completes the proof of Theorem B, and with it Corollary C.

---

## II.1 Set-up and exact translation

Let A ∈ GL₂(Z) have no eigenvalue of modulus 1, and more generally A ∈ GL_n(Z) with irreducible characteristic polynomial χ_A and no eigenvalue of modulus 1. Put K = Q[A] ≅ Q(ε), where ε is a root of χ_A, and identify Q^n with K so that A acts as multiplication by ε. Then M := Z^n is a lattice in K. Let O' := {α ∈ K : αM ⊆ M}, an order containing Z[ε, ε⁻¹]. Every ε^k is a unit of O'.

Write G = M ⋊ ⟨t⟩, with tvt⁻¹ = εv. Every element is uniquely v t^k, with

(v t^k)(w t^l) = (v + ε^k w) t^{k+l} and (v t^k)⁻¹ = (−ε^{−k} v) t^{−k}.

**Translation (Prop F).** Substitute x_i = v_i t^{k_i} into a word W = y₁⋯y_L whose letters are variables, inverses of variables, or constants (c,l). Let e_j be the t-exponent of y_j and E_j = e₁ + … + e_j. Then W = 1 if and only if

E_L = 0 (a linear equation in the k_i) and Σ_j ε^{E_{j−1}} a_j = 0,

where a_j is v_i, −ε^{−k_i}v_i, or c. So D(G) is the existential theory of the two-sorted structure (Z, +; M, +; (k,v) ↦ ε^k v; constants): linear conditions on exponents together with M-linear equations whose coefficients are integer Laurent polynomials in the ε^{k_i}. The converse also holds. {t^k} = C_G(t) is e-definable, and M = {x : x commutes with some fixed nonzero c₀ ∈ M}: indeed C_G(c₀) = M, because ε^k c₀ = c₀ forces k = 0. Every such statement is therefore a system over G. ∎

## II.2 Theorem E: one-variable systems are decidable

**Theorem E.** Let G = Z^n ⋊_A Z with χ_A irreducible over Q and no eigenvalue of A of modulus 1. In particular this covers every Sol lattice Z² ⋊_A Z, A ∈ GL₂(Z) hyperbolic. Then there is an algorithm that decides, for a finite system of equations in one variable x with constants from G, whether it has a solution.

*Proof.* Write x = v t^k. By Prop F, the i-th equation becomes

α_i k + β_i = 0 and f_i(ε^k) v = g_i(ε^k).

Here α_i, β_i ∈ Z, f_i ∈ Z[ε][X^{±1}], and g_i ∈ M[X^{±1}], meaning Laurent polynomials with coefficients in M ⊂ K. The coefficients ε^{β} come from constant exponents, and ε^{β} ∈ Z[ε^{±1}] ⊆ O'.

**Lemma E1 (fixed k).** For fixed k, solvability is decidable. For fixed k the conditions form a linear Diophantine system over Z in the coordinates of v ∈ M ≅ Z^n, solvable by Hermite/Smith normal form.

**Lemma E2 (zero sets).** For 0 ≠ h ∈ K[X^{±1}], the set Z(h) = {k ∈ Z : h(ε^k) = 0} is finite and computable. Each root ξ ∈ K of h equals ε^k for at most one k, since ε is not a root of unity. Fix an embedding with |ε| ≠ 1; the Cauchy root bound then bounds |k| explicitly, and each k in range can be tested.

**Lemma E3 (norm growth).** Let Q₀ = Σ_{j=0}^{d} a_j X^j ∈ O'[X] with d ≥ 1, a₀ ≠ 0 and a_d ≠ 0. Then |N_{K/Q}(Q₀(ε^k))| → ∞ as |k| → ∞, and for every B a k₀(B) is computable with |N(Q₀(ε^k))| > B whenever |k| > k₀.

*Proof of E3.* N(Q₀(ε^k)) = Π_σ σ(Q₀)(σ(ε)^k) over the n embeddings σ. By hypothesis every |σ(ε)| ≠ 1, and since |N(ε)| = 1, both sets S₊ = {σ : |σε| > 1} and S₋ = {σ : |σε| < 1} are nonempty.

As k → +∞: for σ ∈ S₊, |σQ₀(σε^k)| ≥ |σa_d| |σε|^{dk} − C|σε|^{(d−1)k}. For σ ∈ S₋, |σQ₀(σε^k)| ≥ |σa₀| − C|σε|^k → |σa₀| > 0. So the product is at least c·Π_{S₊}|σε|^{dk} for k beyond an explicit bound.

As k → −∞ the roles of S₊ and S₋ swap. All constants C, c are explicit in the coefficients. ∎

*Main argument.*

**Step 0.** If some α_i ≠ 0, then k is determined (or no k exists), and Lemma E1 finishes. Otherwise every β_i must be 0, else there is no solution; from now on only f_i(ε^k)v = g_i(ε^k) remains.

**Step 1.** Suppose all f_i ≡ 0. The system is then g_i(ε^k) = 0 for all i, with v free. It is solvable iff the intersection of the sets Z(g_i) over g_i ≢ 0 is nonempty, or every g_i ≡ 0 (Lemma E2, applied coordinatewise in K). Otherwise fix i₀ with f_{i₀} ≢ 0.

**Step 2.** Put H_{ij} := f_i g_j − f_j g_i ∈ K[X^{±1}]. Any solution with f_{i₀}(ε^k) ≠ 0 has v = g_{i₀}(ε^k)/f_{i₀}(ε^k), and then H_{i i₀}(ε^k) = 0 for all i. If some H_{i i₀} ≢ 0, the candidate k lie in the finite computable set Z(f_{i₀}) ∪ Z(H_{i i₀}), and Lemma E1 finishes.

**Step 3.** Suppose all H_{i i₀} ≡ 0, and set R := g_{i₀}/f_{i₀} ∈ K(X). Let E := Z(f_{i₀}), a finite set; each k ∈ E is checked separately by E1. For k ∉ E the system is equivalent to v = R(ε^k) ∈ M:

- equations with f_i ≢ 0 hold because f_i g_{i₀} ≡ f_{i₀} g_i;
- equations with f_i ≡ 0 have g_i ≡ 0, since f_{i₀}g_i ≡ 0.

So it remains to decide whether there is k ∉ E with R(ε^k) ∈ M.

**Step 4.** Work in the PID K[X^{±1}]. Write R = P/(X^j Q₀) in lowest terms, with Q₀(0) ≠ 0.

*Case deg Q₀ = 0.* Then R = Σ r_j X^j is a Laurent polynomial. Choose D ∈ Z_{>0} with D r_j ∈ M for all j. Then R(ε^k) ∈ M ⟺ Σ_j (D r_j) ε^{jk} ≡ 0 in the finite group M/DM. ε acts on M/DM by an automorphism of some order T, so the solution set S is a union of residue classes mod T, computable by testing k = 0, …, T−1. If S ≠ ∅ it is infinite, so S \ E ≠ ∅. Decided.

*Case deg Q₀ ≥ 1.*
- *Reduce to a bounded quotient.* Use partial fractions: R = S + T/Q₀ with S ∈ K[X^{±1}], deg T < deg Q₀, and gcd(T, Q₀) = 1; T ≠ 0 because the fraction is in lowest terms. Scaling T and Q₀ by a common integer, assume Q₀, T ∈ O'[X]. Choose D with D·S ∈ M[X^{±1}]. Then S(ε^k) ∈ D⁻¹M for all k, because the ε^{jk} lie in O'. So R(ε^k) ∈ M forces T(ε^k)/Q₀(ε^k) ∈ D⁻¹M.
- *Bound the norm.* By Bézout in K[X], a T + b Q₀ = 1. Choose D' with D'a, D'b ∈ O'[X], and D'' with M ⊆ D''⁻¹O'. Then
  1/Q₀(ε^k) = a(ε^k)·T(ε^k)/Q₀(ε^k) + b(ε^k) ∈ (DD'D'')⁻¹ O'.
  Hence Q₀(ε^k) is a nonzero element of O' dividing D₄ := DD'D'' in O', so |N(Q₀(ε^k))| ≤ D₄^n.
- *Finish.* By Lemma E3, |k| ≤ k₀(D₄^n). Test these finitely many k with E1.

Every step is effective. ∎

**Remarks.**
1. Theorem E covers single equations in one variable, and also systems where one variable is unrestricted and the others are constants or have exponents forced by Step 0.
2. The same proof works verbatim for GMO's group O⁺ ⋊ O^×, O real quadratic. Split into the four cases x = v·(±1)·ε^k; each produces coefficients ±ε^{(·)k}.
3. With ≥ 2 independent exponent parameters, Steps 2–4 fail. The kernel lattice then moves with the parameters, and the integrality conditions become ideal-membership statements among exponential polynomials in several variables (see §II.4).
