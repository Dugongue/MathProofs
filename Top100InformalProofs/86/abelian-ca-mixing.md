# Deciding transitivity and mixing for abelian group cellular automata

The dual-module criterion is in the spirit of Kitchens–Schmidt and Schmidt’s Dynamical Systems of Algebraic Origin. The decision uses effective associated-prime computations for the stated finite-type input.

## Theorem T (proved; algorithm at sketch level)
Let A be a finite abelian group, X ⊆ A^{Z^d} a group shift, and F: X → X a group CA. Write M = X̂, the Pontryagin dual. It is a finitely generated module over R_d = Z[u_1^{±},…,u_d^{±}], and F̂: χ ↦ χ∘F is R_d-linear. Then the following are equivalent:
1. F is topologically transitive;
2. F is topologically mixing;
3. F is surjective, and no nontrivial character χ ∈ M satisfies χ∘F^n = χ for some n ≥ 1.

Condition 3 is decidable. Hence transitivity and mixing are decidable for abelian group CA on group subshifts, and so are ergodicity and strong mixing for Haar measure, which are equivalent here.

## Proof
**(1 ⟹ surjective).**
- Suppose F(X) ≠ X. Then F(X) is a closed proper subset. Pick a nonempty open V ⊆ X∖F(X) and a nonempty open U disjoint from V.
- For n ≥ 1, F^n(U) ⊆ F(X) misses V; for n = 0, U ∩ V = ∅. So F is not transitive.

**(1 ⟹ no finite character orbit).**
- Suppose χ ≠ 1 and χ∘F^n = χ. Since X is zero-dimensional, χ has finite image in Q/Z.
- Put Φ = (χ, χ∘F, …, χ∘F^{n−1}): X → (Q/Z)^n. Φ is continuous, takes finitely many values, and Φ∘F = τ∘Φ, where τ is the cyclic coordinate shift.
- Each fibre Φ^{−1}(a) is clopen. Transitivity gives, for any a, b ∈ Φ(X), some k with τ^k a = b.
- Take a = Φ(1) = 0, which is a τ-fixed point. Then every b ∈ Φ(X) equals 0, so χ = 1. Contradiction.

**(3 ⟹ 2).**
- F is a continuous surjective endomorphism of a compact abelian group, so it preserves Haar measure μ.
- Halmos: F is ergodic ⟺ there is no nontrivial character with a finite F̂-orbit. F̂ is injective on characters because F is onto.
- Mixing holds as well. If χ, ψ ≠ 1, then χ∘F^k = ψ for at most one k. Indeed, χ∘F^a = χ∘F^b with a < b would make χ∘F^a a nontrivial fixed point of F̂^{b−a}, unless it is trivial, and then ⟨χ∘F^k, ψ⟩ = 0 for all large k. Characters are orthonormal and span L², so μ(F^{−k}P ∩ Q) → μ(P)μ(Q).
- μ has full support (Haar on a compact group), so measure mixing implies topological mixing.

**(2 ⟹ 1)** is trivial. ∎

## Algorithm for condition 3
1. **Surjectivity.** This is decidable by Béaur–Kari Thm 4.
2. **Presentation of M.**
   - Take a window W such that X = {c : c|_{v+W} ∈ L for all v}, where L = L_W(X) ≤ A^W is computable by B–K Cor 1.
   - Then X^⊥ = R_d·L^⊥. Proof: (R_d L^⊥)^⊥ = {c : every translate of every character in L^⊥ kills c} = {c : c|_{v+W} ∈ L^⊥⊥ = L for all v} = X. Every subgroup of a discrete group is closed.
   - So M = (R_d ⊗ Â)/R_d L^⊥ is finitely presented. F̂ is given by the transpose of the local rule.
3. **Reduction to F_p.**
   - Decompose M = ⊕_p M_p. If 0 ≠ m ∈ M_p and (F̂^n − 1)m = 0, then some p^j m is a nonzero element of V_p := M_p[p] and is still killed.
   - V_p is a finitely generated module over T = F_p[u^{±}, t], with t acting as F̂. It is computable as a syzygy module (Gröbner bases over Z).
4. **Associated primes.**
   - There exist v ≠ 0 and n ≥ 1 with (t^n − 1)v = 0 ⟺ t^n − 1 ∈ ⋃ Ass_T(V_p) for some n.
   - This holds ⟺ some P ∈ Ass(V_p) has P ∩ F_p[t] = (g) with g ≠ 0 and g not an associate of t, i.e. the image of t in T/P is a nonzero element algebraic over F_p, hence a root of unity.
   - Ass is computable over finite fields (Gianni–Trager–Zacharias primary decomposition), and the contractions P ∩ F_p[t] are computable by elimination.
5. Surjectivity checks the remaining half of condition 3. ∎
