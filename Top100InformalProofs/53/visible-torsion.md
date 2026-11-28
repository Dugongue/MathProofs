# Hamiltonian-cycle projections from visible torsion

This proves the stated torsion case of the algebraic hard side.

## 1. Formalisation (extends F1 of STEER to tame templates)

- **Template.** M is a tame structure (UNIFIED D8), or a ring with f.g. additive group (Theorem N, class (R)).
- **Labelling.** A labelling λ assigns each sort s an admissible map λ_s : s → Λ_s onto a finite set:
  - the identity on finite sorts;
  - on group sorts, the quotient by a finite-index normal subgroup N_s.
  - λ is **torsion-faithful** if λ_s is injective on the torsion subgroup T_s. Such λ exist: f.g. nilpotent groups are residually finite and T_s is finite.
- **Finite instances.** An instance Φ (pp-formula with constants) on variables v₁..v_m is *finite* if |Sol(Φ)| < ∞.
  - In tiers I–III finiteness is decidable in P: it is the rank test of Theorem N Lemma 3.1.
- **Polynomial.** P_Φ := Σ_{σ∈Sol(Φ)} Π_i x_{i, λ(σ(v_i))}, with one indeterminate per (variable, label).
- **Families.** A family is (P_{Φ_n}) for a p-bounded sequence of finite instances. Reductions are p-projections or c-reductions, as in Bürgisser.
- **Why torsion-faithful.** Without it, group sorts carry no visible weights and the polynomials over pure group templates are integer constants (Theorem N's counts). The algebraic question is then empty. Any weaker labelling that still separates some t ∈ T from 1 gives the same results with uniform multiplicities. Not written.

## 2. Pinning lemma

Let A be a group sort that is f.g. nilpotent (abelian included), with torsion T and e = exp(T).
- Then x^e = 1 ⇔ x ∈ T. The torsion elements of a nilpotent group form a subgroup, here finite, and every element of T has order dividing e.
- For rings, e·x = 0 ⇔ x ∈ T.
- These equations involve only constants, so they add no multiplicity. ∎

## 3. Theorem H1 (visible torsion ⇒ HC and per as p-projections)

**Hypothesis.** Some sort A has g ∈ T with ord(g) = q ≥ 3, and λ is torsion-faithful.

**Gadgets.** Every gadget variable w carries:
- the pinning w^e = 1;
- the weights x_{w,λ(1)} = 1, x_{w,λ(g)} = 1, and 0 on every other label. Edge variables carry x_{w,λ(g)} = Y_e instead.

Write 0 := 1 and 1 := g. On the surviving solutions all gadget values lie in {1, g} ⊆ ⟨g⟩ ≅ ℤ/q, so words in them compute in ℤ/q.
- **NOT:** y·x = g. This holds iff y = ¬x.
- **AND:** z = x∧y via t = x·y·z^{−2} with t ∈ {0,1}. For q = 3, add u = x·z^{−1} with u ∈ {0,1}. In each case the witnesses are unique (C++ v3_gates: q = 3..7 OK; q = 2 fails as it must).
  - *Proof for q ≥ 4.* t = x+y−2z mod q.
    - (1,1,0) gives 2.
    - (0,0,1) gives −2 ≡ q−2 ≥ 2.
    - (1,0,1) gives −1.
    - None of these lies in {0,1}. On the graph of AND, t ∈ {0,1}.
  - *For q = 3,* (0,0,1) gives 1, so the u-equation excludes it (u = −1 ≡ 2).
- **Exactly-one chain** (for the permanent, no AND needed): s_j = s_{j−1}·x_j, with s₀ = 1, s_n = g and s_j ∈ {0,1}. q ≥ 3 is needed: 1+1 = 2 ∉ {0,1}.

**Theorem H1.**
1. **(per, char ≠ 2.)** Take edge variables x_{rc} and one exactly-one chain per row and per column. Then P_Φ = per_n(Y) exactly. Size O(n²).
2. **(HC, every field.)** Take a poly-size Boolean circuit C_n deciding "x is the adjacency matrix of a Hamiltonian cycle", realised gate by gate with NOT/AND gadgets and output forced to g. Then P_Φ = HC_n(Y). HC_n is VNP-complete under p-projections over every field (Valiant; Bürgisser Thm 3.?).

*Proof.* On assignments with nonzero weight every variable is in {1, g}. Gate values are functions of the inputs, and the gadgets have unique witnesses, so solutions biject with accepted inputs. The weight of a solution is Π_{x_e = g} Y_e. ∎

**C++ check (v3_perm.cpp, n = 3, all edge and auxiliary variables enumerated over {1,g}, so witness uniqueness is tested):**
- ℤ/3, ℤ/5, Q₈ (g = i, order 4) and the mod-3 Heisenberg group (order 27): weighted sum = per(Y) for Y = all-ones and 2 random Y. Solution count = 6.
- ℤ/2: 16 solutions, i.e. the 2^{(n−1)²} odd-parity matrices. This is the expected failure and is BK's Lemma 7 situation.

**Coverage.**
- A group with T ≠ 1 has no element of order ≥ 3 iff T is elementary abelian 2: exponent 2 forces T abelian.
- So H1 together with H1′ covers every nonzero torsion.
- H1′ is weaker (c-reductions, char ≠ 2), and in char 2 V1's sketch says the elementary-2 affine layer is an intermediate band (Bürgisser Cut_2).
