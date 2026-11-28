# Gibbs, ground-state, and steady-state realizations

The proof retains the stated locality and geometry assumptions.

## 1. Theorem A (commuting Gibbs states: entanglement lives on the crossing terms)

**Theorem A.** Let ℋ = ℋ_A ⊗ ℋ_B be finite-dimensional. Let H = H_A ⊗ I + I ⊗ H_B + h_∂ with all operators Hermitian and [H_A ⊗ I + I ⊗ H_B, h_∂] = 0. Then for every β ∈ ℝ:

e^{−βH} is separable (respectively PPT) across A|B ⟺ e^{−β h_∂} is separable (respectively PPT) across A|B.

*Proof.* H_A ⊗ I and I ⊗ H_B commute with each other because their supports are disjoint. By hypothesis their sum commutes with h_∂. Hence
e^{−βH} = (S_A ⊗ S_B) e^{−β h_∂} (S_A ⊗ S_B)^*, with S_X = e^{−β H_X/2}.
S_A and S_B are invertible. A congruence by an invertible product operator maps separable cones onto separable cones in both directions, since Σ p_i a_i⊗b_i ↦ Σ p_i (S_A a_i S_A^*)⊗(S_B b_i S_B^*) and the inverse is of the same form. It also preserves PPT, since (S_A⊗S_B) X (S_A⊗S_B)^* has partial transpose (\bar S_A⊗S_B) X^{T_A} (\bar S_A⊗S_B)^*, and congruence preserves positivity. ∎

The hypothesis holds for any Hamiltonian that is a sum of pairwise commuting terms, with h_∂ the sum of the terms that act nontrivially on both sides. No locality, geometry or translation invariance is used.

**Corollary A1 (1D, finite range).** Let H_n = Σ_i h_i^{(n)} be a commuting Hamiltonian on n sites of dimension d. Suppose every term has range ≤ r, and the terms meeting site 1 (the input boundary terms together with the bulk terms meeting site 1) are the same operators h_∂ for every n ≥ n_0. Then for every β and every n ≥ n_0, the Gibbs state is entangled across {1}|{2..n} iff the fixed operator e^{−β h_∂} on the sites [1,r] is entangled across {1}|{2..r}. Consequently "∃ n: ρ_β(H_n) is entangled across site 1" equals a finite disjunction of separability tests on states of dimension ≤ d^r, computed from the input, with no length left in the problem.

*Remarks.* (i) Entanglement of a single computable state is semi-decidable. A rational witness W ≥ 0 on product states is checked exactly by Tarski–Seidenberg, and tr(Wσ) < 0 is semi-decidable. So the residual problem is c.e. Any undecidability would have to come from exact real-number sign tests on one bounded-dimension matrix exponential (decidable assuming Schanuel's conjecture, by Macintyre–Wilkie). It would not come from the growth of the chain. (ii) The same holds across any cut in any lattice: commuting local Gibbs entanglement is a property of the boundary Hamiltonian alone, at every temperature. (iii) **What this rules out.** For commuting models, c.e.-hardness of "ever entangled across site 1" requires the support of the terms touching site 1 to grow without bound. The coupling of the cut site must be nonlocal. Thm B attains this with the mildest such nonlocality: all-to-all, permutation-symmetric and bounded-body.

**Novelty.** The proof is two lines and the statement is probably folklore. I did not find it stated. Related work: high-temperature separability for local H (Bakshi–Liu–Moitra–Tang); a commuting-H counterexample family (Kiani 2026), whose text I could not check for this lemma.

---

## 2. Theorem B (commuting mean-field Gibbs states, fixed temperature)

**Setup.** Fix a universal polynomial U(y, x_1,…,x_s) ∈ ℤ[y,x]: t ∈ K iff ∃ x ∈ ℕ^s, U(t,x) = 0. Jones (1982) gives degree 4 (the pair ⟨58,4⟩ from memory; re-verify the exact pair in the paper). The system has two qubits A, B and m internal sites of dimension s+2, with letters {0,1,…,s,s+1}. Let N_i = Σ_{j=1}^m |i⟩⟨i|_j be the letter-number operators (commuting, diagonal, 1-body sums). Define the diagonal integer-valued operator
θ = 1 − U(N_{s+1}, N_1,…,N_s)^2 − (N_{s+1} − t)^2,
and
H_{t,m} = −θ ⊗ P_{AB} = H_m^{(0)} + t·(−2 N_{s+1} ⊗ P) + t^2·P,
with H_m^{(0)} = −(1 − U(N)^2 − N_{s+1}^2) ⊗ P independent of t.

**Structure.** Every monomial N_{i_1}⋯N_{i_k} = Σ_{j_1..j_k} Π_l |i_l⟩⟨i_l|_{j_l} is a sum of ≤k-body diagonal terms. So H_{t,m} is a sum of pairwise commuting (diagonal ⊗ {I or P}), permutation-invariant (on the internal sites), integer-coefficient terms of body number ≤ 2·deg U + 2 (≤ 10 with deg U = 4). The input t enters only as the strength of two fixed couplings, −2 N_{s+1}⊗P and P.

**Theorem B.** Let ρ = e^{−βH_{t,m}}/Z.
1. If β ≤ ln 3, ρ is fully separable for all t and m.
2. If β > ln 3 is fixed (e.g. β = 2), then ρ is entangled across A|rest iff some k ∈ ℕ^s satisfies U(t,k) = 0 and t + Σ k_i ≤ m. Hence {t : ∃ m, ρ entangled across A} = K is c.e.-complete. For t ∈ K the state is entangled for all m ≥ m_t. For t ∉ K it is fully separable for all m.

*Proof.* H is block diagonal in the letter basis: e^{−βH} = Σ_w |w⟩⟨w| ⊗ e^{βθ_w P} with θ_w = θ(k(w)) ∈ ℤ. Since P is a projector, e^{βθP} = I + (x−1)P with x = e^{βθ_w}. After normalization this is σ(F) with F = x/(x+3), because the complement eigenvalue is 1/(x+3) = (1−F)/3. Then F > 1/2 ⟺ x > 3 ⟺ βθ_w > ln 3. Now θ_w ≤ 1, with θ_w = 1 iff N_{s+1}(w) = t and U(t, k(w)) = 0, and θ_w ≤ 0 otherwise. If β ≤ ln 3, every block has F ≤ 1/2, so every block is separable, and tensoring each separable decomposition with |w⟩⟨w| gives full separability. If β > ln 3, a block is entangled iff θ_w = 1. Block diagonality with rest-side orthogonal projectors |w⟩⟨w| gives: ρ is entangled across A|rest iff some block is. "If": the local filter |w⟩⟨w| on the rest side followed by a partial trace maps ρ to a multiple of the entangled σ(F_w), and local operations cannot create entanglement. "Only if": a sum of separable blocks is separable. Words with θ_w = 1 exist at length m iff a witness k has t + Σk_i ≤ m (pad with letter 0), and padding persists to all larger m. Membership is c.e. (enumerate m, w and test the integer identity θ_w = 1), and K reduces to it via t ↦ t. ∎

**Remarks.** (a) The fixed temperature is essential to the cleanliness. The integrality of θ turns the PPT threshold into a sharp universal temperature T_c = 1/ln 3, independent of input and size. (b) By Thm A, in this model h_∂ is the whole Hamiltonian, as it must be. (c) Steady states: H_{t,m} is commuting, so its Davies generator has ρ as a fixed point (Kastoryano–Brandão, commuting case). Uniqueness of that fixed point, and the body-count of the generator, are **not checked** here (gap G2). (d) Unlike the base ρ_{t,m}, the marginals here are not maximally mixed. The key-hiding layer of the base construction could be added by conjugating P by controlled Paulis, at the cost of every P-term becoming m-body. That is not done here.

**Why not just use H = −log ρ_{t,m}.** In each flag block, −log ρ_{t,m} = m ln q − ln F_w · P_h − ln((1−F_w)/3)(I−P_h). F_w = 1/2 + J_t(k)/(8L_t b^m) has an m-dependent exponentially small offset, and its logarithm is not a fixed-degree polynomial in counts. The key sum h = Σ g_i makes P_h depend on all m sites. So H is not bounded-body uniformly in m. Thm B replaces the analytic threshold F > 1/2 at a varying F by an integer threshold θ = 1 at a fixed β.

---

## 3. Theorem C (fixed-bond-dimension pure states are decidable)

**Theorem C.** Fix physical dimension d and bond dimension D, a bulk tensor A = (A^i)_{i≤d} with algebraic entries, and computable algebraic boundary data: a left tensor (u_a)_{a≤d} ⊂ ℂ^D for site 1 and a right vector r ∈ ℂ^D. Let |ψ_m⟩ = Σ u_a^T A^{i_1}⋯A^{i_m} r |a,i_1..i_m⟩. Then "∃ m ≥ 1: |ψ_m⟩ is entangled across {1}|rest" is decidable, and so is "for all sufficiently large m".

*Proof.* Let 𝔼 = Σ_i A^i ⊗ \bar A^i. Then ρ_1(m)_{ab} = (u_a⊗\bar u_b)^T 𝔼^m (r⊗\bar r). A pure state is entangled across the cut iff rank ρ_1 ≥ 2, iff some 2×2 minor M(m) = ρ_{ac}ρ_{bd} − ρ_{ad}ρ_{bc} is nonzero. Each minor has the form α^T X^m β with X = 𝔼⊗𝔼 of size N = D^4. By Cayley–Hamilton, x_m = α^T X^m β satisfies an order-N recurrence valid for m ≥ N+1 that involves only x_{m−1},…,x_{m−N}. So x ≡ 0 on m ≥ 1 iff x_1 = … = x_N = 0, which is checked by exact algebraic arithmetic. For "all large m": each zero set {m : M(m) = 0} is a finite set together with a union of residue classes whose modulus and classes are computable (Skolem–Mahler–Lech; Berstel–Mignotte). The set of separable lengths is the intersection over all minors. It is finite iff the intersection of the periodic parts is empty, which is computable. ∎

**Consequence.** Ground-state versions must leave fixed bond dimension. The parent Hamiltonian of a fixed injective MPS can never do it. The base MPO succeeds because mixedness hides the witness in one of exponentially many classical blocks, which no polynomial identity in transfer powers detects. This explains the shift to computation/history states in §§4–6.

---

## 4. Theorem D (zero temperature: 2D commuting frustration-free, unique gapped ground state)

**Model.** Fix a TM M that, on input t, simulates the universal machine. Encode M in a 1D cellular automaton with local rule f : Σ^3 → Σ. The cell alphabet Σ = (Γ ∪ Q×Γ) × {0,1} holds a tape symbol, possibly the head, and a halt-signal bit η. The rule:
- f moves the head as M does, in the one-way-infinite convention: at column 1 a left move stays.
- η(x,y+1) = 1 iff the cell (x,y) contains a halting state, or η(x+1,y) = 1, or (x = 1 and η(1,y) = 1).
- At the edges x = 1 and x = W, a virtual blank neighbour is used (a boundary rule).

Lattice: W = n columns, n rows (y = 0..n−1). Each site is C^{|Σ|} ⊗ C^2 (cell plus auxiliary qubit). Terms, all projectors:
- (bulk, TI) R_{x,y} = Σ_{a ∈ Σ^3} |a⟩⟨a|_{(x−1..x+1,y)} ⊗ (I − |f(a)⟩⟨f(a)|)_{(x,y+1)}, range 2. A standard Wang-tile recoding makes it nearest-neighbour; not needed here.
- (bulk, TI) |1⟩⟨1| on every auxiliary qubit except A := aux(1,n−1) and B := aux(2,n−1).
- (boundary row) I − |c^0_x⟩⟨c^0_x| on cell (x,0), where c^0 = (q_0, t_1) t_2 ⋯ t_ℓ ␣ ⋯ ␣ is the input. The input is in single-site fields on the first ℓ = |t| sites, and the rest is a TI blank field.
- (corner) Π^η ⊗ (I − P)_{AB} + (I − Π^η) ⊗ (I − |00⟩⟨00|)_{AB}, with Π^η = projector onto η = 1 at cell (1,n−1).

**Theorem D.** H_{t,n} is a sum of pairwise commuting projectors and is frustration-free with a unique ground state, spectral gap ≥ 1. The ground state is |c^*⟩ ⊗ |Φ+⟩_{AB} ⊗ |0…0⟩ if η(c^*)_{(1,n−1)} = 1, and |c^*⟩ ⊗ |00⟩_{AB} ⊗ |0…0⟩ otherwise, where c^* is the space-time diagram of M on t. The corner site (1,n−1) is entangled with the rest iff M halts on t at a time τ_h with 2τ_h + 3 ≤ n. So "∃ n: the ground state's corner site is entangled" is c.e.-complete, and for halting t it holds for all n ≥ 2τ_h + 3.

*Proof.* Commutation: the classical terms are diagonal in the cell basis. The corner term is block diagonal in that basis, so it commutes with them, and it is disjoint from the other auxiliary fields. A sum of commuting projectors has integer spectrum, so the gap is ≥ 1 once the zero eigenspace is one-dimensional. Zero energy forces row 0 to equal c^0, and inductively row y+1 = f(row y). This gives the unique configuration c^*. It also forces every non-corner auxiliary qubit to |0⟩, and forces AB into the one-dimensional kernel of the corner term on the η-block of c^*. The vector given is annihilated by every term. Speed of light: after τ steps the head is at column ≤ τ+1 ≤ n, so the width-n truncation is exact for y ≤ n−1. If M halts at τ_h, the head is at x_h ≤ τ_h + 1. The signal reaches column 1 by row τ_h + x_h ≤ 2τ_h + 1 and stays, so η = 1 at (1,n−1) when n−1 ≥ 2τ_h+2. If M never halts, η ≡ 0. A pure state |c^*⟩ ⊗ |Φ+⟩ ⊗ … has the maximally mixed state on qubit A, and the corner site's cell is classical-definite, so the corner site is mixed and hence entangled. In the other case the state is a product. c.e.: simulate. Hardness: t ↦ t. ∎

**Finite-temperature contrast.** By Thm A, at every finite β the Gibbs state of this same H is entangled across the corner iff e^{−β h_∂} is, where h_∂ is the corner term plus the classical terms touching cell (1,n−1). The answer does not depend on t: all η-values occur in h_∂'s support. **Dichotomy for commuting local models:** at T = 0 the problem is c.e.-complete; at every T > 0 it is length-free and local.

**Novelty.** Low. Computation in classical 2D ground states is classical (Berger; Robinson; Gottesman–Irani tilings), and Cubitt–Pérez-García–Wolf argue that ground-state properties in 2D are generically undecidable. The entanglement packaging with a uniform gap and unique pure ground state is clean, but I would not claim priority.

---

## 5. Theorem E (2D local Lindbladian with unique pure steady state)

Same lattice. All jump operators have bounded range, the bulk is TI, and the input is on the boundary row.
- For each rule location and each (a, b) with b ≠ f(a): L = |a⟩⟨a|_{row y} ⊗ |f(a)⟩⟨b|_{(x,y+1)}.
- Boundary row: L = |c^0_x⟩⟨b|_{(x,0)} for b ≠ c^0_x.
- Non-corner auxiliary qubits: L = |0⟩⟨1|.
- Corner: L = Π^η ⊗ |Φ+⟩⟨χ| for χ ∈ {Φ−, Ψ+, Ψ−}, and L = (I−Π^η) ⊗ |00⟩⟨χ'| for χ' ∈ {01, 10, 11}.
- No Hamiltonian part.

**Theorem E.** The Lindbladian has a unique steady state, equal to the pure ground state of Thm D, and every initial state converges to it. Hence "∃ n: the steady state's corner site is entangled" is c.e.-complete.

*Proof.* Call the cells plus the non-corner auxiliary qubits the classical register 𝒞. Every non-corner jump is a classical partial permutation: it maps each basis configuration in its support to one basis configuration, injectively. So for diagonal D on 𝒞, L^†(D⊗I)L and L^†L are diagonal. Corner jumps act on 𝒞 only through the diagonal Π^η. For them L^†(D⊗I)L = DΠ^η ⊗ |χ⟩⟨χ| = ½{L^†L, D⊗I}, so they cancel. Therefore the population vector p(t) of 𝒞 evolves autonomously under a classical Markov generator G. The configuration c^* (with auxiliaries 0) is absorbing, since it has no defects. It is reachable from every configuration: fix row 0, then row 1 (a corrected cell's rule inputs never change again), and so on, then reset the auxiliaries. Hence p(t) → δ_{c^*}.

Let P^* = |c^*⟩⟨c^*| ⊗ |τ⟩⟨τ|_{AB}, with τ the target of the η-block of c^*. Non-corner jumps annihilate |c^*⟩, so their anticommutator part with P^* vanishes and their sandwich part is ≥ 0. The corner jumps of the active block give L^†P^*L = |c^*⟩⟨c^*| ⊗ |χ⟩⟨χ| and L^†L P^* = 0, since χ ⊥ τ. So ℒ^*(P^*) ≥ |c^*⟩⟨c^*| ⊗ (I − |τ⟩⟨τ|), and x(t) = tr(P^*ρ(t)) satisfies x′ ≥ p_{c^*}(t) − x. Since p_{c^*} → 1, liminf x ≥ 1, so ρ(t) → P^* in trace norm. A steady state is its own limit, so it equals P^*. ∎

**Novelty.** This is a dissipative-preparation construction of the Verstraete–Wolf–Cirac / Kraus et al. type, specialised to a deterministic classical computation. The convergence proof above is self-contained.

---
