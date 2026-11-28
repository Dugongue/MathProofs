# Hardness reductions through the five-leaf quiver

The reduction here applies to the displayed quiver, its opposite, and quivers admitting the indicated extension of the construction. The more general wild case requires the separate embedding argument.

## 1. The gadget chain (all field-independent)

**1a. Quadrics → K(n)-bristles (Reineke 1204.5730, adapted to a fixed number of vertices).**
- Input: homogeneous quadrics q_1..q_s in x_0..x_m over F.
- Let Sym = symmetric (m+1)×(m+1) matrices Y. Let Λ_j(Y) = Σ_{i≤k} c^{(j)}_{ik} y_{ik}, where q_j = Σ_{i≤k} c^{(j)}_{ik} x_i x_k.
- Define the K(n)-rep N, with n = m+1 arrows:
  - N_1 = ker Λ ⊆ Sym;
  - N_2 = F^{m+1};
  - φ_i(Y) = i-th column of Y.
- **Claim (P, any field, any char).** [Y] ↦ (⟨Y⟩, column line) is a bijection {[x] ∈ P^m(F) : q(x)=0} ≅ Gr_{(1,1)}(N)(F).
- Proof.
  - A subrep of dim (1,1) is ⟨Y⟩ with all columns of Y in one line ℓ. Y ≠ 0, so ℓ = column space, and the condition is rank Y = 1.
  - A rank-one symmetric Y over F is a b^T with b ∥ a (by symmetry), so Y = λ a a^T with a ∈ F^{m+1}. Then [Y] determines [a] and conversely.
  - Λ_j(λaa^T) = λ q_j(a).
  - N is reduced, since ∩ ker φ_i = {Y = 0}. ∎
- Size: dim N_1 ≤ (m+1)(m+2)/2. Poly.
- BILPS 1911.02534 §8.2 give the same NP-hardness as HMinRank1 (minrank ≤ 1 of a tensor), which is the identical problem read along another tensor axis.

**1b. SAT → quadrics over every field (P).**
- Variables x_0, x_i, and auxiliaries y.
- Equations:
  - x_i² = x_0 x_i;
  - y² = x_0 y;
  - x_0 y = x_i x_j (products);
  - clause (ℓ₁∨ℓ₂∨ℓ₃): x_0 z = (x_0−ℓ₁)(x_0−ℓ₂) and z·(x_0−ℓ₃) = 0, with z Boolean as well.
- If x_0 = 0, every variable has v² = 0, so v = 0. So x_0 ≠ 0, and after normalising every solution is 0/1 and F_p-rational. Points over F, over F_q and over F̄ all ↔ satisfying assignments.
- (Alternatively, cite BILPS Thm 8.6 or Grenet–Koiran–Portier.)

**1c. Ringel's Case-1 functor for a fixed quiver (field-independent).**
- Q* has vertices ω, a, b and arrows α, β: a → b and γ: ω → b. It is wild: the graph K(2) with a pendant vertex is neither Dynkin nor Euclidean.
- X = P_t, the preprojective K(2)-rep on {a, b}:
  - X_a = F^t, X_b = F^{t+1};
  - α(e_i) = e_i, β(e_i) = e_{i+1}.
- X is exceptional over every field: End = F, ⟨x,x⟩ = 1. Put n := t+1 = dim X_b. Y = S(ω), which is injective because ω is a source.
- Φ(N), for a K(n)-rep N = (N_1, N_2; φ_1..φ_n):
  - Φ(N)_ω = N_1;
  - Φ(N)|_{a,b} = N_2 ⊗ X;
  - γ(u) = Σ_i φ_i(u) ⊗ e_i.
- **Φ is exact and fully faithful (P).**
  - Q'-homs N_2⊗X → N_2'⊗X are g⊗id, because X is a brick with End = F.
  - Compatibility with γ is exactly g φ_i = φ'_i f.
  - Exactness is clear.
- **Closure (C) (P, over any field; Ringel's proof, checked to be field-free).** For N reduced, U ↦ Φ⁻¹ gives Gr_{x+y}(ΦN) ≅ Gr_{(1,1)}(N). Here x+y = (1, t, t+1).
  - U_ω is 1-dim, so the image of U in Y^b is ≅ Y.
  - The kernel W ⊆ X^a has dim x. By Euler form ⟨x, dim W⟩ = 1 > 0 there is a nonzero map X → W. Composed into X^a it splits, since X is a brick with End = F. So W ≅ X.
  - Hence U ∈ E = E(Y,X), and U = Φ(B) with B ⊆ N of dim (1,1).
  - Euler forms, the brick property and injectivity of Y hold over every field.
- **C++ check (gadget.cpp).** Exhaustive counts #Gr_{(1,t,t+1)}(ΦN) vs #Gr_{(1,1)}(N), random N:
  - p=2, (t,d1,d2) = (2,2,2): 289/289; (2,3,2): 88/88; (2,3,3): 196/196; (2,4,2): 78/78; (3,2,2): 40/40; (3,3,2): 59/59;
  - p=3, (2,2,2): 98/98; (2,3,2): 99/99.
  - 0 disagreements. Counts also agree on every non-reduced N tested (0 of 53 differ). The reason: when u ∈ ∩ker φ_i, both sides gain P(N_2) many points, because copies of X inside X^{d2} ↔ lines of F^{d2}. So reducedness is not even needed for counts here.
- **Size:** ΦN has dims (d1, t·d2, (t+1)·d2). Poly.

**1d. General wild acyclic Q with ≥3 vertices (S 85%).**
- Lemma (P): every connected wild acyclic quiver with ≥3 vertices contains, as a (not nec. full) subquiver, a Euclidean quiver E plus one extra vertex ω joined to E by a single arrow.
  - Proof: take a Euclidean subgraph.
    - If it misses a vertex, add an adjacent vertex with one arrow.
    - If it spans all vertices, Q has an extra arrow i–j.
      - If i, j are adjacent, this gives a double edge (Ã₁) plus a third neighbouring vertex.
      - If E is a tree (D̃, Ẽ), the new edge closes a cycle through a path. That cycle is a proper Ã_r, since a path meets at most 2 of the ≥3 leaves, and there is a neighbour outside it.
      - If E = Ã_r, a chord gives a shorter cycle plus a neighbour.
- For a subquiver Q₀ ⊆ Q (deleting vertices and/or arrows), extension by zero mod kQ₀ → mod kQ is full, exact and **closed under submodules**. So Gr_e is unchanged, and Hom and monos are unchanged.
- ω is a source or sink in Q₀. For a sink, dualise: Gr_e(M) ≅ Gr_{dim M−e}(DM) over Q^op.
- X := a preprojective τ^{-r}P(i) of E containing the vertex p adjacent to ω. Dimension grows linearly in r (it is rδ + const with δ sincere). It is computable in poly(r) arithmetic operations by Coxeter reflection functors (each step is kernel/cokernel linear algebra over F). It is exceptional over every field (BGP).
- The weak link is a clean poly-time bound on entry sizes over ℚ. Over F_q this is trivial.

**Theorem A (P for Q*; S 85% for all Q).** SAT ≤_p SUB(Q) over every field F. The input is M ∈ rep_F(Q) as matrices over the prime field and a dimension vector e (binary or unary, both fine since dims are poly). The question is whether Gr_e(M)(F) ≠ ∅.
- Over F_q: NP-complete (certificate: a basis of U).
- Over F̄_p and ℂ: NP-hard. The upper bound is HN over that field: PSPACE, and AM under GRH for ℂ (Koiran).
- **Algebras.** If A = kQ_A/I with I ⊆ rad², and Q_A contains a wild subquiver Q₀ with ≥3 vertices and **no path of length 2** (e.g. Q* itself, which is bipartite), then reps of Q₀ satisfy I and their submodules stay in Q₀. So A inherits Theorem A. Q* ⊂ Q_A suffices.

## 2. Over ℚ: projective rational points are HTP(ℚ)-hard (closes R1's Thm-4 step)

**Lemma Q (P 85%).** HTP(ℚ) ≤_m PROJRAT₂(ℚ), where PROJRAT₂(ℚ) asks whether a system of homogeneous quadrics over ℤ has a nontrivial rational zero.

Proof.
- Reduce an affine system to quadratic equations g_1..g_s in variables z_1..z_N (standard auxiliaries).
- New homogeneous variables: x_0, U, W, R, and a_v, b_v, c_v, d_v for each v ∈ {z_1..z_N, R}.
- Equations:
  1. G_j(x_0, z) = 0, the homogenisations of g_j;
  2. U² − 2W² = x_0 R;
  3. v² + a_v² + b_v² + c_v² + d_v² = U² for every v ∈ {z_1..z_N, R}.
- **Points at infinity.**
  - x_0 = 0 makes (2) read U² = 2W², so U = W = 0 over ℚ.
  - Then each (3) is a sum of squares of rationals equal to 0, so v = a_v = … = 0.
  - Every coordinate is 0, so there is no projective point with x_0 = 0.
- **Affine solutions lift.** Given z ∈ ℚ^N solving g:
  - pick rational U ≥ max(1, |z_i|);
  - take a convergent p/q of √2 with |p² − 2q²| = 1 and p² ≥ U, and set W = Uq/p;
  - then R := U² − 2W² = ±U²/p² has |R| ≤ U;
  - every U² − v² ≥ 0 is a nonnegative rational, hence a sum of 4 rational squares (Lagrange), giving a_v..d_v.
- **Conversely**, a rational point has x_0 ≠ 0; normalise to x_0 = 1 and read off z. ∎

The point: R-anisotropic (positive definite) forms cannot work alone, because real points at infinity always exist for unbounded sets. The irrational slope √2 of the dominant pair (U, W) removes rational points at infinity, and four squares make every other coordinate O(U).

**Theorem B (P 85%, given BB).** SUB(Q*) over ℚ is Σ⁰₁-complete.
- Hardness: Lemma Q, then 1a, then 1c. Everything is field-independent, and bijections hold on ℚ-points.
- c.e.: enumerate rational subspaces.
- With BB (HTP(ℚ) Σ⁰₁-complete), it is Σ⁰₁-complete. The same holds for every wild acyclic Q with ≥3 vertices (S, as 1d).

**Theorem B′ (P 90%).** SUB^⋔: additionally given a graded subspace C, require U ∩ C = 0.
- Take C_ω = hyperplane {y_00 = 0} in N_1 (Reineke chart). Then rank-one Y with y_00 = 1 is xx^T with x_0 = 1 over any field.
- So affine quadratic systems reduce directly. Σ⁰₁-complete over ℚ under BB without Lemma Q.
- It is also NP-complete over F_q.

Contrast with model theory (R1 K6, cite Prest): wild ⇒ undecidable *theory of modules* (Prest for strictly wild; Gregory–Prest for controlled wild). That is a first-order-sentence statement. B/B′ are fixed-template decision problems on explicit modules, and their undecidability comes from HTP(ℚ) via geometry, not from the word problem.

## 3. EMB is Edmonds-complete for wild quivers, over every field (answers the R2/R4 secondary lead)

**Theorem E (P for Q*, S 85% general).** Let EDM(F) be the problem: given n×n matrices C_1..C_r over F, does span{C_l} contain a nonsingular matrix (over F)? Then EDM(F) ≤_p EMB(Q*) over every field F.
- Step 1 (R4's gadget, checked).
  - K(r)-module M with M_1 = F^r, M_2 = F^n, and arrow i: x ↦ i-th column of Σ_l x_l C_l, i.e. A_i e_l := (C_l)_{:,i}.
  - P_1 = projective at the source has dims (1, r).
  - Hom(P_1, M) ≅ M_1 ∋ x, and f_x is injective ⟺ the columns A_1x..A_rx are independent ⟺ Σ x_l C_l is nonsingular (r = n).
- Step 2. Φ: mod K(r) → mod Q* from 1c, with t = r−1. It is fully faithful and exact, and so preserves and reflects monos: F(f) has kernel F(ker f), and F is faithful, so F kills no nonzero object. Hence P_1 ↪ M ⟺ ΦP_1 ↪ ΦM.
  - This is the **field-independent** embedding R4 lacked: no distinct scalars are needed.
- Consequences.
  - Over F_q, EDM is NP-complete (Buss–Frandsen–Shallit 1999; R1's bfs-linalg.txt), and EMB(Q*) ∈ NP. So **EMB(Q*) is NP-complete over every fixed F_q**.
  - Over infinite F, EMB ∈ RP for every algebra (R2), and EMB(Q*) is SDIT-hard. So deterministic EMB(Q*) ∈ P ⟺ Edmonds/SDIT ∈ P.
  - Matrix spaces are realised up to the injectivity correspondence: Hom(ΦP_1, ΦM) ≅ M_1 ≅ span{C_l} as parameter spaces.
- The same holds for every wild acyclic Q with ≥3 vertices via 1d, and for kQ/I containing a length-2-free wild subquiver.
- For tame quivers, deterministic EMB ∈ P is R4's conjecture C 60%, not checked here.
- This gives the tame/wild line "deterministic P vs PIT-hard" **only if** the tame side lands.
