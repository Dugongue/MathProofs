# Coordinate compactness for fixed tensor restriction targets

This builds the bounded-coordinate witness and derives the field-specific decision algorithms.

## 1. Theorem 1: coordinate compactness

**Theorem 1.** Let F be any field, T ∈ F^{a×b×c}, S ∈ F^{n₁×n₂×n₃}. Then S ≥_F T iff there are index sets P ⊆ [n₁], Q ⊆ [n₂], R ⊆ [n₃] with |P| ≤ bc, |Q| ≤ ca, |R| ≤ ab such that the coordinate subtensor S[P,Q,R] ≥_F T. More precisely, any solution (A,B,C) can be replaced by a solution (A′,B′,C′) whose nonzero columns are indexed by such P, Q, R.

*Proof.* Let (A⊗B⊗C)S = T. Write S = Σ_p e_p ⊗ S_p with slices S_p ∈ F^{n₂×n₃}, and put a_p = Ae_p ∈ F^a, N_p = (B⊗C)S_p ∈ F^b⊗F^c. Then T = Σ_p a_p ⊗ N_p ∈ F^a ⊗ W with W = span_p N_p, dim W ≤ bc. Choose P with {N_p}_{p∈P} a basis of W. Every element of F^a⊗W is uniquely Σ_{p∈P} a′_p⊗N_p. Let A′ have columns a′_p for p ∈ P and zero columns otherwise. Then (A′⊗B⊗C)S = T, and B, C are unchanged. Repeat with the second leg, holding A′ and C fixed (this changes B only), then the third. The supports obtained are not disturbed by the later steps. ∎

The statement is basis-free in the input: it holds in every basis of the three input spaces. It is "conciseness of the witness in coordinates".

**Corollary 1.1 (order k).** For T ∈ F^{a₁×…×a_k}, a restriction S ≥ T is witnessed on a coordinate subtensor with |P_i| ≤ ∏_{j≠i} a_j. Same proof.

**Corollary 1.2 (degeneration).** Let S ⊵_F T mean: there are A, B, C over F((ε)) with (A⊗B⊗C)S = T + O(ε) (algebraic degeneration; over algebraically closed F this is orbit-closure membership). Then S ⊵_F T iff S[P,Q,R] ⊵_F T for some |P| ≤ bc, |Q| ≤ ca, |R| ≤ ab.

*Proof.* Apply Theorem 1 over the field F((ε)) to the target T_ε := (A⊗B⊗C)S ∈ F((ε))^{a×b×c}. The new maps still produce T_ε = T + O(ε). ∎

**Corollary 1.3 (reduction).** Let 𝔻_T(F) := {S′ ∈ F^{bc×ca×ab} : S′ ≥_F T}. Then S ∈ RES_F(T) iff some coordinate subtensor of S of format ≤ bc×ca×ab (zero-padded) lies in 𝔻_T(F). There are at most n^{ab+bc+ca} subtensors. So RES_F(T) ≤ 𝔻_T(F) by a polynomial-size disjunctive truth-table reduction, and 𝔻_T(F) ≤_m RES_F(T) trivially.

𝔻_T(F) is defined by the fixed existential formula ∃A,B,C: (A⊗B⊗C)X = T in abc cubic equations and a²bc + ab²c + abc² unknowns. This is the mirror image of significance-r6 Prop 6.1 (fixed *large* tensor, concise core of the small one), which is why G1 §5 recorded "fixed-r subrank: not reached, compression not containment". With Theorem 1 the compression case is no harder.

---

## 2. Theorem 2: fields with decidable theories

**Theorem 2.** Fix T.
1. F finite: RES_F(T) ∈ AC⁰ (a depth-2 circuit: OR over ≤ n^{ab+bc+ca} subtensors of a predicate on a constant number of field elements). Deterministic time O(n^{ab+bc+ca}).
2. F algebraically closed (inputs over a number field or a finite field), F real closed (inputs rational), F = ℚ_p (inputs rational): RES_F(T) ∈ P.
3. F algebraically closed: DEG_F(T) ∈ P.

*Proof.* 1 is Cor 1.3. For 2, 𝔻_T(F) is definable by a fixed existential formula. By quantifier elimination (Chevalley for ACF, per characteristic; Tarski for RCF; Macintyre for ℚ_p with the predicates "is an n-th power") it equals a fixed quantifier-free formula in the entries of X. Evaluating fixed polynomials, signs and p-adic n-th-power predicates on rational input is polynomial time. Then Cor 1.3. For 3, use Cor 1.2 and the same argument for the fixed constructible set {X : T ∈ closure of the image}. ∎

Remarks.
- Before finding Theorem 1 I proved 1 and 2 by heavier means, kept here only as cross-checks (methodology rule 8): over F_q the indicator of the solution set is a polynomial of degree ≤ 3abc(q−1), and a nonzero reduced polynomial of degree Δ has a nonzero point of support ≤ Δ (minimal-support monomial), so some solution has ≤ 3abc(q−1) nonzero entries; Warning's second theorem gives solution density ≥ q^{−3abc}, so RES ∈ RP by sampling. Over algebraically closed F a generic affine section of dimension abc meets the solution variety (Krull + Chow form of the part at infinity, degree ≤ 3^{abc} by Bézout), giving a sparse witness of support ≤ abc·3^{abc}. Theorem 1 supersedes both bounds.
- With the target part of the input (FULLSUB: is Q(S) = n?), the problem is NP-complete over F_q and ≡ HTP(K) over any field [G1 Thm A]. The collapse is specific to a fixed target.

---

## 4. Theorem 4: an intrinsic sufficient criterion for P over infinite fields

Let T ∈ F^{a×b×c} be concise, G = GL_a×GL_b×GL_c.
- **(O)** G(F̄)·T is Zariski open in F̄^{a×b×c}.
- **(H)** Every F-rational tensor in G(F̄)·T lies in G(F)·T. (By Hilbert 90 for G this is H¹(F, Aut T) = 1.)

**Theorem 4.** Let F be infinite and T satisfy (O) and (H). Then for every S over F: S ≥_F T ⟺ S ≥_{F̄} T. Hence RES_F(T) ∈ P for F = ℚ, ℝ, number fields, function fields. If (O) holds and (H) fails, RES_F(T) ≠ RES_{F̄}(T) on F-inputs.

*Proof.* If S ≥_{F̄} T, then φ_S(A,B,C) = (A⊗B⊗C)S maps the affine space into the open orbit somewhere, so φ_S^{-1}(G(F̄)T) is nonempty and open, and it has an F-point because F is infinite. Its image is an F-rational tensor in the geometric orbit, hence in G(F)T by (H); compose with the element of G(F). P: Theorem 2 over F̄. For the last sentence take S = a nontrivial F-form of T: a restriction between concise tensors of equal format is an isomorphism. ∎

Examples.
| T | (O) | (H) | consequence |
|---|---|---|---|
| I_r ∈ F^{1×r×r} (matrix of rank r) | yes | yes (Aut ≅ G_m×GL_r) | field-blind |
| F_{a,b} = ⟨a,1,b⟩, format a×b×ab | yes | yes (Aut ≅ GL_a×GL_b) | field-blind |
| T_N: slice space N^⊥ ⊂ F^{b×c}, N of full rank; format (bc−1)×b×c; e.g. sl₂ ⊂ M₂, the generic 3×2×2 tensor | yes | yes (parabolic-type stabiliser, Levi a product of GL's) | field-blind |
| ⟨2⟩ | yes | **no** (forms = quadratic étale algebras) | arithmetic: square classes |
| generic 2×3×3 | yes | no (cubic étale algebras) | arithmetic |
| ⟨r⟩, r ≥ 3; ⟨2,2,2⟩; W | no | — | Theorem 4 silent |

(O)+(H) is the analogue of the "affine / Mal'cev" criterion of #1, and like the first easy-side conjecture there it is **not** necessary: W fails (O) but RES_F(W) looks field-blind (R-tr-small-targets §2). I have no necessary and sufficient criterion, and §6 explains why one over ℚ is out of reach.

---

## 5. Proposition 6: subrank ≥ 2 over every field (T = ⟨2⟩)

**Lemma 5.** Let 𝒮 ⊆ F^{m×m′} be a matrix space, dim 𝒮 ≥ 2, with Σ_s col(s) of dimension ≥ 3 and Σ_s row(s) of dimension ≥ 3. Then some s₁, s₂ ∈ 𝒮 have dim(col s₁ + col s₂) ≥ 3 and dim(row s₁ + row s₂) ≥ 3.

*Proof.* Suppose not. Then every element has rank ≤ 2 (pair it with itself and any other element). If some s₀ has rank 2, every s satisfies col(s) ⊆ col(s₀) or row(s) ⊆ row(s₀). These are two subspaces of 𝒮 with union 𝒮, so one is 𝒮, contradicting the hypothesis on columns or on rows. If all elements have rank ≤ 1, 𝒮 has a common column space or a common row space of dimension 1. ∎

**Proposition 6.** Let F be a field of characteristic ≠ 2 and S a tensor with concise core of format (m₁,m₂,m₃). Then Q_F(S) ≥ 2 iff min m_i ≥ 2 and the core is not a 2×2×2 tensor whose discriminant (Cayley hyperdeterminant) lies outside (F^×)². So RES_ℚ(⟨2⟩) ∈ P, RES_F(⟨2⟩) is field-blind except on 2×2×2 cores, and the only arithmetic is one square-class test.

*Proof.* If some m_i ≤ 1, S is a matrix and Q ≤ 1. Assume all m_i ≥ 2 and S concise.
- All m_i ≥ 3: by Lemma 5 applied to the leg-1 slice space, two slices form a pencil whose concise core is 2×m×m′ with m, m′ ≥ 3. [BCLSZ, Thm 3.19] gives subrank 2 (stated for an arbitrary field; the proof is Gaussian elimination and uses conciseness in two directions only, their Remark 3.23).
- Some m_i = 2: S is a pencil, 2×m×m′. If m, m′ ≥ 3 use [BCLSZ]. Otherwise, after permuting legs, S is 2×2×m with m ∈ {2,3,4}.
  - m = 4: S ≅ F_{2,2} ≥ ⟨2⟩.
  - m = 3: the slice space is N^⊥ ⊂ M₂(F), N ≠ 0. Rank-one elements are uvᵀ with uᵀNv = 0. If N is invertible take u₁, u₂ independent and v_i ⊥ Nᵀu_i; the v_i are independent. If N = pqᵀ take u₁ ⊥ p with v₁ ∉ q^⊥ arbitrary, and v₂ ⊥ q with u₂ ∉ Fu₁. In both cases N^⊥ contains a rational frame, so Q = 2 (G1 Lemma 1).
  - m = 2: a restriction to ⟨2⟩ between concise 2×2×2 tensors is an isomorphism, and the orbit of ⟨2⟩ is {disc ∈ (F^×)²}. ∎

C++ (R-tr-small-targets §4): over F₂ and F₃ there are 8 orbits on 2×2×2; only the orbit of ⟨2⟩ restricts to ⟨2⟩, only W to W, and the eighth orbit is the non-split form (F₄ resp. F₉).

---

## 6. Theorem 7: ⟨3⟩ over ℚ contains a Mordell–Weil rank problem

For N ∈ ℚ^{3×3×3} with slices N₁,N₂,N₃ let S_N ∈ ℚ^{3×3×6} have slice space N^⊥ = {m ∈ M₃ : tr(N_kᵀm) = 0}. By G1 Lemma 1, S_N ≥_ℚ ⟨3⟩ iff N^⊥ contains rank-one matrices u_t v_tᵀ (t = 1,2,3) with {u_t} and {v_t} bases. The rank-one locus is C_N = {(u,v) ∈ ℙ²×ℙ² : uᵀN_kv = 0, k = 1,2,3}, a codimension-3 linear section of the Segre fourfold: for nondegenerate N a smooth genus-one curve, embedded by two degree-3 line bundles L₁, L₂ as plane cubics (u-projection: det(Σ u_i N^{(i)}) = 0).

By [BH, Cor 5.4] (char ≠ 2, 3) the nondegenerate orbits are exactly the triples (C, L₁, P), C a genus-one curve, L₁ of degree 3, 0 ≠ P = L₂ − L₁ ∈ Jac(C)(ℚ) a difference of two rational degree-3 classes.

**Theorem 7.** Let E/ℚ be an elliptic curve with E(ℚ)_tors = ⟨P⟩ of order 2 or 3, and N = N(E,P) a cube with data (E, 𝒪(3O), P) (computable: the kernel of H⁰(L₁)⊗H⁰(L₂) → H⁰(L₁⊗L₂), 9 → 6 dimensions). Then

  S_N ≥_ℚ ⟨3⟩ ⟺ rank E(ℚ) ≥ 1.

So RES_ℚ(⟨3⟩), already on inputs of format 3×3×6, decides positivity of the Mordell–Weil rank for all elliptic curves with torsion subgroup ℤ/2 or ℤ/3. No unconditional algorithm for that is known (it is decidable under BSD or finiteness of Ш).

*Proof.* Three points A₁,A₂,A₃ of C are collinear in the L₁-embedding iff A₁+A₂+A₃ = O, and in the L₂-embedding iff A₁+A₂+A₃ = P (group law with origin O). If rank ≥ 1, E(ℚ) is infinite: pick A₁ ≠ A₂ and then A₃ outside the two lines, at most 6 points. If rank 0, E(ℚ) = ⟨P⟩. Order 2: two rational points, no frame. Order 3: the only triple is {O, P, 2P}, with sum O, collinear in the L₁-embedding. ∎

More generally RES_ℚ(⟨r⟩) on r×r×m inputs asks for r rational points in general position on a linear section of ℙ^{r−1}×ℙ^{r−1}; for r = 4 these include K3 surfaces and curves of genus 11. For torsion ℤ/2×ℤ/2 (congruent-number curves) the torsion points already give a frame ({O, P, T}), so the reduction says nothing there.

---
