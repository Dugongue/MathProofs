# Single equations in free class-two nilpotent groups

The proof closes both the nondegenerate and the degenerate strata in fixed or variable rank.

## 2. Model and the normal form of a single equation

**Model.** N = N_{2,r} = Z^r × Λ²Z^r with the product (x,c)(x',c') = (x+x', c+c'+τ(x,x')), where τ(x,x') = Σ_{a<b} x_a x'_b e_a∧e_b. Then [(x,c),(x',c')] = (0, x∧x'), the centre and derived subgroup both equal Λ²Z^r, and (x,c)^{-1} = (−x, −c+τ(x,x)).

Let w(X_1..X_k) be a word with constants from N, and write X_i = (x_i, c_i). Multiplying out, the abelian coordinate of w is Σ e_i x_i + a_0, where e_i is the exponent sum of X_i. The central coordinate is Σ e_i c_i + Q(x), where Q is an integer polynomial map (Z^r)^k → Λ²Z^r ≅ Z^{r(r−1)/2}, computable from w.

**Lemma 2.1 (nonzero exponent sum ⇒ decidable).** Suppose e ≠ 0, and let g = gcd(e_i). Then w = 1 is solvable iff there exists x with Σ e_i x_i = −a_0 and Q(x) ≡ 0 (mod g·Λ²Z^r). This is decidable.

*Proof.* The central parts c_i are free, and {Σ e_i c_i} = gΛ²Z^r. Since Q has integer coefficients, Q(x) mod g depends only on x mod g. So: enumerate the residues x̄ ∈ ((Z/g)^r)^k with Q(x̄) ≡ 0, and for each one decide the linear Diophantine system {Σ e_i x_i = −a_0, x ≡ x̄ mod g} using Smith normal form. ∎

**Lemma 2.2 (zero exponent sums).** Suppose e = 0. Then w = 1 is solvable iff a_0 = 0 and there exist x_i ∈ Z^r with

  Σ_{i<j} a_ij x_i∧x_j + Σ_i h_i∧x_i = c_0,        (1)

where the integers a_ij, the vectors h_i ∈ Z^r and the bivector c_0 are computable from w.

*Proof.* Work in the class-2 quotient of F(X)*N. There g X^ε = X^ε g [g,X^ε], so moving every constant to the right gives w = w_X · g_0 · ∏(central factors [g,X_i^{±1}]). Here w_X is the word in the variables alone. In class 2, [g,X^{-1}] = [g,X]^{-1} and [g,X][g',X] = [gg',X], so the central factors combine to ∏_i [h̃_i, X_i]. Since w_X has zero exponent sums, in the free class-2 group it equals ∏_{i<j}[X_i,X_j]^{a_ij}. Evaluating sends [X_i,X_j] ↦ x_i∧x_j and [h̃_i,X_i] ↦ h_i∧x_i. The central coordinates c_i of the variables do not occur. ∎

**Lemma 2.3 (symplectic normal form).** Let A = (a_ij) be the alternating k×k matrix of (1). There is P ∈ GL_k(Z) with P^T A P = diag(d_1J, …, d_tJ, 0), where d_l ≥ 1 and d_l | d_{l+1} (Frobenius normal form; Newman, *Integral Matrices*, Thm IV.1). Substitute x_i = Σ_j P_ij y_j, which is a bijection of (Z^r)^k. Then (1) becomes

  Σ_{l≤t} d_l y_l∧z_l + Σ_{l≤t} (y_l∧P_l + z_l∧Q_l) + Σ_{j} s_j∧w_j = c_0,

where (y_l, z_l) are the paired new variables and the w_j are the unpaired ones, with computable vectors P_l, Q_l, s_j. ∎

**Completing the product.** The identity d(d y∧z + y∧P + z∧Q) = (dy−Q)∧(dz+P) + Q∧P holds; expand to check. Moreover (y,z) ↦ (u,v) = (dy−Q, dz+P) is a bijection onto {u ≡ −Q, v ≡ P (mod d)}. The unpaired terms range exactly over the subgroup S∧Z^r, where S = span(s_j). Multiplying by D = d_t, which is injective because Λ²Z^r is torsion-free, we obtain:

**(1) is solvable ⟺** there exist u_l ≡ −Q_l and v_l ≡ P_l (mod d_l), and λ ∈ (DS)∧Z^r, with

  Σ_l (D/d_l)·u_l∧v_l + λ = D c_0 − Σ_l (D/d_l) Q_l∧P_l.        (2)

---

## 3. Theorem 1: SE(N_{2,r}) is equivalent to CSR_r

**Definition (CSR_r).** An instance consists of: t ≥ 0; positive integers m_l and moduli F_l; residues α_l, β_l ∈ Z^r; a subgroup S ≤ Z^r (given by generators); and c ∈ Λ²Z^r. The question is whether there exist u_l ≡ α_l, v_l ≡ β_l (mod F_l) and λ ∈ S∧Z^r with

  Σ_{l≤t} m_l u_l∧v_l + λ = c.

**Theorem 1.** For each r, there is an algorithm that takes a single equation over N_{2,r} and either decides it outright (the case e ≠ 0) or outputs a CSR_r instance with the same answer. Conversely, every CSR_r instance is computably equivalent to the single equation

  ∏_l [a_l Y_l^{F_l}, b_l Z_l^{F_l}]^{m_l} · ∏_j [σ_j, W_j] = g,

where a_l, b_l ∈ N have abelian images α_l, β_l, the σ_j have images generating S, and g = (0, c). Hence **single equations in N_{2,r} are decidable iff CSR_r is decidable.**

*Proof.* Forward: Lemmas 2.1–2.3 and (2). Converse: the abelian image of a_l Y^{F_l} runs over exactly α_l + F_l Z^r. Commutators are central and bilinear, so [A,B]^m = (0, m·Ā∧B̄). Finally, Σ_j σ̄_j∧w_j runs over S∧Z^r. ∎

---

## 4. Theorem 2: decidable strata

**(a)** The case e ≠ 0 is decidable: Lemma 2.1. This case is due to E. K. Burke and J. K. Truss, *Unification for nilpotent groups of class 2*, Forum Math. 7 (1995), doi:10.1515/form.1995.7.435; Levine's survey attributes to them the decidability of equations that are not products of commutators. Lemma 2.1 is a self-contained proof.

**(b) Saturated, congruence-free, unit multipliers.** Suppose all F_l = 1, all m_l = 1, and S is saturated (Z^r/S torsion-free). Then the instance is solvable iff the image c̄ ∈ Λ²(Z^r/S) has rank ≤ 2t.

*Proof.* Choose a basis with S = span(e_1..e_q). Then S∧Z^r = span{e_a∧e_b : a ≤ q}, and Λ²Z^r/(S∧Z^r) ≅ Λ²(Z^r/S) via Λ²π, with π surjective. So the question is whether c̄ is a sum of t integral decomposables in Λ²Z^{r−q}. Rank is subadditive, which gives ⇒. For ⇐, the Frobenius normal form c̄ = Σ_{j≤s} γ_j f_{2j−1}∧f_{2j} with s ≤ t writes c̄ as s integral decomposables. ∎

Examples covered: all orientable quadratic equations ∏_{l≤t}[X_l,Y_l]·∏_j W_j^{-1}κ_jW_j = g with span(κ̄_j) saturated. Use W^{-1}κW = κ[κ,W]; the equation is solvable iff ḡ = Σκ̄_j and rank(c̄) ≤ 2t. In particular, g is a product of t commutators iff g is central of rank ≤ 2t, so the commutator width of N_{2,r} is ⌊r/2⌋. This is classical: Kh. S. Allambergenov and V. A. Roman'kov, *Products of commutators in groups*, Dokl. Akad. Nauk UzSSR 1984, no. 4, 14–15. We know this reference second-hand, from the reference list of a Glasgow Math. J. paper (doi:10.1017/S0017089500032407). See also V. A. Roman'kov, Sibirsk. Mat. Zh. 57(4) (2016) 866–888, which computes the commutator width of free nilpotent groups of finite rank.

**(c) Nondegenerate stratum.** Suppose S is saturated, put n = r − q, and project as in (b). This uses that π maps α + FZ^r onto π(α) + FZ^n. Suppose further that rank(c̄) = 2t (any rank > 2t is impossible). Then the instance is decidable.

*Proof.* Let β = Σ_l m_l f_l∧g_l ∈ Λ²Q^{2t}; it is nondegenerate. A tuple (u_l, v_l) is the same thing as a map φ : Z^{2t} → Z^n with φ(f_l) = u_l and φ(g_l) = v_l. The equation reads Λ²φ(β) = c̄. Let X ⊂ Hom(Q^{2t}, Q^n) be the closed subvariety Λ²φ(β) = c̄, and let P be the support plane of c̄, which has dimension 2t.

Since Λ²φ(β) ∈ Λ²(im φ), we get P ⊆ im φ, and dim im φ ≤ 2t forces φ : Q^{2t} → P to be an isomorphism carrying β to c̄. Nondegenerate bivectors of equal rank are equivalent over Q, so X(Q) ≠ ∅. Fixing φ_0 ∈ X(Q), the map g ↦ φ_0∘g gives X ≅ Sp(β) ≅ Sp_{2t}.

Let O_p = {φ ∈ X(Q_p) : φ(Z_p^{2t}) ⊆ Z_p^n, φ(f_l) ≡ α_l and φ(g_l) ≡ β_l mod F_l}. Each O_p is open in X(Q_p). For p ∤ F·∏m_l·∏γ_j (the γ_j being the invariant factors of c̄), O_p = X(Z_p) ≠ ∅: both β and c̄ restricted to Λ_P ⊗ Z_p are unimodular, where Λ_P = P∩Z^n is a direct summand, and unimodular alternating forms over Z_p have symplectic bases. For almost all p, φ_0 identifies X(Z_p) with φ_0·Sp(β)(Z_p).

Sp_{2t} is simply connected, and Sp_{2t}(R) is noncompact. By strong approximation (Platonov–Rapinchuk, Thm 7.12), X(Q) is dense in X(A_f). So an integral solution with the congruences exists iff O_p ≠ ∅ for each of the finitely many bad primes p. Each such condition is an existential sentence over Q_p with integer parameters (Z_p is definable in Q_p). It is therefore decidable, by Ax–Kochen / Ershov. ∎

Translated back to equations: (c) decides every single equation whose reduction (2) has S saturated and whose target has rank exactly 2t.

---

## 7. The degenerate and unsaturated cases: full decidability

### 7.1 Removing S (saturated or not)

Take a CSR_r instance (m_l, F_l, α_l, β_l, S, c). By Smith normal form, choose a basis e_1..e_r of Z^r with S = ⊕_{a≤q} f_a Z e_a, where f_a ≥ 1 and f_a | f_{a+1}. Put 𝔄 = span(e_1..e_q), 𝔅 = span(e_{q+1}..e_r), and F_S = f_q (F_S = 1 if q = 0). Then

  Λ²Z^r = Λ²𝔄 ⊕ (𝔄⊗𝔅) ⊕ Λ²𝔅,

and L := S∧Z^r satisfies two inclusions:

* L ⊆ Λ²𝔄 ⊕ 𝔄⊗𝔅, because s∧w with s ∈ 𝔄 has no Λ²𝔅-component;
* L ⊇ F_S·(Λ²𝔄 ⊕ 𝔄⊗𝔅), because F_S e_a∧e_b = (F_S/f_a)·f_a e_a∧e_b.

Write u = u^𝔄 + u^𝔅. The condition Σ m_l u_l∧v_l − c ∈ L therefore splits into two parts:

* (i) Σ m_l u_l^𝔅∧v_l^𝔅 = c_{𝔅𝔅} exactly, in Λ²𝔅.
* (ii) The (Λ²𝔄 ⊕ 𝔄⊗𝔅)-component of Σ m_l u_l∧v_l − c lies in L. This component is an integer bilinear expression, and L contains F_S times the whole summand, so (ii) depends only on (u_l, v_l) mod F_S.

Let M = lcm(F_S, F_1..F_t). Enumerate the finitely many residue tuples (u_l, v_l) mod M that are compatible with the congruences mod F_l and satisfy (ii); deciding (ii) for a residue tuple is a membership test in an explicit subgroup. The 𝔄-coordinates are otherwise unconstrained. So the instance is a finite disjunction of instances of the following problem on 𝔅 ≅ Z^n, with n = r − q.

**CSR⁰.** Given β = Σ_{l≤t} m_l f_l∧g_l ∈ Λ²Z^{2t} (all m_l ≥ 1), a modulus M, φ_0 ∈ Hom(Z^{2t}, Z^n) and c ∈ Λ²Z^n: does there exist φ ∈ Hom(Z^{2t}, Z^n) with φ ≡ φ_0 (mod M) and Λ²φ(β) = c?

(Here φ(f_l) = u_l and φ(g_l) = v_l.)

### 7.2 The rational solution set is a finite union of orbits

Let V = Q^{2t}, X_c = {φ ∈ Hom(V, Q^n) : Λ²φ(β) = c}, let 2s = rank c, and let P be the support plane of c (dim P = 2s). Choose a complement C of Λ_P := P∩Z^n in Z^n; it exists because Λ_P is a direct summand. Put d = n − 2s = dim C. Define

  H = Sp(β) × SL(C),  acting by (g,h)·φ = h∘φ∘g^{-1},

where SL(C) acts as the identity on P. This action preserves X_c, because Λ²g^{-1}β = β and Λ²h(c) = c (since c ∈ Λ²P).

Pass to duals. φ^* : (Q^n)^* → V^* is an isometry from the alternating form c(ξ,η) = ⟨ξ∧η, c⟩ to the form β on V^*, which is nondegenerate. The form c has radical R = P^⊥ = (Q^n/P)^*, and it is nondegenerate on A := C^⊥ ≅ P^*, with (Q^n)^* = A ⊕ R. Define the invariant k(φ) := dim φ^*(R).

**Lemma 7.1.** For each k with 0 ≤ k ≤ min(d, t−s), the set X_{c,k} = {φ ∈ X_c : k(φ) = k} is a single H(Q)-orbit, and it has an explicitly computable rational point y_k. For all other k it is empty.

*Proof.*

*Structure.* For ξ ∈ A and ρ, ρ' ∈ R we have β(φ^*ξ, φ^*ρ) = c(ξ,ρ) = 0 and β(φ^*ρ, φ^*ρ') = 0. Write ι := φ^*|_A. It is an isometric embedding of the nondegenerate space (A,c), so it is injective, and E := ι(A)^⊥ is nondegenerate of dimension 2t − 2s. The map ψ := φ^*|_R takes values in E and has totally isotropic image. Hence k ≤ min(d, t−s).

*Existence.* Map A isometrically onto the first s hyperbolic pairs of a symplectic basis of (V^*, β); over Q, nondegenerate alternating spaces of the same dimension are isometric. Then send k basis vectors of R to independent vectors of a Lagrangian of E, and the remaining basis vectors of R to 0. This gives y_k.

*Transitivity.* Let φ_1, φ_2 ∈ X_{c,k}.
1. By Witt's theorem, ι_2∘ι_1^{-1} extends to some g ∈ Sp(V^*,β) ≅ Sp(β). Replacing φ_1^* by gφ_1^* we may assume ι_1 = ι_2.
2. Both ψ_i map R into the same E and have kernels of the same dimension d − k. Pick h ∈ SL(R) with h(ker ψ_2) = ker ψ_1. SL is transitive on subspaces of each dimension: when 0 < dim < d, the stabiliser contains elements of every determinant, and the extreme dimensions are trivial. Here id_A ⊕ h is the transpose of an element of SL(C).
3. Now ψ_1h and ψ_2 have the same kernel, so τ(ψ_1hρ) := ψ_2ρ is a well-defined linear bijection between totally isotropic subspaces of E, and therefore an isometry.
4. By Witt's theorem in E, τ extends to σ ∈ Sp(E). Extend σ by the identity on ι_2(A) to σ̃ ∈ Sp(V^*).
5. Then σ̃∘φ_1^*∘(id_A ⊕ h) = φ_2^*. ∎

### 7.3 Strong approximation lemma

**Lemma 7.2.** Let H be a Q-group that is a product of groups Sp_{2a} and SL_b (simply connected, absolutely almost simple, and R-isotropic whenever nontrivial). Let H act on Q^N through a Q-representation ρ : H → GL_N. The representation need not be faithful: for H in §7.2, (−1,−1) acts trivially when s = 0 and n is even, so H is **not** asserted to be a subgroup of GL_N. Let y_0 ∈ Q^N, M ≥ 1 and a ∈ Z^N, and let B be the set of primes dividing M together with the primes at which y_0 is not integral. Then the following are equivalent:

* there exists γ ∈ H(Q) with γy_0 ∈ Z^N and γy_0 ≡ a (mod M);
* for every p ∈ B there exists η ∈ H(Q_p) with ηy_0 ∈ Z_p^N and ηy_0 ≡ a (mod M Z_p^N).

*Proof.* (⇒) is clear. For (⇐), for each p ∈ B the set V'_p = {η ∈ H(Q_p) : ρ(η)y_0 ∈ Z_p^N ∩ (a + M Z_p^N)} is open and nonempty. For p ∉ B put V_p = ρ^{-1}(GL_N(Z_p)), which is an open subgroup of H(Q_p). For η ∈ V_p we have ρ(η)y_0 ∈ Z_p^N, and the congruence condition is vacuous at p. Fix a Z-model of H. For almost all p, ρ is defined over Z_p, so V_p ⊇ H(Z_p), and therefore ∏_{p∈B} V'_p × ∏_{p∉B} V_p is open and nonempty in the restricted product H(A_f). By strong approximation for the abstract simply connected group H (Kneser–Platonov; Platonov–Rapinchuk, *Algebraic Groups and Number Theory*, Thm 7.12; it holds for each factor, hence for the product), H(Q) is dense in H(A_f). So some γ ∈ H(Q) lies in this set, and this γ works. ∎

*Remark (audit item 3).* The proof of Lemma 7.1 works verbatim over Q_p, so X_{c,k}(Q_p) is a single H(Q_p)-orbit. The local test is therefore intrinsic: it asks whether X_{c,k}(Q_p) contains a point of Z_p^N ∩ (a + M Z_p^N).

### 7.4 Main theorems

**Theorem 3.** CSR⁰ is decidable.

*Proof.* Every integral solution lies in X_c(Q) = ⊔_k H(Q)·y_k (Lemma 7.1). Apply Lemma 7.2 to each k, with N = 2tn, the linear action of H on Hom(V, Q^n), and congruence modulus M. For each of the finitely many computable primes p ∈ B_k, the local condition is an existential sentence over Q_p with rational parameters. Membership in H(Q_p) is polynomial, and Z_p is existentially definable in Q_p. So each local condition is decidable, because the theory of Q_p is decidable (Ax–Kochen; Ershov). The answer is "yes" iff some k ≤ min(d, t−s) passes all of its local tests. ∎

**Theorem 4.** CSR_r is decidable for every r, uniformly in r.

*Proof.* §7.1 reduces it to a finite disjunction of CSR⁰ instances, which Theorem 3 decides. ∎

**Theorem 5.** For every r ≥ 1, there is an algorithm, uniform in r, that decides whether a single equation w(X_1,…,X_k) = 1 with constants from the free nilpotent group N_{2,r} of class 2 and rank r has a solution.

*Proof.* Combine Theorem 1 (with Lemma 2.1 for nonzero exponent sums) and Theorem 4. ∎

For r = 2 this recovers Duchin–Liang–Shapiro's theorem for H(Z). For r ≥ 3 it answers, for free class-2 groups, the subclass that DLS §2 left open (commutator of rank d > 1). Their prediction that it "a priori could be decidable" is confirmed. Roman'kov's class-2 groups with an undecidable `[x,y]=g` show that some special feature of the free group is necessary. Here that feature is the universality of the commutator form x∧y: its fibres X_c are finite unions of orbits of the simply connected group Sp(β) × SL(C). A non-universal form ω, such as the one in our G_D, gives fibres that are not homogeneous, and there the frame trick encodes H10.

### 7.5 Sanity checks

* **The 2-adic example of §5 type.** Take n = 2, t = 1, β = f∧g, c = 0, M = 4, φ(f) ≡ (2,0) and φ(g) ≡ (0,2). Then s = 0 and d = 2, with strata k = 0 (φ = 0, which fails the congruence) and k = 1 (rank-1 φ). The local test at 2 fails: λx_1 ≡ 2, λx_2 ≡ 0, μx_1 ≡ 0, μx_2 ≡ 2 (mod 4) has no 2-adic solution. This matches the direct argument.
* **Nondegenerate case.** s = t forces k = 0, recovering Theorem 2(c).
* **Congruence-free saturated case.** Theorem 2(b) is consistent: every k is locally unobstructed, and solvability reduces to s ≤ t.

### 7.6 Verification status and gaps (update)

* **Checked by hand:** §7.1 splitting; Lemma 7.1 (Witt-theorem steps, SL transitivity, range of k); Lemma 7.2.
* **External inputs:** strong approximation for Sp and SL over Q (standard); Witt's extension theorem for alternating forms (standard); decidability of Th(Q_p) and existential definability of Z_p (standard).
* **Points a referee should check:**
  1. That every solution of the original equation lies in some X_{c,k}(Q) and that integrality is exactly entrywise integrality of φ. Both hold by construction.
  2. That the reduction in Theorem 1 (Lemmas 2.1–2.3 and the completion identity) loses no solutions.
  3. That the Frobenius normal form of an alternating integer matrix is correctly invoked.
* **Not formalized.** The algorithm is non-primitive-recursive in practice, because of the generic Q_p decision procedure. An explicit Hensel-type local test would make it practical, since H is smooth and the local orbit sets are open.
* **Novelty:** we found no prior statement of Theorem 5 (searched 2026-11-22). Confidence: medium-high. The argument is short and uses standard tools, but it has not been independently checked; an independent read of Lemma 7.1 and of the reduction in §§2–3 is recommended before any claim is made.
