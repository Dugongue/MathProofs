# Domination in dimension four and a six-dimensional sufficient criterion

This report proves the specified dimension-four and six-dimensional cases and states the scope of the residual arithmetic problem.

## 0. Conventions

- DOM(N), HTP(Q), QHOM and PQUAD are as in r2 §0 and r4 §0. Inputs are triangulations, under the promise that they are closed simply connected manifolds.
- For a closed simply connected 6-manifold X, write H_X = H²(X;Q), μ_X for the cup cubic, and T_X for its symmetric trilinear form, so μ(v) = T(v,v,v).
- By Poincaré duality, H⁴ ≅ H_X^*, and the product vw ∈ H⁴ is the covector T(v,w,·).
- Further notation: Z_X = {v : v² = 0} and K_X = ker(Sym²H_X → H⁴).
- **6-dimensional criterion** (r4 §4, audited). M dominates N iff:
  - b₃(M) ≥ b₃(N), and
  - there are λ ∈ Q^× and an injective linear g: H_N → H_M with g^*μ_M = λμ_N and T_M(g(s),·) = 0 for all s ∈ K_N.

  This uses Miller formality and Theorem B.
- **Wall realisation** (r2 §4.2, inherited). Every integral cubic whose monomial coefficients are divisible by 12, together with any even b₃, is realised by a closed, simply connected, smooth, spin 6-manifold with torsion-free homology. A triangulation is found by certified enumeration (r2 §4.3).
- Multiplying μ_M by a nonzero constant changes none of the conditions below.

---

## 1. Dimension 4: complete proof

Let M and L be closed, oriented, simply connected 4-manifolds. Let A and B be their intersection matrices on H²(−;Z), of ranks m and n. Both are unimodular, so d_A := det A and d_B := det B are ±1. Write q_A and q_B for the associated rational quadratic forms.

**Theorem 4D.**

(a) M dominates L ⟺ there are κ ∈ Q^× and a rational m×n matrix P with PᵀAP = κB. Equivalently, κq_B is a subform of q_A over Q (an orthogonal summand, by Witt).

(b) In (a) one may take κ ∈ Κ₀ = {±1, ±2, ±3, ±5, ±6, ±7, ±10, ±14}.

(c) For each fixed κ the subform test is decidable. Hence DOM in dimension 4 is decidable, uniformly in (M, L).

### 1.1 Proof of (a)

**(⇒)** Let f have degree k ≠ 0, and let P be the matrix of f^* on H². Then

  ⟨f^*x ∪ f^*y, [M]⟩ = ⟨xy, f_*[M]⟩ = k⟨xy, [L]⟩,

so PᵀAP = kB.

**(⇐), step 1: integrality.** Given rational P and κ, put P′ = cP with c ∈ Z_{>0} clearing denominators. Then P′ᵀAP′ = c²κB =: kB. The left side is integral. Since B is unimodular, kI = (kB)B^{−1} is integral, so k ∈ Z∖0.

**(⇐), step 2: cell structures.**
- M° := M ∖ int D⁴ is simply connected with free H₂ and H₃ = H₄ = 0. By Hurewicz and Whitehead, M° ≃ ∨_{i=1}^m S², so M ≃ (∨_m S²) ∪_{φ_M} e⁴.
- Likewise L ≃ (∨_n S²) ∪_{φ_L} e⁴. For n = 0, L is a homotopy 4-sphere and the collapse map has degree 1.

**(⇐), step 3: the Hopf matrix.** For φ ∈ π₃(∨_n S²), let H(φ) ∈ Sym_n(Z) be the cup-product matrix of the cofibre (∨_n S²) ∪_φ e⁴, taken in the basis dual to the spheres.
- By Hilton's theorem, π₃(∨_n S²) is free abelian on the Hopf maps η_j and the Whitehead products [ι_a, ι_b] (a < b).
- H(η_j) = E_jj, because CP² has x² = 1.
- H([ι_a, ι_b]) = E_ab + E_ba, by the cell structure of S²×S².
- H is additive.

So H: π₃(∨_n S²) → Sym_n(Z) is an isomorphism. This is classical: J.H.C. Whitehead 1949, Milnor 1958. It is cited from memory.

**(⇐), step 4: the map on the 3-skeleton.** Let f₀: ∨_m S² → ∨_n S² induce Pᵀ on H₂ (any integer matrix is realised by a map of wedges of 2-spheres). Then f₀ extends to the cofibre map

  M → C′ := (∨_n S²) ∪_{f₀∘φ_M} e⁴,

which has degree 1 on the top cell. By naturality of cup products, H(f₀∘φ_M) = PᵀAP = kB = H(kφ_L). By step 3, f₀∘φ_M = kφ_L in π₃(∨_n S²).

**(⇐), step 5: extension and degree.**
- kφ_L is null-homotopic in L, because φ_L bounds the top cell. So f₀ extends to f: M → L.
- Pick a, b with B_ab ≠ 0. Then f^*(y_a y_b) = (PᵀAP)_ab [M]^* = kB_ab [M]^*, while y_a y_b = B_ab [L]^*.
- Hence deg f = k ≠ 0. ∎

This re-proves the direction of Duan–Wang (arXiv math/0402119, 4-dimensional theorem) that is needed. I checked only its abstract: L simply connected, M closed orientable, criterion stated in terms of intersection forms. The proof above does not depend on that paper.

### 1.2 Local invariants (tools; Serre, *A Course in Arithmetic*, Ch. IV, cited from memory)

For a nondegenerate rational form q = ⟨a_1,…,a_r⟩, let d(q) = Πa_i (mod squares) and ε_v(q) = Π_{i<j}(a_i,a_j)_v. Then:

- **HM.** Two forms are isometric iff they have the same rank, d, all ε_v, and signature (Serre IV, Thm 9).
- **Ex.** (Serre IV, Prop. 7.) There is a rational form with data (r, δ, (ε_v), (r₊, r₋)) iff:
  - ε_v = 1 for almost all v, and Π_v ε_v = 1;
  - ε_v = 1 whenever r = 1, or r = 2 and δ ≡ −1 in Q_v^×/Q_v^{×2};
  - signature compatibility at ∞: δ_∞ = (−1)^{r₋} and ε_∞ = (−1)^{r₋(r₋−1)/2}.
- **Formulas.**
  - ε(q ⊥ q′) = ε(q)ε(q′)(d(q), d(q′)).
  - ε(κq) = ε(q)(κ,−1)^{r(r−1)/2}(κ, d(q))^{r−1}. (Expand Π_{i<j}(κa_i, κa_j).)
- **Unimodular forms.** For a unimodular integral form and an odd prime p, ε_p = 1, because the form diagonalises over Z_p with unit entries.

### 1.3 The subform test for fixed κ

Let κ be squarefree and d := m − n ≥ 0 (d < 0 is impossible by Fact 0.1). A subform κq_B ⊂ q_A exists iff there is a form q′ of rank d with q_A ≅ κq_B ⊥ q′. By HM, the invariants of q′ are forced:

- δ′ = d_A d_B κ^n;
- signature (p_A − p_κ, n_A − n_κ), where (p_κ, n_κ) is the signature of κq_B;
- ρ_v := ε_v(q′) = ε_v(q_A) ε_v(κq_B) (d(κq_B), δ′)_v.

By Ex, such a q′ exists iff the following hold.

1. **Signature.** Both entries of the signature are ≥ 0. This depends only on sign(κ). The conditions at ∞ in Ex then hold automatically: they hold for real forms with these signatures.
2. **Global product.** Π_v ρ_v = 1 always holds, by Hilbert reciprocity and the product formula for q_A and κq_B. Also ρ_v = 1 for almost all v.
3. **Local conditions when d ≤ 2.**
   - **Odd p ∤ κ.** Every entry is a p-adic unit and ε_p(q_A) = ε_p(q_B) = 1, so ρ_p = 1.
   - **Odd p | κ.** Then (κ,u)_p = (u/p) for units u. Using the formulas of 1.2:

     ρ_p = (−1/p)^{n(n−1)/2} (d_B/p)^{n−1} · [(−d_A/p) if n is odd].

     Since d_A, d_B = ±1, this is (−1/p)^e for a fixed exponent e = e(n, d_A, d_B) ∈ {0, 1}.
   - **p = 2.** ρ₂ depends only on the class of κ in Q₂^×/Q₂^{×2}, together with the fixed numbers ε₂(q_A), ε₂(q_B), d_A and d_B.

   The local conditions (ρ_v = 1 where Ex requires it) are:
   - **d ≥ 3:** none. The test is the signature alone.
   - **d = 1:** ρ_v = 1 at every finite v. At odd p | κ this reads (−1/p)^e = 1.
   - **d = 2:** ρ_v = 1 where δ′ ≡ −1 mod squares.
     - If n is odd, δ′ has odd valuation at every odd p | κ, so the condition can only bite at p = 2.
     - If n is even, δ′ = d_A d_B is constant, and at odd p | κ the condition is (−1/p)^e = 1 or vacuous.
   - **d = 0:** q_A ≅ κq_B. This needs:
     - d_A ≡ d_B κ^n; for n odd this forces κ = ±1;
     - equal ε₂;
     - (−1/p)^{e₀} = 1 at odd p | κ;
     - equal signatures.

All quantities are Hilbert symbols of explicit integers at 2, at the odd primes dividing κ, and at ∞. ε₂(q_A) comes from a rational Gram–Schmidt diagonalisation of A. So (c) holds.

### 1.4 Proof of (b)

By 1.3, whether κ passes depends only on three things:
- (i) sign κ;
- (ii) the class of κ in Q₂^×/Q₂^{×2}, which for squarefree κ is fixed by v₂(κ) and sign·(odd part) mod 8;
- (iii) when the odd-prime condition bites (exponent e* = 1), whether every odd prime factor of κ is ≡ 1 mod 4.

Suppose κ passes.
- **e* = 1.** Every odd prime factor of κ is ≡ 1 mod 4, so the odd part of κ is ≡ 1 mod 4. Choose κ′ ∈ {±1, ±2, ±5, ±10} with the same sign, the same v₂, and the same odd part mod 8 (1 or 5). The only odd prime that can divide κ′ is 5, which is ≡ 1 mod 4, so κ′ passes.
- **e* = 0 or the condition is vacuous.** Κ₀ contains a representative of every pair (sign, 2-adic class):
  - the positives 1, 3, 5, 7, 2, 6, 10, 14;
  - the negatives −7, −5, −3, −1 (≡ 1, 3, 5, 7 mod 8) and −14, −10, −6, −2.

  The representative with the same data as κ passes.
- **d = 0, n odd.** Here κ = ±1 ∈ Κ₀. ∎

**Checks.**
- \bar{CP²} → CP²: κ = −1, degree −1.
- CP² # \bar{CP²} → S²×S²: d = 0 and ⟨1,−1⟩ ≅ H, realised by k = 2 with u = (1,1), v = (1,−1).
- CP² # CP² ↛ S²×S²: definite versus indefinite, so the signature test fails for every κ.

**Corollary 4D′.** For every simply connected 4-manifold target, DOM is decidable. Together with r4 Proposition 3.2 (dimension ≤ 3, and dimension 5 via b₂(M) ≥ b₂(N)), every simply connected target of dimension ≤ 5 has a decidable DOM.

---

## 2. Representing values by cubic forms (task item 1)

Let R1(C) be the question: given an integral cubic form C in n variables, is there x ∈ Q^n with C(x) = 1? Equivalently, does C represent a nonzero cube?

- **R1 ≤_m HTP(Q)** trivially, so R1 is c.e.
- **n = 2.** R1(C) ⟺ the plane cubic X_C: u³ = C(s,t) has a rational point with u ≠ 0. If disc C ≠ 0, X_C is smooth of genus one. It carries the automorphism u ↦ ωu, so its Jacobian has j = 0. If C has no rational root, the condition is just X_C(Q) ≠ ∅.
  - Line sections give a rational 0-cycle of degree 3, so X_C has period dividing 3. If it is everywhere locally soluble, its class lies in Sha(Jac X_C)[3].
  - Local solubility is checkable. At a prime p ∤ 3·disc C, Hasse–Weil gives an F_p-point with u ≠ 0 when C mod p has no root, and that point lifts.
  - **Assuming Sha[3^∞] is finite**, R1 for binary forms is decidable: enumerate points, and in parallel run 3^k-descents. This is standard and cited from memory. No unconditional algorithm is known.
- **n = 3.** R1(C) is about rational points with u ≠ 0 on the cubic surface u³ = C(s,t,w). The surface is smooth iff C = 0 is a smooth plane cubic.
  - Decidability would follow if the Brauer–Manin obstruction is the only one for cubic surfaces (the Colliot-Thélène–Sansuc conjecture), with Kresch–Tschinkel effectivity. Unconditionally it is open. Cited from memory.
- **Smooth C, n ≥ 9.** Then u³ − C is a nonsingular cubic form in ≥ 10 variables, so it has a nontrivial zero (Heath-Brown, Proc. LMS 1983, from memory). The hypersurface is smooth of dimension ≥ 8 with a rational point, hence unirational (Kollár, J. Inst. Math. Jussieu 2002, from memory). So rational points are Zariski dense, some have u ≠ 0, and R1(C) holds. Smooth R1 is therefore trivial in ≥ 9 variables. The difficulty sits in bounded dimension and in singular forms.
- **Hardness of R1.** HTP(Q) ≤ R1 is not known. Two standard routes fail:
  - Compressing a system into a single equation over Q uses Σ P_i² and needs degree 4.
  - Anisotropic cubic forms over Q exist only in ≤ 9 variables (every cubic form over Q_p in ≥ 10 variables is isotropic; Lewis, from memory), so they cannot merge many equations.
  - Separately, a cubic form that is linear in some variable with a nonzero coefficient form represents every value. So the hard instances of R1 must be "nowhere linear".

  I make no claim either way.

---

## 3. Six-dimensional targets with Z_N = 0 and b₂(N) ≥ 2

### 3.1 Structure of the binary case (b₂(N) = 2)

- A binary cubic μ_N has Z_N ≠ 0 iff it has a repeated rational linear factor, or vanishes. So Z_N = 0 ⟺ disc μ_N ≠ 0.
- K_N is spanned by one element s₀ ∈ Sym²H_N, the apolar quadric. It is rational-split iff −3·disc μ_N ∈ Q^{×2}.
- **Split type.** μ_N ≅ αs³ + βt³, with r := β/α ∈ Q^×/Q^{×3}. CP³#CP³ ≅_Q CP³ # \bar{CP³} is r = 1. M dominates N iff there are a, b ∈ H_M with ab = 0 and μ(b)/μ(a) ∈ rQ^{×3} ∪ r²Q^{×3}. Injectivity is automatic: if b = ca, then ab = ca² ≠ 0, because a³ ≠ 0.
- **Non-split type.** μ_N(z) = Tr_{K/Q}(αz³) on H_N ≅ K = Q(√δ). M dominates N iff there is a ∈ H_M⊗K with a·ā = 0 and μ(a) ∈ αQ^× (up to the λ-scaling).
- **Sources with b₂(M) = 2.** Here M dominates N iff μ_M is similar to μ_N over Q. The K-condition is automatic, because the apolar quadric is covariant. This is decidable for binary cubics (compare root fields and the cube class).

**Lemma 3.1 (difference reformulation, r = 1).** M dominates CP³#CP³ (with b₃(M) ≥ b₃(N), as always) iff there are u, v ∈ H_M with u² = v² in H⁴(M), μ(u) ≠ 0 and μ(v) = 0.

*Proof.*
- **(⇒)** Rescale b so that μ(a) = μ(b). Put u = a + b and v = a − b. Then u² − v² = 4ab = 0. Expanding μ(a ± b) with T(a,b,·) = 0 gives μ(u) = 2μ(a) ≠ 0 and μ(v) = μ(a) − μ(b) = 0.
- **(⇐)** From u² = v², T(u,u,w) = T(v,v,w) for all w. So T(u,u,v) = μ(v) = 0 and T(u,v,v) = μ(u). Put a, b = (u ± v)/2. Then ab = (u² − v²)/4 = 0, and μ(a) = μ(b) = (μ(u) + 3μ(u))/8 = μ(u)/2 ≠ 0. ∎

So the question is whether the squaring map H² → H⁴, which is the quadratic map ∇μ/3, has a fibre that meets the cubic hypersurface {μ = 0} and also its complement.

### 3.2 The no-zero-divisor property

**Definition.** An integral cubic form C, with trilinear form T_C, has property (Z0) if T_C(v,w,·) = 0 implies v = 0 or w = 0, for all rational v and w.

Since T_C(v,·,·) = Hess C(v)/6, a sufficient condition is that det Hess C(v) ≠ 0 for every rational v ≠ 0, i.e. the Hessian form is anisotropic over Q.

**Lemma 3.2 (binary).** Write C = as³ + 3bs²t + 3cst² + dt³. Then

  det Hess C(v)/36 = H_C(v) := (ac − b²)s² + (ad − bc)st + (bd − c²)t²,

with discriminant D′ = a²d² − 6abcd + 4ac³ + 4b³d − 3b²c², and disc C = −27D′. Hence C has (Z0) iff D′ ∉ Q² (D′ = 0 included in "square"). Equivalently, −3·disc C ∉ Q^{×2}. In that case disc C ≠ 0, so X_C is smooth.

*Proof.*
- C_ss = 6(as + bt), C_tt = 6(cs + dt), C_st = 6(bs + ct). Expanding (as + bt)(cs + dt) − (bs + ct)² gives H_C.
- The discriminant of H_C is (ad − bc)² − 4(ac − b²)(bd − c²) = D′.
- The identity disc C = −27D′ is the standard discriminant of a binary cubic written with binomial coefficients.
- A binary quadratic form has no nontrivial rational zero iff its discriminant is a nonzero non-square. ∎

**Lemma 3.3 (any n; a decidable p-adically open family).**
- **The seed form.** Let F/Q have degree n, let p be inert in F, and let α ∈ F^×. Put C₀(z) := Tr_{F/Q}(αz³). Its Hessian at z is the bilinear form (x,y) ↦ 6Tr(αzxy). This is a nondegenerate twisted trace form whenever z ≠ 0 in the field F⊗Q_p. So det Hess C₀ is anisotropic over Q_p.
- **The open set.** U_p := {C : det Hess C has no nontrivial Q_p-zero}. It is nonempty (it contains C₀) and open in the p-adic topology on coefficients: anisotropy is a positive minimum on the compact unit sphere, and that minimum varies continuously.
- **Decidability.** Membership in U_p is decidable by Hensel's lemma and a finite congruence check.
- Every C ∈ U_p has (Z0). ∎

For n = 2, Lemma 3.2 is sharper: it characterises (Z0) completely.

### 3.3 Theorem L (lower bound for diagonalisable targets)

**Setting.** Let N be a closed simply connected 6-manifold with μ_N ≅_Q Σ_{i=1}^k r_i x_i³, where k = b₂(N) ≥ 2 and r_i ∈ Z∖0 (after scaling by a common constant and by cubes). Then:
- Z_N = 0, since ∇μ_N = (3r_i c_i²) vanishes only at c = 0;
- K_N = span{x_i x_j : i < j} (dimension count: the x_i² are independent).

Define the finite set of cube classes

  S_N := { λ r_{i₀} mod Q^{×3} : i₀ ∈ [k], τ: [k]∖{i₀} → [k−1] a bijection, λ ∈ Q^× with r_{τ(i)}/r_i ∈ λQ^{×3} for all i ≠ i₀ }.

S_N is computable from (r_i) and contains r_k (take τ = id and λ = 1).

**Theorem L.** For an integral cubic form C with (Z0), in any number of variables, let M_C be the Wall manifold of 12·(Σ_{i<k} r_i x_i³ + C(v)), with b₃(M_C) = b₃(N). Then M_C dominates N iff C represents an element of some class in S_N.

Consequently REP_{S_N}, restricted to (Z0)-forms, many-one reduces to DOM(N). Here REP_{S}(C) asks: ∃v, ∃c ∈ S with C(v) ∈ cQ^{×3}.

*Proof.*

1. **Criterion.** By §0, M_C dominates N iff there are a_1,…,a_k ∈ H_M and λ ≠ 0 with:
   - a_i a_j = 0 for i ≠ j, and
   - μ_M(Σc_i a_i) = λΣ r_i c_i³.

   Given pairwise zero products, every mixed term T(a_i,a_j,·) vanishes. So the second condition is exactly μ_M(a_i) = λr_i for each i. Injectivity is automatic: multiplying Σc_i a_i = 0 by a_j gives c_j a_j² = 0, and a_j² ≠ 0 since μ(a_j) ≠ 0.
2. **Slots.** Write elements of H_M = Q^{k−1} ⊕ H_C as (s, v). The cubic is block-diagonal: T_M = ⊕ r_j(x_j*)³ ⊕ T_C. So (s,v)·(s′,v′) = 0 iff s_j s′_j = 0 for every j and T_C(v,v′,·) = 0. By (Z0), the second condition means v = 0 or v′ = 0. Hence pairwise zero products mean pairwise disjoint supports among the k slots {x_1,…,x_{k−1}, H_C}.
3. **Each element fills one slot.** There are k nonzero elements and k slots, so each a_i occupies exactly one slot. Then:
   - a_i = s_i x_{τ(i)} with r_{τ(i)} s_i³ = λr_i, for i ≠ i₀;
   - a_{i₀} = v with C(v) = λr_{i₀}.

   This is precisely the condition "C represents a class in S_N".
4. **Converse.** Given such data, define g by these a_i. The K-condition holds by disjointness of supports, and b₃ matches. The criterion and Theorem B then give a map of nonzero degree.
5. **Effectivity.** C ↦ M_C is computable (Wall realisation and certified enumeration, inherited from r2). ∎

**Corollary L1.**
- (a) For N = kCP³ # m(S³×S³) with k ≥ 2, S_N = {1}. So R1 restricted to (Z0)-forms reduces to DOM(N).
- (b) **Binary instances.** If DOM(CP³#CP³) were decidable, there would be an algorithm deciding, for binary integral C with D′(C) ∉ Q², whether the genus-one curve u³ = C(s,t) has a rational point with u ≠ 0. For C irreducible, this is "whether X_C(Q) ≠ ∅".
- (c) **Ternary instances.** The same would decide rational points (with u ≠ 0) on the cubic surfaces u³ = C(s,t,w) for every C ∈ U_p (Lemma 3.3, n = 3).
- (d) **General diagonal targets.** For general r_i, the same holds with "represents 1" replaced by "represents a class in S_N". For example, μ_N = x³ + 2y³ gives S_N = {2, 4}.

**Remarks.**
- Diagonal binary C, i.e. Selmer-type curves ax³ + by³ + cz³, are exactly the excluded case D′ ∈ Q². For those, W(C) contains its own orthogonal pair, and the reduction breaks.
- The family in (b) consists of the j = 0 cyclic plane cubics whose Hessian covariant is anisotropic.
- Local solubility is decidable (§2), so the content of (b) is global, and lives in Sha[3]. I computed no explicit counterexample to the Hasse principle in the family (no computation, per the workspace rules). That such counterexamples exist is heuristic.

### 3.4 Upper bound and position

- DOM(N) ≤_m HTP(Q) for every 6-dimensional N, by Theorem B and Miller formality.
- So for diagonalisable N with Z_N = 0 and k ≥ 2:

  REP_{S_N}(Z0-cubics) ≤_m DOM(N) ≤_m HTP(Q).

- The left end already contains the binary genus-one problem, whose decidability is unknown unconditionally and follows from finiteness of Sha[3^∞].
- Non-diagonalisable targets in this class have only the upper bound. Examples:
  - irreducible binary μ_N with non-split apolar quadric;
  - smooth non-diagonal ternary μ_N.
- A Weil-restriction analogue of Theorem L should give, for the non-split binary case, rational points on genus-one curves over K = Q(√δ). That is not written out (gap 3).

### 3.5 Why HTP(Q)-hardness is not proved (ammunition)

- **Why 6H does not transfer.** The Theorem 6H mechanism needs a class entering μ_N linearly, which is a square-zero class. Z_N = 0 excludes this.
- **Fixed partners give only R1.** In the pair criterion, fixing either partner makes the other range over the linear space Ann(a) = ker Hess(a). Every reduction with a rigid partner therefore lands in R1-type problems (§2), as in Theorem L.
- **The approach that should work.** Hardness needs both partners to vary. The natural device is an inhomogeneous bilinear system between blocks A and B, indexed by a third block C, i.e. a trilinear term αβγ, with T(x,y,·) = ε to break the trivial pair. Inhomogeneous bilinear systems are HTP(Q)-hard by themselves:
  - α₀β₀ = −1;
  - α_iβ_j − α_jβ_i = 0, which forces β ∝ α;
  - α^T Q_k β = 0, which gives q_k(α) = 0 with α₀ ≠ 0, i.e. QHOM.

  The intended pairs (x + α, y + β) work.
- **The obstacle: spurious pairs inside A ⊕ B ⊕ C.** The trilinear block has its own nonzero cubes 6Θ(α,β,γ). For a direct-sum Θ, explicit spurious pairs exist (the (S²)³ # (S²)³ pattern). A proof needs a Θ with no such pairs, or a proof that they occur only when q is solvable.
- **Status.** I have neither. The conjecture "DOM(N) ≡ HTP(Q) for all Z_N = 0, b₂ ≥ 2" (r4 §5) stays open. Theorem L shows that the opposite conjecture (decidability) is at least as hard as an open problem about genus-one curves.

---

## 4. Classification theorem, dimension ≤ 6

**Theorem C.** Let N be a closed simply connected n-manifold, and consider DOM(N) on closed simply connected sources.

1. **n ≤ 3.** Always true, by collapse. Decidable.
2. **n = 4.** Decidable, uniformly in source and target (Theorem 4D). The test is: κq_N ⊂ q_M over Q for some κ ∈ Κ₀.
3. **n = 5.** Decidable: M dominates N ⟺ b₂(M) ≥ b₂(N) (r4 Prop. 3.2).
4. **n = 6.** Let Z_N = {y ∈ H²(N;Q) : y² = 0}.
   - (a) Z_N ≠ 0 ⟹ DOM(N) ≡_m HTP(Q) (r4 Theorem 6H, audited).
   - (b) Z_N = 0 and b₂(N) ≤ 1 ⟹ decidable (r4 Prop. 6D):
     - b₂ = 0: the criterion is b₃(M) ≥ b₃(N);
     - b₂ = 1: the criterion is μ_M ≢ 0 and b₃(M) ≥ b₃(N).
   - (c) Z_N = 0 and b₂(N) ≥ 2 ⟹ DOM(N) ≤_m HTP(Q). If μ_N is diagonalisable over Q, then also REP_{S_N}(Z0-cubics) ≤_m DOM(N). This includes:
     - rational points with u ≠ 0 on the genus-one curves u³ = C(s,t), D′(C) ∉ Q²;
     - rational points with u ≠ 0 on the cubic surfaces u³ = C(s,t,w), C ∈ U_p.

     The exact degree is open. Three outcomes are consistent with what is proved:
     - ≡ HTP(Q), as r4 conjectures;
     - strictly between;
     - decidable, which would require solving the genus-one problem above.

**What is ≡ HTP(Q):** exactly case 4(a) among targets of dimension ≤ 6, unless case 4(c) also is. Dimension 6 is the threshold, and this is now unconditional.

**What reduces to rational points on cubic hypersurfaces:**
- Into DOM(N): genus-one cyclic cubic curves and cyclic cubic surfaces, for diagonalisable 4(c).
- From DOM(N): only the general route DOM(N) ≤ HTP(Q). No reduction of DOM(CP³#CP³) to a bounded-dimensional cubic problem is known. Sources have unbounded b₂, and the pair condition is a genuine bilinear system.

---

## 5. Verified citations and sources

- **Checked this session.** Duan–Wang, *Non-zero degree maps between 2n-manifolds*, arXiv math/0402119: abstract only (4-dimensional result: M closed orientable, L simply connected, criterion via intersection forms). Theorem 4D(a)(⇐) is re-proved here independently.
- **Checked earlier and inherited.** Poonen, JEMS 11 (2009), Remark 1.2(c) (r4); Manin, PAMS 150 (2022) (r2/r3); Loughran–Smeets arXiv 1511.08027 (r3).
- **Cited from memory, not re-checked:**
  - Serre, *A Course in Arithmetic*, Ch. IV, Thm 9 and Prop. 7;
  - Hilton's theorem on π₃(∨S²);
  - J.H.C. Whitehead (1949) and Milnor (1958) on simply connected 4-complexes;
  - Heath-Brown, *Cubic forms in ten variables* (Proc. LMS 1983);
  - Kollár, *Unirationality of cubic hypersurfaces* (J. Inst. Math. Jussieu 2002);
  - Lewis on p-adic cubic forms in 10 variables;
  - Kresch–Tschinkel (effectivity of Brauer–Manin);
  - the Sha-conditional decidability of genus-one rational points;
  - Miller formality;
  - Wall's realisation conditions.
