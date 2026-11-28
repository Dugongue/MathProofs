# Domination of six-manifolds and rational tensor isomorphism

The rational TI decision input and the arithmetic hardness conclusions carry the dependencies stated below.

## 0. Conventions and inputs

- 𝓜₆: closed simply connected smooth 6-manifolds. For M ∈ 𝓜₆: V_M = H²(M;Q), μ_M the cup cubic on V_M, b₃(M). Miller: every M ∈ 𝓜₆ is formal. Herrmann 1409.8036 §2.2 (checked in lane4): the K-homotopy type (char K = 0) is (b₃, μ up to GL(V_K) × K^×).
- Encoding: Wall/Jupp systems (H, μ, w₂, p₁, b₃) as in lane4 T3/T4(c). With triangulation input every reduction below is still computable many-one (r2 §4.3 certified enumeration), but not polynomial-time.
- DOM(M,N): ∃ f: M → N with deg f ≠ 0.
- **[B] r3 Theorem B** (audited PASS with fixes; rests on Manin PAMS 2022 Lemmas 5.3–5.5 read via a summary, flagged): for N with positive weights (every formal N), M dominates N iff there is a CDGA map ΛV_N → ΛV_M nonzero on H^top. For formal M, N this is: ∃ graded Q-algebra map H*(N;Q) → H*(M;Q) nonzero on top degree (lift through the quasi-isomorphisms; minimal models are cofibrant).
- **[T4c] lane4 Theorem T4(c)** (audit PASS with fix): CFE over Q ≤_p RHE6, with outputs (Z^{n+m}, N·F⁺, 0, 0), (Z^{n+m}, N·G⁺, 0, 0), F⁺ = F₀ ⊕ t_L, L = Q(2^{1/m}), 3 ∤ m > n. Uses Lemma L (centroid) and L′ (cube marker).
- **[GQ]** Grochow–Qiao: cubic form equivalence and commutative unital algebra isomorphism are TI-complete over fields of char 0 (Thm A(4a), Cor. B; as checked in lane4).
- **[T5] lane4 Theorem T5** (audit PASS): M_E, M_{E′} with Wall systems (Z⁶, 6t_E, 0, 0), (Z⁶, 6t_{E′}, 0, 0) are Q_v-equivalent for all v and not Q-equivalent.

## 1. The equal-Betti lemma and DT1

**Lemma E.** Let f: M → N be a map of closed connected oriented n-manifolds with deg f = d ≠ 0. Then f*: H*(N;Q) → H*(M;Q) is injective. If b_k(M) = b_k(N) for some k, then f* is an isomorphism in degree k.

*Proof.* For x ≠ 0 in H^k(N;Q) choose y with ⟨xy,[N]⟩ ≠ 0 (Poincaré duality). Then ⟨f*x·f*y,[M]⟩ = d⟨xy,[N]⟩ ≠ 0, so f*x ≠ 0. Injective plus equal dimension gives isomorphism. ∎

**Lemma E6.** Let M, N ∈ 𝓜₆ with b₂(M) = b₂(N). Then M dominates N iff b₃(M) ≥ b₃(N) and μ_M∘g = λμ_N for some g ∈ GL(V_N → V_M) over Q and some λ ∈ Q^× (projective equivalence of the cup cubics).

*Proof.* (⇒) By Lemma E, f* is injective on H³ (so b₃(M) ≥ b₃(N)) and an isomorphism g on H². On H⁶, f* is multiplication by d. Then μ_M(gx,gy,gz) = ⟨f*(xyz),[M]⟩ = d·μ_N(x,y,z). Take λ = d.
(⇐) Build a graded algebra map φ: H*(N;Q) → H*(M;Q).
- H²: φ = g. H⁶: φ = λ (on fundamental classes).
- H⁴: Poincaré duality identifies H⁴ with V*; set φ on H⁴(N) to be the unique map with ⟨φ(u)·g(a),[M]⟩ = λ⟨u·a,[N]⟩ for all a ∈ V_N. Since g is an isomorphism this exists and is unique, and it makes φ(a)φ(b) = φ(ab) for a,b ∈ H²: both sides pair with g(c) to λμ_N(a,b,c), and g(V_N) = V_M.
- H³: H³ carries a nondegenerate alternating form (cup into H⁶). Choose a linear embedding h: H³(N) → H³(M) with ω_M(hx,hy) = λω_N(x,y); possible because b₃(M) ≥ b₃(N) and symplectic forms of each even rank are unique up to isomorphism (scale one half of a symplectic basis by λ).
- Products H²·H³ ⊂ H⁵ = 0 on both sides. All product identities hold, and φ is nonzero on top.
By [B] (both formal), M dominates N. ∎

**Theorem DT1.** Let DOM6⁼ be: given Wall systems of M, N ∈ 𝓜₆ with b₂(M) = b₂(N), decide whether M dominates N. Then DOM6⁼ ≡_p TI_Q.

*Proof.*
- *Hardness.* [T4c] outputs pairs with equal b₂ = n+m and b₃ = 0, and they are projectively equivalent iff F₀ ≅ G₀. By Lemma E6 (b₃ = 0 on both sides), M dominates M′ iff they are projectively equivalent. So CFE_Q ≤_p DOM6⁼, and CFE_Q is TI_Q-complete [GQ].
- *Membership.* By Lemma E6, decide b₃(M) ≥ b₃(N) (trivial) and projective equivalence of μ_M, μ_N.
  - Split radicals: μ = μ₀ ⊕ 0_R by linear algebra. Any g with μ_M∘g = λμ_N maps rad μ_N onto rad μ_M (if μ_N(u,·,·) = 0 then μ_M(gu, g·, g·) = λμ_N(u,·,·) = 0). So answer NO if radical dimensions differ; otherwise projective equivalence of μ_M, μ_N ⟺ projective equivalence of the nondegenerate parts.
  - For nondegenerate cubics, projective equivalence ⟺ isomorphism of the commutative unital algebras A_μ = Q ⊕ V ⊕ V* ⊕ Q (lane4 T4(c)(ii) membership argument: H²·H² = H⁴ by duality, so m^k = A^{≥2k} and ungraded isomorphisms are graded). Commutative algebra isomorphism ∈ TI_Q [GQ].
  ∎

**Decidability of the slice.** Šimková, arXiv 2512.21182 Thm D (unrefereed; via Sarkisyan 1980) decides rational homotopy equivalence of finite simply connected complexes; Sarkisyan's theorem also decides TI_Q directly (orbit equality for G(Q), G = GL³). Both inputs are flagged unverified in the KB (lane3/lane4 audits). Conditional on them, DOM6⁼ is decidable.

## 2. DT2: the whole problem

**DT2 (inherited).** DOM on all pairs in 𝓜₆ is ≡_m HTP(Q).
- Upper bound: the criterion of [B] for formal M, N is an existential statement over Q in the entries of φ, uniformly in (M, N) ("≠ 0 on top" via an inverse variable). This is r5 §0 criterion + r3 Thm B(2).
- Lower bound: the fixed target S²×S⁴ (r4 Thm 1, audited): DOM(M, S²×S⁴) ⟺ ∃ a ≠ 0 in V_M with a² = 0 ⟺ a rational singular point of μ_M, ≡ HTP(Q).
- With BB (user directive 11-24) this is Σ⁰₁-complete.

So DT1 + DT2: one Σ⁰₁-complete problem whose equal-b₂ slice is TI_Q-complete.

## 3. DT3: codimension stratification on the square-zero family

Let N_s = #_s(S²×S⁴) (b₂ = s, b₃ = 0, μ = 0, H*(N_s) has a_i·a_j = 0, a_i·b_j = δ_ij).

**Lemma S.** M ∈ 𝓜₆ dominates N_s iff V_M contains an s-dimensional subspace W with W·W = 0 in H⁴(M;Q), i.e. μ_M(W, W, V_M) = 0.

*Proof.* N_s is formal; apply [B]. An algebra map sends a_i ↦ α_i, b_i ↦ β_i with α_iα_j = 0 and α_iβ_j = dδ_ij[M]*, d ≠ 0; the second condition forces the α_i to be independent. Conversely, given independent α_i spanning a square-zero W, Poincaré duality gives β_i ∈ H⁴(M) with ⟨α_iβ_j,[M]⟩ = δ_ij; the remaining products (b_ib_j ∈ H⁸ = 0, H³ ↦ 0) impose nothing. ∎

**Theorem DT3.** Fix c ≥ 0 and let DOM_c be DOM(M, N_s) restricted to s = b₂(M) − c.
1. If DOM_c(M) holds, μ_M has concise dimension (dim V_M − dim rad μ_M) at most c(c+3)/2.
2. DOM_c many-one reduces, uniformly, to deciding rational points of systems of cubic equations in at most c²(c+3)/2 unknowns. DOM_0 (μ_M = 0) and DOM_1 are decidable in polynomial time.
3. With s = 1 (codimension b₂(M) − 1, unbounded), DOM(M, N_1) = DOM(M, S²×S⁴) ≡_m HTP(Q).

*Proof.*
1. Choose a complement K = ⟨k_1..k_c⟩ to W, coordinates v = w + Σ t_a k_a. Since μ(W,W,V) = 0: μ_M(v) = 3μ(w, k, k) + μ(k) = Σ_{a≤b} t_a t_b L_ab(w) + C(t) with L_ab linear. So μ_M is a cubic in the c + c(c+1)/2 linear forms t_a, L_ab, hence its concise dimension is ≤ c(c+3)/2.
2. Compute R = rad μ_M. If dim V/R > c(c+3)/2, answer NO. Otherwise, WLOG W ⊇ R: W + R is still square-zero (R·V = 0), and any s-dimensional subspace of a square-zero subspace is square-zero. So DOM_c(M) ⟺ the nondegenerate cubic μ̄ on V/R (dim n̄ ≤ c(c+3)/2) has a square-zero subspace of codimension c. Cover the Grassmannian by its finitely many standard charts (at most C(n̄, c)); in each chart the subspace has c(n̄ − c) ≤ c²(c+3)/2 affine coordinates, and "μ̄(W,W,V/R) = 0" is a system of polynomial equations of degree ≤ 3 in them.
   - c = 0: W = V, so the test is μ_M = 0.
   - c = 1: n̄ ≤ 2, μ̄ is a binary cubic (or zero, or unary), and the test is whether μ̄ has a repeated linear factor w (then μ̄(w,w,·) = 0) or is identically zero. A repeated root of a binary cubic over Q is automatically rational (its Galois conjugates would also be double roots, giving degree > 3). Decidable by gcd(μ̄, ∂μ̄).
3. r4 Thm 1 (audited). ∎

**Consequence.** Every HTP(Q)-hardness proof for domination into this family must use unbounded codimension b₂(M) − b₂(N), unless HTP(Q) with boundedly many unknowns in cubic systems is already undecidable. The latter is open (only 1 unknown is known decidable). The codimension-0 end of this family is trivial, whereas in DT1 the codimension-0 end is TI_Q. So TI-hardness at codimension 0 comes from targets with nondegenerate cup cubic, and arithmetic hardness comes from codimension.

## 4. DT4: codimension 1 with a nondegenerate target

**Lemma K (the splitting criterion; equivalent to the r5 §0 "K-condition").** Let M, N ∈ 𝓜₆ with rad μ_N = 0. Then M dominates N iff b₃(M) ≥ b₃(N) and there are an injective linear f: V_N → V_M, a complement K of W = f(V_N) and λ ∈ Q^× with μ_M∘f = λμ_N and μ_M(W, W, K) = 0.

*Proof.* (⇐) Define φ on H² by f, on H⁶ by λ, on H⁴(N) = V_N·V_N (duality, rad 0) by φ(ab) := f(a)f(b). Well defined: if Σ a_ib_i = 0 in H⁴(N), then Σ f(a_i)f(b_i) pairs to λΣμ_N(a_i,b_i,c) = 0 with f(c) ∈ W and to Σ μ_M(fa_i, fb_i, k) = 0 with k ∈ K; by duality it is 0. Products into H⁶ are multiplicative by μ_M∘f = λμ_N. H³ as in Lemma E6. Apply [B].
(⇒) f = φ|_{H²} is injective (Lemma E). Let K be the annihilator of φ(H⁴(N)) under the H²×H⁴ pairing on M; dim K = b₂(M) − b₂(N) because φ is injective on H⁴. Then μ_M(fa, fb, k) = ⟨φ(ab)k, [M]⟩ = 0. If f(x) ∈ K then ⟨φ(u)f(x)⟩ = λ⟨ux⟩ = 0 for all u ∈ H⁴(N), so x = 0; thus K ∩ W = 0. ∎

**Theorem DT4.** If b₂(M) = b₂(N) + 1, rad μ_N = 0 and b₃(M) ≥ b₃(N), then M dominates N iff μ_M is GL(V_M)-equivalent to

  Φ(x, t) = λμ_N(x) + 3t²ℓ(x) + ct³

for some λ ∈ Q^×, ℓ ∈ V_N*, c ∈ Q.

*Proof.* Write v = f(x) + tk with K = ⟨k⟩. Then μ_M(v) = λμ_N(x) + 3tμ_M(fx,fx,k) + 3t²μ_M(fx,k,k) + t³μ_M(k), and the middle term vanishes by Lemma K. Conversely, if μ_M∘h = Φ, take f = h|_{V_N×0}, k = h(e_t). ∎

So codim-1 domination is "the orbit of μ_M meets the (n+1)-parameter family Φ". It contains a TI_Q instance (ℓ = 0) but is a priori larger.

**Open reduction (isolated).** Put M = M_{F⁺} # CP³ (μ_M = F⁺ ⊕ s³) and N = M_{G⁺}. Write W ∩ V_{F⁺} = U (a hyperplane if W ≠ V_{F⁺}) and k = y₁ + βe. Lemma K forces F⁺(u, u′, y₁) = 0 for all u, u′ ∈ U, so the quadratic form F⁺(·,·,y₁) vanishes on a hyperplane and has rank ≤ 2. The t_L block has F⁺(·,·,z) of rank m ≥ 4 for z ≠ 0 (z is invertible in L), so y₁ ∈ V_{F₀}.
- **Proved:** if F₀ has no nonzero rational y with rank F₀(·,·,y) ≤ 2, then y₁ = 0, k = βe, the K-condition gives β·w_s·w′_s = 0, so W = V_{F⁺}. Then μ_M|_W = F⁺ ≅_proj G⁺, so F₀ ≅ G₀ by Lemma L′. Hence CFE_Q restricted to "Hessian rank ≥ 3 at every nonzero rational point" ≤_p codim-1 DOM6.
- **Missing:** TI_Q-hardness of CFE on that promise. For the trilinear embedding F_T of a concise 3-tensor T, rank F_T(·,·,y) ≥ 2·max rank of the nonzero slices of y's components (restrict to the complementary block). So "no rank-≤1 slice in any direction" would suffice for the F_T part. But GQ's TI → CFE route goes through commutative unital 3-nilpotent algebras and Agrawal–Saxena (1907.00309 Cor. 8.5(1), 8.6), whose gadget would also have to be controlled. Restriction of scalars T ↦ T_K (which multiplies slice ranks by [K:Q]) does not work: it only reflects isomorphism over K, and Galois twists break descent. Not done.

**The promise is necessary (counterexample to naive padding).** Without it the reduction fails. Take F₀ = x³ + y³ and G₀ = a³ + 2b³. They are not projectively equivalent over Q: x³ + y³ has a rational linear factor, x³ + 2y³ has none, and scaling does not create one. But μ_M = x³ + y³ + s³ (M = #₃CP³) dominates N = M_{12(a³+2b³)}. Take k = (1, −1, 0) and W = ker(x − y) = ⟨(1,1,0), (0,0,1)⟩. Then μ_M(·,·,k) = x² − y² = (x − y)(x + y) vanishes on W×W, k ∉ W, and μ_M(a(1,1,0) + b(0,0,1)) = 2a³ + b³ ≅ a³ + 2b³. So Lemma K applies. With the markers added, the same W ⊕ V_L works. The step "rank t_L(·,·,z) = m" in the analysis above forces V_L ⊂ W, so the markers cannot prevent this. In general, a YES instance of codim-1 DOM *requires* a rational point of Hessian rank ≤ 2 in μ_M: the vector k of Lemma K. Padding with a summand whose Hessians all have rank ≥ 3 (for example a second marker t_{L₁}) makes every instance NO.

**DT1′ (integral slice, degree one).** Let M, N be closed simply connected 6-manifolds with torsion-free homology and equal Betti numbers. Then M admits a degree-one map to N iff M and N are oriented homotopy equivalent.
*Proof.* A degree-one map f has f_* surjective on integral homology (Umkehr: f_*(f^!(x)) = x with f^!(x) = PD_M f*PD_N⁻¹(x)). The groups are free of equal ranks, so f_* is an isomorphism. By Whitehead's theorem (simply connected CW complexes), f is a homotopy equivalence, and it is orientation preserving since its degree is 1. The converse is immediate. ∎
Consequence (with lane4 T3(b), audited PASS): degree-one domination on this slice is 3FTI_Z-hard. This is the integral counterpart of DT1.

## 5. DT5: domination fails the Hasse principle

Define, for a place v of Q, LocDOM_v(M,N): there is a graded Q_v-algebra map H*(N;Q_v) → H*(M;Q_v) that is nonzero on top degree. By Miller formality over Q_v this is the same as a Q_v-CDGA map of minimal models nonzero on top, i.e. "M dominates N over Q_v" in the algebraic sense of lane4 T5(a). It is implied by DOM(M,N).

**Theorem DT5.** For the lane4 pair M = M_E, M′ = M_{E′} (spin, b₂ = 6, b₃ = 0):
1. LocDOM_v(M, M′) and LocDOM_v(M′, M) hold for every place v (including ∞);
2. neither M dominates M′ nor M′ dominates M.

The 2^r family (lane4 Cor. T5.1) gives 2^r pairwise non-dominating manifolds that dominate each other locally everywhere.

*Proof.* (1) T5(1) gives graded Q_v-algebra isomorphisms in both directions. (2) Equal b₂: by Lemma E6, a nonzero-degree map in either direction would give projective equivalence of the cubics over Q, i.e. a rational equivalence, contradicting T5(2). ∎

*Comment.* This is T5 transported through Lemma E. What it adds to the domination cluster: the 6-dimensional domination problem cannot be decided by local (Hilbert-symbol–type) tests, unlike dimension 4, where r5 Thm 4D decides DOM by finitely many Hilbert-symbol computations. Caveat: whether DOM in dimension 4 satisfies a Hasse principle in the LocDOM sense (the multiplier d_v may vary with v) was not checked. The r5 test fixes κ from a finite global set, which is a different formulation.

## 6. Dependencies (flag unaudited)

- r3 Thm B: audited PASS with fixes; Manin's §5 lemmas read via a summary (r3 gap 1).
- lane4 T4(c), T5, Lemma L, L′: audited PASS (fix in T4(c) step 4: C(F₀) commutative Artinian, handled there).
- r4 Thm 1 (S²×S⁴ ≡ HTP(Q)): audited (per U1 inputs).
- GQ Thm A / Cor. B: checked in lane4.
- Šimková Thm D, Sarkisyan: unrefereed / not verified (decidability remark only).
- Miller formality, Herrmann §2.2: checked in lane4.
- Lemmas E, E6, S, K and Theorems DT1, DT3, DT4, DT5: new here, **unaudited**.
