# Matrix tuple isometry in characteristic two

Scope: finite fields of characteristic two with the stated linear algebra and module-isomorphism procedures. The commutative dyadic cases use a different argument.

## 0. The problem

**The open problem.** Grochow–Qiao–Stange–Sun, *Part V*, §1.4 (arXiv 2611.00735), say that it "remains open to just do the last step — solve Matrix Tuple Isometry — over fields of characteristic 2 ... in polynomial time". Concretely: given A = (A_1..A_m) and B = (B_1..B_m) in M_n(F_q) with q = 2^e, decide whether some P ∈ GL_n(F_q) has PᵀA_iP = B_i for all i.

**Prior state.**
- Ivanyos–Qiao solve odd q.
- GIQS (arXiv 2610.00874) and Sun (arXiv 2611.05920, App. A) obtain subexponential algorithms on the char-2 side. Their bottleneck is enumerating (𝒜/J)^×.
- Our 11-12 note ([research manuscript]) proved P for untwisted classes and Loewy length ≤ 3.
- The repo packet `[local reference omitted]` (Matrix.md, OriginalMatrix.md, Round2/3Matrix.md) proves sufficient cases (one or two active Tate grades, symplectic blocks of dimension ≥ 10, point stabilisers). It names the missing ingredient a "universal affine-stabiliser lemma" (Matrix.md §4).

**The main result.** Theorem A below removes the need for that ingredient, and for any stabiliser recursion.

## 1. Setup (characteristic-free reduction; Lemma 1 of the 11-12 note)

**Step 1.** Close both tuples under transpose. Then find a module isomorphism (X, Y) with XᵀA_iY = B_i; this is polynomial time (Brooksbank–Luks; Chistov–Ivanyos–Karpinski). If none exists, the answer is no.

**Step 2.** Let 𝒜 = {(L,R) : LᵀA_i = A_iR ∀i} ⊂ M_n × M_n^op be the adjoint algebra, with involution (L,R)* = (R,L).

**Step 3.** Put c := (YX⁻¹, YX⁻¹). Then c ∈ Sym(𝒜) ∩ 𝒜^×.

**Lemma 1.** A ≅ B ⟺ c = u*u for some u ∈ 𝒜^×.

**Notation.** All of it is computable in polynomial time by F₂-linear algebra (dimension ≤ e·2n²).
- J = rad 𝒜, N = 1+J, S = 𝒜/J, Ḡ = U(S) = {ū : ū*ū = 1}.
- Q(x) := x*x.
- Tr(J) := {j + j* : j ∈ J}.
- **D₀ := Tr(J) + Q(J) = {j + j* + k*k : j, k ∈ J}.** This is an additive group: Q(k₁+k₂) = Q(k₁) + Q(k₂) + Tr(k₁*k₂), and k₁*k₂ ∈ J.
- D₀ is stable under y ↦ y*dy for every y ∈ 𝒜 (not only units): y*(j + j* + k*k)y = (y*jy) + (y*jy)* + (ky)*(ky).

**The invariant Φ.** Define Φ: S → Sym(𝒜)/D₀ by Φ(x̄) := [x*x].
- It is well defined: (x+j)*(x+j) = x*x + j*j + Tr(x*j), and x*j ∈ J.
- It is a quadratic map: Φ(x̄+ȳ) = Φ(x̄) + Φ(ȳ) + [x*y + (x*y)*].
- Unitaries preserve it.
- **Stab(Φ) = {ū ∈ Ḡ : u*u − 1 ∈ D₀}**, for any lift u. For "⊆" take x̄ = 1. For "⊇" use x*(1+d)x = x*x + x*dx with x*dx ∈ D₀. The condition does not depend on the lift, because (un)*(un) − 1 = n*(u*u−1)n + (n*n − 1) and n*n − 1 ∈ D₀.

## 2. Theorem A (lifting theorem / decoupling theorem)

**Theorem A.** Let 𝒜 be a finite-dimensional algebra with involution over any field of characteristic 2, with J = rad 𝒜. Then

  image( U(𝒜) → U(𝒜/J) ) = { ū : u*u − 1 ∈ Tr(J) + Q(J) }.

Equivalently, for s ∈ (1+J) ∩ {u*u : ū ∈ Ḡ}:

  s ∈ {n*n : n ∈ N} = {1 + k + k* + k*k} ⟺ s − 1 ∈ {j + j* + k*k}.

That is, the coupled orbit condition (one variable k) linearises to the decoupled one (two variables j, k).

**Sanity check in odd characteristic.** There Tr(J) = Sym(J), so the condition is empty and every unitary lifts, which is Taft's theorem. In characteristic 2 the condition is a genuine F₂-linear constraint.

### 2.1 Lemma W (Wall form)

Let S_j be a *-simple component of S over k = F_{q'}, and ḡ ∈ Ḡ_j with r = rank(ḡ − 1). Then

  ḡ = 1 + x̄βx̄*

for some idempotent ē ∈ S_j, some x̄ ∈ S_jē and some β ∈ ēS_jē* that is invertible: there is β′ ∈ ē*S_jē with ββ′ = ē and β′β = ē*.

**Self-dual components** (orthogonal, symplectic, unitary): S_j = M_a(k) with X* = H̄⁻¹X^{τT}H̄ and h̄(x,y) = x^{τT}H̄y.
- For an isometry ḡ, ker(ḡ−1) = im(ḡ−1)^⊥. If ḡx = x, then h̄(x, ḡy) = h̄(ḡx, ḡy) = h̄(x,y); the dimensions then match.
- Write ḡ − 1 = X₀β₀[h̄(w_i, ·)]_i, where X₀ = (w_1..w_r) is a basis of im(ḡ−1) and β₀ ∈ GL_r(k).
- With ē = diag(1_r, 0), x̄ = (X₀ | 0) and β := diag(β₀, 0)H̄, one checks β ∈ ēSē*. Its inverse is β′ = H̄⁻¹diag(β₀⁻¹, 0).

**Exchange components:** S_j = M_a × M_a^op, ḡ = (X, X⁻¹).
- im(X−1) = im(X⁻¹−1) = W, and the two maps have the same kernel. So X − 1 = X₀β₁R and X⁻¹ − 1 = X₀β₂R.
- Take ē = (E_r, E_r), which satisfies ē = ē*, and x̄ = (X₀ | 0, R-rows).
- Then x̄(β₁,β₂)x̄* = (X₀β₁R, X₀β₂R) = ḡ − 1.

### 2.2 Lemma L (every Φ-stable Wall element lifts)

**Statement.** If ḡ = 1 + x̄βx̄* is as in Lemma W and ḡ ∈ Stab(Φ), then ḡ has a unitary lift.

**Proof.**
1. **Set up lifts.**
   - Lift ē to an idempotent e ∈ 𝒜. Then e* lifts ē*, and e ~ e*.
   - Take x ∈ 𝒜e lifting x̄.
   - Take b ∈ e𝒜e* lifting β. It is invertible: there is b′ ∈ e*𝒜e with bb′ = e and b′b = e*.
   - Put m := x*x ∈ B := e*𝒜e.
2. **Reduce unitarity to one element of B.** With T := 1 + xbx*,

     T*T − 1 = x(b + b* + b*mb)x* = w* r w,  where w := bx* and r := b′ + b′* + m ∈ Sym(B).

   This uses b*b′b = b* and b*b′*b = b.
3. **Use the hypothesis.** ḡ ∈ Stab(Φ) gives w*rw ∈ D₀.
4. **Compress back into B.**
   - Choose ȳ ∈ Sē* with x̄*ȳ = ē*. This exists because x̄ has full column rank on ē.
   - Lift it to y ∈ 𝒜e*. Then g := wy ∈ e𝒜e* is invertible (its residue is β).
   - So g*rg = y*(w*rw)y ∈ D₀.
   - Hence r = (g⁻¹)*(g*rg)g⁻¹ lies in

       (g⁻¹)*D₀g⁻¹ ⊆ Tr(e*Je) + Q(Je).

     The inclusion holds because (g⁻¹)* ∈ e*𝒜e, so (g⁻¹)*jg⁻¹ ∈ e*Je and kg⁻¹ ∈ Je.
5. **Correct the lifts.** Write r = s + s* + k*k with s ∈ e*Je and k ∈ Je. Replace

     x ← x + k,  b′ ← b′ + s + x*k.

   Here x*k ∈ e*Je, and neither residue changes.
6. **Conclude.** The new r is

     r + (s + s*) + k*k + Tr(x*k) + Tr(x*k) = 0,

   using characteristic 2: 2k*k = 0 and the two Tr(x*k) terms cancel. So T := 1 + x(b′)⁻¹x* is unitary, and its residue is ḡ. ∎

**Proof of Theorem A.**
1. Φ is additive across *-components, and cross terms vanish. So Stab(Φ) = ∏_j (Stab(Φ) ∩ Ḡ_j).
2. Each factor lifts by Lemmas W and L.
3. Products of lifts are lifts of products.
4. The reverse inclusion "⊆" is trivial. ∎

**Remarks.**
- No generation lemma is needed, so there are no Dieudonné-type exceptions such as O⁺₄(2).
- There is no restriction on rank, field, Loewy length, multiplicity or cross-radicals.
- The proof is constructive.

## 3. Theorem B: char-2 MTI ∈ P

**Theorem B.** Matrix Tuple Isometry over F_{2^e} (general, symmetric or alternating tuples) is decidable in deterministic polynomial time in n, m and e, and an isometry is constructed when one exists.

Determinism: radical, Wedderburn and matrix-unit computations need polynomial factoring over F_{2^e}. Berlekamp's algorithm is deterministic polynomial for fixed p = 2.

**Algorithm.**
1. Compute the module isomorphism (X, Y), the adjoint algebra 𝒜 and c (§1).
2. Compute J and S = ⊕ S_j, the *-simple components with explicit matrix units.
3. **Residue norm.**
   - Solve c̄ = ū₀*ū₀ component by component (11-12 note §3 table):
     - exchange: always solvable;
     - unitary: always solvable;
     - orthogonal: solvable iff h̄c̄ is non-alternating;
     - symplectic: solvable iff h̄c̄ is alternating.
   - If unsolvable, answer NO.
   - Lift u₀ and set c′ := u₀^{-*}cu₀⁻¹ ≡ 1.
4. **Marked residue isometry.** Find w̄ ∈ Ḡ with w*w − c′ ∈ D₀, i.e. Φ_1∘w̄ = Φ_{c′} where Φ_h(x̄) := [x*hx]. If there is none, answer NO. Prop C shows this is polynomial.
5. **Layer test.** Put c″ := w^{-*}c′w⁻¹, which lies in 1 + D₀. Decide whether c″ ∈ {n*n : n ∈ N} by the layer test: Sun Lemma A.24, or 11-12 note §2 (subgroups S_k, homomorphisms t_k, polycyclic kernels). The answer is YES iff it passes. The witness is P = (n w u₀)_L·X.

**Correctness (uses Theorem A).**
- **If c′ = v*v**, then v̄ satisfies step 4.
  - For any other solution w̄: Φ_1∘v̄ = Φ_1∘w̄, so v̄w̄⁻¹ ∈ Stab(Φ_1).
  - By Theorem A, v = uwn′ with u unitary and n′ ∈ N.
  - Then c″ = (wn′w⁻¹)*(wn′w⁻¹) ∈ N·1.
  - So the verdict does not depend on which w̄ step 4 returns.
- **Conversely,** c″ ∈ N·1 makes c′ a norm.
- **If step 4 fails,** c′ is not a norm, since a norm v would give a solution v̄.

### 3.1 Prop C (the residue step is classical Witt theory)

The condition Φ_1∘w̄ = Φ_{c′} decouples over components.

**Restriction to one column space.** Fix a component j and an idempotent ē (rank 1, or rank (1,1) for exchange). Put B = e*𝒜e. Then Φ restricted to V := Sē ≅ k^a takes values in Γ_B := Sym(B)/D₀(B).
- The map Γ_B → Sym(𝒜)/D₀ is injective. By compression, D₀ ∩ B ⊆ D₀(B).
- The condition on S_j is equivalent to the condition on V, because Φ(x̄ā) = ā*Φ(x̄)ā.

**Structure of φ := Φ|_V.** It is quadratic with polar τ_B∘h̄, where τ_B(s̄) = [s + s*].
- Its image modulo Γ₂ := τ_B(B̄) is additive; this is the old q̄.
- Λ̂ := ker τ_B is a k-subspace of the line B̄, closed under s̄ ↦ μ²s̄ (D₀ is congruence-stable). So **Λ̂ ∈ {0, B̄}.**

**Key reduction: additive markings are vector markings.** Every F₂-linear map V → (F₂-space) is a finite list of F₂-functionals. Each functional is Tr_{k/F₂}(h̄(f, ·)) for a unique f ∈ V. So "preserve an additive map" means "fix vectors f_i".

**The cases.**

| Case | What the condition becomes |
|---|---|
| (E) Exchange | Subtract the canonical hyperbolic refinement; the rest is additive. Linear algebra in GL_a. |
| (U) Unitary | φ = ψ₀ + additive, with ψ₀(x) = [ω(h̄(x,x))] (Teichmüller is additive in char 2). Unitary Witt with marked vectors. |
| (O) Orthogonal, h̄ non-alternating | Γ₂ = 0 (symmetric e and symmetric Teichmüller lifts), so φ is additive. Marked vectors, including the characteristic vector w₀. Solved by Lemma O. |
| (S) Symplectic, Λ̂ = B̄ | Additive. Symplectic Witt with marked vectors. |
| (S′) Symplectic, Λ̂ = 0 ("ε-twisted") | Reduces to marked vectors plus one quadratic form with polar h̄ (details below). Witt for nondegenerate-polar quadratic spaces with marked vectors: classical, and constructive in GrochowFunctorLifting/Matrix.md §1.2 and OriginalMatrix.md "Constructive Witt extension". |

**Details of case (S′).**
1. Pick an F₂-section s of Γ_B → Γ₁, used for both sides once the markings match.
2. Then Q̃ := φ − s∘q̄ is an F₂-quadratic map V → Γ₂ ≅ k with polar h̄.
3. Fix any k-quadratic form Q₀ with polar h̄. Then Q̃ − Q₀ is F₂-linear, and splits by Galois descent into σ^j-semilinear parts.
4. Q₀∘w̄ − Q₀ is purely (·)²-semilinear. So the parts with j ≠ 1 are vector markings, and the j = 1 part gives one genuine quadratic form Q := Q₀ + L^{(1)}, which must be preserved.

**Lemma O (Witt with w₀). PROVED; also COMPUTED.** Let b be nondegenerate symmetric non-alternating over a perfect field of characteristic 2, with characteristic vector w₀ (b(x,x) = b(w₀,x)²). A partial isometry σ: U → U′ extends to O(b) iff σ ⊕ (w₀ ↦ w₀) is a well-defined isometry on U + Fw₀.

*Proof.*
- **dim V odd:** V = Fw₀ ⊥ w₀^⊥ with w₀^⊥ symplectic, and O(b) = Sp(w₀^⊥). Apply symplectic Witt to the w₀^⊥-components.
- **dim V even:** embed V ⊥ ⟨z⟩ with b(z,z) = 1. The new characteristic vector is w₀ + z, and O(V) = Stab(z). Apply the odd case to σ ⊕ (z ↦ z). ∎

*Brute-force check (`witt.cpp`):* 0 failures among 391,056 extension instances over F₂ (a ≤ 5) and 42,394 over F₄ (a ≤ 3). Omitting the w₀ condition gives thousands of failures, so the hypothesis is needed.

**Complexity.** Each Witt routine is polynomial in a and log q (cf. Magma polar-space isometry; OriginalMatrix.md appendix).

## 5. Consequences and relation to prior work

- **Subsumes our 11-12 results:** Theorems 9, 10 and 12 and Prop 11. Untwisted classes have D₀-condition = D-condition. Theorem 12's Loewy-length-3 analysis is a special case.
- **Subsumes the repo's sufficient cases:** one active grade per factor; two grades with a point stabiliser; mixed V ⊕ V/Ev modules. Their missing "universal affine-stabiliser lemma" is not needed. Theorem A replaces the whole grade-by-grade stabiliser recursion with a single residue Witt problem followed by a unipotent layer test.
- **Correctness check of the repo packet:** consistent. Their theorems are true statements about the image group. Their κ-coefficient λ_j is nonzero exactly in the S′ case. No contradiction was found. Their Arf-type binary-linear conditions (Matrix.md §1.3) are what case S′ needs. Their proofs were read, not independently re-proved line by line.
- **Effect on GIQS and Sun:** the MTI subroutine in their pipelines becomes polynomial over fields of characteristic 2. Whether this yields polynomial group isomorphism for the classes they treat needs their reductions, which go through quadratic-form tuples or Z/2^ℓ. Not claimed.
- **TI state-of-the-field row:** should become "GIQS 2026 / Sun, char-2 MTI: **CLOSED (local, informal, unaudited)**: P via Theorem A; old R* refuted".
