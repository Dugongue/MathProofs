# Base extension and asymptotic tensor spectra

The finite-extension arguments give the specified Galois blindness and catalysis statements.

## 1. Setting

- Tensors are 3-tensors over a field k. Δ(k) is Strassen's asymptotic spectrum: monotone semiring homomorphisms to R_{≥0} for restriction ≤, ⊗ and ⊕, with F(⟨1⟩) = 1.
- ≲ is asymptotic restriction. Strassen duality [cl, Strassen 1988, valid over every field]: S ≲ T ⟺ F(S) ≤ F(T) for all F ∈ Δ(k). Write S ~_Δ T when both directions hold ("spectral TI").
- For a finite field extension L/k, let M_L ∈ L⊗L⊗L be the structure tensor of L as a k-algebra.
- **Restriction of scalars [cl].** For an L-tensor X, the k-tensor Res_{L/k}X (X viewed as a k-trilinear object) equals X ⊗_k M_L whenever X is defined over k. If S ≤_L T, then S⊗M_L ≤_k T⊗M_L, because L-linear maps are k-linear.

## 2. Theorem A (Galois blindness)

Let S and T be k-tensors.

1. S ≲_k T ⟺ S ≲_{k̄} T. [OAI lem:comparison; cl]
2. If S ≅_{k̄} T, then F(S) = F(T) for every F ∈ Δ(k), so S ~_Δ T over k. Consequently, no family of spectral points, including the Euclidean prices H(·;x) of [OAI] Thm 1.1, the quantum functionals and the support functionals, separates the k-forms of a geometric orbit. The fibre of the spectral map over a geometric orbit O contains all |H¹(k, Stab)| k-orbits in O(k). Over F_q, Lang's theorem gives H¹(F_q, Stab) = H¹(F_q, π₀ Stab).
3. **(Spectral comparison is not degeneration.)** Over F_q, let M := M_{F_{q²}} (2×2×2) and U := ⟨2⟩.
   - F(M) = F(U) = 2 for all F ∈ Δ(F_q).
   - rank_{F_q} M = 3 ≠ 2, so M ≇_{F_q} U.
   - M ⋬_q U: M is not an F_q-rational degeneration of U, so the F_q-border rank of M is > 2.
   - Hence the spectral preorder does not decide F_q-degeneration, even on the gap-0 (TI) slice.

**Proofs.**
- (1) ⇐: given S^{⊗n} ≤_{k̄} T^{⊗m}, the restriction is defined over a finite L. So S^{⊗n}⊗M_L ≤_k T^{⊗m}⊗M_L, which gives F(S)^n F(M_L) ≤ F(T)^m F(M_L). Since M_L ≠ 0, F(M_L) > 0. Let m/n → 1. Alternatively, apply [OAI] surjectivity directly.
- (2) Isomorphism over k̄ gives ≤ both ways over k̄. Apply (1).
- (3)
  - The values: M ≅_{F̄_q} U, because F_{q²}⊗F̄_q ≅ F̄_q², so (2) applies.
  - The rank: rank_{F_2}(M_{F_4}) = 3 by brute force (C++ log). For general q this is classical: the bilinear complexity of F_{q²}/F_q is 3.
  - No degeneration: [ours, R-B2 Thm D2, audit-B2 PASS] says that if Stab_U is smooth and the orbit dimensions are equal, then M ⊴_q U ⟺ M ≅_{F_q} U.
    - Stab_U is the 4-torus ⋊ S₂. Its Lie algebra consists of diagonal (X,Y,Z) with x_i+y_i+z_i = 0, which has dimension 4 = dim Stab_U, so it is smooth.
    - The orbit dimensions are equal because M and U lie in one geometric orbit.
    - Therefore M ⋬_q U. ∎

**Kronecker cancellation fails over non-closed fields.** By (2)'s mechanism, S ≇_k T can still give S⊗M_L ≅_k T⊗M_L. For example, M⊗M ≅_{F_2} U⊗M, via the algebra isomorphism F_4⊗F_4 → F_4×F_4, a⊗b ↦ (ab, ab²). This is checked exhaustively in the C++ log: bijective, with 0 multiplicativity failures. Yet M ≇ U.

## 3. Theorem B (geometric TI = catalytic k-TI)

Let k be perfect (e.g. finite or a number field), and let S, T be k-tensors of the same format. Then

  S ≅_{k̄} T ⟺ ∃ a finite extension L/k with S⊗M_L ≅_k T⊗M_L.

**Lemma (Krull–Schmidt via the centroid; char-free).** For a concise tensor X ∈ U⊗V⊗W, define the centroid C(X) = {(a,b,c) ∈ End U × End V × End W : (a⊗1⊗1)X = (1⊗b⊗1)X = (1⊗1⊗c)X}.
- (i) C(X) is commutative.
- (ii) Direct-sum decompositions of X, splitting all three spaces, correspond bijectively to idempotents of C(X).
- (iii) The decomposition of X into directly indecomposable summands is unique as a triple of subspace decompositions. In particular S^{⊕e} ≅ T^{⊕e} implies S ≅ T, for concise S and T. For general S, T, apply this to their concise cores.

*Proof.*
- (i) For (a,b,c), (a′,b′,c′) ∈ C(X), the chain (aa′⊗1⊗1)X = (a⊗1⊗1)(1⊗b′⊗1)X = (1⊗b′⊗1)(1⊗1⊗c)X = (1⊗1⊗c)(a′⊗1⊗1)X = (a′a⊗1⊗1)X holds. Conciseness in the U-mode then gives aa′ = a′a. The other two modes are the same.
- (ii) The block projections of a decomposition X = X₁⊕X₂ lie in C(X). Conversely, for an idempotent e = (e₁,e₂,e₃): (e₁⊗1⊗1)X = (e₁⊗e₂⊗e₃)X ∈ e₁U⊗e₂V⊗e₃W, and the same holds for 1−e.
- (iii) A commutative finite-dimensional algebra has exactly one complete set of primitive orthogonal idempotents.
  - So an isomorphism g: S^{⊕e} → T^{⊕e} carries the unique indecomposable decomposition to the unique one.
  - The multisets of isomorphism classes then agree: e·[summands of S] = e·[summands of T]. Divide by e. ∎

*Proof of Thm B.*
- (⇒) For perfect k, Iso(S,T) has a point over a finite separable L, and Res gives the k-isomorphism.
- (⇐) Choose L separable; if needed, pass to the separable closure inside L, or note that for perfect k every finite L is separable. Over k̄, M_L ≅ ⟨e⟩ with e = [L:k], so S^{⊕e} ≅_{k̄} T^{⊕e}. The Lemma gives S ≅_{k̄} T. ∎

**Reading.** Geometric TI is rational TI with a field catalyst. By Thm A, the asymptotic spectrum sees at most the geometric orbit. Whether it sees exactly the geometric orbit is open question Q1 below.

## 4. Theorem C (rank: exact = arithmetic, asymptotic = geometric)

Over k = Q:

1. "rank_Q T ≤ r" is Σ⁰₁-complete.
   - Shitov 2016 [cl, arXiv 1611.01559]: tensor rank over an integral domain R is polynomial-time equivalent to polynomial-system solvability over R.
   - BB [OAI/user-directive "PROVED"]: HTP(Q) is undecidable and Σ⁰₁-complete.
2. R̃_Q(T) = R̃_{Q̄}(T) = inf_n R_{Q̄}(T^{⊗n})^{1/n}. This is a right-c.e. real, i.e. {r ∈ Q : R̃ < r} is c.e., because each R_{Q̄}(T^{⊗n}) is computable (an existential sentence of ACF₀, which is decidable).
3. **Q-forms of the unit tensor** [ours R-B1-rext-forms (b) for the classification; this note for the spectrum]. The Q-tensors T with T ≅_{Q̄} ⟨s⟩ are exactly the T_E, for E an étale Q-algebra of dimension s. For each of them:
   - F(T_E) = s for every F ∈ Δ(Q), so T_E ~_Δ ⟨s⟩ (Thm A(2));
   - yet rank_Q T_E = s iff E ≅ Q^s, and rank_Q T_E = 2s−1 when E is a field (de Groote / Winograd, [cl]);
   - and the bilinear-system degree is BL_Q(T_E) ≡ ∏HTP(L_i(E)) (R-B1, unaudited for this round).
   - So the whole arithmetic hierarchy that R-B1 attaches to T_E sits inside one spectral class.

*Proof of 2.*
- Fekete's lemma gives lim = inf, by submultiplicativity.
- The inequality R̃_Q ≤ R̃_{Q̄}: if T^{⊗n} ≤_L ⟨r⟩, then T^{⊗nm} ≤_L ⟨r^m⟩, so T^{⊗nm} ≤_Q ⟨r^m⟩⊗M_L ≤ ⟨r^m R_Q(M_L)⟩. Take m-th roots and let m → ∞. This is Schönhage's argument.
- The reverse inequality R̃_{Q̄} ≤ R̃_Q is trivial. ∎

**Top-30 links.**
- Undecidability cluster: #8 rank-two completion over Q, BB, domination ≡ TI_Q (#4).
- Thm C is the tensor-rank instance of the Manin pattern (#1): exact problems over Q are arithmetic and undecidable, while their asymptotic shadows are geometric and semi-computable.
- **Corollary for #4.** Every spectral or asymptotic invariant of TI_Q instances, and so of the cubic forms in DOM((S²)³), is a function of the Q̄-orbit. Any undecidability of TI_Q is spectrally invisible.
