# Conditional generator lower bound for orthogonal tensor invariants

The orthogonal lower bound depends on OpenAI’s unrefereed grid lower bound. The transfer and the invariant construction are the claims proved here.

## 0. Statement

**Theorem O.** Work over C. Let G = O_N^{×3} or SO_N^{×3} act on U = C^N⊗C^N⊗C^N in the standard way. This is the TI_O action.

For every n there is N = O(n⁴) such that every generating set of C[U]^G contains an element g with

  L̄(g) ≥ n^{Ω((log n)^{1/12})} / poly(n).

The same lower bound holds for every succinct encoding C(x, y) of generators in the sense of GIMOWW Def. 1.3. Here L̄ is border circuit size (degree-component border suffices).

Hence **Mulmuley's Conjecture 1.6 (GIMOWW 1910.01251) fails for the connected reductive group SO_N^{×3} acting on single 3-tensors.** This holds unconditionally, given OpenAI's grid theorem.

**Context.**
- GIMOWW open problem (2) asks the single-3-tensor question for SL³ (TI_SL). It remains open: M2 reduced it to BI Problem 5.16, and A4 Thm 3 shows that tensor-network slices die there because of a residual torus.
- GIMOWW Theorem 1.8 gives an earlier torus result conditional on NP ⊄ P/poly. The result below concerns a nonabelian orthogonal group. It also gives a precise explanation of the gap: the A4 torus comes from GL-scalings of marker vectors, and an orthogonal group cannot scale a non-isotropic vector. §5 makes this precise.

**Corollary O′ (gauge action, every field).** Let Γ be a connected graph with oriented edges. Put H = ∏_e GL(V_e) and let it act on the tables X = ⊕_v ⊗_{e∋v} V_e^{±}, using V_e at the tail and V_e* at the head. Then the lowest-degree invariant of C[X]^H is unique: it is the graph state sum Z_Γ, of degree |V|. For brick walls or grids, every generating set therefore has border size n^{Ω((log n)^{1/12})}.
- This holds over every infinite field. The uniqueness step is characteristic-free, as is OpenAI's bound.
- For 4-regular grid tables this is exactly the 2D-PEPS gauge action without physical legs. Lysikov–Walter (LW) show that PEPS gauge OCI is TOCI-complete, though their model has physical legs. So, for (a variant of) a TOCI-complete action, Mulmuley fails at the lowest degree.

## 1. Construction

**The graph.** Γ_L is the toroidal brick wall. Its vertices are (i, j) ∈ Z_L×Z_L with L even.
- Horizontal edges are (i, j)–(i+1, j). The edge starting at (i, j) gets colour 1 if i+j is even and colour 2 otherwise.
- Vertical edges are (i, j)–(i, j+1) when i+j is even, with colour 3.

Γ_L is cubic, and every vertex sees each colour exactly once. Its treewidth is Θ(L), and its planar patch contains an Ω(L)×Ω(L) grid minor. Orient every edge arbitrarily.

Bond dimensions n_e are pairwise distinct with n_e ≥ max(2, n²). Take for example n_e = n² + 2 + index(e).

**The factors.** For an edge e of colour c, write c+1 and c+2 mod 3. We use orthogonal direct sums with standard forms and real orthonormal bases.
- W_e = C^{2n_e} has basis f_1..f_n, g_1..g_n. Its complex structure J_e is given by J f_i = g_i and J g_i = −f_i. J is real, orthogonal and antisymmetric. Its ±i-eigenspaces are the Lagrangians V_e* = ⟨f − ig⟩ and V_e = ⟨f + ig⟩, and the form identifies V_e* with the dual of V_e.
- W′_e is a copy of W_e. X_e and Y_e are 3-dimensional. S_e = ⟨u, u′⟩ is 2-dimensional.
- Factor F_c ⊇ W_e ⊕ X_e, factor F_{c+1} ⊇ W′_e ⊕ Y_e, and factor F_{c+2} ⊇ S_e.
- A = F_1, B = F_2, C = F_3 are the orthogonal sums over all edges. So N = Σ_e(2n_e + 3)·2/3 + … = O(|E|·n²) = O(n⁴) per factor, with L = O(n).

**The marker tensor.** It is written in factor order (c, c+1, c+2) and then placed into A⊗B⊗C:

  w0_e = Id_e⊗u + J_e⊗u′ + Σ_{k=1}^{3} x_k⊗y_k⊗(u + a_k u′),  w0 = Σ_e w0_e.

Here Id_e = Σ_i (f_i⊗f′_i + g_i⊗g′_i) and J_e = Σ_i (g_i⊗f′_i − f_i⊗g′_i). The constants a_k are real and generic; (2, 3, 7) works (see §3).

**The slice summand.** For a vertex v with incident edges e_1, e_2, e_3 of colours 1, 2, 3, put

  N1_v = V^{s_1}_{e1}⊗V^{s_2}_{e2}⊗V^{s_3}_{e3} ⊂ A⊗B⊗C,

where V^{+} = V_e if v is the tail of e and V^{−} = V_e* if v is its head. These sit in the primary blocks W_e. Put N1 = ⊕_v N1_v.

## 2. Proof of Theorem O

**Step 1 (closed orbit).** Every entry of w0 is real. For K = O_N(R)³ and real ξ ∈ so(N), the moment map is μ(w0)(ξ) = Im⟨ξw0, w0⟩ = w0ᵀξw0 = 0. By Kempf–Ness, G·w0 is closed, so H := Stab_G(w0) is reductive (Matsushima). For SO³, a closed O³-orbit is a finite union of closed SO³-orbits.

**Step 2 (identity component H° = ∏_e GL(V_e)).**
1. *No cross terms.* The pieces w0_e live in pairwise disjoint block triples (A_e, B_e, C_e) and each is concise in its blocks. Consider an off-diagonal block ξ_A^{fe}: A_e → A_f with f ≠ e. It contributes in the block triple (A_f, B_e, C_e). No ξ_B or ξ_C term reaches that triple, because that would need a piece whose A-block is A_f and whose C-block is C_e. So ξ_A^{fe} kills the A-image of w0_e, which is A_e, and hence ξ_A^{fe} = 0.
2. *Within one piece.* Read w0_e as a pencil over S_e: M(α, β) = (αI + βJ) ⊕ diag(α + a_kβ). Its determinant is (α² + β²)^{n_e}·∏_k(α + a_kβ). Its roots are ±i, each with multiplicity n_e, and three generic real roots.
   - An element (g, g′, h) must have h permuting these roots.
   - Elements of O(S_e) that preserve {±i} act on P¹ as w ↦ λw or w ↦ λ/w, where w = (z−i)/(z+i).
   - For generic real roots, which lie on |w| = 1, only λ = 1 survives. So h = ±1 on S_e, and infinitesimally ξ_C = 0.
   - Then g(αI + βJ)g′ᵀ = ±(αI + βJ), which gives g′ = ±g and gJ = Jg, i.e. g ∈ GL(V_e).
   - On X⊕Y the conditions are gdiag(·)g′ᵀ = ±diag(·) with distinct linear forms, so g = g′ = diagonal signs.
3. *Lie algebra.* Lie H = ⊕_e gl(V_e).
4. **C++ check (`ostab.exe`).** The computed dim Lie Stab equals Σ n_e² exactly:
   - theta graph, n = (1, 2, 3): 14 = 14;
   - theta graph, n = (2, 3, 4): 29 = 29;
   - K₄ with a 1-factorisation and n = 1..6, a non-bipartite case with mixed orientations: 91 = 91.

   The computation is mod p = 10⁹+9. Since gl(V_e) ⊆ stab is proved, the equality also holds over Q.

**Step 3 (component group, so N1 is H-stable).** Take h ∈ H. Then Ad h normalises H°.
- Since the dimensions n_e ≥ 2 are distinct, Ad h fixes every simple factor SL(V_e).
- In A, the only H°-submodules on which SL(V_e) acts nontrivially are V_e and V_e* inside W_e. The same holds for W′_e in its factor. Hence h preserves W_e and W′_e.
- h preserves W_e and its orthogonal complement. It therefore maps the C-image of (π_{W_e}⊗1⊗1)w0 to itself. That image is S_e, so h preserves S_e.
- Then (1⊗1⊗π_{S_e})w0 = w0_e is h-fixed, and h preserves the blocks of w0_e.
- By step 2, h acts on W_e as an element of GL(V_e) (−1 included), and as signs on X, Y, S.

So H acts on N1 through ∏_e GL(V_e). In particular **H contains no swap V_e ↔ V_e***. Without the three X-markers the swap does lie in H: the pencil αI + βJ admits the reflection h(α, β) = (β, α) with g′ = −Jg, g anticommuting with J. This is why the X-markers are there. A single extra root, or two, is not enough, since a reflection of the circle always swaps or fixes them. Three generic roots are needed.

**Step 4 (N1 lies in a slice).** The tangent space T = Lie(G)·w0 is spanned by three kinds of terms:
- (ξ_A⊗1⊗1)w0_e, whose B-support lies in a copy block or a Y-block;
- (1⊗ξ_B⊗1)w0_e, whose C-support lies in a marker block S_e (colour-1 pieces; the other colours are cyclic, with the support in a copy or marker block);
- (1⊗1⊗ξ_C)w0_e.

In each case one factor of the support avoids the primary W-blocks. N1 lies entirely in primary blocks, so N1 ∩ T = 0. H is reductive, so there is an H-stable complement N ⊇ N1 to T, with N1 a direct summand.
- **C++ check.** rank(T + N1) = rank T + dim N1 in all three cases: 12/12, 48/48, 115/115.

**Step 5 (unique lowest invariant on N1).** The centre λ ∈ GL(V_e) acts on the table at the tail of e by λ and at the head by λ⁻¹, and trivially on the other tables. So every invariant has deg_{T_tail} = deg_{T_head} on each edge. Γ is connected, so all the vertex degrees are equal to some d, and the total degree is d|V|.

For d = 1 the invariant space is ⊗_e (V_e⊗V_e*)^{GL(V_e)} = ⊗_e C·tr. This is the line C·Z_Γ, where

  Z_Γ(T) = Σ_{labels} ∏_v T_v[labels at v]

is the OpenAI state sum Z_{Γ,(n_e)} with independent vertex tables. There is nothing in degrees 1..|V|−1. The argument is characteristic-free, which proves Cor. O′.

**Step 6 (transfer).** By M2 Thm 1 (Luna completion), every generating set {g_i} of C[U]^G contains g with [g(w0 + n1)]_{|V|} = λZ_Γ(n1), with λ ≠ 0. So L̄(Z_Γ) ≤ 3(|V|+1)²·(L̄(g) + 2·dim U·(dim N1 + 1)).

**Step 7 (hardness of Z_Γ).**
1. Zeroing the labels > n² is a projection from Z_{Γ,(n_e)} to Z_{Γ,n²}.
2. OpenAI's Lemma "projection to a minor", with b = ⌊Δ(grid)/2⌋ = 2 and q² ≤ n², gives Z_{grid_r, q} as a projection of Z_{Γ,n²}, using only variables, 0 and 1, for r = Ω(L).
3. Take L = Θ(n) and q = r = n. OpenAI Thm 1.1 then gives L̄(Z_{grid_n, n}) ≥ n^{Ω((log n)^{1/12})}, in degree-component border complexity, which is exactly what step 6 produces.
4. With N = O(n⁴), this is N^{Ω((log N)^{1/12})}.

For succinct encodings, apply the argument to {C(·, y₀)}. ∎
