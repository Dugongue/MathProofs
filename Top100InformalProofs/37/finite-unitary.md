# Unitary tensor isomorphism in fixed finite characteristic

The reduction uses the stated fixed-characteristic input model, the FGS ring reduction and the split-Levi construction.

## Theorem U

Let q = p^a, let K = F_{q²}, and take U = U_n(K) for the standard Hermitian form. For each of the five CGQTZ actions (i)–(v):
1. **U-TI(K) ≤ TI(F_p)** in time poly(n, a), for every q.
2. **U-TI(K) ≤ TI(K)** in time poly((na)^p). This is polynomial for each fixed characteristic p, in particular for each fixed finite field.
3. **TI(K) ≤ U-TI(K)**, linear size, every q.

Hence **TI_U = TI over F_{q²} for every q of fixed characteristic.** This answers the finite-field sentence of Q7.3 and the U-part of Q7.1 over finite fields. Together with TI_O = TI and TI_Sp = TI over finite fields (09-15 Lean `ti_eq_tisp`; CGQTZ Theorem 1.10 for membership), all three classical families equal TI over finite fields.

### Proof

**Part 1 (restriction of scalars, which makes the Galois twist linear).** View each mode space V (dimension n over K) as an F_p-space V_res of dimension 2an. Build the following representation over F_p:
- the operator A (multiplication by a generator α of K) on each V_res;
- the F_p-bilinear form t_H = Tr_{K/F_p} ∘ H on each V_res, where H is the Hermitian form;
- the trilinear form Tr_{K/F_p} ∘ T. Modes acted on by P^{−t} become dual spaces, i.e. reversed arrows.

Correctness:
- F_p-linear maps commuting with A are exactly the K-linear maps.
- For K-linear g, D(x,y) := H(gx,gy) − H(x,y) is sesquilinear, and Tr(λD) = Tr(D(x,λy)) = 0 for all λ. The trace form is nondegenerate, so D = 0. Hence preserving t_H is equivalent to g ∈ U.
- The same trace argument handles the tensor.

This is a fixed bipartite graph with arity ≤ 3, so FGS (arbitrary field) gives 3TI over F_p of size poly(n·a). The Frobenius x ↦ x^q is F_p-linear, so no conjugation needs to be forced at all.

**Part 2.** Compose Part 1 with Theorem F (Φ): TI(F_p) ≤ TI(F_{q²}). The Frobenius-marker ladder ι : V → Sym^p V pins GL(F_p) inside GL(F_{q²}).

**Part 3 (Theorem S).** Over a finite field, every nondegenerate Hermitian form of dimension 2m is hyperbolic. In a hyperbolic basis, H = [[0, I],[I, 0]], and diag(g, (ḡ^T)^{−1}) is unitary for every g ∈ GL_m(K). So U_{2m} has a GL_m-Levi section, and `LeviHardness.lean` gives X_GL ≤ X_U linearly for all five actions.
- The Lean actions use the linear dual P^{−t}, matching CGQTZ's definitions.
- Transporting the standard form to hyperbolic form needs one element c with c^{q+1} = −1. That is randomized poly(log q), and trivial if instances may carry their form. ∎

**Corollary over ℂ.** Part 1 with ℂ/ℝ in place of K/F_p gives **TI_U(ℂ) ≤ TI(ℝ)** in a few lines. Lysikov–Walter's TI_U(ℂ) ≤ TI(ℂ) uses Kempf–Ness. The two statements are incomparable: different target fields, and TI(ℝ) ≤ TI(ℂ) is open.
