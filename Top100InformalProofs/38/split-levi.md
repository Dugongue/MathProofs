# A hardness theorem for actions with a split GL section

This is the informal argument accompanying the public Levi hardness formalization.

## 1. Hypothesis

Let F be a field and G = (G_n) a family of subgroups of GL_n(F).

**Definition (GL-Levi section).** G admits a *polynomial GL-Levi section* if, for every m, one can compute in time poly(m):
- a size n = n(m) ≤ poly(m), and
- a matrix C_m ∈ GL_n(F), whose first m columns span U and whose remaining columns span U′.

These must satisfy:

> (Lev) for every g ∈ GL(U) there is P ∈ G_n with P(U) = U, P(U′) = U′ and P|_U = g.

The weaker condition (Lev⁻) drops the requirement P(U′) = U′. It suffices for actions (i), (ii) and (v).

Two remarks on (Lev):
- No homomorphism g ↦ P is required, and nothing is required of P on U′.
- In the adapted basis, (Lev) says C^{-1} G_n C contains, for each g, an element of the form diag(g, ∗). (Lev⁻) says it contains an element of the form [[g, ∗], [0, ∗]].

## 2. Theorem

**Theorem S (split-rank hardness).** Suppose G admits a polynomial GL-Levi section. Then for each of the five actions X ∈ {(i), (ii), (iii), (iv), (v)} of CGQTZ Definition 1.6:

  X_GL ≤ X_G,

by a map that is linear in the input array, with output side n(m). Consequently

  **TI ≤ X_G for all five actions, over F.**

This uses Grochow–Qiao 2023 Theorem A, which gives TI ≤ X_GL over arbitrary fields. For actions (i), (ii) and (v), condition (Lev⁻) suffices.

### 2.1 Construction

Write ι(x) := C·(x, 0) ∈ F^n for x ∈ F^m, and ι*(y) := C^{-t}·(y, 0) for y ∈ F^m.

Put ι on every mode where P acts, and ι* on every mode where P^{-t} acts. The modes and their maps are:

| Action | Mode 1 | Mode 2 | Mode 3 |
|---|---|---|---|
| (i) | ι | ι | ι |
| (ii) | ι | ι | ι (separate family member) |
| (iii) | ι | ι* | ι (separate family member) |
| (iv) | ι | ι | ι* |
| (v) | ι | ι | ι |

The instance A ↦ Ã := (ι ⊗ · ⊗ ·)(A) is a linear coordinate embedding followed by a fixed change of basis.

**Key identity.** If P′ := C^{-1}PC = diag(g, φ), then
- P·ι(x) = ι(gx), and
- P^{-t}·ι*(y) = C^{-t} P′^{-t} (y, 0) = ι*(g^{-t} y).

### 2.2 Forward direction

An X_GL-transporter, built from g's, lifts by (Lev) to an X_G-transporter. The key identity shows that it sends Ã to B̃. For actions (i), (ii) and (v), only P·ι = ι∘g is used, and (Lev⁻) gives that.

### 2.3 Backward direction

**Support lemma.** Let C_i(T) be the image of the mode-i flattening. Then C_i((h₁,h₂,h₃)·T) = h_i·C_i(T), and T ∈ C₁(T) ⊗ C₂(T) ⊗ C₃(T). The supports of Ã lie in ι(F^m) or ι*(F^m), mode by mode.

**Dual-support extension lemma.** Let P ⊆ V and Q ⊆ V* be subspaces, with dim V = dim V′. Let f : P → P′ and h : Q → Q′ be isomorphisms with (hα)(fp) = α(p). Then some g ∈ GL(V, V′) has g|_P = f and g^{-T}|_Q = h.

*Proof.*
- Let E := Ann(Q) and E′ := Ann(Q′). Duality V/E ≅ Q* turns h into an isomorphism ḡ : V/E → V′/E′, characterized by (hα)(ḡ[v]) = α(v).
- The hypothesis says ḡ[p] = [fp]. So f maps P ∩ E onto P′ ∩ E′.
- Pick bases as follows: a basis of P ∩ E; a complement p_k of P ∩ E inside P; a completion e_j to a basis of E; and lifts v_l of a basis completion of V/E.
- Define g by: g := f on P ∩ E and on the p_k; g sends the e_j to a completion of f(P ∩ E) to a basis of E′; g sends v_l to any lift of ḡ[v_l].
- Then g is invertible, extends f, and induces ḡ. So (hα)(gv) = α(v), i.e. g^{-T}α = hα. ∎

**Recovering the GL-transporter.** Let t be an X_G-transporter with t·Ã = B̃, and P its G-component.

- **Modes where only P acts** (actions (i), (ii), (v), and modes 1–2 of (iv)):
  - P maps S := Σ_{those modes} C_i(Ã) ⊆ ι(F^m) injectively into Σ C_i(B̃) ⊆ ι(F^m).
  - Extend P|_S to g ∈ GL(ι(F^m)) ≅ GL_m.
  - Since Ã is supported on S in those modes, replacing P by g there does not change t·Ã.
- **Actions (iii) and (iv)** (modes acted on by both P and P^{-t}):
  - Identify ι*(F^m) = Ann(U′) with U* by restriction to U. This identification is valid because U ⊕ U′ = F^n.
  - Take f := P on the P-mode supports, which lie in U, and h := P^{-t} on the P^{-t}-mode supports, which lie in Ann(U′) by the support lemma.
  - The pairing condition (P^{-t}α)(Pp) = α(p) holds identically.
  - The extension lemma gives g ∈ GL(U) with g = P on the P-supports and g^{-t} = P^{-t} on the P^{-t}-supports. So (g, g^{-t}, …)·A = B.
- **Independent modes:** treat each family member separately in the same way.

Hence X_GL-isomorphism holds. ∎

## 3. Where (Lev) holds: the corollary table

| Family | Section (U, U′, P) | Hypothesis | Recovers |
|---|---|---|---|
| Sp_{2m} (any field, incl. char 2) | Lagrangian U, U′ = U*; P = diag(g, g^{-t}) | Lev | TIEqTISp.lean, Sp five actions |
| Isom(Ω), Ω ⊇ explicit hyperbolic block [[0, αI], [βI, 0]] ⊕ R | P = diag(g, g^{-t}, I_R) | Lev | FormTI.lean (all B_a(n) ⊕ W) |
| O(Q), Witt index ≥ m^ε, explicit isotropic basis | as above | Lev | Lane B5.2, OrthogonalTI.lean (finite fields, level ≤ 2, char 2) |
| U_n over F_{q²} (Hermitian) | isotropic U; P = diag(g, ḡ^{-t}) | Lev | finite-field unitary TI (MathProofsCrossovers) |
| SL_n | U = F^{n−1}, U′ = line; P = diag(g, det g^{-1}) | Lev | JouxNarayanan54.lean, TI ≤ TI_SL |
| Parabolic P_U (stabilizer of U) | Levi block | Lev | TIParStandalone.lean |
| Affine [[A, b], [0, 1]] | U = F^m, U′ = last coordinate | Lev | AffineTensorIsomorphism |
| O(p,q) with q ≥ m^ε (ℝ) | hyperbolic block of size 2m | Lev | Lane B5.2 |

## 4. Scope

**What the theorem does not need:**
- conciseness of the input;
- a homomorphic section;
- symmetry or invertibility of any form;
- any assumption on the field.

**What it does not give.**
- **Upper bounds X_G ≤ TI.** These are separate. They are known for form-preserving groups (CGQTZ Theorem 1.10), parabolic and affine groups (repo), and U over ℂ (Lysikov–Walter). They are **open for SL** (CGQTZ Q7.2).
- **Linear length.** For Lev families, n(m) = O(m) gives linear-length hardness, but the reverse direction still goes through Futorny–Grochow–Sergeichuk.
- **Groups without a large GL-Levi.** High split rank alone is not enough. For example, the block-diagonal SL₂^k ⊆ GL_{2k} has split rank k but no GL_m Levi acting on a big subspace. The correct invariant is the largest m with a GL_m-Levi acting by its standard representation. For classical groups this equals the Witt index, which is why "split rank" works as shorthand there.

**Converse side (§2 of the map).**
- Over ℝ and ℂ, continuous reductions to O(p,q) or U(p,q) need Witt index q ≥ c·log n / log log n. This is the BD_q theorem in [research manuscript].
- With Theorem S, the classical-group picture is:
  - Witt index ≥ m^ε: hard;
  - Witt index ≲ log n / log log n: no continuous reduction;
  - anything in between: open.
