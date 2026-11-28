# Twisted quotients of group rings

The algebraic quotient construction is the claim proved here.

## 2. Theorem U4-A: twisted quotients of R[Γ]
**Setting.** Γ is one of the six dim-5 Bieberbach groups with a central holonomy involution c, dim Fix c = 3, and Γ/K ≅ P, where K = Z⁵ ∩ E₋(c) ≅ Z² (pquot: min.88.1.1.13, min.88.1.1.15, min.88.1.6.7, min.90.1.10.3, min.90.1.3.5, min.90.1.3.7).

**Lemma 1 [proved].** Let χ : K → R^× be a P-invariant character (R a domain). Then χ is ±1-valued. Moreover R[Γ]/(k − χ(k) : k ∈ K) ≅ R^{α_χ}[P], where α_χ ∈ H²(P; ±1) is the class of the central extension 1 → K/ker χ → Γ/ker χ → P → 1.
*Proof.* c acts on K by −1, so χ = χ∘c = χ⁻¹. The second statement is the standard description of R[E]/(ζ+1) for a central ζ of order 2. ∎

**Lemma 2 [proved].** H²(P; Z/2) = Ext(H₁P, Z/2) = (Z/2)², because H₂(P) = 0. A central Z/2-extension E of P has class 0 iff E_ab ≅ Z/4 × Z/4 × Z/2; otherwise E_ab contains an element of order 8. Aut(P) acts transitively on the three nonzero classes.
*Proof of transitivity [computational check of a proved fact].* The class mod 2 of g ∈ P is its holonomy image in C2². `hwnorm.cpp` finds 384 signed-permutation affinities normalising the K2 model of P. These include the cyclic coordinate permutation, which induces the 3-cycle a ↦ [ab], b ↦ [a], ab ↦ [b] on the nonzero classes, and hence a 3-cycle on the dual. ∎

**Computation** (`twistclass.cpp`: exact Smith normal form of a complete Reidemeister–Schreier presentation of Γ_ab plus the ker χ relations):

| Γ | Γ_ab | invariant χ ≠ 1 | E_ab | α_χ |
|---|---|---|---|---|
| min.88.1.1.15 (Δ) | Z/2·Z/4·Z/4 | (1,1) | Z/2·Z/4·Z/4 | 0 |
| min.88.1.6.7 | Z/4·Z/8 | (1,1) | Z/4·Z/8 (ord x1 = 8, x0x1 = 8) | **≠ 0** |
| min.90.1.10.3 (P-quotient via involution #3) | Z/4·Z/8 | (1,1) | Z/4·Z/8 (ord x0 = 8, x0x1 = 8) | **≠ 0** |
| min.90.1.3.7 (#3) | Z/2·Z/4·Z/4 | (1,1) | Z/2·Z/4·Z/4 | 0 |
| min.88.1.1.13 (contains P) | Z/2·Z/4·Z/4 | (1,1) | Z/2·Z/4·Z/4 | 0 |
| min.90.1.3.5 (contains P) | Z/2·Z/4·Z/4 | (1,1) | Z/2·Z/4·Z/4 | 0 |

Consistency checks: χ = 1 gives E_ab = Z/4² = H₁(P) in every case. HW itself (min.10.1.1.7) gives Γ_ab = Z/4². For min.90.x the second central involution (#2) has a torsion quotient, and there the Z/2 dies in E_ab, as expected when H₂ ≠ 0.

**Theorem U4-A [proved, given the SNF computation; 0.9].** For Γ = min.88.1.6.7 or min.90.1.10.3 and every commutative ring R there is a surjection R[Γ] ↠ R^ω[P], where ω = λ*e·μ*e is Gardam's class (K4 T1). Hence:
- Z[Γ] ↠ Z^ω[P]. The target contains Gardam's integral ±1 unit ᾱ (K4 T1), and Z[ζ8][Γ] ↠ Z[ζ8][P] carries it to Gardam's C-unit.
- For char R ≠ 2, R[Γ/ker χ] ≅ R[P] × R^ω[P] when 2 ∈ R^×.

For Δ and min.90.1.3.7, R[Γ] has two untwisted quotients R[P] (χ = 1 and χ₀) and no twisted one.
- *Meaning.* Lifting ᾱ to Q[Γ] is a well-posed target for a non-trivial **Q-unit in a torsion-free group**. It is untouched by K1's gauge no-go N1 (this is a quotient, not a gauge map) and by K4's N2 (the kernel is non-central: c acts by −1, and no fibre-product-with-Z argument applies).

**Proposition U4-B (2-adic congruence) [proved, 0.9].** Let E = Γ/ker χ₀ with ζ the central involution. Then Z_(2)[E] ≅ {(x,y) ∈ Z_(2)[P] × Z_(2)^ω[P] : x ≡ y mod 2}, using Z[C2] = {(a,b) : a ≡ b mod 2}.
- So if u ∈ Z_(2)[Γ] is a unit whose twisted image u₂ reduces to a non-trivial unit of F_2[P], then its untwisted image u₁ is a non-trivial unit of Z_(2)[P] ⊂ Q[P] with ū₁ = ū₂.
- In particular, an integral lift of Gardam's ᾱ to Z[Γ] would yield a Z[P]-unit ≡ Gardam's F_2-unit mod 2. That is Higman's question for P itself, and Tabei finds none in B(4).
- Honest weight: the implication "unit of Z_(2)[Γ] nontrivial mod 2 ⇒ unit of Z_(2)[P]" is immediate from Γ ↠ P. What the congruence adds is that the twisted side gives nothing extra integrally. **Over Z or Z_(2) the Γ-route is no easier than Z[P]; over Q it is a new route.**

**Corollary U4-B′ [proved from K4 C1, 0.9].** There is no pair of monomial ±1 lifts (ũ on S, ṽ on T) of Gardam's (ᾱ, β̄) with ũṽ = 1 in Z[Γ], for **any** Γ ↠ P. The reason: the untwisted image would be a ±1 pattern on S with rational inverse on T in Q[P], and K4 found 0 such patterns in class c = 0.
