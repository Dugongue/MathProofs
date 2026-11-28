# Filtered deformations in the stated class-three nilpotent families

The Lie-algebra isomorphism reduction uses Grochow–Qiao [Theorem A(4b)](https://arxiv.org/abs/1907.00309). These arguments cover the displayed SBE-class construction and the central-extension result.

## S1. Theorem SBE-3: classification of the entire SBE class of G_{3,n,m}

**Statement.** Let m ≥ 2 and n ≥ 0. Simply connected nilpotent Lie groups whose associated Carnot algebra is g_{3,n,m} (equivalently, by Pansu and Cornulier, the full SBE class of G_{3,n,m}) correspond bijectively to orbits of
- the parabolic group P_V = Stab_{GL(W)}(V), times ℝ^×,
- acting on Ψ ∈ Hom(Λ²W, W/V) by Ψ ↦ a²·B̄∘Ψ∘(L^{-1}∧L^{-1}), where L ∈ P_V and B̄ is the map L induces on W/V ≅ E.

The algebra n_Ψ is the vector space g with
- [e, f] = Df and [e, Df] = D²f;
- [w, w′] = D²Ψ(w, w′) for w, w′ ∈ W.

**Proof.**
1. **Normal form.** Any n with gr(n) ≅ g is μ₀ + μ₊, where μ₊ raises the filtration degree. For c = 3 the only possible term is μ₊ : Λ²g₁ → g₃ = D²E. Every other raising term lands in g_{≥4} = 0.
2. **Jacobi is automatic.** For every triple, Jac(μ₀ + μ₊) = Jac(μ₀). The values of μ₊ are central, and g₂ × g₁ → g₄ = 0.
3. **The e-components can be removed.**
   - Write the filtered automorphism as id + φ, with φ₁ = (u, α, β) : g₁ → g₂ and φ₂ = γ : g₂ → g₃.
   - This shifts ψ_{eV} by α and ψ_{eE} by β − γ, so both can be removed.
   - It leaves ψ_{VV} = j, ψ_{VE} = k and ψ_{EE} = ℓ unchanged. Quadratic terms land in g₄ = 0.
4. **Graded automorphisms of g.**
   - V is the degree-1 part of the centre, so L preserves it.
   - V ⊕ E is the set of elements whose ad has rank ≤ 1 (this uses m ≥ 2), so L preserves it too.
   - Hence L(e) = ae + v₀ + f₀, L|_V = A, and L(f) = Bf + Cf with C : E → V. The induced maps are L₂ = aB on DE and L₃ = a²B on D²E.
   - Transporting Ψ by L gives exactly the action stated above.
5. **Isomorphisms.** Every isomorphism preserves the lower central series and factors as a graded L followed by a filtered unipotent map. ∎

**Numerical check.** The predicted isomorphism (j, 0, 0) ~ (j, −j(·, C·), j(C·, C·)) gives identical Betti numbers, cup-rank tables and extension invariant (iso_test.txt).

**Corollaries.**
- **(a) n = 0.** The SBE class of H_{3,m} (dimension 1 + 3m) is classified by isomorphism classes of m-dimensional anticommutative algebras (E, ψ), with no Jacobi condition on ψ.
  - Hence isomorphism, and commensurability over ℚ, **across one entire SBE class** is TI-complete. Hardness: take ψ to be the bracket of the Grochow–Qiao hard class-2 Lie algebras. Membership: algebra isomorphism ≤ TI, also by Grochow–Qiao. *Cite-check pending: the exact Grochow–Qiao theorem number for anticommutative algebras.*
  - Theorem H gave TI-hardness only on a subfamily.
- **(b) Counting.** The SBE class of H_{3,2} (dim 7) has exactly 2 isomorphism classes: ψ = 0, or ψ(f₁, f₂) = u ≠ 0.
  - The SBE class of H_{3,3} (dim 10) has continuum many. The family is ψ ↔ a bilinear form B up to twisted congruence, with modulus the spectrum {1, e^{±iθ}} of the cosquare. Explicit family: B_t = [[1, t, 0], [−t, 1, 0], [0, 0, 1]].
  - This lowers the continuum dimension from 16 (AMANN-COUNTING (C)) to 10, but **without** distinct cohomology rings (see S2). So it does **not** strengthen the Amann answer.
- **(c) Sauer sees the j-shadow of every Ψ.** For every Ψ, N₃ ∩ e*∧Λ²H¹ = e* ∧ (S_Ψ + W*∧E*), by the same weight argument as Lemma 3: w(e) = 1, w(W) = 2, w(DE) = 3, w(D²E) = 4, and d is homogeneous for every Ψ.
  - So the real cohomology ring determines the GL(V)-class of the matrix space span{Ψ_a|_{Λ²V}} ⊂ Λ²V*, and nothing about k or ℓ through this channel.

## S3. Proposition P: no class-(c+1) central extension, giving a p_ME window

**Statement.** For c ≥ 3, if j(Λ²V) spans E, then n_j has no central extension of class c + 1. The Carnot algebra g_{c,n,m} does have one, via ω = e* ∧ (D^{c−1}f₁)*.

**Proof.**
1. Let ω be a 2-cocycle. A class-(c+1) extension needs ω(n, C^c) ≠ 0, where C^c = D^{c−1}E. Coboundaries vanish on n × C^c, because C^c is central.
2. For x, y ∈ V and any z: dω(x, y, z) = −ω(D^{c−1}j(x, y), z) + ω([x,z], y) − ω([y,z], x).
3. First, ω(D^{c−1}f, v) = 0 for every v ∈ V: dω(e, D^{c−2}f, v) = −ω(D^{c−1}f, v), because [e, v] = 0 and [D^{c−2}f, v] = 0 (c ≥ 3).
4. For z ∉ V we have [x, z] = [y, z] = 0, so (2) gives ω(D^{c−1}j(x,y), z) = 0. Together with (3) and the surjectivity of j, ω(D^{c−1}E, ·) = 0 on e, on V and on every D^bE. ∎

**C++ check.** The extension rank is 3 for j = 0 and 0 for surjective j (n = 3, m = 2).

**Corollary (with DLT 2505.17865, Thm 1.13 with s = c + 1, and Thm 1.11).** For every surjective j:
- c/2 ≤ p_ME(Γ_j, Γ₀) ≤ c + 1;
- this holds on a TI-complete continuum, sharpening Theorem ME to a bounded window.

DLT proved such windows only for G_{m,n} (their Cor 1.14–1.15). The obstruction cannot separate Γ_j from Γ_{j′}: both lack the extension. That case is DLT Q10.3 and Q10.4 territory and stays open.

---
