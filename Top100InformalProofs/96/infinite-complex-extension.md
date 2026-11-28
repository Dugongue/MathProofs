# Extension over computable infinite complexes

The lower bounds are for the promised input classes in the construction. The sparse integer system reduction is written out in Lemma L.

## 1. Setting

Y is a simply connected finite simplicial complex, D ≥ 2.

An **instance** is a computable sequence of finite simplicial pairs (X_n, A_n), with X_n ⊆ X_{n+1}, A_n = A_{n+1} ∩ X_n, dim X_n ≤ D, together with simplicial maps f_n: A_n → Y that are compatible. Put X = ∪X_n, A = ∪A_n, f = ∪f_n. X is a countable simplicial complex with the weak topology. It is locally finite in all constructions below, but local finiteness is not needed for the upper bounds.

EXT^ω_D(Y) is the set of indices of instances for which f extends to a continuous map X → Y. The boldface version replaces "computable sequence" by "arbitrary sequence", coded as a point of Baire space.

## 2. Upper bound

**Lemma 1.** Let E_n be the set of homotopy classes rel A_n of extensions of f_n over X_n, with restriction maps E_{n+1} → E_n. Then f extends over X iff lim E_n ≠ ∅.

*Proof.* (⇒) Restrict. (⇐) Take representatives g_n with g_{n+1}|X_n ≃ g_n rel A_n. Assume g′_n ≃ g_n rel A_n has been built. The homotopy from g_{n+1}|X_n to g′_n rel A_n, together with the stationary homotopy on A_{n+1}, is defined on X_n ∪ A_{n+1}; the two pieces agree on X_n ∩ A_{n+1} = A_n. By the homotopy extension property for the pair (X_{n+1}, X_n ∪ A_{n+1}) it extends, and its end is g′_{n+1} with g′_{n+1}|X_n = g′_n and g′_{n+1}|A_{n+1} = f_{n+1}. The union of the g′_n is continuous in the weak topology. ∎

**Theorem A.** EXT^ω_D(Y) is Σ¹₁.

*Proof.* By Lemma 1 and simplicial approximation, f extends iff there is a sequence (r_n, g_n, h_n), where g_n is a simplicial map from the r_n-th barycentric subdivision of X_n to Y whose restriction to A_n is a simplicial approximation of f_n in the contiguity class of f_n, and h_n is a simplicial homotopy, on a subdivision of X_n × I, between g_{n+1}|X_n and g_n, constant up to contiguity on A_n. The sequence is one element of Baire space and each condition is a finite check. ∎

## 3. Lemma L: infinite linear systems over ℤ

A *linear system* is a computable list of equations Σ a_i t_i = b with integer coefficients, finitely many unknowns per equation, countably many unknowns in total.

**Lemma L.** The set of indices of solvable (over ℤ) computable linear systems is Σ¹₁-complete. This holds for systems in which every equation has at most 3 unknowns and every unknown occurs in at most 3 equations.

*Proof.* Membership is clear. For hardness, reduce from the set of computable trees T ⊆ ω^{<ω} that have an infinite path, which is Σ¹₁-complete.

Put B_n = ∏_{l<n} 2^{l+1} = 2^{n(n+1)/2}, so B_0 = 1 and B_{n+1} = 2^{n+1}·B_n.

Unknowns: t_σ for σ ∈ T; u_{σ,n} and w_{σ,n} for σ ∈ T, n ∈ ω. Equations:

- (R) t_∅ = 1;
- (S) t_σ = u_{σ,0};
- (U) u_{σ,n} = t_{σ⌢n} + u_{σ,n+1}, where the term t_{σ⌢n} is omitted if σ⌢n ∉ T;
- (W) u_{σ,n} = w_{σ,n} − 2^{n+1}·w_{σ,n+1}.

Reading: u_{σ,n} is "the mass of σ not yet handed to the children 0, …, n−1". (W) says that the 2-adically convergent sum Σ_n u_{σ,n} B_n is an ordinary integer; indeed (W) for n < N gives

  w_{σ,0} = Σ_{n<N} u_{σ,n} B_n + B_N·w_{σ,N}.  (∗)

*T has an infinite path p ⇒ solvable.* Put t_σ = 1 if σ ⊂ p and 0 otherwise. For σ = p|k with p(k) = j put u_{σ,n} = 1 for n ≤ j and 0 for n > j; for σ off the path put u_{σ,n} = 0. Then (R), (S), (U) hold: for n < j, 1 = 0 + 1; for n = j, 1 = 1 + 0; for n > j, 0 = 0 + 0. Each sequence (u_{σ,n})_n has finite support, so w_{σ,n} = Σ_{i≥n} u_{σ,i}·B_i/B_n is a finite sum of integers, and w_{σ,n} − 2^{n+1}w_{σ,n+1} = u_{σ,n} because B_{n+1} = 2^{n+1}B_n.

*T well-founded ⇒ unsolvable.* Suppose an integer solution exists. We show t_σ = 0 for every σ ∈ T by induction on the rank of σ in the well-founded tree; this contradicts (R). Let σ be such that t_{σ⌢n} = 0 for every child (vacuous for leaves). By (U), u_{σ,n} = u_{σ,n+1} for all n, so u_{σ,n} = c for all n, and c = t_σ by (S). By (∗), w_{σ,0} ≡ c·Σ_{n<N} B_n modulo B_N for every N, so w_{σ,0} = c·β in ℤ₂, where β = Σ_{n≥0} 2^{n(n+1)/2}. The binary digits of β are 1 exactly at the triangular positions 0, 1, 3, 6, 10, …; they are not eventually periodic, so β is irrational. If c ≠ 0 then β = w_{σ,0}/c is rational. Hence c = 0.

Counting occurrences: t_σ occurs in (S) for σ and in one equation (U) of its parent; u_{σ,n} occurs in (U) for n and n−1 (or (S)) and in (W) for n; w_{σ,n} occurs in (W) for n and n−1. The map T ↦ system is computable. ∎

**Remarks.**
1. The same proof gives boldface Σ¹₁-completeness: the set of solvable systems is not Borel.
2. For a *fixed* row-finite matrix M the set {b : Mt = b solvable} is Borel (a continuous injective image of a Polish group modulo a closed kernel). Lemma L says that the Borel rank is unbounded as M varies. In the language of Bergfalk–Lupini–Panagiotopoulos and Casarosa–Lupini this is the existence of phantom classes of every countable order in lim¹ of towers of finitely generated free abelian groups, equivalently in Ext(F, ℤ) for countable torsion-free F.
3. Algebraic form: for a computable countable torsion-free abelian group E with a distinguished element e, "there is a homomorphism φ: E → ℤ with φ(e) = 1" is Σ¹₁-complete. Equivalently: "does a given extension 0 → ℤ → E → F → 0 split" is Σ¹₁-complete. (By Stein's theorem "every extension of F by ℤ splits" is the Borel property "F is free".)
4. The naive gadget "u_{σ,n} divisible by n!" is unsound (the intended solution has u = 1 for small n), and "Σ u_n p^n ∈ ℤ for one prime p" is unsound (the constant sequence gives −c/(p−1)). A lacunary base is what excludes exactly the constant sequences.

## 4. Theorem B: any infinite homotopy group gives Σ¹₁

**Theorem B.** Let Y be a simply connected finite complex and suppose π_m(Y) is infinite for some 2 ≤ m ≤ D−1. Then EXT^ω_D(Y) is Σ¹₁-complete. The instances are locally finite, of dimension m+1, of the form X = A ∨ ⋁_i S^m_i ∪ ⋃_q e^{m+1}_q with A a wedge of m-spheres.

*Proof.* Membership is Theorem A. Let g ∈ π_m(Y) have infinite order and let λ: π_m(Y) → ℤ be a homomorphism with λ(g) = N ≠ 0.

Given a linear system S as in Lemma L, build X_S:
- A is a wedge of m-spheres a_q, one for each equation with nonzero right-hand side, and f maps each by a fixed simplicial representative of g;
- one sphere S^m_i for each unknown t_i;
- for each equation Σ a_i t_i = b, one (m+1)-cell attached along Σ a_i s_i − b·a_q ∈ π_m(A ∨ ⋁S^m_i). This group is free abelian on the spheres because m ≥ 2.

Each cell meets at most 4 spheres and each sphere at most 3 cells, so X_S is locally finite; it is computable from S (degree-a maps of spheres have triangulations of size O(log|a|), CKMVW 2014 §6, but for the present purpose any computable triangulation will do).

A map X′ = A ∨ ⋁S^m_i → Y extending f is, up to homotopy rel A, a choice of classes v_i ∈ π_m(Y) (Y is simply connected). It extends over the cell of an equation iff Σ a_i v_i = b·g in π_m(Y). The cells are attached to X′ only, so f extends over X_S iff the system S has a solution in π_m(Y) with right-hand sides b·g.

Apply this to the system S_T of Lemma L.
- If T has a path, the integer solution (t, u, w) gives the solution (t·g, u·g, w·g) in π_m(Y).
- If T is well-founded and (v_i) is a solution in π_m(Y), then (λ(v_i)) is an integer solution of the system with right-hand side N in (R) and 0 elsewhere. The induction in Lemma L does not use (R) and shows that all t_σ vanish, contradicting t_∅ = N ≠ 0.

So T ↦ X_{S_T} reduces ill-foundedness to EXT^ω_{m+1}(Y). ∎

**Corollary B1.** For every n ≥ 2, EXT^ω(Sⁿ) is Σ¹₁-complete at dimension n+1. For finite pairs EXT_{n+1}(Sⁿ) is in P (the stable range). So is EXT^ω for S³, S⁷ and every simply connected compact Lie group, which are in P for finite pairs in all dimensions.

**Corollary B2 (cohomological form).** For computable countable CW pairs (X, A) of dimension m+1 and a class α ∈ H^m(A; ℤ), "α is the restriction of a class of H^m(X; ℤ)" is Σ¹₁-complete. Equivalently, vanishing of a class in H^{m+1}(X, A; ℤ) given by a computable cocycle is Σ¹₁-complete. This holds for m = 1 as well (target S¹: the same construction with 2-cells attached along words, since π₁(S¹) is abelian).

## 5. Theorem C: finite homotopy gives Π⁰₁

**Theorem C.** Let π_m(Y) be finite for all m ≤ D−1 and let P_{D−1}Y be non-contractible. Then EXT^ω_D(Y) is Π⁰₁-complete, and f extends over X iff it extends over every X_n. If P_{D−1}Y is contractible, every instance is a YES instance.

*Proof.* Let W = Y ∪ (cells of dimension ≥ D+1) be a model of P_{D−1}Y, and let E_n be the set of homotopy classes rel A_n of extensions over X_n into W.

- E_n is finite: the classes are counted by successive choices in the finite groups H^i(X_n, A_n; π_i(Y)), i ≤ D−1.
- So lim E_n ≠ ∅ iff every E_n ≠ ∅ (an inverse limit of non-empty finite sets is non-empty).
- By Lemma 1 (applied to W), lim E_n ≠ ∅ iff f extends to a map X → W. As dim X ≤ D, cellular approximation rel A compresses such a map into Y.
- E_n ≠ ∅ iff f_n extends over X_n into Y, by the same compression. This is decidable (all groups finite: E. H. Brown 1957; or thm:NP).

So EXT^ω_D(Y) = {instances : ∀n f_n extends over X_n} is Π⁰₁.

Hardness. Some π_m(Y) ≠ 0 with m ≤ D−1; let g ≠ 0 in it. Given a Turing machine M, let A = ⋁_n S^m_n with f = g on each sphere, and attach an (m+1)-cell to S^m_n by the identity iff M halts in exactly n steps. Then f extends iff M does not halt.

If P_{D−1}Y is contractible, Y is (D−1)-connected and every obstruction group H^{i+1}(X, A; π_i(Y)), i ≥ D, vanishes on pairs of dimension ≤ D; for infinite X this is still cellular: extend cell by cell. ∎

## 6. The classification

**Theorem (phantom dichotomy).** Let Y be a simply connected finite complex and D ≥ 2. On computable countable pairs of dimension ≤ D:

| Condition on P_{D−1}Y | EXT^ω_D(Y) | EXT_D(Y) on finite pairs (#1) |
|---|---|---|
| contractible | trivial | trivial |
| non-contractible, rationally trivial (all π_m finite, m ≤ D−1) | Π⁰₁-complete; compactness holds | P or NP-complete |
| not rationally trivial (some π_m infinite) | Σ¹₁-complete | P, NP-complete or Σ⁰₁-complete |

Boldface: the set of extendable instances is closed in the first non-trivial case and Σ¹₁-complete, hence not Borel, in the second.

Consequences worth stating.
1. **The rungs of #1 are a finiteness phenomenon.** On infinite complexes S³ (P), S⁵ (NP-complete from D = 10) and S² (Σ⁰₁ from D = 4) are all Σ¹₁-complete from the first stage on; Moore spaces M(ℤ/p, n) (NP-complete on finite pairs from D = 2n or 2n+1) are Π⁰₁.
2. **The criterion changes from "rational H-space" to "rationally trivial".** The source of hardness is not nonlinearity but lim¹: ℤ is not algebraically compact.
3. **Compactness of extendability** ("f extends iff it extends over every finite subcomplex") holds exactly for the rationally trivial targets. This is the homotopy-theoretic analogue of the fact that compactness for infinite CSPs holds for finite templates.
