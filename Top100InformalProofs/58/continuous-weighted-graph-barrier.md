# The continuous reduction obstruction for weighted graph isomorphism

The obstruction is for continuous kernel reductions with the stated graph-action topology.

## G3. No continuous reduction from TI to weighted GI (Lean)

**Theorem G3 (Lean).** Take:
- any nontrivially normed source field 𝕜 (ℝ, ℂ, ℚ_p, …);
- any nonempty tensor format;
- any number of vertices n;
- any Hausdorff space of weights.

Then no continuous map r from tensors to weighted adjacency matrices satisfies

  A ≅_GL B ⟺ r(A) and r(B) are isomorphic weighted graphs.

The Lean name is `ContinuousBarrier.no_continuous_reduction_TI_to_weightedGI`. It specializes the compact-target barrier to S_n with the discrete topology.

**Meaning.** Every TI → GI reduction over a topological field must be discontinuous, branching on zero or sign tests. Over finite fields the question is purely combinatorial.

## G4. Hypergraph states: the uniformity-3 jump

**Setting.** For a 3-uniform hypergraph H on [n], let f_H = Σ_{abc ∈ H} x_a x_b x_c over F₂, and let |H⟩ = D_{f_H}|+⟩^{⊗n} be the hypergraph state.

**Theorem G4.**
- **Equivalence.** |H⟩ and |H′⟩ are related by a circuit of CNOT, CZ and Z gates iff f_{H′} ≡ f_H ∘ A (mod RM(2, n)) for some A ∈ GL_n(F₂). This is iff the alternating trilinear forms ω_H and ω_{H′} are GL_n(F₂)-equivalent: ALTEQ over F₂.
- **Count.** The minimal number of CCZ gates in such a preparation circuit equals the alternating tensor rank rk_Λ(ω_H).

*Proof.*
1. A CNOT circuit P fixes |+⟩^{⊗n} and conjugates D_f to D_{f∘A}.
2. A diagonal Clifford gate is Z_q for some quadratic q.
3. Suppose Z_q P |H⟩ = |H′⟩. |+⟩^{⊗n} has full support, so the phase functions agree pointwise: f′ = f ∘ A + q.
4. The rest is CCZ-IS-TI, Theorems 1 and 2. ∎

**Consequences.**
- **Graph states (uniformity 2):** f is quadratic, so the same equivalence is trivial (all classes collapse), and LC-equivalence is in P (Bouchet).
- **Hypergraph states (uniformity 3):** the equivalence is ALTEQ over F₂. That is GI-hard, and TI-complete provided GQ's ALTEQ completeness holds in characteristic 2 (flagged in CCZ-IS-TI).
- So "equivalence of hypergraph states" jumps from trivial to TI-complete at uniformity 3.
- A polynomial-time canonical form would put TI over F₂, and hence GI, in P (HypoWorlds: HyperStateEqP ⇒ GIinP).
- The average-case hardness of ALTEQ over F₂ is equivalent to that of random hypergraph states (HW-16).
