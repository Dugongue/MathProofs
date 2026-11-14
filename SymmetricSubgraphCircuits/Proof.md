# Grochow–Jacob Open Question 1.11: negative answer for symmetric circuits

**Status.** Informal proof. Publication priority has not been established.

**The question.** Grochow–Jacob, *GCT and Graph Isomorphism* (arXiv:2606.26244), Open Question 1.11:

> "Can S_H be computed symbolically by (symmetric) algebraic circuits of size f(H)|G|^{O(tw(H))}?"

Here S_H is the invariant polynomial counting H-subgraphs. Their context:
- Dawar–Pago–Seppelt give symmetric circuits of size n^{O(hdtw(H))}.
- Alon–Yuster–Zwick color coding gives time f(H)|G|^{O(tw(H))}, but that algorithm is not symmetric.

## Theorem

**No.** There is no constant C such that, for every graph H, S_H has symmetric algebraic circuits of size f(H)·n^{C·tw(H)}.

More precisely, for connected H, every family of symmetric algebraic circuits computing S_H on n-vertex graphs has size n^{Ω(hdtw(H))}. With Dawar–Pago–Seppelt, the **symmetric circuit complexity of S_H is n^{Θ(hdtw(H))}**. For paths P_L, tw(P_L) = 1 while hdtw(P_L) ≥ √(2L) − 1.

## Proof

**Three inputs.**
1. **Grochow–Jacob Cor. 5.12.** For constant ε and k ≤ n^{1−ε}, invariants computed by symmetric algebraic circuits of size n^{O(k)} are simulated by O(k/ε)-WL. Contrapositive: such an invariant takes equal values on O(k/ε)-WL-equivalent graphs.
2. **Neuen (2024).** The H-subgraph count is k-WL-invariant **iff** k ≥ hdtw(H), where hdtw(H) = max{tw(F) : F ∈ spasm(H)} is the hereditary treewidth.
3. **Curticapean–Dell–Marx.** sub(H, ·) = Σ_{F ∈ spasm(H)} c_F hom(F, ·), with every c_F ≠ 0. This is why hdtw is the right parameter.

**Step 1: lower bound.**
- Suppose symmetric circuits of size s(n) ≤ n^{k} compute S_H for all large n.
- By Cor. 5.12 (ε = 1/2, H fixed, n large), S_H is k′-WL-invariant on n-vertex graphs, with k′ = O(k).
- Suppose k′ < hdtw(H). Neuen gives graphs G, G′ that are k′-WL-equivalent with sub(H, G) ≠ sub(H, G′).
- **Padding.** Add the same number of isolated vertices to both. This keeps them k′-WL-equivalent and keeps the H-counts unchanged, since H is connected. So such pairs exist on n vertices for all large n, which contradicts invariance.
- Hence hdtw(H) ≤ k′ = O(k), i.e. s(n) ≥ n^{Ω(hdtw(H))}.

**Step 2: paths have small treewidth but large hereditary treewidth.**
- Let m be odd and L = m(m−1)/2. K_m is Eulerian, so it has a trail v₀v₁…v_L using every edge exactly once.
- Map vertex i of P_L to v_i. Consecutive path vertices go to distinct vertices, so every identified pair is non-adjacent in P_L. The quotient simple graph has edge set {v_{i−1}v_i} = E(K_m).
- So K_m ∈ spasm(P_L), and hdtw(P_L) ≥ tw(K_m) = m − 1 ≥ √(2L) − 1.
- But tw(P_L) = 1.

**Step 3: conclusion.**
- If f(H)·n^{C·tw(H)} symmetric circuits existed, then for H = P_L the size would be f(L)·n^{C} ≤ n^{C+1} for large n.
- Step 1 would then give √(2L) − 1 ≤ hdtw(P_L) = O(C + 1) for all L, which is false. ∎

**Smallest instance.** P₃ (3 edges): merging its endpoints gives K₃. So tw = 1 while hdtw ≥ 2, already a gap.


This answers the symmetric-circuit version in the characteristic-zero setting. The unrestricted-circuit version remains open. Related lower bounds for matrix-symmetric circuits appear in [Dawar–Pago–Seppelt](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2026.46). The Weisfeiler–Leman threshold is from [Neuen](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2024.53). [Original question and simulation theorem](https://arxiv.org/html/2606.26244v2)
