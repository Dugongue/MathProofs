# The silver covering upper bound

The conversion to sum-of-squares bounds has the field restrictions stated in the proof. The exact exponential rate remains open.

## 0. Reformulation (used throughout)

Let t = 2m+1. Even([t]) with b(A,B) = |A∩B| mod 2 is a nondegenerate alternating space F₂^{2m}, i.e. the m-qubit Pauli group modulo phases, and "even intersection" means "commute".
- D(t) is the least dimension of unit vectors on Pauli strings such that distinct commuting strings are orthogonal. Over ℂ this is the symmetric minrank of that pattern.
- The automorphism group contains all of Sp(2m,2). H24 only used S_t ⊂ Sp. **That one observation is the source of the new upper bound.**
- For even t, D(t) ≤ D(t+1), because Even([t]) ⊂ Even([t+1]) with the same intersections.
- The Lovász theta of the symplectic SRG (k = 2^{2m−1}, eigenvalues ±2^{m−1}) is (4^m−1)/(2^m+1) = 2^m − 1. So PSD/theta methods only see 2^{t/2}.
  - Thm B (0.618) lies strictly beyond theta. It also covers real and Hermitian representations: a Hermitian representation of dimension D realifies to a real one of dimension 2D.

## 1. Theorem S (silver covering): D(t) ≤ 2^{(2−log₂(1+√2))t + O(log t)}

**Statement.** Over ℂ, or over any F as in H24 Lemma 9 (with an extra constant factor r), every t admits a t-parity representation of dimension

  D(t) ≤ 1 + ⌈(2^{t−1}/C(t,k))·ln 2^{t−1}⌉·C(t,k/2)

for every even k. Take k ≈ (1 − 1/√2)t. Then log₂D(t) ≤ (2 − log₂(1+√2))t + O(log t) = 0.728447t + O(log t).

**Proof** (t odd; for even t use monotonicity).
1. **The slice.** Let S = the k-subsets of [t], with k even, so S ⊂ Even([t]) \ {∅}.
   - H24 Lemma 9 gives ψ: S → ℂ^{C(t,k/2)} with ⟨ψA,ψA⟩ = 1 and ⟨ψA,ψB⟩ = 0 when A ≠ B and |A∩B| is even (k even).
   - The Gram matrix is g(|A∩B|) with g(x) = Π_{i even < k}(x−i)/Π_{i even<k}(k−i).
2. **Images.** For g ∈ Sp(Even([t]), b), the map ψ_g(v) := ψ(g⁻¹v) on g(S) satisfies the same constraints, because b(g⁻¹v, g⁻¹w) = b(v,w).
   - Concretely, products of transvections T_u(x) = x + b(x,u)u preserve b, since b(u,u) = 0.
3. **Covering.** Sp acts transitively on nonzero vectors (Witt). So for uniformly random g, P(v ∈ g(S)) = |S|/(2^{t−1}−1) for every v ≠ 0.
   - N = ⌈(2^{t−1}/|S|)·ln 2^{t−1}⌉ + 1 random images cover Even([t]) \ {∅} with positive probability (union bound).
4. **Assemble.** Assign each v to the first image that covers it, and give each image its own orthogonal block. Pairs in different blocks are orthogonal. Pairs inside a block satisfy the constraints by step 2. Give ∅ its own coordinate.
   - So D ≤ N·C(t,k/2) + 1.
5. **Optimise.** log₂D = t[1 − H(κ) + H(κ/2)] + O(log t). Setting d/dκ = 0 gives 2κ² − 4κ + 1 = 0, so κ* = 1 − 1/√2.
   - With L = log₂(1+√2) one has log₂κ* = −L − ½, log₂(κ*/2) = −L − 3/2 and log₂(1 − κ*/2) = L − 3/2.
   - Hence H(κ*) = κ*(L+½) + 1/(2√2) and H(κ*/2) = κ*L − L + 3/2.
   - So H(κ*) − H(κ*/2) = L − 1 exactly. silver.cpp confirms 0.271553303 for both sides. ∎

**K3 checks.**
- Lemma 9 slice Gram matrices: 0 constraint violations, and the numerical rank equals C(t,k/2) for t ≤ 11 and all even k.
- Explicit greedy coverings by random transvection products were built for t = 7…17. N is about (|E|/|S|)·ln|E|.
- Asymptotics: the covering bound beats H24's slice maximum from t ≈ 100 onward (0.7328 against 0.8069 at t = 1600, tending to 0.7284 against 0.8113). For small t the log factor loses.

**Corollaries.**
- **S1. The middle slice is the whole problem.** D(t/2,t) ≤ D(t) ≤ 2^{(1−H(1/2))t}·D(t/2,t)·poly = D(t/2,t)·poly. So D(t) ≍ D(t/2,t), and every (k,t)-parity representation has D(k,t) ≤ D(t) ≤ 2^{0.7284t}.
  - Odd k (t odd) embeds into Even([t]) by complement, since |A^c∩B^c| ≡ |A∩B| + 1.
  - At κ = ½ this beats Lemma 9's 2^{H(1/4)t}.
- **S2. σ(n,n²) ≤ n^{5−2L+o(1)} = n^{2.4569}.** Two routes give the same number:
  - H24 Thm 11 with this D(t) and t = 2log₂n;
  - or, elementarily, Thm 11 at κ* plus subadditivity (H24 (2)) over n^{2−2H(κ*)} blocks.
  - In general σ(n,n^α) ≤ n^{α + 3 − 2L + o(1)} = n^{α+0.4569} for α ≥ 2H(κ*) = 1.745. The R-C3 check compared against 1 + 2H(1/4) = 2.62 at α = 2 and missed this.
- **Not improved:** σ(n,n) stays at 1.615. The needed family has only n = 2^{t/2} members, and sub-universe coverings do not help at H(κ) = ½ (checked: g(x)/x is decreasing).
- **Prior art (K0).**
  - H24, TR24-026r1, ITCS'26 (Rossman–Zhu, arXiv 2512.01227: PT-rank ≤ n^{0.81d}) and arXiv 2605.00590 (Zhang–Zhu, [12,12,18]) all still quote 0.81/1.62. None uses Sp-symmetry.
  - Possible spin-off, not checked: PT-rank(I_{n^d}) for odd d via unbalanced σ.
