# Hardness for a symmetric promise CSP outside three tractable classes

The reductions have a computer-assisted finite obstruction step. The corresponding formula and certificates are described in the verification notes.

## 1. R\*

R\* ⊆ [3]³ consists of the permutations of (0,0,1), (0,0,2) and (1,1,2). Equivalently, R\* is the set of triples in which the two smallest entries are equal and the maximum is strictly larger.

- R\* = LO₃ ∖ {rainbow triples}.
- On two colours the same definition gives LO₂ = 1-in-3, so R\* is the 3-colour analogue of 1-in-3 SAT.
- Each pair of colours carries a copy of 1-in-3: {0,1} via 001, {0,2} via 002, {1,2} via 112.
- Every proper sub-union of these orbits is in P: {001,002} has a fixed count, while {001,112} and {002,112} have a weighted count (s = 1).

The census found no other outside relation on three colours. On four colours there are 26 candidates (symR4.txt). Most contain R\* on three of the colours; {013,023,112} and {011,022,033,123} are new shapes.

## 2. The weighted-count class (correction to P1's T2 classes)

**Claim.** Suppose w : [c] → ℤ gives Σ_i w(t_i) = s for every t ∈ R, with s/r ∉ ℤ. Then PCSP(R, NAE_r[2]) is in P.

**Proof.**
1. Solve the system Σ_{v ∈ e} y_v = s over ℤ (AIP).
2. Round y ↦ [y ≥ θ] with θ the integer in (s/r, s/r + 1).
3. All entries ≥ θ would force a sum ≥ rθ > s. All entries ≤ θ − 1 would force a sum ≤ r(θ−1) < s. So no edge is monochromatic. ∎

Lemma B.2 is the case w = 1_C, s = k.

## 3. Why no standard algorithm solves (R\*, NAE₃[q])

**(a) Affine relaxations.** Suppose h : [3] → G maps R\* into {x+y+z = s} for an abelian group G.
- From 2h(0)+h(1) = 2h(0)+h(2) we get h(1) = h(2).
- From 2h(0)+h(1) = 3h(1) we get 2(h(0)−h(1)) = 0.
- So s = 3h(1), and the constant triple (h(1),h(1),h(1)) satisfies the equation. Every rounding then makes it monochromatic.

**(b) AIP, i.e. alternating ternary f with f(x,y,z) = f(z,y,x) and f(x,y,y) = f(x,z,z) = g(x).** Take the matrix with columns (1,2,1), (0,2,0), (0,1,0), all in R\*.
- Its rows are (1,0,0), (2,2,1), (1,0,0).
- They evaluate to g(1), g(1), g(1): monochromatic.

**(c) BLP.** Look for 3×n matrices with columns in R\* whose three rows have equal colour multisets.
- n = 3: columns 001, 010, 100.
- n = 4: columns (2,1,1), (0,2,0), (0,0,2), (1,0,0). Every row is the multiset {0,0,1,2}.
- So every n ≥ 6 works, and so do n = 3, 4. A symmetric polymorphism of any such arity is constant on the three rows. BLP needs symmetric polymorphisms of all arities, so it fails.
- n ∈ {1, 2} is impossible (checked by hand).

**(d) BLP+AIP.** This needs block-symmetric polymorphisms on blocks (L+1, L) for every L. At L = 3, place the n = 4 matrix on the first block and the n = 3 matrix on the second. The three rows are then equal block-wise, so the output is monochromatic. BLP+AIP fails.

**(e) Tight cycles and Lemma B.1.** Consider the window successor map:
- 00 → {1,2}
- 01, 10, 02, 20 → 0
- 11 → 2
- 12, 21 → 1
- 22 → none

So every infinite legal word has period 3. Hence there is no CYCLE₃[L] → R\* with L ≢ 0 (mod 3), and BGKR Thm 2.2 and Lemma B.1 do not apply directly.

**(f) q ≥ 3.** In a 2-colouring, 001 and 002 force col(1) = col(2) ≠ col(0), and then 112 is monochromatic.

## 4. The hardness proof (T2-e)

**The free-structure source principle.** This is BBKO Thm 4.12 combined with BGKR Thm 2.1. Let H = CYCLE₃[L] with L ≡ 1 (mod 3) and let M = Pol(A,B). Suppose no f ∈ M^{(|H|)} satisfies f(x∘c₁) = f(x∘c₂) = f(x∘c₃) for all x : V(H) → A, where c_k : H → V(H) is the k-th coordinate.
- Then F := F_M(H) has no constant tuple.
- H → F via the projections.
- There is a minion homomorphism M → Pol(H, F).
- Composing with the identity F → NAE₃[|F|], PCSP(H, NAE₃[|F|]) ≤ PCSP(A, B).
- BGKR Thm 2.1 makes the left-hand side NP-hard. P1 line-checked App. A.1.

**Computation for (R\*, NAE₃[3]), L = 4.**
- The unknown is f : [3]^12 → [3].
- Identified vectors: x∘c_k for x : ℤ₄ → [3], 243 vectors.
- Family: those vectors together with all vectors having at most 2 nonzero entries. Then, for two rounds, every third row Z completing a pair (X, Y) from the family columnwise inside R\*, with at most 3 free (0,0) columns.
- Constraints: rows of every such matrix are NAE.
- This subsystem has 250 281 classes and 11.46M distinct constraints, and CaDiCaL reports it UNSAT.
- A subsystem being UNSAT implies the full loop condition is UNSAT.

**Controls (same encoder, same parameters).**
- (LO₂, NAE₂): SAT. It is in P.
- ({002,011}, NAE₂): SAT. It is in P by §2.
- The same encoder on (LO₂, LO₃) is UNSAT. That template is Krokhin–Vagnozzi-hard; see R-P4-T1.

**Weakest links.**
- (i) Correctness of the encoder tightR.cpp. Cross-checked against the independent full encoder tightac.cpp on the LO₂ cases, and against the controls.
- (ii) The solver verdict. The DRAT proof trs3.drat (87 KB) is checked by rupcheck.cpp; result in LOG-P4.
- (iii) BGKR Thm 2.1. AI-written, but App. A.1 was verified by P1, and Zhou independently covers the graph case only.
