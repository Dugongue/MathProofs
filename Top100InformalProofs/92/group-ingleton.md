# Central quotients and group-theoretic Ingleton bounds

The group-theoretic results are written and independently unaudited.

## 1. Prior art (checked in source)

- Chan 2007: abelian groups satisfy Ingleton. Mao–Hassibi 0910.1335: PGL2(p), p ≥ 5, violate; S5 is the smallest violator.
- Stancu–Oggier, NetCod 2012, claimed nilpotent and metacyclic groups never violate. The proof has a gap (Paajanen 1308.2069 §1; Craven §3): an intersection of quotients is not a quotient of the intersection.
- Paajanen 1308.2069 (Lazard correspondence): p-groups of class < p are abelian-characterisable, so they satisfy Ingleton. Nilpotent groups whose class is below the least prime divisor of |G| also satisfy it. Prop 3.3: a nilpotent group satisfies Ingleton if every Sylow subgroup does.
- Craven 2505.22565 (May 2025):
  - metacyclic groups never violate (Thm 1.1);
  - p^{1+2}_+ ⋊ C_{p−1} violates for every p ≥ 5 (Thm 1.2, supersoluble);
  - every violator of order < 1024 is known (Thm 1.4, Magma), so no nilpotent violator has order < 1024;
  - no odd-order violator up to order 2000;
  - open questions (i) nilpotent violators? (ii) odd order? (iii) H1 abelian? (iv) H3 cyclic? (v) all |H_ij| odd?
- Ingleton score M = sup(−Ing/h_1234) lies in [0.0925000777, 19/124]. DFZ's older upper bound 3/19 is enough for everything below. (E1 row 25.)

No 2025–26 paper settling (i) or (ii) was found (web search, 2026-11-26).

## 2. Theorems

### T1. Shrinking to a square. PROVED (confidence 0.97). Essentially Craven Lemma 2.4 / Remark 2.5, re-proved here.
Every offender H contains an offender H' (H'_i ≤ H_i) with
H'_1 = ⟨A,B⟩, H'_2 = ⟨C,D⟩, H'_3 = ⟨A,C⟩, H'_4 = ⟨B,D⟩, where A = H'_13, B = H'_14, C = H'_23, D = H'_24.
Also ratio(H') ≥ ratio(H).

*Proof.* Replace H1 by ⟨H13,H14⟩ ≤ H1.
- H13 and H14 are unchanged, because H13 ≤ H1' ≤ H1 forces H1'∩H3 = H13.
- H123 = H13∩H2 and H124 are unchanged.
- Only |H1| (in L) and |H12| (in R) move. Lemma 2.2 (|A:A∩C| ≤ |B:B∩C| for A ≤ B) gives |H12 : H12'| ≤ |H1 : H1'|, so the ratio does not drop.

The same argument handles H2. Replacing H3 by ⟨H13,H23⟩ changes only H34, which shrinks, and similarly for H4. One pass reaches a fixed point, because later steps never change H13, H14, H23 or H24. ∎

### T2. Craven's Thm 1.3 as stated is false; the proved version. KILL (confidence 0.99).
The statement reads: "either H_i ∩ N = 1 for all i, or the images in G/N form an offender". Take N = G and the S5 offender. Every H_i ∩ G ≠ 1, but in G/G = 1 every order is 1, so L = R and there is no offender. A proper counterexample also exists: N = A5 ⊴ S5. The images lie in C2, which is abelian, so they cannot offend.

What the proof does establish is the following, re-checked line by line, including the quantitative form. If N ⊴ G and N ≤ H_i for some i, then ratio(HN/N) ≥ ratio(H).

Craven's later uses are safe:
- the metacyclic proof uses a characteristic subgroup of a cyclic normal K, so N ≤ H1;
- the definition of "irreducible" (no H_i contains a nontrivial normal subgroup) is the correct notion.

For N central of prime order the two versions coincide, because H_i ∩ N ≠ 1 forces N ≤ H_i.

### T3. Central-lifting inequality. PROVED (confidence 0.93). New as far as we know.
Let G be any finite group and N ≤ Z(G) with |N| = q prime, and let H_i ∩ N = 1 for all i. Write H̄_i = H_iN/N and h̄ for the entropy vector of (G/N; H̄). Then
**Ing_G(H) ≥ Ing_{G/N}(H̄) − log q.**
Moreover, if H is an offender and H̄ is not, then all of the following hold:
- |H̄_S| = |H_S| for every S ≠ {3,4} (all pairs other than 34, all triples, and 1234);
- |H̄_34| = q|H_34|;
- equivalently, N ⊆ H3H4 and N ∩ H_iH_j = 1 for ij ∈ {12,13,14,23,24}.

*Proof.* Since H_i ∩ N = 1, the map H_i → H̄_i is an isomorphism; let s_i be its inverse.
- For x ∈ W_ij := H̄_i∩H̄_j put φ_ij(x) = s_i(x)s_j(x)^{-1} ∈ N. Since N is central, φ_ij is a homomorphism W_ij → C_q.
- On triple intersections φ_ik = φ_ij + φ_jk.
- H_S maps isomorphically onto {x ∈ W_S : φ_ij(x) = 0 for all i,j ∈ S}. Hence |H_S| = |W_S|/q^{r_S}, where r_S = dim span{φ_ij|W_S}, and h_S = h̄_S + (1 + r_S) log q.
- The constants cancel in Ing (five positive and five negative terms), so Ing(h) = Ing(h̄) + log q · (r12+r13+r14+r23+r24 − r34 − r123 − r124).
- Bounds: r123 ≤ r13 + r23 and r124 ≤ r14 + r24. Each holds because the span on W123 is spanned by φ13 and φ23, and each of these is nonzero on W123 only if it is nonzero on the larger W13, resp. W23. Also r34 ≤ 1. So the bracket is ≥ r12 − r34 ≥ −1.
- If H offends and H̄ does not, then Ing(h) < 0 ≤ Ing(h̄), so the bracket is a negative integer ≥ −1, hence exactly −1. That forces r12 = 0, r34 = 1, r123 = r13 + r23 and r124 = r14 + r24.
- With r12 = 0 we have φ13 = φ23 on W123, so r123 ≤ 1. If r13 = 1 and r23 = 0, then φ13 = φ23 = 0 on W123, so r123 = 0 ≠ 1. Hence r13 = r23 = r123 = 0, and likewise r14 = r24 = r124 = 0. Then r134, r234 and r1234 are 0 as well, since they are spans of zero maps. Finally, im φ_ij = N ∩ H_iH_j. ∎

*Machine check.* G = 3 × PSL2(7) (Craven Ex. 5.1), all 12 offenders found by the search (`C3xPSL27.txt`). Mod Z every intersection is unchanged except |H34|: 1 → 3. The image ratio is 3/8 = (9/8)/3, exactly as T3 predicts.

### T4. Quantitative Paajanen: violation is bounded by γ_p. PROVED (confidence 0.9). New as far as we know.
For every finite p-group G and every quadruple, ratio(H) ≤ |γ_p(G)|, i.e. **Ing ≥ −log|γ_p(G)|**. For nilpotent G, take the product over the Sylow subgroups. In particular:
- p-groups of class exactly p with |γ_p(G)| = p (for example maximal class of order p^{p+1}) have ratio ≤ p;
- 2-groups have ratio ≤ |G'|.

*Proof.* Let maxratio(K) be the largest ratio over quadruples of K; it is ≥ 1. For N ≤ Z(G) of prime order q, every quadruple satisfies one of two cases:
- some H_i ⊇ N, in which case T2 (proved version) gives ratio(H) ≤ maxratio(G/N);
- all H_i ∩ N = 1, in which case T3 gives ratio(H) ≤ q·maxratio(G/N).

So maxratio(G) ≤ q·maxratio(G/N). Iterate along the lower central series from γ_{c+1} = 1 up to γ_p, splitting each central factor γ_j/γ_{j+1} into prime steps. This gives maxratio(G) ≤ |γ_p(G)|·maxratio(G/γ_p(G)), and maxratio(G/γ_p(G)) = 1 by Paajanen (class < p). The same argument gives maxratio(G) ≤ |N|·maxratio(G/N) for any central N in any finite group. ∎

### T5. Anatomy of a minimal nilpotent violator. PROVED (confidence 0.9).
Suppose a nilpotent Ingleton violator exists, and let G be one of least order. Then G is a p-group: Paajanen Prop 3.3, since subgroups of a nilpotent group split over the Sylow subgroups. Furthermore every offender H of G, and every T1-shrink of it, satisfies (a)–(g):
- (a) H_i ∩ Z(G) = 1 for all i. Equivalently H_i is core-free, by T2 and minimality.
- (b) **ratio(H) = p exactly.** By T3, Ing ≥ Ing(image) − log p ≥ −log p, and ratios are powers of p.
- (c) For every N ≤ Z(G) of order p, the image mod N is Ingleton-TIGHT (Ing = 0). Every intersection lifts isomorphically except H̄34, so N ⊆ H3H4 and N ∩ H_iH_j = 1 for the other five pairs. Hence **Ω1(Z(G)) ⊆ H3H4** and **Ω1(Z(G)) ∩ H_iH_j = {1}** for ij ≠ 34. Modulo the whole of Ω1(Z(G)) (rank z), φ34 is onto and every other φ_ij vanishes, so Ing(image) = (z−1) log p.
- (d) G = ⟨H_i,H_j⟩ for all i ≠ j, and G = ⟨H_k,H_ij⟩ for {i,j} ≠ {3,4}, k ∉ {i,j}. This is Craven Prop 5.3, re-checked for the cases used.
- (e) For the shrunk square (A,B,C,D): **any three of A,B,C,D generate G**, because ⟨A,B,C⟩ ⊇ ⟨H1,H23⟩ and so on. So with π: G → G/Φ(G) = F_p^d, any three of π(A),…,π(D) span F_p^d. No sum of two of them along the cycle (a+b, c+d, a+c, b+d) is everything, by the Frattini argument, since H_i ≠ G. Consequences: **d(G) ≥ 3**, and A, B, C, D ⊄ Φ(G).
- (f) Normaliser constraints. These hold for minimal violators in ANY subgroup- and quotient-closed class, including odd order.
  - A = H13 is not normalised by both B and C. Otherwise A ⊴ ⟨A,B,C⟩ = G with A ≤ H1, contradicting (a).
  - Likewise for B (neighbours A, D), C (A, D) and D (B, C).
  - In particular A is not normal in both H1 and H3, and not central in both. So for each vertex of the 4-cycle A–B–D–C–A, at least one incident edge is non-commuting. Hence **H1 and H2 are both non-abelian, or H3 and H4 are both non-abelian**. This is partial progress on Craven's question (iii), for minimal violators.
  - H_k does not normalise H_ij for the generating pairs in (d).
- (g) Score bound: −Ing/h_1234 = log p / log|G:H1234| ≤ M ≤ 3/19 (DFZ), so **|G:H1234| ≥ p^7** and |G| ≥ p^7. For p ≥ 5 this is new beyond Craven's < 1024 search. With Paajanen, class(G) ≥ p.

*Self-audit of T5.*
- (b) and (c) need G/N to be a non-violator, which holds by minimality. They also need the ratios in G/N to be integral powers of p. That holds since G/N is a p-group, so a non-offender has Ing ≥ 0 in units of log p.
- (a) needs N ≤ H_i ⇒ image offender (T2-proved), applied to N ≤ Z(G) ∩ H_i of order p. A nontrivial subgroup of Z(G) ∩ H_i contains such an N.
- (e) needs (d) with exactly the pairs used: (k;ij) = (1;23), (1;24), (2;13), (2;14). Each was re-derived (one Lemma 2.2 step per case).
- I first believed H_i ∩ Φ(G) = 1, hence H_i elementary abelian. That would have closed the problem via (f). **It is FALSE reasoning**: it used the stated (false) Thm 1.3 with N = Φ(G), and was caught by the N = G counterexample. Recorded as a near miss.

### T6. Computation (C++, `[local reference omitted]`). Exact parameters.
Search family: all 4-tuples (A,B,C,D) of subgroups from a pool P, with H = (⟨A,B⟩,⟨C,D⟩,⟨A,C⟩,⟨B,D⟩).
- By T1 this covers every offender whose shrunk square has A,B,C,D ∈ P.
- Pool "cyc" = all nontrivial cyclic subgroups. Pool "two K" = cyclic subgroups plus joins of two cyclic subgroups of order ≤ K.
- Exhaustive within the family modulo conjugacy and the Klein symmetry (1↔2, 3↔4).
- Prunes, all valid for shrunk offenders: H1,H2 non-cyclic (Craven Cor 2.7); for p-groups H3,H4 non-cyclic (Craven Rem 2.5); no H_i ≤ H_j; H12 ≠ 1. "nocentral" adds T5(a), valid for order-1024 2-groups given Craven's < 1024 result.

Validation (reproduces Craven's Table 3 scores):

| group | order | offenders | best ratio | score |
|---|---|---|---|---|
| S5 (pool two |G| = all subgroups, fully exhaustive) | 120 | 8 | 16/15 | 0.01348 |
| PGL2(7) | 336 | 12 | 8/7 | 0.02295 |
| A4×A4 | 144 | 9 | 9/8 | 0.02370 |
| 5^{1+2}:4 (u1, u4, diag(2,1,3)) | 500 | 2400 | 32/25 | 0.03972 |
| 3×PSL2(7) | 504 | 12 | 9/8 | 0.01893 |

New ground (orders not covered by Craven, or natural candidates):

| group | order | pool | tuples tested | offenders |
|---|---|---|---|---|
| U_4(3) (sanity; covered by Craven) | 729 | cyc | 1.1e8 | 0 |
| **U_5(2)**, Sylow-2 of GL5(2), class 4 | 1024 | cyc | 2.14e9 | **0** |
| **Syl_2(S_12)** = Syl_2(S_8) × D_8 | 1024 | cyc | 4.59e9 | **0** |
| **C9 ≀ C3** | 2187 | cyc | 2.6e7 | **0** |
| U_5(2) | 1024 | two 8 + nocentral | killed in join-table phase (not finished) | -- |
| **7^{1+2} ⋊ (C3×C3)**, odd Borel of SL3(7) | 3087 (odd, > 2000) | cyc | 4.27e9 | **0** |
| 13^{1+2} ⋊ C3, two tori | 6591 | cyc | killed in join-table phase (not finished) | -- |

These searches are exhaustive only within their families. They are evidence, not proof.
