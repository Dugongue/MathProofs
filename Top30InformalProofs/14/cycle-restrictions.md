# Cycle-length-restricted permanents in characteristic two

The proven dichotomy is for the stated cycle-length sets. The separation from VP inherits the named external input.

## Definitions
- For L ⊆ Z_{>0}: per_{L,n}(X) = Σ_{σ ∈ S_n, every cycle length of σ in L} Π_i x_{i,σ(i)}.
- L is **p-dense** if there is a polynomial q such that for every N ≥ 1 some ℓ ∈ L has N ≤ ℓ ≤ q(N). Examples: every cofinite L, 2Z, odd numbers, primes, {2^j}, {ℓ ≡ r mod d}. Non-examples: finite L, {2^{2^j}}.
- Reductions are p-projections with constants 0 and 1 only.

## Theorem (char 2)
Let F have characteristic 2 and let L be p-dense.
1. If L ⊇ {2, 3, 4, ...}, i.e. L = N or L = N∖{1}, then per_L ∈ VP. Here per_N = det, and per_{N∖{1}}(X) = det(X − diag X).
2. Otherwise, i.e. some j ≥ 2 has j ∉ L, per_L is VNP-complete under p-projections with constants {0, 1}. The family is in VNP⁰ when membership of a length in L is decidable in poly time.

So over char 2, for p-dense L: **per_L ∈ VP ⟺ L ⊇ N_{≥2}.** Any single missing length j ≥ 2 makes it VNP-complete.

Manthey's decision/optimisation dichotomy for L-cycle covers (cs/0504038) is the Boolean shadow: there the tractable cases are L = {2} and L = N_{≥2}. Here, in char 2, the algebraic tractable cases are L = N and L = N∖{1} on the p-dense side, and L ⊆ {1, 2} on the finite side (haf = Pf, loop-haf = Pf of an augmented graph, see the remark at the end).

## Proof of 2
**Step 0. Bipartite Karp graph.** Take an HC_m instance X on the complete digraph [m]. For each v ∈ [m] create v_in, v_a, v_b, v_out with undirected weight-1 edges v_in–v_a, v_a–v_b and v_b–v_out. For each arc (u, v) with u ≠ v create an edge u_out–v_in of weight x_{uv}. Call this H, with N_H = 4m vertices.
- H is bipartite: A = {v_in, v_b}, B = {v_a, v_out}. Every edge joins A to B, including out–in.
- Put s := 1_out and t := 1_b. Then UHP^{s,t}(H) = HC_m(X), where UHP^{s,t} is the weighted sum over undirected Hamiltonian s–t paths.
- Why: v_a and v_b have degree 2. For v ≠ 1 they are not endpoints, so every gadget is crossed in → a → b → out. The path leaves s = 1_out into some v_in. Gadget 1 is entered at 1_in and ends at 1_a → 1_b = t. The edge s–t is unusable because t is visited last. Inductively every gadget is traversed forward, and the sequence of out→in edges is a directed Hamiltonian cycle of G through 1, with weight Π x. This is a bijection.

**Step 1. Unequal blowup.** Fix j ≥ 2 with j ∉ L, and write j = k_1 + k_2 with k_1, k_2 ≥ 1. Replace every A-vertex h by a directed path h^(1) → ... → h^(k_1), and every B-vertex by a directed path of k_2 vertices, with arcs of weight 1. For each H-edge {u, v} of weight w add both arcs u^(last) → v^(1) and v^(last) → u^(1), each of weight w. Inside a path the arcs are forced: h^(i) has its only out-arc to h^(i+1), and h^(i+1) its only in-arc from h^(i). So the directed cycles of the blown-up graph H^bl are exactly the lifts of the closed walks of H that are cycles (length ≥ 2). A base cycle C has lift length Σ_{h∈C} k_h. Since H is bipartite, a base cycle of length 2ℓ lifts to length ℓ·j, and a base 2-cycle {u, v} lifts to a cycle of length **exactly j**.

**Step 2. Directed closing chain.** Pick n ∈ L with n ≥ |V(H^bl)| + 1 = k_1|A| + k_2|B| + 1 and n ≤ poly(m), which p-density allows. Add c_0 and pads p_1..p_r with r = n − |V(H^bl)| − 1. Add arcs t^(k_1) → c_0 → p_1 → ... → p_r → s^(1), all of weight 1. Every other entry of Y is 0, including the whole diagonal.

**Step 3. Reversal involution (char 2).** Let S = {c_0, p_1, ..., p_r}. The only in-arc of c_0 comes from t^(k_1), and each p_i's only in-arc is from its chain predecessor. So any cycle meeting S contains c_0. Let σ be a cycle cover of Y with all cycle lengths in L, nonzero weight, and at least two cycles. Every cycle other than the one through c_0 is the lift of a base cycle of H.
- If some such cycle has base length ≥ 3, let C* be the one containing the least vertex, and reverse its base cycle. The lift of the reversed base cycle is again a cycle of H^bl on the same vertex set: arcs exist in both directions with equal weight, and the paths are re-traversed forward. It has the same length and the same weight, and it is different because the base length is ≥ 3. This is a fixed-point-free, weight- and L-preserving involution, so these σ sum to 0 in char 2.
- Otherwise every non-c_0 cycle is the lift of a base 2-cycle, so it has length j ∉ L, and σ is not counted.
- There are no 1-cycles, since the diagonal is 0.

Hence per_L(Y) = HC_n(Y), because n ∈ L. A Hamiltonian cycle of Y runs c_0 → pads → s^(1) ⇝ t^(k_1) → c_0, with the middle part a Hamiltonian path of H^bl that is the lift of a unique undirected Hamiltonian s–t path of H. So **per_L(Y) = UHP^{s,t}(H) = HC_m(X)**, a p-projection with constants {0, 1} of size poly(m).

**Membership.** By Valiant's criterion, the coefficient of a multilinear monomial is [it is a permutation with all cycle lengths in L ∩ [1, n]], which is in P/poly with advice L ∩ [1, n] (C1). ∎

## Corollaries (Hexagon: HC ∉ VP and ∉ VP-bar over every field)
Over every field of characteristic 2, per_L ∉ VP and ∉ VP-bar for every p-dense L that misses some j ≥ 2. Examples, all new in char 2 (char ≠ 2 is mostly C1):
- **per_{2Z} (all cycles even):** its decision analogue is easy for bipartite hosts, and det-like formulas fail.
- **N∖{2}:** this settles the "open" boundary point of C-V3-f. The 1-cycles were never an obstruction, since the instance has zero diagonal.
- **N∖{3}, N∖{4}, …:** every cofinite L except N and N∖{1}.
- **{1} ∪ 2Z, odd lengths, primes, {2^j}, and every residue class ℓ ≡ r (mod d) with d ≥ 2.**
Combined with C1 (char 0: complete), per_L for p-dense L is now classified in char 0 and char 2. Char p > 2 still has the periodic N_{L_k} ≡ 0 gap of C1.

## Not covered (char 2)
- **Finite L ∌ only {1,2}.** L = {3} is VNP-complete via V3's triangle gadget (CLOSE-V3 AMMO-A2) together with A1's per3 completeness over every field (A1.3, verified). General finite L: see R-A2-finite-L if written; otherwise open.
- **Super-sparse infinite L**, e.g. {2^{2^j}}: no cycle of the needed length within a polynomial size.

## Remark: VP side for finite L ⊆ {1, 2} in char 2
- per_{{2}} = haf(x_ij x_ji) = Pf (alternating = symmetric with zero diagonal in char 2).
- per_{{1,2}} = loop hafnian. Add twins i' with edge i–i' of weight x_ii, and weight-1 edges among all twins. The twins of matched vertices are perfectly matched among themselves in (2k−1)!! ≡ 1 ways, so the hafnian of the augmented graph is the loop hafnian, which equals a Pf.
- per_{{1}} = Π x_ii.
