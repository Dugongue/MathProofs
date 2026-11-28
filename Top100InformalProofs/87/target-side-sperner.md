# Target-side Sperner search and primary obstructions

For an unoriented input simplex extend the integer cocycle by the sign of vertex order, with value zero on repeated vertices. For subdivision compare instances on a sufficiently fine common refinement and simplicially re-approximate into the subdivided old triangulation. Oriented crossing arms occur in, in, out, out. The composite-modulus examples complement the earlier results of [Filos-Ratsikas, Hollender, Sotiraki and Zampetakis](https://arxiv.org/abs/2003.11974).

## 0. The problem

Fix a finite simplicial complex Y, an integer D ≥ 2, and a simplicial map g : S^{D−1}_0 → Y on a fixed triangulation, representing α ∈ π_{D−1}(Y) with α ≠ 0.

**TOPSPERNER(Y, α, D).** The input is a circuit C: [0,2^n]^D ∩ Z^D → V(Y) labelling the vertices of the Freudenthal (Kuhn) triangulation T_n of the cube Q = [−1,1]^D at scale 2^{1−n}. On ∂Q the label is not read from C. It is forced to be g∘c_n, where c_n: ∂T_n → S^{D−1}_0 is a fixed polytime simplicial "pinch" map of degree 1. All of ∂Q goes to the base vertex except one constant-size patch, which is a copy of S^{D−1}_0.

**Find:** a simplex σ of T_n whose label set λ(σ) is not a simplex of Y (a *witness*).

**Totality.** If there is no witness, λ is a simplicial map Q → Y extending g∘c_n ≃ g, so α = 0. **TFNP:** witnesses are checkable in polynomial time.

Classical instances:
- (∂Δ^D, deg 1) is Sperner, PPAD-complete (Papadimitriou 1994; Chen–Deng for D = 2).
- (S^{D−1}, odd-equivariant) and the p-polygon versions are domain-side or equivariant variants (Tucker: PPA, Aisenberg–Bonet–Buss; p-polygon Tucker: PPA-p, FHSZ 2003.11974).

## 1. Structural lemmas (all proofs elementary)

**L1 (subdivision).** TOPSPERNER(Y) ≡ TOPSPERNER(sd Y) under polytime reductions.

- (sd Y → Y): compose the labels with a simplicial approximation of the identity, sd Y → Y (barycentre of τ ↦ a vertex of τ).
- (Y → sd Y): replace T_n by sd T_n, which is again succinct. Label the barycentre of τ by the barycentre of λ(τ) when λ(τ) ∈ Y, and arbitrarily otherwise. A chain τ_0<…<τ_k of sd T_n inside a good τ_k maps to the chain λ(τ_0)⊆…⊆λ(τ_k), which is a simplex of sd Y. So a witness lies in a bad τ_k, and a witness of T_n can be read off. ∎

**L2 (homotopy invariance and functoriality).** If φ: Y → Y′ is any map and φ∘α = α′ in π_{D−1}(Y′), then TOPSPERNER(Y,α) ≤ TOPSPERNER(Y′,α′).

*Proof.*
1. By L1, assume φ is simplicial.
2. Compose the labels with φ. A face whose image under φ∘λ is bad was already bad under λ, because φ maps simplices to simplices.
3. The new boundary is φ∘g ≃ g′. Insert a collar Q∖Q′ carrying a fixed simplicial homotopy H: S^{D−1}×I → Y′ on a constant-size Freudenthal subdivision.
   - Freudenthal at scale 2^{−n} subdivides Freudenthal at scale 2^{−k}, because the hyperplane arrangement x_i ∈ 2^{−n}Z, x_i−x_j ∈ 2^{−n}Z refines the coarse one.
   - The "carrier vertex" map is a simplicial approximation of the identity and is polytime (sort fractional parts). So the collar is simplicial and contains no witnesses. ∎

**Corollary.** The complexity of TOPSPERNER depends only on the pair (Y, α) up to homotopy equivalence, and it is monotone along maps.

**L3 (suspension).** TOPSPERNER(Y,α,D) ≤ TOPSPERNER(ΣY, Σα, D+1).

*Proof.*
1. Use Q×[−1,1] with the Freudenthal triangulation. Label (x,t) by λ(x) on the middle layers, and by the cone points N or S on the top and bottom layers.
2. A Freudenthal simplex spans two adjacent t-layers and projects onto a Freudenthal simplex π(σ). Its label set is contained in λ(π(σ)) ∪ {N} (or ∪ {S}). This is a simplex of ΣY iff λ(π(σ)) is a simplex of Y.
3. The boundary map is ≃ Σg; fix it with a collar as in L2. ∎

**L4 (pinch boundary).** With the pinch boundary, only O(1) boundary facets are nondegenerate.

## 2. Theorem A: the primary (Hurewicz-visible) classification

Let h: π_{D−1}(Y) → H_{D−1}(Y;Z) be the Hurewicz map. Let m = ord h(α) ∈ {1,…,∞} and M = ord α ∈ {1,…,∞}.

**Theorem A.** Let D ≥ 2 and α ≠ 0.
- (a) If m = ∞, TOPSPERNER(Y,α,D) is **PPAD-complete**.
- (b) If 1 < m < ∞, it lies in **∩_{p|m} PPA-p**. It is hard for PPAD, and for ∩_{p|M} PPA-p when M < ∞. It is complete for ∩_{p|m} PPA-p whenever rad M = rad m. In particular this holds whenever h|⟨α⟩ is injective, e.g. Y (D−2)-connected (Hurewicz iso).
- (c) If m = 1, it is PPAD-hard, and ∩_{p|M} PPA-p-hard if M < ∞. Upper bound: see §3 and §4.

**Corollary A′ (complete classification for (D−2)-connected Y, D ≥ 3).** Here π_{D−1}Y = H_{D−1}Y is finitely generated.
- α of infinite order: PPAD-complete.
- α of order m: complete for ∩_{p|m} PPA-p = PPA-m[#1] (Hollender 2019, Prop. 2.1 as quoted in FHSZ).

The search class is therefore exactly the "prime support" of α, with ∞ ↦ PPAD.

### Proof of the upper bounds (flux)

Choose a cocycle z ∈ Z^{D−1}(Y;A) with ⟨z, h(α)⟩ ≠ 0.
- For (a), take A = Z.
- For (b), fix p | m. The p-primary part of h(α) is nonzero. A coordinate projection H_{D−1} → Z/p^a is nonzero on it. By UCT, Hom(H_{D−1}, Z/p^a) is a quotient of H^{D−1}(Y;Z/p^a), so take A = Z/p^a.

Extend z to all ordered (D−1)-tuples of labels: degenerate tuples get 0, and non-simplices get 0.

For a D-simplex σ of T_n (ordered), define flux(σ) = Σ_i (−1)^i z(λ(∂_iσ)) = (δ(λ^*z))(σ).
- **Good σ have flux 0.** If λ(σ) is a nondegenerate simplex, flux(σ) = (δz)(λσ) = 0. If λ(σ) is degenerate, the two faces dropping a repeated label cancel and the remaining faces are degenerate.
- **Total.** Summing over σ gives the boundary sum ⟨z, (g∘c_n)_*[S^{D−1}]⟩ = ⟨z, h(α)⟩ ≠ 0. By L4, the boundary sum comes from O(1) explicit facets.

Turn this into a graph:
- Nodes are the D-simplices plus one outer node. For each interior facet with value c, draw |c| arcs between the two adjacent simplices, oriented by sign.
- Imbalance equals flux. The outer node is a known node with imbalance −⟨z,h(α)⟩ ≠ 0. Degrees are bounded.
- Any other unbalanced node is a witness.

This is Imbalance over Z, which is in PPAD (standard pairing of in-arcs and out-arcs). Over Z/p^a it is Imbalance-mod-p^a, which is in PPA-p^a = PPA-p (GKSZ Thm 1; FHSZ Def. 4). Doing this for every p | m gives membership in ∩_{p|m} PPA-p. ∎

### Proof of the lower bounds

Write M(Z/k,n) = S^n ∪_k e^{n+1}, with bottom class ι.

A map M(Z/k, D−1) → Y carrying ι to α exists iff kα = 0 in π_{D−1}Y: extend α over the cell. A map S^{D−1} → Y carrying ι to α always exists (α itself). By L2, it suffices to prove:

**Theorem M (Moore and sphere completeness).** For every n ≥ 1:
- (i) TOPSPERNER(S^n, d·ι, n+1) is PPAD-complete for every d ≠ 0.
- (ii) TOPSPERNER(M(Z/k,n), ι, n+1) is complete for ∩_{p|k} PPA-p.

*Proof.*

**Membership.** This is the flux argument above: H_n(S^n) = Z, and H_n(M(Z/k,n)) = Z/k with h(ι) a generator.

**Hardness of (ii).** By L3, and since ΣM(Z/k,n) = M(Z/k,n+1) and Σι = ι, it suffices to treat n = 1 (D = 2). I also give D = 3 directly. Reduce from Bipartite-mod-k[#1], which is complete for PPA-k[#1] = ∩_{p|k} PPA-p by Hollender Prop. 2.1. Orient its edges from side 0 to side 1. This gives Imbalance-mod-k[#1]: the source 0^n has imbalance 1, and solutions are nodes with imbalance ≢ 0 mod k or inconsistent adjacency.

Embed it in the standard way (Papadimitriou's 3D Sperner, Chen–Deng, Grigni, FHSZ §3 "cables"):

1. **Nodes and strands.** Each node v gets a junction ball B_v at a polytime-computable location. Each consistent directed edge u→w gets a *strand*: a routed tube I×D^{D−1}. On a strand the map is the Thom collapse D^{D−1}/∂ → S^{D−1} = bottom sphere, with its sign. Everything outside tubes and balls maps to the base vertex.
2. **Junction balls.** On ∂B_v the map is a pinch onto the arriving disks, so its degree is imbalance(v).
   - If imbalance(v) ≡ 0 mod k, write the boundary as S^{D−1} →(deg j) S^{D−1} →(deg k) S^{D−1}. The second map extends over D^D through the characteristic map of the top cell. Bounded degree gives finitely many local configurations, so use fixed constant-size fillings.
   - Otherwise fill B_v with the base vertex. Witnesses then occur only inside B_v, and v is a solution.
3. **Inconsistent pairs.** For an inconsistent pair (x,y), the strand from x stops at a stub near B_x. A small sphere around the stub has degree ±1 ≢ 0, so witnesses occur there, and (x,y) can be decoded.
4. **Source.** Join the source ball B_{0} to the outer pinch disk by one strand. The outer boundary has degree 1, so B_0 has imbalance 1−1 = 0 and is filled.
5. **D = 2.** Strands are arcs. Replace each crossing by its oriented smoothing. Two incoming and two outgoing arms alternate, and joining each in-arm to an adjacent out-arm gives disjoint arcs. This changes no junction degree, so it is locally computable. The target M(Z/k,1) is a 2-complex.
6. **D ≥ 3.** Tubes route disjointly; alternatively, use L3.

**Hardness of (i).** Take the PPAD-complete 2D Sperner instance. L3 gives every D. The degree-d self-map of S^n and L2 give every d ≠ 0. ∎

**Wedge remark.** The pinch construction gives directly the reduction ⊓_{p|k} TOPSPERNER(M(Z/p^{a_p})) ≤ TOPSPERNER(∨_p M(Z/p^{a_p}), Σι_p) ≃ TOPSPERNER(M(Z/k), ι). Put one instance in each of disjoint sub-balls; a witness of any of them is accepted. This is Johnson's meet ⊓ (= ∩). It is not Buss–Johnson's & (instance chooses the prime), which is how PPA-k is built (GKSZ Thm 1). For a fixed α, the topology always produces the meet, i.e. the "#1" classes.

**More examples of Theorem A.**
- Lens-space targets L(k) at D = 2, using the 2-skeleton M(Z/k,1): complete for ∩_{p|k} PPA-p.
- RP^n targets at D = 2: **PPA-complete**. This is the target-side twin of Deng et al.'s domain-side RP²/Möbius result.
