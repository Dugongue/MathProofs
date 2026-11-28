# Completeness of three-index polynomial families

The projection reductions establish VNP-completeness. The separate VP separation follows only from its named unrefereed input.

## Definitions
Let F be any field and N ≥ 1. Write T = (T_{r,a,b}) for an N×N×N tensor of indeterminates.
- **3-dimensional permanent:** per3_N(T) = Σ_{π,σ ∈ S_N} Π_r T_{r,π(r),σ(r)}.
- **Combinatorial (Cayley first) hyperdeterminant:** Det3_N(T) = Σ_{π,σ} sgn(π) sgn(σ) Π_r T_{r,π(r),σ(r)}.
- **Mixed discriminant** of N×N matrices A_1..A_N: D_N(A) = [t_1⋯t_N] det(Σ_k t_k A_k) = Σ_{π,σ} sgn(σ) Π_i (A_{π(i)})_{i,σ(i)}. This is the tensor sum above with T_{i,k,j} = (A_k)_{ij} and the sign on one coordinate only.
- **Order-d versions** for d ≥ 3: per_d and Det_d sum over (d−1) permutations.

In characteristic 2 all signs equal 1, so per3 = Det3 = D, and the same holds for every d.

## Theorem
Over every field F, the families (per3_N), (Det3_N) and (D_N), and per_d, Det_d for every fixed d ≥ 3, are VNP-complete under p-projections.

## Proof
**Membership.** Each family is Σ φ(e) x^e. The coefficient φ is ±1 on monomials coming from a tuple of permutations, since distinct tuples give distinct monomials, and 0 otherwise. φ is computable in polynomial time, so Valiant's criterion places each family in VNP⁰ ⊆ VNP over any field (Bürgisser, Completeness and Reduction, Prop. 2.20). The criterion is applied to the #P functions [tuple valid ∧ even sign] and [tuple valid ∧ odd sign], and VNP is closed under subtraction.

**Hardness in characteristic ≠ 2 (folklore).** Set T_{r,a,b} = x_{r,a}·[b = a]. Then σ = π is forced, sgn(π)² = 1, and per3 = Det3 = per_N(X). For D, take A_k = diag(x_{1k},…,x_{Nk}). Then det(Σ t_k A_k) = Π_i(Σ_k t_k x_{ik}), whose t_1⋯t_N coefficient is per(X). The permanent is VNP-complete under p-projections when char ≠ 2 (Valiant).

**Hardness in every characteristic, characteristic 2 included.** We reduce the Hamiltonian cycle polynomial HC_n(X) = Σ_{n-cycles π} Π_u x_{u,π(u)}. HC is VNP-complete under p-projections over every field (Valiant; Bürgisser Cor. 3.19).

Set N = n². Index the three coordinates as follows.
- Rows: r = (u,p), u ∈ [n] a vertex, p ∈ Z/n a position.
- Coordinate 2: (v,q) ∈ [n] × Z/n.
- Coordinate 3: for each vertex u, n slots: t_u, and z_{u,1},…,z_{u,n−1}.

The nonzero entries of T are of two kinds. All other entries are 0, so T is a projection of X.
- *Active* entries: T[(u,p),(v,p+1),t_u] = x_{u,v} for all v.
- *Inactive* entries: T[(u,p),(u,p),z_{u,p}] = 1 for 1 ≤ p ≤ n−1, and T[(u,p),(u,p),z_{u,p−1}] = 1 for 2 ≤ p ≤ n. Here positions are taken in 1..n.

Two exceptions pin the rotation: row (1,1) has only its active entries, and rows (1,p) with p ≠ 1 have only their inactive entries.

**Claim.** per3_N(T) = HC_n(X) as polynomials over Z, hence over every field. Fix a nonzero term (π,σ), and call a row active if it uses an active entry.

1. **One active position per vertex.** The coordinate-3 slots of vertex u are reachable only from the n rows (u,·). Exactly one of those rows hits t_u, so u has exactly one active row.
2. **The inactive rows of u are matched uniquely.** Let a be the active position of u. Row (u,1) has only z_{u,1} available, so it takes z_{u,1}. Then row (u,2) takes z_{u,2}, and so on up to row (u,a−1). From the other end, row (u,n) has only z_{u,n−1}, row (u,n−1) takes z_{u,n−2}, and so on down to row (u,a+1), which takes z_{u,a}. Every z_{u,·} is used exactly once. So, given the active set, σ is unique.
3. **Active rows form cycles.** Each coordinate-2 index (v,q) is hit exactly once. An inactive row (v,q) hits itself. An active row (u,p) hits (v,p+1) ≠ (u,p).
   - If the target (v,p+1) of an active row were inactive, it would be hit twice. So targets are active.
   - Each active (v,q) is hit by exactly one active row (u,q−1).

   So succ is a permutation of the active rows. It raises the position by 1 at each step, so every succ-cycle has length divisible by n.
4. **The active set is one Hamiltonian cycle.** By step 1 there are exactly n active rows. So there is one succ-cycle of length n. Its positions are distinct and, by step 1, so are its vertices: it is a Hamiltonian cycle u_1→u_2→…→u_n→u_1 with weight Π x_{u_i,u_{i+1}}. Because vertex 1 is pinned to position 1, the positions are determined by the cycle. Conversely, every Hamiltonian cycle gives exactly one term, of weight 1 on the inactive rows. ∎

All entries of T are variables or constants in {0,1}, so this is a p-projection of size N = n².

**Order d > 3.** Set T'_{r,a,b,c_4,…} = T_{r,a,b}·Π_j [c_j = r]. This forces σ_j = id, so per_d is a projection of per3, and likewise Det_d of Det3.

**Det3 and D in characteristic ≠ 2 without the permanent.** This is not needed, since the permanent route covers it.

**Sanity check.** `[local reference omitted]` enumerates per3_N(T) by backtracking over the sparse entries and compares it with HC_n(X) on random integer X. It returned OK for n = 2..6, that is N = 4..36. This is a check of the claim, not part of the proof.

## Separation corollary (Hexagon: HC ∉ VP and HC ∉ VP-bar over every field)
1. per3, Det3, D and per_d, Det_d (d ≥ 3) are ∉ VP, and ∉ VP-bar, over **every** field.
2. **Characteristic-2 contrast.** Over a field of characteristic 2, per_N = det_N ∈ VP, while per3_N ∉ VP. Adding a third index to the permanent is exactly the step from VP to outside VP. The mixed discriminant D_N = [t_1⋯t_N] det(Σ t_k A_k) is ∉ VP in characteristic 2, although det(Σ t_k A_k) ∈ VP. So multilinear-coefficient extraction from a determinantal pencil is VNP-hard in every characteristic.
3. **Transfer.** The projection has size n², so any circuit for per3_{n²} gives a circuit of the same size for HC_n. No explicit numbers are claimed, since the Hexagon bound is ineffective.

## Prior art and caveats
- The VNP-hardness of the mixed discriminant and of Cayley's hyperdeterminant in characteristic ≠ 2, via diagonal matrices or the permanent, is folklore. The #P-hardness side is due to Gurvits and Hillar–Lim, and our LEDGER line 185 (F2) records it.
- Hrubeš (ECCC TR15-067) lists the char-2 VNP-complete families clique* and edge cover. Its full text was not retrievable here, because ECCC blocked the download. Mahajan–Saurabh (arXiv 1603.04606, on F:) do not treat tensor permanents. **A literature check is owed** on whether per3 in characteristic 2 appears in Hrubeš 2015 or in Capelli–Durand–Mengel (tensor contractions).
