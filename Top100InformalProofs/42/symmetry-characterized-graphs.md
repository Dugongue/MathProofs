# Symmetry-characterized graphs and prime order

The open questions are from [Grochow–Urisman](https://arxiv.org/abs/2606.26244). The proof is written and remains independently unaudited.

## The setting

Grochow–Urisman, *GCT and Graph Isomorphism* (arXiv:2606.26244), §1.3.

**Definition.** A graph G on n vertices is **symmetry-characterized (SC)** if every graph H on the same vertex set with Aut(G) ≤ Aut(H) is isomorphic to one of ∅, K_n, G or Ḡ.

**The remark in the paper** (attributed to Babai):

> If a symmetry-characterized graph is not trivial … nor a star graph … nor its complement, then its automorphism group must have "permutation rank 3".

That remark is the stated motivation for:
- **OQ 1.8:** do multiplicity obstructions distinguish SC graphs?
- **OQ 1.9:** isomorphism of SC graphs, and the complexity of recognizing them.

**Notation.**
- Γ = Aut(G).
- O_1, …, O_r are the orbits of Γ on unordered pairs of distinct vertices.
- N = C(n, 2) and a = |E(G)|.
- The graphs H with Γ ≤ Aut(H) are exactly the 2^r unions of orbits.

## Theorem 1 (exact structure)

Let G be nontrivial (neither ∅ nor K_n). Then G is SC if and only if one of the following holds.
- **(i) r = 2.** Then the orbits are exactly E(G) and E(Ḡ).
- **(ii) r = 3.** All three orbits have size N/3, and the normalizer N_{S_n}(Γ) permutes {O_1, O_2, O_3} transitively. G is one orbit or the union of two.

Moreover:
- In case (i), either G is vertex-transitive and **strongly regular** with an edge- and non-edge-transitive automorphism group, or G is a star K_{1,n−1} or its complement.
- In case (ii), G is vertex-transitive and **never** a star.

*Proof.*

**(a) Counting forces r ≤ 3.**
1. Every nonempty proper union of orbits must have size a or N − a, the sizes of G and Ḡ (∅ and K_n are the empty and full unions).
2. So each orbit size s_i ∈ {a, N − a}.
3. Let r ≥ 3. Then s_i + s_j is also a proper union, so it lies in {a, N − a}. Since s_i, s_j ∈ {a, N − a}, this forces 2a = N − a or 2N − 2a = a. Hence a = N/3 or a = 2N/3.
4. In either case every s_i = N/3. (If some s_i = 2N/3, the remaining r − 1 ≥ 2 orbits would have total size N/3 while each is ≥ N/3.) So r = 3.
5. r = 1 would make G trivial.

**(b) Case r = 3.** Suppose σ maps the graph O_1 isomorphically onto O_2, so σ(O_1) = O_2.
1. The graph O_1 is isomorphic to G or Ḡ, so |Aut(O_1)| = |Γ|. Also Γ ≤ Aut(O_1). Hence Aut(O_1) = Γ, and likewise Aut(O_2) = Γ.
2. Therefore σΓσ⁻¹ = Aut(σ(O_1)) = Aut(O_2) = Γ, so σ ∈ N_{S_n}(Γ).
3. **SC ⇒ transitive.** All three single orbits are isomorphic to the same one of G, Ḡ (they all have size N/3). By steps 1–2 those isomorphisms lie in the normalizer, so it permutes the orbits transitively.
4. **Transitive ⇒ SC.** A transitive subgroup of S_3 (A_3 or S_3) is also transitive on 2-subsets. So the three single orbits are pairwise isomorphic, and so are the three pairwise unions. One of each family is G or Ḡ.

**(c) Case r = 2 is automatically SC.** The unions are exactly ∅, G, Ḡ and K_n.

**(d) Vertex orbits.** Suppose Γ has vertex orbits V_1, …, V_t with t ≥ 2. Pairs inside each V_i of size ≥ 2, and pairs across each V_i × V_j, lie in distinct Γ-orbits.
- **r = 2.** With t ≥ 3 there are already at least 3 orbits. With t = 2 and both |V_i| ≥ 2 there are 3 orbits. So t = 2 with V_1 = {c}, Γ is 2-homogeneous on V_2, and G is the star or the co-star.
- **r = 3.**
  - With t = 2 and |V_1| = |V_2| = m ≥ 2, the sizes C(m, 2), C(m, 2), m² cannot all be equal.
  - With V_1 = {c}, the equation n − 1 = N/3 gives n = 6. The pairs inside V_2 must then split into two orbits of size 5, so Γ acts on V_2 as D_5. But the orbit graphs K_{1,5} and C_5 + K_1 are not isomorphic, so G is not SC.
  - With t ≥ 3, the singletons and cross-pairs produce more than 3 orbits.

  So G is vertex-transitive.
- **Strong regularity for vertex-transitive r = 2.** G is regular. λ is constant because the edges form one orbit, and μ is constant because the non-edges form one orbit. ∎

## Theorem 2 (the rank-3 remark is false: an infinite family of rank-4 SC graphs)

For every prime p ≡ 1 (mod 3), the **cubic Paley graph**

  P₃(p) = Cay(ℤ_p, C₀),  where C₀ = {nonzero cubes},

is symmetry-characterized, and Aut(P₃(p)) has **permutation rank 4**. The smallest case is P₃(7) = C₇, the 7-cycle.

*Proof.*
1. **The automorphism group.** C₀ ≠ ∅ and C₀ ≠ ℤ_p^*. By Alspach's theorem on circulants of prime order (1973), Aut = {x ↦ ax + b : a·C₀ = C₀} = ℤ_p ⋊ C₀. For C₇ one can check this directly: Aut(C₇) = D₇.
2. **The orbits on pairs.** The class of x − y in ℤ_p^*/C₀ is invariant under Aut. Here −1 = (−1)³ is a cube, so the class does not depend on the order of x and y. Multiplication by C₀ and translations act transitively on each class. So the orbits on pairs are C₀, C₁, C₂ (r = 3), the orbitals on ordered pairs are the diagonal plus these three, and the rank is 4.
3. **Symmetry-characterized.** Multiplication by a generator g of ℤ_p^* normalizes ℤ_p ⋊ C₀ and maps C_i to C_{i+1}. That is cyclic and transitive, so Theorem 1(ii) applies. ∎

**Machine check (`sc.cpp`).**
- **Range:** p = 7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97.
- **Orbit sizes:** (p − 1)/3 each.
- **The 8 unions** fall into exactly 4 isomorphism classes: ∅, P₃, its complement, and K_p. Isomorphism of prime-order circulants is by multipliers (Turner 1967).

**C₇ concretely.**
- The D₇-invariant graphs are the circulants C₇(S) with S a union of {±1}, {±2}, {±3}.
- C₇(1), C₇(2) and C₇(3) are all 7-cycles.
- C₇(1, 2), C₇(1, 3) and C₇(2, 3) are all complements of 7-cycles.
- But D₇ has rank 4.

**Corrected statement.** SC graphs other than ∅, K_n, stars and co-stars are exactly:
- the vertex-transitive graphs whose automorphism group has 2 orbits on pairs (rank 3, or rank 4 or 5 when the edge orbit splits into two ordered orbitals);
- the graphs of Theorem 1(ii) (rank 4 to 7), which include all P₃(p).

**Consequence for OQ 1.9.** The rank-3 classification (Liebeck; Kantor–Liebler; Liebeck–Saxl) covers only part of the SC graphs. Any approach to OQ 1.9 through that classification must also handle the "cyclic three-class" family (ii), whose prototypes are the cyclotomic schemes.

## Theorem 3 (OQ 1.8 is a Gassmann question)

Write m(G) for the multiplicity data, i.e. the S_n-module F[S_n / Aut(G)] in characteristic 0.

**(a)** m(G) = m(H) iff Aut(G) and Aut(H) are **Gassmann-equivalent** in S_n: their permutation characters on S_n agree, which is the same as having equal cycle indices.

**(b)** Let G and H be SC, and suppose H is isomorphic to neither G nor Ḡ. Then Aut(G) and Aut(H) are **not conjugate** in S_n. So:

  OQ 1.8(i) ⟺ no two non-isomorphic, non-complementary SC graphs have automorphism groups with the same cycle index.

**(c)** Let G be SC of type (i) (r = 2). Then "G is characterized by its multiplicities" (OQ 1.8(ii)) is equivalent to OQ 1.8(i) restricted to type-(i) graphs.

*Proof.*

(a) For subgroups A, B ≤ S_n, the permutation characters 1_A↑ and 1_B↑ are equal iff |A ∩ C| = |B ∩ C| for every S_n-conjugacy class C. A conjugacy class of S_n is a cycle type, so this is equality of cycle indices.

(b) Suppose Aut(G) = σAut(H)σ⁻¹. Then σH has automorphism group Aut(G), so σH is a union of Aut(G)-orbits. Since G is SC, σH ≅ G or Ḡ. ∎

(c)
1. The number of orbits of a subgroup of S_n on 2-subsets is a Gassmann invariant: by Burnside it is computed from the cycle index.
2. So if m(H) = m(G), then Aut(H) has two orbits on pairs.
3. H is a union of Aut(H)-orbits and is nontrivial, so H is one of the two orbits.
4. Then the orbits of Aut(H) on pairs are exactly E(H) and E(H̄), so H is SC of type (i).
5. Part (b) now applies. ∎

**Remark (why OQ 1.8 is delicate).** Gassmann-equivalent, non-conjugate subgroups of S_n exist; footnote 16 of the paper gives two of order 16 in S_8. The classical ones come from parabolic subgroups P_k, P_{n−k} of PSL_n(q). But those images become conjugate in S_N, because the graph automorphism g ↦ g^{−T} interchanges the two actions. So the obvious sources of Gassmann pairs do not produce counterexamples. A counterexample to OQ 1.8 needs a Gassmann pair of rank-≤ 3-on-pairs groups that remains non-conjugate in S_n after allowing automorphism twists.

## The other part of OQ 1.9: the complexity of recognizing SC graphs

Recognizing SC graphs is in **P^GI**, hence in quasi-polynomial time (Babai):
1. Compute generators of Aut(G) with a GI oracle (Mathon 1979).
2. Compute the orbits on pairs.
3. Check that r ∈ {2, 3}, by Theorem 1.
4. If r = 3, test transitivity of the normalizer. This amounts to isomorphism tests among the three orbit graphs.

Theorem 1 also turns recognition into "is G vertex-transitive with at most 3 orbits on pairs?", apart from the star exceptions. That is a structural certificate an algorithm can aim for. A polynomial-time algorithm remains open, as does whether recognition is GI-hard.

## Theorem 4 (OQ 1.8 and OQ 1.9 closed for graphs on a prime number of vertices)

Let p be prime, and let G be a nontrivial graph on p vertices.

**(a) Classification.** G is SC iff it is one of the following:
- a star K_{1,p−1} or its complement;
- the Paley graph P(p), when p ≡ 1 (mod 4);
- the cubic Paley graph P₃(p) or its complement, when p ≡ 1 (mod 3).

**(b) OQ 1.8 holds.** Every SC graph on p vertices is characterized by its multiplicities: m(H) = m(G) ⟹ H ≅ G or Ḡ. In particular, any two non-isomorphic, non-complementary SC graphs on p vertices are separated by a multiplicity obstruction.

**(c) OQ 1.9 holds in polynomial time.** For both questions below there is a polynomial-time algorithm:
- deciding whether a graph on p vertices is SC;
- deciding isomorphism between an SC graph and an arbitrary graph on p vertices.

### Proof

**(a) Classification.**
1. Assume G is not a star or co-star. By Theorem 1, Γ = Aut(G) is transitive. So p divides |Γ|, and Γ contains a p-cycle. Hence G ≅ Cay(ℤ_p, S) with S = −S.
2. **Burnside (1911).** A transitive group of prime degree is either 2-transitive or contained in AGL(1, p).
3. If Γ is 2-transitive, G is trivial. So the translations ℤ_p form the normal Sylow p-subgroup of Γ, and Γ = ℤ_p ⋊ M with M = {a ∈ ℤ_p^* : aS = S}. Since S = −S, we have −1 ∈ M.
4. The Γ-orbits on pairs {x, y} are the cosets of M containing x − y, so r = (p − 1)/|M|.
5. By Theorem 1, r ∈ {2, 3}.
   - **r = 2.** M is the group of squares, and −1 ∈ M forces p ≡ 1 (mod 4). S is the squares or the non-squares, so G ≅ P(p).
   - **r = 3.** M is the group of cubes (the unique subgroup of index 3). −1 is always a cube. S is one cubic coset or a union of two, so G ≅ P₃(p) or its complement.
6. **Converse.**
   - P(p) has rank 3.
   - P₃(p) is SC by Theorem 2.
   - Stars and co-stars have r = 2.

**(b) Multiplicities.** Suppose m(H) = m(G). By Theorem 3(a), Aut(H) and Γ have the same cycle index: the same order and the same number of elements of each cycle type.
- **Vertex-transitive case.** Γ contains p-cycles, so Aut(H) does too, and Aut(H) is transitive.
  1. Its order p|M| ≤ p(p − 1)/2 is not divisible by p(p − 1). So Aut(H) is not 2-transitive, and by Burnside Aut(H) ≤ AGL(1, p) up to conjugacy.
  2. A subgroup of AGL(1, p) of order p·m contains the normal Sylow subgroup ℤ_p. It is therefore ℤ_p ⋊ μ_m, which is unique because ℤ_p^* is cyclic.
  3. So Aut(H) is conjugate to Γ, and Theorem 3(b) gives H ≅ G or Ḡ.
- **Star case.** Γ = S_{p−1}, the stabilizer of a point. Aut(H) has the same order, so its index in S_p is p. For p ≠ 6, every subgroup of index p in S_p is a point stabilizer. So Aut(H) is conjugate to Γ, and again H ≅ G or Ḡ.
- In both cases H is nontrivial, since Aut(K_p) = S_p is not Gassmann-equivalent to Γ. ∎

**(c) Algorithms.**
1. Stars and co-stars are recognized from the degree sequence.
2. Otherwise, decide in polynomial time whether the input graph is a circulant of prime order, and find a connection set T (Muzychuk–Tinhofer, *Recognizing circulant graphs of prime order in polynomial time*, Electron. J. Combin. 5 (1998) #R25).
3. By Turner (1967), circulants of prime order are isomorphic iff their connection sets are related by a multiplier.
4. So the graph is SC iff T is, up to one of the p − 1 multipliers, the set of squares (when p ≡ 1 (mod 4)) or a union of one or two cubic cosets (when p ≡ 1 (mod 3)).
5. Isomorphism of an arbitrary H to a given SC graph G is the same test against G's connection set. ∎

### What remains open (composite n)

The prime case works because transitive groups of prime degree are tightly constrained (Burnside), and circulants of prime order have multiplier isomorphism (Turner). For composite n:
- **OQ 1.8** needs Gassmann-rigidity of edge- or non-edge-transitive groups, plus the r = 3 class.
- **OQ 1.9** needs the rank-3 classification extended by the cyclic three-class family.

The next tractable rung is n = p² or n = 2p, where the transitive groups are again classified.
