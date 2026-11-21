# A counterexample to the characteristic-two symmetric determinantal factorization conjecture

There is a two-variable polynomial over `F2` with a symmetric determinantal representation, with entries restricted to constants or the two variables, whose generic multilinearization admits no factorization into affine linear factors with polynomial coefficients modulo any of the four square relations allowed over `F2`. This disproves the conjecture in Section 7, including the version requiring a factorization for only one choice of square relations. [Grenet–Monteil–Thomassé, Symmetric Determinantal Representations in Characteristic 2, Proposition 3.3, Theorem 4.12 and Section 7](https://arxiv.org/pdf/1210.5879)

## A local obstruction

Let `R` be a discrete valuation ring of characteristic two with uniformizer `π`. In the algebra `R[X,Y]/(X²,Y²)`, suppose `Q` has constant coefficient of valuation exactly two, both linear coefficients of valuation at least two, and `XY` coefficient a unit. Then `Q` is never a product of affine linear factors over `R`.

Indeed, write a putative factorization as `prod_i(a_i+ell_i)` with homogeneous linear `ell_i`. All `a_i` are nonzero and their valuations sum to two. In the fraction field divide through by their product. The degree-one part `sum_i ell_i/a_i` is integral, whereas the normalized `XY` coefficient has valuation `−2`. If one constant has valuation two, every other normalized linear term is integral, so the first one is integral too. Then the contribution at degree two is integral. In the remaining case two constants have valuation one. Write the two potentially nonintegral terms as `v_i/π,v_j/π` with integral linear forms `v_i,v_j`. Their sum is integral, hence their reductions agree. Their product modulo `π` is a square of a linear form and vanishes because `X²=Y²=0` in characteristic two. Hence their product after dividing by `π²` has coefficient valuations at least `−1`. Every other pair of factors likewise contributes terms of valuation at least `−1`. This contradicts the required quadratic coefficient of valuation `−2`.

## The representable polynomial

Index four polynomials `π_λ(u)` by `λ=(λ_1,λ_2)∈F2²`. Choose, in lexicographic order, `u²+u+1`, `u³+u+1`, `u³+u²+1`, and `u⁴+u+1`. These are distinct irreducibles. The quadratic and cubics have no root in `F2`, and the quartic has no root and is not divisible by the sole irreducible quadratic. Let `h` be their product. By the Chinese remainder theorem choose polynomials `s,t∈F2[u]` with

```text
s ≡ λ_1,  t ≡ λ_2    modulo π_λ², for every λ∈F2².
```

Use the representatives of degree less than `deg(h²)` to make the construction unique. In `F2[u,v]` define

```text
a = s+t,     d=v+t+h,     e=u+s,     c=s d+t e.
```

In the following formula evaluate `a,c,d,e` at `(u,v)=(x,y)`:

```text
P(x,y) = (a(x,y)² + x+y)(c(x,y)² + d(x,y)² x + e(x,y)² y).
```

Each factor is a square plus the sum of the variables times squares. Proposition 3.3 therefore gives a symmetric determinantal representation of `P` in precisely the entry-restricted sense of the conjecture.

## Failure for every choice of squares

Let `Q(u,v;x,y)` be the multilinear remainder of `P` under `x²=u²` and `y²=v²`. Fix `λ∈F2²`. To test factorization modulo `x²=λ_1²,y²=λ_2²`, shift `x=X+λ_1,y=Y+λ_2` and work modulo `X²=Y²=0`. Fix the height-one valuation of `F2[u,v]` at `π=π_λ(u)`, whose local ring is a discrete valuation ring. All auxiliary coefficients in what follows are evaluated at `(u,v)`.

Write `A=a+λ_1+λ_2` and `C=c+λ_1 d+λ_2 e`. Expanding the two factors before multilinearization and then shifting gives

```text
constant = A² C² + [d(u+λ_1)+e(v+λ_2)]²,
linear   = (A²d²+C²)X + (A²e²+C²)Y,
quadratic= (d²+e²)XY.
```

The congruences ensure `A,C≡0 mod π²`. They also give `d(u+λ_1)+e(v+λ_2) ≡ h(u+λ_1) mod π²`. The right side has valuation one since `h` has a single factor `π` and `u+λ_1` has none. Therefore the constant has valuation exactly two, and the linear coefficients have valuation at least two. The quadratic coefficient has reduction `(u+v+λ_1+λ_2)²`, which is nonzero because `v` stays transcendental over `F2[u]/(π)`. The local obstruction applies. A factorization over `F2[u,v]` would induce one over this local ring, a contradiction. This works for every `λ`. If the generic square parameters are written without squares, a putative factorization there would specialize under the substitution of `u²,v²` for those parameters to one in the version just ruled out. The proof is informal.

# Matrix-symmetric VNP is strictly larger than matrix-symmetric VP in every characteristic

Use the row-and-column matrix-symmetry action and Boolean-sum definition of `symVNP` from Definition 7.1, over an arbitrary field. There is a single explicit polynomial family in `symVNP` with polynomial-total-size symmetric witnesses, whose `symVP` circuits require orbit size `n^Ω(sqrt(n))` for infinitely many `n`, in every characteristic. In particular the characteristic-two equality of determinant and permanent leaves a different explicit separating family available. [Dawar–Dwivedi–Pago–Seppelt, Depth Hierarchies for Symmetric Algebraic Circuits, Sections 2 and 7](https://arxiv.org/html/2611.23541#S7)

Let the variables `X` encode the biadjacency matrix of a bipartite graph with `n` vertices per side. Let witness bits form two `n × n` matrices `U,V`. Require exactly one bit per row and per column in each matrix. For a list of bits `w_i` this test is computed by `(sum_i w_i) prod_{i<j}(1−w_i w_j)`, valid over every field. Multiply all these row and column tests by

```text
prod_{i,j,a,b} [1−U_(i,a) V_(j,b) (X_(i,j)−X_(a,b))²].
```

Let `A_n(X)` be the sum of this witness polynomial over the Boolean choices. It has polynomial degree and a polynomial-size witness. Permuting row labels simultaneously relabels both indices of `U`; permuting column labels simultaneously relabels both indices of `V`. These permutations extend to automorphisms of the witness gates by the displayed indexing. On zero-one inputs, the witness is one precisely for an automorphism preserving the two sides, so `A_n` evaluates to the number of such automorphisms in the base field.

## A pair of colored structures

In characteristic `p>0` choose `q=3` if `p=2` and `q=2` otherwise. In characteristic zero choose `q=2`. Use `F_q` for a label set, independently of the circuit field. Take a connected cubic expander on `v` vertices, orient its base edges, and give each vertex `w` a charge `b_w∈F_q`. Its inner fiber consists of triples on the three incident base edges with signed incident sum `b_w`. Its edge fiber on `e` consists of labels `(e,a)` with `a∈F_q`. Join an inner tuple at `w` to the corresponding label of each of its three edges. In each edge fiber add the directed successor relation `(e,a)→(e,a+1)`. Distinguish all base vertex and edge fibers by separate colors. Use charge zero everywhere for `D_0` and charge one at a single vertex for `D_1`. This is the usual additive CFI defect construction with the successor relation included to control edge-fiber automorphisms. [Dawar–Richerby, The Power of Counting Logics on Restricted Classes of Finite Structures](https://www.cl.cam.ac.uk/~ad260/papers/counting-treewidth.pdf)

An isomorphism between these structures must translate each edge fiber, as these are exactly the permutations commuting with the directed prime-length successor cycle. Incidence then forces the inner tuple maps to be the corresponding coordinatewise translations. If the edge translation vector is `δ`, its signed boundary must be the charge difference. The image of the oriented incidence map of a connected graph is the space of vectors of sum zero. This follows, for instance, by routing a unit difference between any two vertices along a path. Thus the two structures are nonisomorphic, and each has automorphism group of order `a=q^(|E|−|V|+1)`. Their graphs of incidences and successor links are connected, since successors connect every edge fiber and each inner tuple is attached to its three edge fibers.

## A balanced bipartite encoding without extra automorphisms

First convert `D_b` to a simple undirected graph `G_b`. The old vertices are its cores. At each core attach four pendant paths of lengths `1,2,3,L`, where the lengths `L≥4` distinguish the original fiber colors and are `O(v)`. Each incidence is replaced with a length-two path. Each directed successor arc is replaced with a length-three path with one extra pendant leaf at the first internal vertex from the tail. All intermediate vertices are new. The cores are precisely the vertices of degree at least four. Removing them leaves components recognizable as individual pendant tags, incidence paths, or directed successor paths. The last type has its tail distinguished by the leaf. This recovers exactly the colors and relations, and each gadget is rigid once its attached core or cores are fixed. Distinct successor arcs between the same two cores, possible for `q=2`, are distinguished by their opposite tails. Thus `G_b` is connected and its automorphism group is precisely that of `D_b`.

Convert `G_b` to a simple bipartite graph `H_b` with a row and column copy of each vertex of `G_b`. Connect the two copies of each vertex by a length-three path, and for every ordered adjacency `u~v` connect the row copy of `u` and column copy of `v` by a length-five path. Attach a pendant path of length one and another of length two at each row and column copy. The core copies are exactly the vertices of degree at least three. The link-path lengths distinguish equality links from adjacency links. A side-preserving automorphism consequently applies the same permutation to the row and column cores, and the original adjacencies force it to belong to `Aut(G_b)`. Every such permutation extends uniquely because the gadgets are rigid. The graph is connected because equality links join the two copies of each vertex and adjacency links recover connectedness of `G_b`. Each side has the same number of vertices, since every odd-length link contributes equally to both sides and every pendant gadget is included on both sides. The row count is `Θ(v²)` and identical for `b=0,1`. The graphs `H_0,H_1` are side-preserving nonisomorphic and each has exactly `a` side-preserving automorphisms.

Now take the balanced bipartite disjoint unions `H_0⊔H_0` and `H_0⊔H_1`. Their side-preserving automorphism counts are `2a²` and `a²`, respectively. Their difference is nonzero in the circuit field by the choice of `q`. The same matrices therefore have different values of `A_n`.

## The counting and circuit lower bounds

The encodings retain the fiber organization of the CFI construction. Every original vertex and its tags carry its inner tuple or edge label. The internal vertices of an incidence path carry the inner tuple, which determines its matched edge label. The internal vertices of a successor path and its tail leaf carry the tail label, which determines the head. In the second encoding, the link paths for original graph adjacencies carry the label of the corresponding original adjacency, specified by the same tuple or edge label. The other copy and equality gadgets inherit their original vertex labels. Thus each of these new fibers has fixed metadata and one label set from an inner or edge fiber. All tests for adjacency between these fibers use equality, successor, or coordinate projection, along with the fixed metadata.

A pebble on a tuple fiber blocks its base vertex and one on a bit fiber blocks both ends of its base edge. For `k=floor(c v)` with a sufficiently small constant `c>0`, deletion of at most `2k` base vertices leaves a unique connected component on more than half of the base vertices. Otherwise a union of residual components with size between one quarter and one half would violate edge expansion because all boundary edges end at one of the at most `2k` deleted vertices. These large components are nested under enlargement of the blocked set.

In the bijective game maintain a vector of translations on edge labels whose signed boundary agrees with the charge difference away from one unpebbled defect in the large component. Start with the zero vector. When one pebble is removed, and for each possible new fiber independently, choose a defect in the large component after that fiber is blocked. Move the old defect there by modifying the edge translations along an oriented unit flow on a path within the current large component. The path avoids the remaining blockers. For that possible fiber use the modified translations to define its map. These maps define a single bijection of the universes, since fibers and side labels are kept. Whichever new vertex Spoiler picks, the chosen vector preserves all old pebbles and realizes the new position. Adjacencies on pebbled tuples and labels are preserved by the common translations, including the successor condition. This gives a winning strategy for `k` pebbles on the encoded graphs. It gives the same bound on the two disjoint unions by pairing their two components and playing separately on each.

For completeness, the group-theoretic support bound of Theorem 2.6 in Depth Hierarchies applies to the reduced arithmetic circuit in any characteristic. Its reduction and support argument are syntactic and use only gate types, wire incidences and their multiplicities. Reduction merges identical input labels and equal typed multisets of children bottom-up and is equivariant. For a reduced circuit with supports of size at most `s`, the bijective `2s`-pebble game preserving the two sides controls every gate value. Fix pebbles on a gate support and split its children into orbits under the pointwise stabilizer of that support. For an orbit representative, extend the pebbled assignments to its child support. Duplicator's bijections match these injective extensions bijectively, and each member of the child orbit occurs equally often by transitivity. Induction on gate height gives equal multisets of child values on the two inputs. Addition and multiplication give equal values, with wire multiplicities preserved. The output has empty support. This argument applies over the original field and uses no arithmetic properties of the characteristic.

Here the dimension satisfies `n=Θ(v²)`. Theorem 2.6 with `r=floor(k/2)` shows that an orbit bound strictly less than `binom(n,r)` would give supports smaller than `r`, contradicting the different output values. Thus for the resulting infinitely many dimensions the orbit size is at least `binom(n,r)=n^Ω(sqrt(n))`. This proves strict separation, with an explicit symmetric-witness family in the two-part matrix model. The proof is informal.
