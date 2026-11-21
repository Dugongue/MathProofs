# Linear-size symmetric linear IPS for the CFI equations over F2

The inconsistent system in Definition 14 has a symmetric placeholder-linear IPS refutation over `F2` of total size `O(|V|+|E|)` including gates and wires. This settles the open question after Theorem 16 about an exponential separation between the linear and unrestricted symmetric IPS on those instances. The construction works for any loopless graph of bounded maximum degree, with total charge one. [Dawar–Grädel–Kullmann–Pago, Section 6.1](https://arxiv.org/html/2504.16820#S6.SS1)

Use their `F2` variables `x^e_0,x^e_1` for each edge `e` and let `s_e=x^e_0+x^e_1`. For every vertex `v` and choice of incident bits `i`, use `y_(v,i)` for the equation polynomial `f_(v,i) = sum_(e∋v) (x^e_(i(e)) + i(e)) + b_v`, where the bits `b_v` sum to one. Use `y^e` for the edge equation `s_e+1`. Write `E(v)` for the set of incident edges. Fix an edge ordering `e_1,...,e_m`, as the edge-flip group fixes all edge names.

For every assignment `λ` of bits to all edges, the identity `sum_v f_(v,λ|E(v))=1` holds as a polynomial. Each selected variable and each selected bit constant occurs twice, and the total charge is one. Multiply by `prod_e x^e_(λ(e))` and sum over `λ`. Summing the bits away from `v` factors on the left-hand side. Thus the polynomial

```text
L(X,Y) = sum_v [(prod_{e∉E(v)} s_e)
              (sum_{i:E(v)→F2} y_(v,i) prod_{e∈E(v)} x^e_(i(e))) ]
```

substitutes to `prod_e s_e`. The telescoping polynomial

```text
T(X,Y) = sum_{j=1}^m y^(e_j) prod_{r<j} s_(e_r)
```

substitutes to `1 + prod_e s_e`. Consequently `L+T` gives `1` after axiom substitution, is placeholder-linear, and gives zero when all placeholders vanish. The Boolean axioms need not be used.

For syntactic symmetry, an edge flip sends the summand tag `i` at `v` to the tag obtained by flipping the same incident bits, and it sends each used variable and placeholder to the corresponding variable or placeholder. It fixes the `s_e`, edge placeholders, and all tags indexing the ordered products. This induces a circuit automorphism. The local sums and products at a vertex use constantly many gates because the maximum degree is bounded. For the wire bound, greedily color the base edges with at most 2Δ−1 colors for maximum degree Δ. In each color class, fix an ordering and precompute the prefix and suffix products of the s_e in linear total size. At a vertex, at most one edge of a given color is incident. The product of the nonincident edges of that color is therefore either the full product or the product of the prefix and suffix on either side of the excluded edge. Combining the constantly many colors costs constantly many gates and wires per vertex. Edge flips fix the entire indexed construction. Prefixes for `T` can be accumulated in `O(|E|)` gates and wires. The proof is informal.
