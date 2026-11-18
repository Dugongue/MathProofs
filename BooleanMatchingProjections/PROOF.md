# Boolean perfect-matching projections with controlled repeated labels

Grochow's Open Question 5.1 asks for a lower bound on monotone projections from bipartite to general perfect matching when the projection need only preserve the existence of a matching. The following results give quantitative lower bounds even with arbitrary extra labels in the supports of some source matchings. They leave the unrestricted question open. [Grochow, Open Question 5.1](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=9)

## Source model

Let \(n\) be even. The target input is the edge set of a simple graph on \([n]\). Write \(H\) for a bipartite multigraph with \(r\) vertices on each side and \(s\) edges. Each source edge is labeled either by a target edge \(\lambda\in E(K_n)\) or by the constant \(1\). To evaluate a projected bipartite matching instance on an input graph \(X\), retain all constant edges and retain a variable edge exactly when its label is an edge of \(X\). A monotone affine Boolean projection is covered by this model: expand the OR of the labels permitted at each bipartite position into parallel edges.

For a perfect matching \(M\) of \(H\), let \(S(M)\) be the set of its distinct nonconstant labels. A correct projection has the following two properties.

1. Every \(S(M)\) contains a perfect matching of \(K_n\). Indeed the input \(S(M)\) accepts.
2. For every perfect matching \(P\) of \(K_n\), there is a source matching \(M\) with \(S(M)=P\). Indeed the input \(P\) accepts, and no proper subset of \(P\) contains a perfect matching.

Call a matching in item 2 a pure witness for \(P\). Its selected labels can repeat, and its optimality is only about its set of distinct labels.

## Exponential lower bounds from few repeated labels

**Theorem.** Suppose the projection is correct and every target perfect matching has a pure witness in which at most \(k\) distinct variable labels occur more than once. Then

$$
\operatorname{xc}(\operatorname{PM}(K_n))\le (s+1)^{k+1},
\qquad
\log_2(s+1)=\Omega\!\left(\frac{n}{k+1}\right).
$$

Here \(\operatorname{PM}(K_n)\) denotes the perfect-matching polytope, and extension complexity counts inequalities, with equations free. In a simple monotone projection \(s\le r^2\), so \(\log_2(r+1)=\Omega(n/(k+1))\). In an affine Boolean projection \(s\le r^2(1+\binom n2)\). In either model \(k=o(n/\log n)\) rules out polynomial-size projections. There is no bound on how many times any one of the exceptional labels may occur.

More generally, assign real weights \(w_a\) to the labeled source edges. Assume that for every source perfect matching and every label it uses, the sum of the weights contributed by occurrences of that label is at least \(1\). The same conclusion holds if every target perfect matching has a pure witness in which at most \(k\) labels have contributed weight greater than \(1\). Unit weights give the repeated-label version. This weighted condition also handles forced repetitions, since copies which always occur together can share unit weight.

**Proof.** The standard bipartite matching polytope of \(H\) has variables \(x_a\ge0\) and equations

$$
\sum_{a\ni v}x_a=1
$$

at every vertex. It is the convex hull of perfect matchings, including for parallel edges. For example, the support of a nonnegative point satisfying the equations has a perfect matching by Hall's theorem. Subtract the smallest weight on that matching and iterate after renormalizing the degree equations. This exhausts the positive coordinates and gives a convex decomposition.

Consider any selection \(A\) of at most \(k\) labeled source edges, with distinct labels, and let \(R\) be its label set. Require \(x_a=1\) for \(a\in A\) and

$$
\sum_{\ell(a)\notin R,\ \ell(a)\ne 1}w_a x_a=\frac n2-|R|.
$$

The sum is over nonconstant labels outside \(R\). The added equality selects a face within the face forcing \(A\). In fact every source matching containing \(A\) has at least \(n/2\) distinct variable labels by item 1, and contains every label in \(R\). Every other present label contributes at least \(1\) to the displayed cost. Thus the cost is always at least \(n/2-|R|\).

Every matching in this face has exactly \(n/2\) distinct variable labels and every present label outside \(R\) contributes exactly \(1\). By item 1 its support is a target perfect matching. Consequently the affine readout of its indicator takes the value \(1\) on \(R\) and the weighted sum of all matching coordinates bearing \(\lambda\) on each other label \(\lambda\). This readout sends the whole face into \(\operatorname{PM}(K_n)\), by convexity.

In the other direction take any target perfect matching \(P\) and a pure witness having at most \(k\) overweight labels. Select one used source edge for each overweight label to form \(A\). For this choice the witness belongs to the stated face, and its readout is exactly \(P\). Thus the convex hull of all face images equals \(\operatorname{PM}(K_n)\).

For completeness, an extended formulation for this convex hull uses a nonnegative weight \(\theta_A\) for each choice \(A\), with sum \(1\), and a scaled copy of the corresponding face. Impose nonnegativity on the copy and multiply each of its equality right-hand sides by \(\theta_A\). Define the target vector to be the sum of the linear readouts on these copies plus the affine offset of each readout multiplied by \(\theta_A\). A copy with positive weight can be divided by its weight, and a copy with zero weight is zero because of nonnegativity and the vertex equations. This gives exactly all convex combinations of face images.

There are at most \((s+1)^k\) choices, by encoding each size-at-most-\(k\) set of forced edges as a sorted list padded with a dummy symbol. Each choice contributes \(s+1\) nonnegativity inequalities. Rothvoß's \(2^{\Omega(n)}\) lower bound for the perfect-matching polytope gives the claimed estimates. [Rothvoß, Theorem 1](https://arxiv.org/abs/1311.2369)

## A separate conclusion from collision-free restrictions

There is also a useful condition that leaves repeated copies entirely unrestricted. Define a 3-uniform hypergraph \(\mathcal C_H\) on the target vertices. Put \(\{a,v,b\}\) in it whenever some source perfect matching uses both distinct labels \(\{a,v\}\) and \(\{v,b\}\). This hypergraph is obtainable by testing whether a pair of source edges can extend to a source perfect matching. One can test all source edge pairs by ordinary bipartite matching with their endpoints deleted.

**Theorem.** If \(\mathcal C_H\) has an independent set of size \(t\ge4\), the complete graph on the largest even number \(t'\le t\) of these vertices has a perfect-matching polytope with extension complexity at most \(rs\). In particular \(rs\ge 2^{\Omega(t)}\).

**Proof.** Take an even independent subset \(U\) of size \(t'\). Outside \(U\) fix any one perfect matching. Set its labels to constant \(1\), set all other labels outside \(E(K_U)\) to \(0\), and keep the labels of \(E(K_U)\) variable. By correctness the restricted source projection decides perfect matching on \(K_U\). Every support in the restricted source consists of the fixed outside matching and a label set inside \(U\) containing a perfect matching on \(U\). Inside \(U\) a support can never use two distinct labels incident to the same vertex. Such a pair would realize a hyperedge of \(\mathcal C_H[U]\) in the original source graph. Therefore the support inside \(U\) is exactly a perfect matching. Every target perfect matching on \(U\) occurs.

Now apply the distinct-label support-polytope theorem. Its label groups are the stars of the vertices of \(U\). Every source support meets each star in exactly one label, and each star realizes \(t'-1\ge3\) labels as the source matching varies. The theorem builds an affine readout from the glued bipartite matching polytopes of the tight-cut pieces, yielding an extended formulation with at most \(rs\) inequalities. Rothvoß's bound proves the conclusion. [MathProofs, distinct-label support-polytope theorem](https://github.com/Dugongue/MathProofs/blob/6e92c4a3af341d5d6202e20e220b53662822b84f/BooleanCountingPermanent/PROOF.md) · [Rothvoß, Theorem 1](https://arxiv.org/abs/1311.2369)

For example, if \(\mathcal C_H\) has average vertex degree \(d\), random sampling followed by deleting one vertex from each surviving triple gives an independent set of size \(\Omega(n/\sqrt{\max(1,d)})\). Indeed retention probability \(p=1/\sqrt{\max(1,d)}\) gives expected selected size \(pn\) and expected number of surviving triples \(p^3nd/3\le pn/3\). Thus a correct projection whose average collision degree is \(d=o(n^2/(\log n)^2)\) requires superpolynomial size. This condition can be used after any edge deletions retaining one pure witness for each target perfect matching.

## Scope

These theorems cover two different mechanisms. Low repeated-label overhead is enough even when other source matchings have arbitrarily many additional labels. A large collision-free target restriction is enough even when each label in that restriction repeats arbitrarily often. Neither property is guaranteed by the unrestricted Boolean projection contract.
