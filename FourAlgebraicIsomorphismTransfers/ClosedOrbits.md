# Finite-field tensor isomorphism as closed orbit comparison

## Statement and scope

Fix a prime $p$, and allow $q=p^e$ to vary with the input. Ordinary tensor isomorphism over $\mathbb F_q$ reduces in deterministic polynomial time to Zariski orbit-closure intersection over $k=\overline{\mathbb F_p}$, for explicit tensor systems with natural modules, their duals, and first Frobenius twists. Each output orbit is itself closed. The payload is unchanged, and a mode of dimension $n$ uses an additional $2en^2$ scalar coordinates. Equivalently one can include the marker factors inside symmetric powers of order $p$, so the additional arity is at most $p+1$, independent of the extension degree. The construction also works with a fixed mixed-variance tensor system as payload.

The target here is a positive-characteristic orbit-closure problem with the stated representations. Lysikov–Walter define their original TOCI class over $\mathbb C$. [Orbit-closure framework](https://arxiv.org/html/2411.04639v2#S2).

## The cyclic markers

For one original mode $V_0=k^n$, use auxiliary copies $V_1,\ldots,V_{e-1}$ and a product of $e$ general linear groups. Write $F(g)$ for entrywise $p$-power Frobenius and $V_i^{[p]}$ for the representation with matrix $F(g_i)$. At every edge of the cycle attach two inverse maps between $V_i^{[p]}$ and $V_{i+1}$, initially the identity matrices. Use the arrow from $V_{i+1}$ to $V_i^{[p]}$ to denote the first map. Under $g=(g_i)$ the resulting matrices of the arrow and its inverse are
$$
 M_i=F(g_i)g_{i+1}^{-1},\qquad M_i^{-1}=g_{i+1}F(g_i)^{-1},
$$
where indices are taken modulo $e$. The stabilizer of the marked identities is given by $g_{i+1}=F(g_i)$; the last equation gives $g_0=F^e(g_0)$. It projects bijectively to $\operatorname{GL}_n(\mathbb F_q)$ on the original mode. Repeat for each distinct mode and let the payload transform under the original modes. Thus equality of marked orbits is exactly equality of the finite-field iso orbits. Any finite-field isomorphism extends by the specified Frobenius powers.

The first twist embeds in $\operatorname{Sym}^p V_i$ as the span of the pure coordinate powers $v_j^p$. This is a subrepresentation by the binomial formula in characteristic $p$. The dual of the twist is likewise carried by the span of pure powers in $\operatorname{Sym}^p(V_i^*)$. Hence one can realize each arrow in a mixed tensor product of one symmetric-power factor and one linear factor, with the ordinary polynomial action on the symmetric-power factor. These spaces have dimension polynomial in $n$ for fixed $p$, and their pure-power conditions are closed linear conditions. The marker construction works directly in the twist basis, with matrices of order $n$.

## Why the orbit cannot degenerate

The affine variety of marker pairs $(M_i,N_i)$ with $M_iN_i=N_iM_i=I$ is closed. The map from the basis-change group to this variety, whose image records all markers, is finite. To see this in coordinates, the relations
$$
 F(g_i)=M_i g_{i+1}
$$
express each successive $g_i$ polynomially using $g_0$ and the $M_i,N_i$. After going once around the cycle they express $F^e(g_0)=B g_0$ for an invertible matrix $B$ computed from the marker maps and their Frobenius powers. Thus every $q$-th power of an entry of $g_0$ is a linear combination of entries with coefficients in the marker coordinate ring. Reducing any monomial with exponent at least $q$ in an entry lowers its degree in the entries, so finitely many bounded-exponent monomials span the coordinate algebra as a module. The same equation on determinants gives $\det(g_0)^{q-1}=\det B$; thus its determinant inverse belongs to the same finite algebra. Every other determinant inverse is then also in it. This proves finiteness without a choice of a point in any fiber. Taking products over modes preserves finiteness.

For a fixed payload $T$, take the graph of the regular map $g\mapsto gT$ inside the basis-change group times the affine payload space. The graph is closed. The product of the finite marker map with the identity on the payload space is finite, hence closed. It sends this graph to the full marked orbit of $T$. This orbit is therefore closed inside the inverse-pair variety times the payload space, and also inside the entire marked affine space. Consequently intersection of two marked closures is equivalent to equality of their orbits, which by the stabilizer computation is exact finite-field tensor isomorphism. Omitting the inverse arrows would lose the closed inverse-pair locus and this proof.

The same closure argument holds for each system point, even if its payload has nonclosed orbit by itself. Polynomial construction uses the input table and $e$ pairs of fixed identity markers per mode. The proof of closedness uses a finite morphism whose degree can be large, while the reduction itself constructs only its marked coordinate spaces and never expands the finite module basis. The Frobenius and inverse-pair arguments are classical. The contribution here is their bounded-arity, extension-uniform comparison construction. [Lang and Frobenius in algebraic groups](https://assets.cambridge.org/97805216/74546/excerpt/9780521674546_excerpt.pdf).

## Exact separating degree for the scalar case

For a single scalar payload $x$ and $n=1$, the action is a torus action on $2e+1$ coordinates. The weight of $x$ is $e_0$, and the two marker weights at edge $i$ are $\pm(p e_i-e_{i+1})$, where $e_i$ are the standard character coordinates. The points with all marker coordinates $1$ and payload $0$ or $1$ lie in disjoint closed orbits by the theorem.

An invariant polynomial is a sum of zero-weight monomials. Any of its monomials that involves $x^t$ with $t>0$ has a weight relation
$$
 t e_0=\sum_i w_i(p e_i-e_{i+1}),
$$
where $w_i$ is the difference of the inverse- and forward-marker exponents. In coordinates $j=1,\ldots,e-1$ this gives $w_{j-1}=p w_j$. The coordinate $0$ then gives $t=(p^e-1) w_{e-1}$. It follows that the least possible degree of a monomial involving $x$ is at least
$$
 (p^e-1)+\sum_{i=0}^{e-1} p^i = \frac{p(p^e-1)}{p-1}.
$$
It is attained by $x^{p^e-1}\prod_i N_i^{p^{e-1-i}}$, where $N_i$ are the inverse markers. Monomials with no payload have the same value on the two points, so the displayed bound is the exact least degree of a polynomial invariant separating them. This exhibits an exponential separating degree for the specific bounded-weight marker action, even though its scalar orbit test is elementary. The monomial method is standard for torus actions. [Torus orbit algorithms and monomial invariants](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.32).
