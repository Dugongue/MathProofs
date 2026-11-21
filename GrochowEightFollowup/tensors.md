# Laminar quantum functionals at border rank two and random tensor networks

## Every border-rank-two tensor is laminar-quantum-robust

Let \(T\) be a nonzero complex tensor of any order \(k\) and border rank at most two. The upper and lower quantum functionals agree on \(T\) for every weight distribution supported on a compatible family of bipartitions. More explicitly, on the \(k\)-party W tensor the common log-value is
\[
  \max_{p_1+\cdots+p_k=1,\ p_i\ge0}
  \ \sum_{\{S,S^c\}}\theta(\{S,S^c\})\,h\!\left(\sum_{i\in S}p_i\right),
\]
where \(h\) is binary entropy. This extends the four-party W result of the source paper to every order and gives the whole border-rank-two stratum. The general intrinsic characterization in GP140 remains open. The strict containment of the embedded-tensor semiring was already proved in the source. [Upper and lower quantum functionals, Definitions 2.11 and 2.15 and Theorem 4.17](https://arxiv.org/html/2604.18283v1)

### From a joint Schur block to a common excitation distribution

Put \(W_k=\sum_{i=1}^k |0\cdots 1_i\cdots 0\rangle\). For a supported bipartition choose the side \(S\) that omits a fixed root party. These sides form a laminar family, so their Schur isotypic projectors in the \(N\)-copy space commute. The projectors are linear combinations of operators permuting the \(N\) copies simultaneously on the parties of \(S\). In particular every projector \(P_S\) commutes with every joint eigenspace projection \(R_{\mathbf n}\) for the \(k\) leaf excitation counts across the \(N\) copies.

Suppose the product \(\prod_S P_S\) is nonzero on \(W_k^{\otimes N}\). Take a joint count sector \(\mathbf n=(n_1,\ldots,n_k)\) in which the output is nonzero. Each limb permutation preserves total excitation, so \(n_i\ge 0\) and \(\sum_i n_i=N\). Fix a supported side \(S\). By commutation, \(R_{\mathbf n}P_S W_k^{\otimes N}\ne0\). In the single-copy \(S\)-flattening the \(S\)-side Schmidt space lies in the span of \(|0_S\rangle\) and \(|W_S\rangle\). These basis vectors have \(S\)-excitation 0 and 1, respectively. That two-dimensional space is preserved on each copy when permuting copies.

Thus the \(P_S\) label has at most two rows, say \((N-r_S,r_S)\). On the two-dimensional Schmidt space, the corresponding Schur representation is \((\det)^{r_S}\otimes\mathrm{Sym}^{N-2r_S}\). For the diagonal torus that counts excitation, its weights are precisely \(r_S,\ldots,N-r_S\). The sum of the leaf counts in \(S\) must therefore satisfy
\[
 r_S\le \sum_{i\in S}n_i\le N-r_S .
\]
The same \(\mathbf n\) works for every supported cut. Write \(p_i=n_i/N\). Monotonicity of binary entropy on \([0,1/2]\) gives \(h(r_S/N)\le h(p(S))\) cut by cut. This bounds every admissible log-term in the upper quantum functional by the displayed maximum.

Conversely, diagonal scaling of \(W_k\) realizes the state \(\sum_i\sqrt{p_i}\,|0\cdots 1_i\cdots 0\rangle\) for any positive \(p\), with limit for zero entries. Its squared Schmidt coefficients across \(S\mid S^c\) are \(p(S)\) and \(1-p(S)\). The lower functional therefore attains the displayed supremum. Its general inequality with the upper functional gives equality.

### All nonzero tensors of border rank at most two

A point of the second secant variety of a Segre variety is on an honest secant line or on an embedded tangent line. For this assertion, let the two Segre points in a sequence of secant lines converge. At distinct limiting points one obtains the ordinary secant. At a common limiting point, any limiting secant direction belongs to the embedded tangent space, as follows by using a smooth local product chart and its first-order difference formula. Projective compactness supplies a limiting line and keeps its distinguished limit point on that line. The same argument applies to the Zariski secant closure over \(\mathbb C\), since the constructible set of secant points is Euclidean dense in its Zariski closure.

In the honest rank-two case strip the common one-dimensional factors. In every remaining factor the two summand vectors are independent, so the active tensor is a two-point diagonal tensor. In tangent form, choose the pure base point as the vacuum and write the tangent vector as a vacuum coefficient plus one perturbation per active factor. Strip inactive factors. If some perturbation is nonzero, a change of the second basis vector at an active factor absorbs the vacuum coefficient. The tensor is then \(W_a\) on its \(a\) active factors, or a pure tensor if no more than one is active. Restoring the one-dimensional factors turns a cut into its restriction on the active parties, with zero entropy for cuts that do not separate them. The surviving cuts are still compatible, and duplicate cut weights may be combined. The normalized diagonal, pure-tensor, and W formulas give all cases. In particular, the same conclusion holds whenever all bipartition flattening ranks are at most two, by the secant criterion. [Landsberg–Manivel](https://arxiv.org/abs/math/0311388)

## Equal restriction and degeneration rates on random uniform hypergraphs

Fix two nonzero order-\(k\) complex tensors \(T,S\), \(k\ge2\). Use either the all-orientations network convention, or symmetric local tensors so that assigning an orientation to an edge does not matter. For a simple \(k\)-uniform hypergraph \(H\) with edges, let \(a_{\mathrm R}(H)\) and \(a_{\mathrm D}(H)\) be the minimum global GHZ dimensions permitting restriction and degeneration from its \(T\)-network to its \(S\)-network. Rates below are per unordered edge in the all-orientations convention.

Take \(H_N\) from the binomial \(k\)-uniform model on \(N\) vertices with edge probability \(p_N>0\) satisfying \(\log (1/p_N)=o(\log N)\). Then almost surely both per-edge log rates converge and equal the optimal value over finite motifs:
\[
 \lim_{N\to\infty}\frac{\log_2 a_{\mathrm R}(H_N)}{|E(H_N)|}
 =
 \lim_{N\to\infty}\frac{\log_2 a_{\mathrm D}(H_N)}{|E(H_N)|}
 =
 \inf_{F}\frac{\log_2 a_{\mathrm D}(F)}{|E(F)|}.
\]
The infimum ranges over all finite nonempty simple \(k\)-uniform hypergraphs. The complete hypergraphs have this same rate in the stated conventions. Independence between different values of \(N\) is unnecessary. This permits dense random host sequences and densities tending to zero subpolynomially. It addresses a further family in Christandl's Open Problem 3. [Network model and Open Problem 3](https://doi.org/10.1093/pnasnexus/pgae254) · [Previous complete and balanced blow-up result](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblemSolutions/TENSOR-NETWORKS.md)

### Pack a fixed motif in a random host

Write \(s=|V(F)|\) and \(f=|E(F)|\). Remove isolated vertices of \(F\), which do not affect the assistance dimensions. For \(f=1\) the packing is exact. Otherwise \(s>k\). Form an auxiliary \(f\)-uniform hypergraph with vertex set \(E(H_N)\), with an auxiliary edge for each distinct image of the edge set of \(F\) under an injective embedding. A matching is an edge-disjoint packing of copies. Labeled embeddings cover each auxiliary edge the same number of times, namely \(|\operatorname{Aut}(F)|\), so it suffices to count embeddings.

Conditional on a particular potential host edge \(e\) being present, the expected embedding count through \(e\) equals
\[
 f k!\,(N-k)_{s-k}\,p_N^{f-1}.
\]
For a different potential host edge \(e'\), let \(u=|e'\setminus e|\ge 1\). Changing its presence affects the count by at most \(O_F(N^{s-k-u})\), by fixing the vertices of \(e\cup e'\) and choosing the images of the remaining vertices. There are \(O_k(N^u)\) choices for \(e'\) of each \(u\). Thus the sum of squares of the bounded differences is \(O_F(N^{2(s-k)-1})\). The bounded-differences inequality gives, for a relative error of \(N^{-1/8}\), a failure probability at most \(2\exp(-N^{3/4-o(1)})\) for this conditional count. A union bound over at most \(N^k\) possible edges and Borel–Cantelli establish uniform edge degrees \(D_N(1+o(1))\), with \(D_N=\Theta_F(N^{s-k}p_N^{f-1})\), for all sufficiently large \(N\). The number of host edges grows to infinity, by the binomial tail bound.

Two different host edges fix at least \(k+1\) vertices, so their auxiliary codegree is at most \(O_F(N^{s-k-1})=o(D_N)\) irrespective of host randomness. The nearly regular hypergraph matching theorem therefore packs copies of \(F\) covering \(1-o(1)\) of the random host edges. For complete hosts the degrees are exactly constant and the same deterministic codegree argument applies. The countably many fixed motifs are covered simultaneously on an event of probability one. [Pippenger–Spencer](https://doi.org/10.1016/0097-3165(89)90074-6)

### Assemble the rate bound

Fix \(F\) before taking \(N\) to infinity. Choose a one-parameter degeneration on \(F\) with assistance dimension \(a_{\mathrm D}(F)\); after division by its lowest power of the parameter its output polynomial has some fixed degree \(D_F\). Pack \(\nu\) edge-disjoint copies of \(F\), with \(r\) uncovered host edges. Tensor the local degeneration maps from all the copies, grouping maps at any shared vertices. Their normalized product has degree at most \(\nu D_F\). A single Vandermonde interpolation in the common parameter extracts the constant term, using an additional global GHZ index of size \(\nu D_F+1\). Independent GHZ labels for the copies cost \(a_{\mathrm D}(F)^\nu\). Preparing each leftover edge by a fixed rank decomposition contributes at most a fixed factor \(C_S\) per edge, allowing for all its orientations.

Consequently
\[
 a_{\mathrm R}(H_N)\le a_{\mathrm D}(F)^\nu(\nu D_F+1)C_S^r .
\]
Divide its logarithm by the number of host edges and pass to the limit using \(r=o(|E(H_N)|)\). The limsup is bounded by the motif's rate. The liminf of the degeneration rate is at least the infimum over all motifs because each host itself is one such hypergraph. Finally \(a_{\mathrm D}\le a_{\mathrm R}\), yielding the two limits claimed.

The Schur weight, secant, and random-network conclusions above are paper proofs.
